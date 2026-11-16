// marked-swift v4 — a fast drop-in for marked 18.1.3 (MIT, vendored untouched
// under vendor/marked/). One index-based pass over the source string builds
// the block tokens; each queued inline run is then scanned once more for its
// inline tokens; marked's own Parser (imported from the vendor bundle) turns
// the tokens into HTML. Nothing is kept between parse() calls: every call
// lexes its input from scratch.
//
// Only the default grammar is implemented: GFM on, breaks off, pedantic off.
// Block matching uses sticky regexes anchored at a cursor, so the source is
// never sliced or copied while blocks are found; lists are scanned line by
// line in a single loop; inline emphasis scans its closers once per pass.

import { Parser } from './vendor/marked/marked.esm.js';

// ---------- small string helpers ----------

// Drop every trailing copy of one character.
function stripTail(s, ch) {
  let n = s.length;
  while (n > 0 && s.charAt(n - 1) === ch) n--;
  return n === s.length ? s : s.slice(0, n);
}

// Drop trailing blank lines, keeping at most one trailing blank line.
function trimBlankTail(s) {
  const lines = s.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && /^[ \t]*$/.test(lines[end])) end--;
  if (lines.length - end <= 2) return s;
  return lines.slice(0, end + 1).join('\n');
}

// Expand tabs to the next multiple-of-4 column, counting from `col`.
function expandTabs(line, col) {
  let out = '';
  let c = col || 0;
  for (const ch of line) {
    if (ch === '\t') {
      const add = 4 - (c % 4);
      out += '    '.slice(0, add);
      c += add;
    } else {
      out += ch;
      c++;
    }
  }
  return out;
}

// Leading-whitespace expander for String.replace: one shared function
// instead of a fresh closure per line.
function expandLeadWs(ws) {
  return expandTabs(ws);
}

// Fold a link label the way definitions and references compare it: trim,
// collapse inner whitespace runs to one space, then Unicode case-fold.
function foldLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the bracket that closes an unbalanced run of `pair` (`()` or
// `[]`), skipping backslash escapes; -1 when balanced, -2 when too many
// openers are left over.
function findClose(str, pair) {
  if (str.indexOf(pair[0]) === -1 && str.indexOf(pair[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') {
      i++;
    } else if (str[i] === pair[0]) {
      level++;
    } else if (str[i] === pair[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  return level > 0 ? -2 : -1;
}

// Split one table row on unescaped pipes, trimming cells and honouring an
// expected column count.
function splitCells(row, count) {
  const marked = row.replace(/\|/g, (m, off, s) => {
    let escaped = false;
    let cur = off;
    while (--cur >= 0 && s[cur] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = marked.split(/ \|/);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  }
  return cells;
}

const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Resolve numeric character references outside code; a stray `&` that cannot
// start one becomes `&amp;` so it cannot join its neighbours into a new one.
function decodeNumRefs(text) {
  if (!NUM_REF.test(text)) return text;
  return text.replace(NUM_REF_OR_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

const UNESC_PUNCT = /\\([\p{P}\p{S}])/gu;

// Undo backslash escapes in front of punctuation.
function unescPunct(s) {
  return s.replace(UNESC_PUNCT, '$1');
}

// Remove a fenced block's own indentation from every line of its text.
function fenceIndent(raw, text) {
  const m = /^(\s+)(?:```)/.exec(raw);
  if (m === null) return text;
  const ind = m[1];
  return text.split('\n').map((line) => {
    const lead = /^\s+/.exec(line);
    if (lead === null) return line;
    return line.slice(Math.min(lead[0].length, ind.length));
  }).join('\n');
}

// ---------- pattern assembly ----------

// Build a pattern from a template regex and named fragments. A fragment's
// stray start-anchors are dropped: they only make sense at the very start
// of a pattern, never in the middle of one. A string key replaces its first
// occurrence, a global regex key every occurrence.
function build(template, subs, flags) {
  let s = typeof template === 'string' ? template : template.source;
  for (const [key, val] of subs) {
    let v = typeof val === 'string' ? val : val.source;
    v = v.replace(/(^|[^[])\^/g, '$1');
    s = key instanceof RegExp ? s.replace(key, () => v) : s.replace(key, () => v);
  }
  return new RegExp(s, flags);
}

// Sticky twin of an anchored pattern: the match must start at lastIndex.
function sticky(re) {
  const src = re.source.charAt(0) === '^' ? re.source.slice(1) : re.source;
  return new RegExp(src, re.flags + 'y');
}

function execAt(re, s, pos) {
  re.lastIndex = pos;
  return re.exec(s);
}

function testAt(re, s, pos) {
  re.lastIndex = pos;
  return re.test(s);
}

// ---------- small shared patterns ----------

const CODE_DEDENT = /^(?: {0,3}\t| {1,4})/gm;
const OUT_LINK = /\\([\[\]])/g;
const LEAD_WS = /^[ \t]+/;
const NON_SPACE = /[^ ]/;
const NL_GLOBAL = /\n/g;
const TAB_GLOBAL = /\t/g;
const BLANK_LINE = /^[ \t]*$/;
const DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const BQ_START = /^ {0,3}>/;
const BQ_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const BQ_SETEXT2 = /^ {0,3}>[ \t]?/gm;
const BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const LIST_NEST = /^ {1,4}(?=( {4})*[^ ])/g;
const LIST_TASK = /^\[[ xX]\][ \t]+\S/;
const LIST_TASK_STRIP = /^\[[ xX]\][ \t]+/;
const LIST_TASK_BOX = /\[[ xX]\]/;
const ANY_LINE = /\n.*\n/;
const HREF_BRACKETS = /^<(.*)>$/;
const TABLE_DELIM = /[:|]/;
const TABLE_ALIGN_TRIM = /^\||\| *$/g;
const TABLE_ROW_BLANK = /\n[ \t]*$/;
const TABLE_RIGHT = /^ *-+: *$/;
const TABLE_CENTER = /^ *:-+: *$/;
const TABLE_LEFT = /^ *:-+ *$/;
const START_A = /^<a /i;
const END_A = /^<\/a>/i;
const START_PRE = /^<(pre|code|kbd|script)(\s|>)/i;
const END_PRE = /^<\/(pre|code|kbd|script)(\s|>)/i;
const START_ANGLE = /^</;
const END_ANGLE = />$/;
const UNI_ALNUM = /[\p{L}\p{N}]/u;
const SETEXT_LINE = /^ {0,3}(?:=+|-+) *$/;

// Block tags that can open or close a raw HTML block (CommonMark §4.6).
const TAG_LIST = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

// Indent-capped patterns, cached per indent (0-3) the way the list scanner
// needs them. These are tested against single lines, so they stay anchored.
function indentCached(make) {
  const cache = [];
  return (n) => {
    const idx = Math.max(0, Math.min(3, n - 1));
    let re = cache[idx];
    if (!re) {
      re = make(idx);
      cache[idx] = re;
    }
    return re;
  };
}
const nextBulletRe = indentCached((i) => new RegExp('^ {0,' + i + '}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))'));
const hrAtRe = indentCached((i) => new RegExp('^ {0,' + i + '}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)'));
const fencesAtRe = indentCached((i) => new RegExp('^ {0,' + i + '}(?:```|~~~)'));
const headingAtRe = indentCached((i) => new RegExp('^ {0,' + i + '}#{1,6}(?:\\s|$)'));
const htmlAtRe = indentCached((i) => new RegExp('^ {0,' + i + '}(?:</?(?:' + TAG_LIST + ')(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)', 'i'));
const bqAtRe = indentCached((i) => new RegExp('^ {0,' + i + '}>'));

function listItemRe(bull) {
  return new RegExp('( {0,3}' + bull + ')((?:[\\t ][^\\n]*)?(?:\\n|$))', 'y');
}

// ---------- block grammar ----------

const NEWLINE = /^(?:[ \t]*(?:\n|$))+/;
const IND_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const ATX = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const LIST_OPEN = /^( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/;
const BLOCK_TEXT = /^[^\n]+/;

const FR_BULLET = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const FR_INDCODE = /(?: {4}| {0,3}\t)/;
const FR_FENCE = / {0,3}(?:`{3,}|~{3,})/;
const FR_BQ = / {0,3}>/;
const FR_ATX = / {0,3}#{1,6}(?:\s|$)/;
const FR_HTML_LINE = / {0,3}<[^\n>]+>\n/;
const FR_TABLE_LINE = / {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/;
const FR_FENCE_PARA = / {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)/;
const FR_HTML_PARA = / {0,3}(?:<\/?(?:TAG)(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)/;

// Setext heading: the underline may not be preceded by a line that opens
// another block, and the heading text itself may not contain one.
const LHEADING = build(
  /^(?!BULL |INDCODE|FENCE|BQ|ATX|HTML|TABLE)((?:.|\n(?!\s*?\n|BULL |FENCE|BQ|ATX|HR|HTML|TABLE))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/,
  [[/BULL/g, FR_BULLET], [/INDCODE/g, FR_INDCODE], [/FENCE/g, FR_FENCE], [/BQ/g, FR_BQ],
   [/ATX/g, FR_ATX], [/HR/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/], [/HTML/g, FR_HTML_LINE], [/TABLE/g, FR_TABLE_LINE]],
);

// GFM table: header line, delimiter row, then body rows until a line that
// opens another block.
const TABLE_GFM = build(
  /^ *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n|HR|ATX|BQ|CODE|FENCE|LIST|HTML).*(?:\n|$))*)\n*|$)/,
  [['HR', HR], ['ATX', FR_ATX], ['BQ', FR_BQ], ['CODE', /(?: {4}| {0,3}\t)[^\n]/],
   ['FENCE', FR_FENCE_PARA], ['LIST', / {0,3}(?:[*+-]|1[.)])[ \t]/], ['HTML', FR_HTML_PARA],
   ['TAG', TAG_LIST]],
);

// Paragraph (GFM): lines until one that opens another block. The blockquote
// variant lets any numbered bullet interrupt, and never lets a table in.
const PARA_TMPL = /^([^\n]+(?:\n(?!HR|ATX|SETEXT|BQ|FENCE|LIST|HTML|TABLE|[ \t]+\n)[^\n]+)*)/;
const PARA_GFM = build(PARA_TMPL, [
  ['HR', HR], ['ATX', FR_ATX], ['|SETEXT', ''], ['TABLE', TABLE_GFM], ['BQ', FR_BQ],
  ['FENCE', FR_FENCE_PARA], ['LIST', / {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]/],
  ['HTML', FR_HTML_PARA], ['TAG', TAG_LIST],
]);
const PARA_BQ = build(PARA_TMPL, [
  ['HR', HR], ['ATX', FR_ATX], ['|SETEXT', ''], ['|TABLE', ''], ['BQ', FR_BQ],
  ['FENCE', FR_FENCE_PARA], ['LIST', / {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/],
  ['HTML', FR_HTML_PARA], ['TAG', TAG_LIST],
]);

// Blockquote: `>` lines, with lazy continuation lines folded in.
const BQ = build(
  /^( {0,3}> ?(?:(?![ \t]*(?:\n|$))(PARA)|[^\n]*)(?:\n|$))+/,
  [['PARA', PARA_BQ]],
);

// Raw HTML block (CommonMark §4.6, types 1-7).
const HTML_BLOCK = build(
  /^ {0,3}(?:<(SCRIPT)[\s>][\s\S]*?(?:<\/\1>[^\n]*\n*|$)|COMMENT[^\n]*(\n+|$)|<\?[\s\S]*?(?:\?>[^\n]*\n*|$)|<![A-Z][\s\S]*?(?:>[^\n]*\n*|$)|<!\[CDATA\[[\s\S]*?(?:\]\]>[^\n]*\n*|$)|<\/?(TAG)(?:[ \t]+|\n|\/?>|$)[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:ATTR)*? *\/?>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$)|<\/[a-z][a-z0-9-]*\s*>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ \t]*)+\n|$))/i,
  [['SCRIPT', 'script|pre|style|textarea'], ['COMMENT', /<!--(?:-?>|[\s\S]*?(?:-->|$))/],
   ['TAG', TAG_LIST],
   ['ATTR', / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/]],
  'i',
);

// Link reference definition.
const DEF = build(
  /^ {0,3}\[(LABEL)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(TITLE))? *(?:\n+|$)/,
  [['LABEL', /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/],
   ['TITLE', /(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/]],
);

// ---------- inline grammar ----------

const ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const CODE_SPAN = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const PUNCT = /^((?![*_])[\s\p{P}\p{S}])/u;
const ANY_PUNCT_OUT = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;

const BLOCK_SKIP = build(/LINK|PRECODE-CODE|HTML/g, [
  ['LINK', /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/],
  ['PRECODE-', '(?<!`)()'],
  ['CODE', /(?<b>`+)[^`]+\k<b>(?!`)/],
  ['HTML', /<(?! )[^<>]*?>/],
], 'g');

const AUTOLINK = build(/^<(SCHEME:[^\s\x00-\x1f<>]*|EMAIL)>/, [
  ['SCHEME', /[a-zA-Z][a-zA-Z0-9+.-]{1,31}/],
  ['EMAIL', /[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])/],
]);

// An inline HTML tag, comment, processing instruction, declaration or CDATA.
const INLINE_TAG = build(
  /COMMENT|<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|<[a-zA-Z][a-zA-Z0-9-]*(?:ATTR)*?\s*\/?>|<\?[\s\S]*?\?>|<![a-zA-Z]+\s[\s\S]*?>|<!\[CDATA\[[\s\S]*?\]\]>/,
  [['COMMENT', /<!--(?:-?>|[\s\S]*?-->)/],
   ['ATTR', /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/]],
);

const BLOCK_LABEL = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
const INLINE_LABEL = build(
  /(?:\[(?:BRACKETS|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/,
  [['BRACKETS', /\[(?:\\[\s\S]|[^\[\]\\])*\]/]],
);

const LINK = build(/^!?\[(LABEL)\]\([ \t\n]*(HREF)(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)(TITLE))?[ \t\n]*\)/, [
  ['LABEL', INLINE_LABEL],
  ['HREF', /<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\))/],
  ['TITLE', /"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)/],
]);
const REFLINK = build(/^!?\[(LABEL)\]\[(REF)\]/, [['LABEL', INLINE_LABEL], ['REF', BLOCK_LABEL]]);
const NOLINK = build(/^!?\[(REF)\](?:\[\])?/, [['REF', BLOCK_LABEL]]);

const BOUND_BLOCK_LABEL = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}/;
const BOUND_INLINE_LABEL = build(
  /(?:[^\[\]\\`]*(?:\[(?:BRACKETS|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/,
  [['BRACKETS', /\[(?:\\[\s\S]|[^\[\]\\])*\]/]],
);
// Unanchored search form: every `[` in the run is a start position, but the
// label scan is bounded so a hopeless candidate cannot cost O(n^2).
const REFLINK_SEARCH = build('REFLINK|NOLINK(?!\\()', [
  ['REFLINK', build(/^!?\[(LABEL)\]\[(REF)\]/, [['LABEL', BOUND_INLINE_LABEL], ['REF', BOUND_BLOCK_LABEL]])],
  ['NOLINK', build(/^!?\[(REF)\](?:\[\])?/, [['REF', BOUND_BLOCK_LABEL]])],
], 'g');

const EXT_EMAIL = /[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/;
const URL = build(/EMAILPROTO|((?:PROTO):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|EMAIL/, [
  ['EMAILPROTO', build(/(?:mailto:EMAIL|xmpp:EMAIL(?:\/[A-Za-z0-9@.]+)?)/, [[/EMAIL/g, EXT_EMAIL]])],
  ['PROTO', /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/],
  ['EMAIL', /[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/],
]);
const BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
const DEL = /^(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/;

// Emphasis openers (GFM: `~` counts as punctuation around `*`/`_`).
const EM_STRONG_L = build(/(?:\*+(?:((?!\*)PUNCT)|([^\s*]))?)|_+(?:((?!_)PUNCT)|([^\s_]))?/, [
  [/PUNCT/g, /(?!~)[\p{P}\p{S}]/],
], 'u');
const DEL_L = build(/^~~?(?:((?!~)PUNCT)|[^\s~])/, [['PUNCT', /[\p{P}\p{S}]/]], 'u');

// Emphasis/strong closers, scanned with the `g` flag over a clipped window.
// Placeholders are replaced longest-first: PUNCTSPACE holds PUNCT.
const EM_R_AST = build(
  /^[^_*]*?__[^_*]*?\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\*)PUNCT(\*+)(?=[\s]|$)|NOTPUNCTSPACE(\*+)(?!\*)(?=PUNCTSPACE|$)|(?!\*)PUNCTSPACE(\*+)(?=NOTPUNCTSPACE)|[\s](\*+)(?!\*)(?=PUNCT)|(?!\*)PUNCT(\*+)(?!\*)(?=PUNCT)|NOTPUNCTSPACE(\*+)(?=NOTPUNCTSPACE)/,
  [[/NOTPUNCTSPACE/g, /(?:[^\s\p{P}\p{S}]|~)/], [/PUNCTSPACE/g, /(?!~)[\s\p{P}\p{S}]/],
   [/PUNCT/g, /(?!~)[\p{P}\p{S}]/]],
  'gu',
);
const EM_R_UND = build(
  /^[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)|[^_]+(?=[^_])|(?!_)PUNCT(_+)(?=[\s]|$)|NOTPUNCTSPACE(_+)(?!_)(?=PUNCTSPACE|$)|(?!_)PUNCTSPACE(_+)(?=NOTPUNCTSPACE)|[\s](_+)(?!_)(?=PUNCT)|(?!_)PUNCT(_+)(?!_)(?=PUNCT)/,
  [[/NOTPUNCTSPACE/g, /[^\s\p{P}\p{S}]/], [/PUNCTSPACE/g, /[\s\p{P}\p{S}]/],
   [/PUNCT/g, /[\p{P}\p{S}]/]],
  'gu',
);
const DEL_R = build(
  /^[^~]+(?=[^~])|(?!~)PUNCT(~~?)(?=[\s]|$)|NOTPUNCTSPACE(~~?)(?!~)(?=PUNCTSPACE|$)|(?!~)PUNCTSPACE(~~?)(?=NOTPUNCTSPACE)|[\s](~~?)(?!~)(?=PUNCT)|(?!~)PUNCT(~~?)(?!~)(?=PUNCT)|NOTPUNCTSPACE(~~?)(?=NOTPUNCTSPACE)/,
  [[/NOTPUNCTSPACE/g, /[^\s\p{P}\p{S}]/], [/PUNCTSPACE/g, /[\s\p{P}\p{S}]/],
   [/PUNCT/g, /[\p{P}\p{S}]/]],
  'gu',
);

// Plain inline text (GFM). The replacement order below is load-bearing: the
// first `protocol` hit lands inside the first `emailProtocol`, so the lone
// `protocol:\/\/` lookahead stays literal — reproduced exactly as upstream.
const INLINE_TEXT = build(
  /^(?:[^a-zA-Z0-9](?=EMAILPROTO)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|protocol:\/\/|WWWSTART|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=EMAILPROTO)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/,
  [['protocol', /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/],
   [/EMAILPROTO/g, /(?:mailto|xmpp):/],
   ['WWWSTART', /(?<![^\s*_~(])www\./]],
);

// Sticky twins for the cursor-based scanners.
const ESCAPE_S = sticky(ESCAPE);
const CODE_SPAN_S = sticky(CODE_SPAN);
const BR_S = sticky(BR);
const PUNCT_S = sticky(PUNCT);
const AUTOLINK_S = sticky(AUTOLINK);
const INLINE_TAG_S = sticky(INLINE_TAG);
const LINK_S = sticky(LINK);
const REFLINK_S = sticky(REFLINK);
const NOLINK_S = sticky(NOLINK);
const EM_STRONG_L_S = sticky(EM_STRONG_L);
const DEL_L_S = sticky(DEL_L);
const URL_S = sticky(URL);
const INLINE_TEXT_S = sticky(INLINE_TEXT);
const DEL_S = sticky(DEL);
const NEWLINE_S = sticky(NEWLINE);
const IND_CODE_S = sticky(IND_CODE);
const FENCES_S = sticky(FENCES);
const HR_S = sticky(HR);
const ATX_S = sticky(ATX);
const LIST_OPEN_S = sticky(LIST_OPEN);
const BLOCK_TEXT_S = sticky(BLOCK_TEXT);
const LHEADING_S = sticky(LHEADING);
const TABLE_GFM_S = sticky(TABLE_GFM);
const PARA_GFM_S = sticky(PARA_GFM);
const PARA_BQ_S = sticky(PARA_BQ);
const BQ_S = sticky(BQ);
const HTML_BLOCK_S = sticky(HTML_BLOCK);
const DEF_S = sticky(DEF);

// ---------- shared run state ----------

// Fresh for every parse() call: links, the inline queue and the inline
// scanner flags. Nothing here survives a call.
function newState() {
  return {
    links: Object.create(null),
    queue: [],
    top: true,
    inLink: false,
    inRawBlock: false,
    linkEmitted: false,
    linkParenPossible: true,
  };
}

// Queue an inline run; returns the token array the run will fill in later.
function queueInline(text, st) {
  const tokens = [];
  st.queue.push({ src: text, tokens });
  return tokens;
}

// ---------- inline masking and closer hints ----------

// Last `*` / `_` / `~` run that can close emphasis, strong or del: a run
// counts only when its predecessor is not ASCII whitespace or a line start.
function scanClosers(masked) {
  let star = -1, under = -1, tilde = -1;
  const len = masked.length;
  for (let i = 0; i < len; i++) {
    const ch = masked[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : masked[i - 1];
    let j = i + 1;
    while (j < len && masked[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') tilde = i;
      else if (ch === '*') star = i;
      else under = i;
    }
    i = j - 1;
  }
  return { star, under, tilde };
}

// Does this link text hold a link already? An image does not count: an image
// may hold a link, a link may not.
function linkInText(text, st) {
  if (!text.includes('[')) return false;
  for (const m of text.matchAll(BLOCK_SKIP)) {
    if (testAt(LINK_S, m[0], 0) && text.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of text.matchAll(REFLINK_SEARCH)) {
    const m0 = m[0];
    const refStart = m0.lastIndexOf('[');
    if (m0.charAt(0) === '!' || !Object.hasOwn(st.links, foldLabel(m0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(m0.slice(1, refStart - 1), st)) continue;
    return true;
  }
  return false;
}

// Hide links, code spans, HTML and backslash escapes from the emphasis
// scanner by replacing them with same-length filler, so a `*` inside one
// cannot open or close emphasis outside it.
function maskSrc(src, st) {
  let out = src;
  if (st.links && src.includes('[')) {
    const maskReflink = (m0) => {
      const refStart = m0.lastIndexOf('[');
      if (!Object.hasOwn(st.links, foldLabel(m0.slice(refStart + 1, -1)))) return m0;
      if (refStart > 1 && m0.charAt(0) !== '!') {
        const text = m0.slice(1, refStart - 1);
        if (linkInText(text, st)) {
          return '[' + text.replace(REFLINK_SEARCH, maskReflink)
            + '][' + 'a'.repeat(m0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(m0.length - 2) + ']';
    };
    out = out.replace(REFLINK_SEARCH, maskReflink);
  }
  out = out.replace(ANY_PUNCT_OUT, (m0, code, punct) => {
    if (punct) return '+'.repeat(m0.length);
    if (code) return code + m0.slice(code.length, -code.length).replace(/`/g, '+') + code;
    return m0;
  });
  out = out.replace(BLOCK_SKIP, (m0) => '[' + 'a'.repeat(m0.length - 2) + ']');
  return out;
}

// True when a `<...>` that starts inside a link label runs past the label's
// end, so the label is not really closed there.
function isLabelEndInsideToken(src, label, pos, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') {
      i++;
      continue;
    }
    if (label[i] === '`') {
      const code = execAt(CODE_SPAN_S, label, i);
      if (code) {
        i += code[0].length - 1;
        continue;
      }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(pos + labelStart + i);
    const token = execAt(INLINE_TAG_S, tokenSrc, 0) || execAt(AUTOLINK_S, tokenSrc, 0);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

// Build a link or image token, lexing its text inline. Returns undefined
// when the text already holds a link (links may not nest), so the caller
// falls through to plain text.
function outputLink(cap, href, title, raw, st) {
  const text = cap[1].replace(OUT_LINK, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const outerInLink = st.inLink;
  const outerEmitted = st.linkEmitted;
  const outerRaw = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  const tokens = inlineTokens(text, st);
  const textHasLink = st.linkEmitted;
  st.linkEmitted = outerEmitted;
  st.inLink = outerInLink;
  if (!isImage) {
    if (textHasLink) {
      st.inRawBlock = outerRaw;
      return undefined;
    }
    st.linkEmitted = true;
  }
  return {
    type: isImage ? 'image' : 'link',
    raw,
    href,
    title: title || null,
    text,
    tokens,
  };
}

// ---------- block lexer ----------

// Walk `src` from `pos`, appending block tokens. `clipped` is set when the
// caller is a blockquote continuation: its first paragraph may merge with
// the paragraph the previous chunk left open.
function lexBlocks(src, st, tokens, clipped) {
  let pos = 0;
  const end = src.length;
  let lastLen = Infinity;
  clipped = !!clipped;
  while (pos < end) {
    const remaining = end - pos;
    if (remaining >= lastLen) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    lastLen = remaining;
    let m;

    // blank lines
    if ((m = execAt(NEWLINE_S, src, pos))) {
      pos += m[0].length;
      const last = tokens[tokens.length - 1];
      if (m[0].length === 1 && last !== undefined) last.raw += '\n';
      else tokens.push({ type: 'space', raw: m[0] });
      continue;
    }

    // indented code; it cannot interrupt a paragraph, it joins it
    if ((m = execAt(IND_CODE_S, src, pos))) {
      const raw = trimBlankTail(m[0]);
      const text = raw.replace(CODE_DEDENT, '');
      const last = tokens[tokens.length - 1];
      if (last && (last.type === 'paragraph' || last.type === 'text')) {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + raw;
        last.text += '\n' + text;
        st.queue[st.queue.length - 1].src = last.text;
      } else {
        tokens.push({ type: 'code', raw, codeBlockStyle: 'indented', text });
      }
      pos += raw.length;
      continue;
    }

    // fenced code
    if ((m = execAt(FENCES_S, src, pos))) {
      const raw = m[0];
      const text = fenceIndent(raw, m[3] || '');
      const lang = m[2] ? m[2].trim().replace(UNESC_PUNCT, '$1') : m[2];
      tokens.push({ type: 'code', raw, lang, text });
      pos += raw.length;
      continue;
    }

    // ATX heading
    if ((m = execAt(ATX_S, src, pos))) {
      let text = m[2].trim();
      if (text.endsWith('#')) {
        const trimmed = stripTail(text, '#');
        if (!trimmed || /[ \t]$/.test(trimmed)) text = trimmed.trim();
      }
      const raw = stripTail(m[0], '\n');
      tokens.push({ type: 'heading', raw, depth: m[1].length, text, tokens: queueInline(text, st) });
      pos += raw.length;
      continue;
    }

    // thematic break
    if ((m = execAt(HR_S, src, pos))) {
      const raw = stripTail(m[0], '\n');
      tokens.push({ type: 'hr', raw });
      pos += raw.length;
      continue;
    }

    // blockquote
    {
      const next = tryBlockquote(src, pos, st, tokens);
      if (next >= 0) {
        pos = next;
        continue;
      }
    }

    // list
    {
      const next = tryList(src, pos, st, tokens);
      if (next >= 0) {
        pos = next;
        continue;
      }
    }

    // raw HTML block
    if ((m = execAt(HTML_BLOCK_S, src, pos))) {
      const raw = trimBlankTail(m[0]);
      tokens.push({
        type: 'html',
        block: true,
        raw,
        pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style',
        text: raw,
      });
      pos += raw.length;
      continue;
    }

    // link reference definition; it cannot interrupt a paragraph either
    if ((m = execAt(DEF_S, src, pos))) {
      if (!(m[2].charAt(0) !== '<' && findClose(m[2], '()') !== -1)) {
        const tag = foldLabel(m[1]);
        const href = m[2] ? m[2].replace(HREF_BRACKETS, '$1').replace(UNESC_PUNCT, '$1') : '';
        const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(UNESC_PUNCT, '$1') : m[3];
        const raw = stripTail(m[0], '\n');
        const last = tokens[tokens.length - 1];
        if (last && (last.type === 'paragraph' || last.type === 'text')) {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + raw;
          last.text += '\n' + raw;
          st.queue[st.queue.length - 1].src = last.text;
        } else {
          if (!Object.hasOwn(st.links, tag)) st.links[tag] = { href, title };
          tokens.push({ type: 'def', tag, raw, href, title });
        }
        pos += raw.length;
        continue;
      }
    }

    // GFM table
    if ((m = execAt(TABLE_GFM_S, src, pos))) {
      const tok = tryTable(m, st);
      if (tok) {
        tokens.push(tok);
        pos += tok.raw.length;
        continue;
      }
    }

    // setext heading
    if ((m = execAt(LHEADING_S, src, pos))) {
      const text = m[1].trim();
      const raw = stripTail(m[0], '\n');
      tokens.push({
        type: 'heading',
        raw,
        depth: m[2].charAt(0) === '=' ? 1 : 2,
        text,
        tokens: queueInline(text, st),
      });
      pos += raw.length;
      continue;
    }

    // paragraph (only at the top level of a block run)
    if (st.top && (m = execAt(PARA_GFM_S, src, pos))) {
      const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
      const tok = { type: 'paragraph', raw: m[0], text, tokens: queueInline(text, st) };
      const last = tokens[tokens.length - 1];
      if (clipped && last && last.type === 'paragraph') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        last.text += '\n' + tok.text;
        st.queue.pop();
        st.queue[st.queue.length - 1].src = last.text;
      } else {
        tokens.push(tok);
      }
      clipped = false;
      pos += m[0].length;
      continue;
    }

    // leftover line of text
    if ((m = execAt(BLOCK_TEXT_S, src, pos))) {
      const tok = { type: 'text', raw: m[0], text: m[0], tokens: queueInline(m[0], st) };
      const last = tokens[tokens.length - 1];
      if (last && last.type === 'text') {
        last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        last.text += '\n' + tok.text;
        st.queue.pop();
        st.queue[st.queue.length - 1].src = last.text;
      } else {
        tokens.push(tok);
      }
      pos += m[0].length;
      continue;
    }

    throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  st.top = true;
  return tokens;
}

// GFM table from a table match: header, alignments and body rows, or null
// when the delimiter row is not a delimiter or the columns do not line up.
function tryTable(m, st) {
  if (!TABLE_DELIM.test(m[2])) return null;
  const headers = splitCells(m[1]);
  const aligns = m[2].replace(TABLE_ALIGN_TRIM, '').split('|');
  const rows = m[3] && m[3].trim() ? m[3].replace(TABLE_ROW_BLANK, '').split('\n') : [];
  if (headers.length !== aligns.length) return null;
  const item = {
    type: 'table',
    raw: stripTail(m[0], '\n'),
    header: [],
    align: [],
    rows: [],
  };
  for (const align of aligns) {
    if (TABLE_RIGHT.test(align)) item.align.push('right');
    else if (TABLE_CENTER.test(align)) item.align.push('center');
    else if (TABLE_LEFT.test(align)) item.align.push('left');
    else item.align.push(null);
  }
  for (let i = 0; i < headers.length; i++) {
    item.header.push({
      text: headers[i],
      tokens: queueInline(headers[i], st),
      header: true,
      align: item.align[i],
    });
  }
  for (const row of rows) {
    item.rows.push(splitCells(row, item.header.length).map((cell, i) => ({
      text: cell,
      tokens: queueInline(cell, st),
      header: false,
      align: item.align[i],
    })));
  }
  return item;
}

// ---------- blockquote ----------

// A blockquote token starting at `pos`, or null. Lazy lines join the quote;
// a continuation after a nested blockquote or list is folded into it.
function blockquoteToken(src, pos, st) {
  const m = execAt(BQ_S, src, pos);
  if (!m) return null;
  let lines = stripTail(m[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const inner = [];
  while (lines.length > 0) {
    let inBq = false;
    const current = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (BQ_START.test(lines[i])) {
        current.push(lines[i]);
        inBq = true;
      } else if (!inBq) {
        current.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);
    const currentRaw = current.join('\n');
    const currentText = currentRaw
      .replace(BQ_MARKER_WS, (_, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(BQ_SETEXT, '\n    $1')
      .replace(BQ_SETEXT2, '');
    raw = raw ? raw + '\n' + currentRaw : currentRaw;
    text = text ? text + '\n' + currentText : currentText;
    const top = st.top;
    st.top = true;
    lexBlocks(currentText, st, inner, true);
    st.top = top;
    if (lines.length === 0) break;
    const lastToken = inner[inner.length - 1];
    if (lastToken && (lastToken.type === 'code' || lastToken.type === 'heading'
      || lastToken.type === 'hr' || lastToken.type === 'html' || lastToken.type === 'table')) {
      break;
    } else if (lastToken && lastToken.type === 'blockquote') {
      const oldToken = lastToken;
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(BQ_SETEXT2, '');
      const rebuilt = blockquoteToken(newText, 0, st);
      if (!rebuilt) break;
      const newToken = rebuilt.tok;
      inner[inner.length - 1] = newToken;
      const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = raw + '\n' + consumed.join('\n');
      text = text.substring(0, text.length - oldToken.text.length) + newToken.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && BQ_START.test(lines[0])) continue;
      break;
    } else if (lastToken && lastToken.type === 'list') {
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const rebuilt = listToken(newText, 0, st);
      if (!rebuilt) break;
      const newToken = rebuilt.tok;
      inner[inner.length - 1] = newToken;
      const consumedCount = newToken.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
        : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw = raw + '\n' + consumed;
        text = text + '\n' + consumed;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
  }
  return { tok: { type: 'blockquote', raw, tokens: inner, text }, next: raw.length };
}

function tryBlockquote(src, pos, st, tokens) {
  const r = blockquoteToken(src, pos, st);
  if (!r) return -1;
  tokens.push(r.tok);
  return pos + r.next;
}

// ---------- list ----------

// A list token starting at `pos`, or null when no item follows the bullet.
function listToken(src, pos, st) {
  const m = execAt(LIST_OPEN_S, src, pos);
  if (!m) return null;
  const startPos = pos;
  let cur = pos;
  const end = src.length;
  const lineAt = (p) => {
    const n = src.indexOf('\n', p);
    return n === -1 ? src.slice(p) : src.slice(p, n);
  };
  let bull = m[1].trim();
  const isOrdered = bull.length > 1;
  const list = {
    type: 'list',
    raw: '',
    ordered: isOrdered,
    start: isOrdered ? +bull.slice(0, -1) : '',
    loose: false,
    items: [],
  };
  bull = isOrdered ? '\\d{1,9}\\'.concat(bull.slice(-1)) : '\\'.concat(bull);
  const itemRe = listItemRe(bull);
  let endsWithBlank = false;
  while (cur < end) {
    let endEarly = false;
    let itemContents = '';
    const cap = execAt(itemRe, src, cur);
    if (!cap) break;
    if (testAt(HR_S, src, cur)) break;
    const itemStart = cur;
    cur += cap[0].length;
    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(LEAD_WS, (ws) => expandTabs(ws, bulletIndent));
    const nextLine = lineAt(cur);
    let blankLine = !line.trim();
    let indent;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(NON_SPACE);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }
    if (blankLine && BLANK_LINE.test(nextLine)) {
      cur += nextLine.length + 1;
      endEarly = true;
    }
    if (!endEarly) {
      const nextBull = nextBulletRe(indent);
      const hrR = hrAtRe(indent);
      const fencesR = fencesAtRe(indent);
      const headR = headingAtRe(indent);
      const htmlR = htmlAtRe(indent);
      const bqR = bqAtRe(indent);
      while (cur < end) {
        const rawLine = lineAt(cur);
        const nextLine2 = rawLine;
        const c0 = nextLine2.charCodeAt(0);
        const withoutTabs = (c0 === 9 || c0 === 32)
          ? nextLine2.replace(LEAD_WS, expandLeadWs)
          : nextLine2;
        if (fencesR.test(nextLine2)) break;
        if (headR.test(nextLine2)) break;
        if (htmlR.test(nextLine2)) break;
        if (bqR.test(nextLine2)) break;
        if (nextBull.test(nextLine2)) break;
        if (hrR.test(nextLine2)) break;
        const nsIdx = withoutTabs.search(NON_SPACE);
        const isBlank = nsIdx === -1;
        if (nsIdx >= indent || isBlank) {
          itemContents += '\n' + withoutTabs.slice(indent);
        } else {
          if (blankLine) break;
          if (line.replace(TAB_GLOBAL, '    ').search(NON_SPACE) >= 4) break;
          if (fencesR.test(line)) break;
          if (headR.test(line)) break;
          if (htmlR.test(line)) break;
          if (hrR.test(line)) break;
          const setextCont = SETEXT_LINE.test(nextLine2)
            && testAt(LHEADING_S, line + '\n' + nextLine2, 0);
          const cont = setextCont
            ? '    ' + withoutTabs.replace(/^ {0,3}/, '')
            : nextLine2;
          itemContents += '\n' + cont;
        }
        blankLine = isBlank;
        cur += rawLine.length + 1;
        line = withoutTabs.slice(indent);
      }
    }
    const raw = src.slice(itemStart, cur);
    if (!list.loose) {
      if (endsWithBlank) list.loose = true;
      else if (DOUBLE_BLANK.test(raw)) endsWithBlank = true;
    }
    list.items.push({
      type: 'list_item',
      raw,
      task: LIST_TASK.test(itemContents),
      loose: false,
      text: itemContents,
      tokens: [],
    });
  }
  const lastItem = list.items[list.items.length - 1];
  if (!lastItem) return null;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = src.slice(startPos, cur).trimEnd();
  for (const item of list.items) {
    st.top = false;
    item.tokens = lexBlocks(item.text, st, []);
    if (!list.loose) {
      const spacers = item.tokens.filter((t) => t.type === 'space');
      list.loose = spacers.length > 0 && spacers.some((t) => ANY_LINE.test(t.raw));
    }
  }
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && itemToken && (itemToken.type === 'text' || itemToken.type === 'paragraph')) {
      item.text = item.text.replace(LIST_TASK_STRIP, '');
      itemToken.raw = itemToken.raw.replace(LIST_TASK_STRIP, '');
      itemToken.text = itemToken.text.replace(LIST_TASK_STRIP, '');
      for (let i = st.queue.length - 1; i >= 0; i--) {
        if (LIST_TASK.test(st.queue[i].src)) {
          st.queue[i].src = st.queue[i].src.replace(LIST_TASK_STRIP, '');
          break;
        }
      }
      const taskRaw = LIST_TASK_BOX.exec(item.raw);
      if (taskRaw) {
        const checkbox = {
          type: 'checkbox',
          raw: taskRaw[0] + ' ',
          checked: taskRaw[0] !== '[ ]',
        };
        item.checked = checkbox.checked;
        if (list.loose) {
          if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type)
            && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
            item.tokens[0].raw = checkbox.raw + item.tokens[0].raw;
            item.tokens[0].text = checkbox.raw + item.tokens[0].text;
            item.tokens[0].tokens.unshift(checkbox);
          } else {
            item.tokens.unshift({
              type: 'paragraph',
              raw: checkbox.raw,
              text: checkbox.raw,
              tokens: [checkbox],
            });
          }
        } else {
          item.tokens.unshift(checkbox);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const token of item.tokens) {
        if (token.type === 'text') token.type = 'paragraph';
      }
    }
  }
  return { tok: list, next: list.raw.length };
}

function tryList(src, pos, st, tokens) {
  const r = listToken(src, pos, st);
  if (!r) return -1;
  tokens.push(r.tok);
  return pos + r.next;
}

// ---------- inline lexer ----------

// Lex one inline run into `tokens` (a fresh array when omitted). The
// paren-presence flag is saved and restored so a nested run (a link label)
// does not disturb the run around it.
function inlineTokens(src, st, tokens) {
  tokens = tokens || [];
  const prevFlag = st.linkParenPossible;
  st.linkParenPossible = prevFlag && src.includes(')');
  try {
    return inlineInner(src, st, tokens);
  } finally {
    st.linkParenPossible = prevFlag;
  }
}

function inlineInner(src, st, tokens) {
  const hasDelims = src.includes('*') || src.includes('_') || src.includes('~');
  const masked = hasDelims ? maskSrc(src, st) : src;
  const closers = hasDelims ? scanClosers(masked) : { star: -1, under: -1, tilde: -1 };
  return inlineLoop(src, masked, closers, st, tokens);
}

// First characters that can start an extended autolink (scheme, www., or
// an email address): letters, digits, '.', '_', '+' and '-'.
const URL_START = new Uint8Array(128);
for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._+-') {
  URL_START[c.charCodeAt(0)] = 1;
}

function inlineLoop(src, masked, closers, st, tokens) {
  let pos = 0;
  const end = src.length;
  let lastLen = Infinity;
  let keepPrev = false;
  let prevChar = '';
  while (pos < end) {
    const remaining = end - pos;
    if (remaining >= lastLen) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    lastLen = remaining;
    if (!keepPrev) prevChar = '';
    keepPrev = false;
    let m;
    let tok;
    const ch = src.charCodeAt(pos);

    // escape
    if (ch === 92 && (m = execAt(ESCAPE_S, src, pos))) {
      tokens.push({ type: 'escape', raw: m[0], text: m[1] });
      pos += m[0].length;
      continue;
    }

    // tag
    if (ch === 60 && (m = execAt(INLINE_TAG_S, src, pos))) {
      if (!st.inLink && START_A.test(m[0])) st.inLink = true;
      else if (st.inLink && END_A.test(m[0])) st.inLink = false;
      if (!st.inRawBlock && START_PRE.test(m[0])) st.inRawBlock = true;
      else if (st.inRawBlock && END_PRE.test(m[0])) st.inRawBlock = false;
      tokens.push({
        type: 'html',
        raw: m[0],
        inLink: st.inLink,
        inRawBlock: st.inRawBlock,
        block: false,
        text: m[0],
      });
      pos += m[0].length;
      continue;
    }

    // link
    if ((ch === 91 || ch === 33) && (tok = tryLink(src, pos, st))) {
      tokens.push(tok);
      pos += tok.raw.length;
      continue;
    }

    // reflink / nolink
    if (ch === 91 || ch === 33) {
      const r = tryReflink(src, pos, st);
      if (r) {
        if (r.tok.type === 'text') {
          const last = tokens[tokens.length - 1];
          if (last && last.type === 'text') {
            last.raw += r.tok.raw;
            last.text += r.tok.text;
          } else {
            tokens.push(r.tok);
          }
        } else {
          tokens.push(r.tok);
        }
        pos += r.next;
        continue;
      }
    }

    // em & strong
    if ((ch === 42 || ch === 95) && (tok = tryEmStrong(src, pos, masked, closers, prevChar, st))) {
      tokens.push(tok);
      pos += tok.raw.length;
      continue;
    }

    // code span
    if (ch === 96 && (m = execAt(CODE_SPAN_S, src, pos))) {
      let text = m[2].replace(NL_GLOBAL, ' ');
      const hasNonSpace = NON_SPACE.test(text);
      const hasSpaceBoth = text.startsWith(' ') && text.endsWith(' ');
      if (hasNonSpace && hasSpaceBoth) text = text.substring(1, text.length - 1);
      tokens.push({ type: 'codespan', raw: m[0], text });
      pos += m[0].length;
      continue;
    }

    // hard break
    if ((ch === 32 || ch === 92) && (m = execAt(BR_S, src, pos))) {
      tokens.push({ type: 'br', raw: m[0] });
      pos += m[0].length;
      continue;
    }

    // strikethrough
    if (ch === 126 && (tok = tryDel(src, pos, masked, closers, prevChar, st))) {
      tokens.push(tok);
      pos += tok.raw.length;
      continue;
    }

    // autolink
    if (ch === 60 && (m = execAt(AUTOLINK_S, src, pos))) {
      let text;
      let href;
      if (m[2] === '@') {
        text = m[1];
        href = 'mailto:' + text;
      } else {
        text = m[1];
        href = text;
      }
      tokens.push({
        type: 'link',
        raw: m[0],
        text,
        href,
        autolink: true,
        tokens: [{ type: 'text', raw: text, text }],
      });
      pos += m[0].length;
      continue;
    }

    // extended autolink (www / scheme / email), never inside a link
    if (!st.inLink && URL_START[ch] === 1 && (tok = tryUrl(src, pos, st))) {
      tokens.push(tok);
      pos += tok.raw.length;
      continue;
    }

    // plain text
    if ((m = execAt(INLINE_TEXT_S, src, pos))) {
      const escaped = st.inRawBlock;
      const textTok = {
        type: 'text',
        raw: m[0],
        text: escaped ? m[0] : decodeNumRefs(m[0]),
        escaped,
      };
      if (textTok.raw.slice(-1) !== '_') prevChar = textTok.raw.slice(-1);
      keepPrev = true;
      const last = tokens[tokens.length - 1];
      if (last && last.type === 'text') {
        last.raw += textTok.raw;
        last.text += textTok.text;
      } else {
        tokens.push(textTok);
      }
      pos += m[0].length;
      continue;
    }

    throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  return tokens;
}

// Inline link or image starting at `pos`, or null.
function tryLink(src, pos, st) {
  if (st.linkParenPossible === false) return null;
  const m = execAt(LINK_S, src, pos);
  if (!m) return null;
  const labelStart = m[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, m[1], pos, labelStart)) return null;
  const trimmedUrl = m[2].trim();
  if (START_ANGLE.test(trimmedUrl)) {
    if (!END_ANGLE.test(trimmedUrl)) return null;
    const rtrimSlash = stripTail(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return null;
  } else {
    const lastParen = findClose(m[2], '()');
    if (lastParen === -2) return null;
    if (lastParen > -1) {
      const start = m[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + m[1].length + lastParen;
      m[2] = m[2].substring(0, lastParen);
      m[0] = m[0].substring(0, linkLen).trim();
      m[3] = '';
    }
  }
  const unescaped = stripTail(m[0].slice(0, -1), '\\');
  if ((m[0].length - unescaped.length) % 2 === 0) return null;
  let href = m[2];
  const title = m[3] ? m[3].slice(1, -1) : '';
  href = href.trim();
  if (START_ANGLE.test(href)) href = href.slice(1, -1);
  return outputLink(
    m,
    href ? href.replace(UNESC_PUNCT, '$1') : href,
    title ? title.replace(UNESC_PUNCT, '$1') : title,
    m[0],
    st,
  );
}

// Reference link (or shortcut) starting at `pos`, or null. When the label
// has no definition it yields a single literal character of text instead.
function tryReflink(src, pos, st) {
  const m = execAt(REFLINK_S, src, pos) || execAt(NOLINK_S, src, pos);
  if (!m) return null;
  const labelStart = m[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src, m[1], pos, labelStart)) return null;
  const link = st.links[foldLabel(m[2] || m[1])];
  if (!link) {
    const ch = m[0].charAt(0);
    return { tok: { type: 'text', raw: ch, text: ch }, next: 1 };
  }
  const out = outputLink(m, link.href, link.title, m[0], st);
  if (!out) return null;
  return { tok: out, next: m[0].length };
}

// Emphasis or strong emphasis starting at `pos`, or null. The opener's
// whole delimiter run decides flanking (rules 9-10); the closer scan walks
// the masked window once.
function tryEmStrong(src, pos, masked, closers, prevChar, st) {
  const m = execAt(EM_STRONG_L_S, src, pos);
  if (!m) return null;
  if (!m[1] && !m[2] && !m[3] && !m[4]) return null;
  const delim = m[0][0];
  const midRun = prevChar === delim;
  const srcStart = pos;
  let runStart = srcStart;
  while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
  const runPrevChar = [...masked.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_'
    || !!PUNCT.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!PUNCT.exec(prevChar);
  if (m[4] && prevChar.match(UNI_ALNUM)) return null;
  const nextChar = m[1] || m[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const lLength = [...m[0]].length - 1;
    let rDelim;
    let rLength;
    let delimTotal = lLength;
    let midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim()
      && (!!nextChar || (delim === '*' && !runPrevPunct));
    if (delim !== '*' && delim !== '_') return null;
    const endReg = delim === '*' ? EM_R_AST : EM_R_UND;
    const lastCloser = delim === '*' ? closers.star : closers.under;
    const windowStart = pos + lLength;
    if (lastCloser < windowStart) return null;
    const window = masked.slice(windowStart);
    const lastInWindow = lastCloser - windowStart;
    endReg.lastIndex = 0;
    let match;
    while ((match = endReg.exec(window)) !== null) {
      if (match.index > lastInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = [...rDelim].length;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      } else if (match[5] || match[6] || openerCanClose) {
        if (midRun && (match[5] || match[6])) break;
        if (runLength % 3 && !((runLength + rLength) % 3)) {
          midDelimTotal += rLength;
          continue;
        }
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal + midDelimTotal);
      const lastCharLength = [...match[0]][0].length;
      const raw = src.slice(pos, pos + lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: inlineTokens(text, st) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: inlineTokens(text, st) };
    }
  }
  return null;
}

// Strikethrough starting at `pos`, or null.
function tryDel(src, pos, masked, closers, prevChar, st) {
  const m = execAt(DEL_L_S, src, pos);
  if (!m) return null;
  const nextChar = m[1] || '';
  if (!nextChar || !prevChar || PUNCT.exec(prevChar)) {
    const lLength = [...m[0]].length - 1;
    let rDelim;
    let rLength;
    let delimTotal = lLength;
    const windowStart = pos + lLength;
    if (closers.tilde < windowStart) return null;
    const window = masked.slice(windowStart);
    const lastInWindow = closers.tilde - windowStart;
    DEL_R.lastIndex = 0;
    let match;
    while ((match = DEL_R.exec(window)) !== null) {
      if (match.index > lastInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = [...rDelim].length;
      if (rLength !== lLength) continue;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal);
      const lastCharLength = [...match[0]][0].length;
      const raw = src.slice(pos, pos + lLength + match.index + lastCharLength + rLength);
      const text = raw.slice(lLength, -lLength);
      return { type: 'del', raw, text, tokens: inlineTokens(text, st) };
    }
  }
  return null;
}

// Extended autolink (bare URL or email) starting at `pos`, or null.
function tryUrl(src, pos, st) {
  const m = execAt(URL_S, src, pos);
  if (!m) return null;
  let text;
  let href;
  if (m[2] === '@') {
    text = m[0];
    href = 'mailto:' + text;
  } else {
    let prevCapZero;
    do {
      prevCapZero = m[0];
      m[0] = BACKPEDAL.exec(m[0])?.[0] ?? '';
    } while (prevCapZero !== m[0]);
    text = m[0];
    if (m[1] === 'www.') href = 'http://' + m[0];
    else href = m[0];
  }
  return {
    type: 'link',
    raw: m[0],
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
  };
}

// ---------- entry point ----------

// The HTML marked 18.1.3 renders for `markdown`, with marked's defaults.
export function parse(markdown) {
  const st = newState();
  const src = markdown.replace(/\r\n|\r/g, '\n');
  const tokens = lexBlocks(src, st, []);
  for (let i = 0; i < st.queue.length; i++) {
    st.inRawBlock = false;
    const job = st.queue[i];
    inlineTokens(job.src, st, job.tokens);
  }
  return new Parser().parse(tokens);
}
