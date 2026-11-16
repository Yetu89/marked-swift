// Fast drop-in for marked 18.1.3 with its default options (GFM on,
// breaks off, pedantic off). The block and inline lexers below are an
// index-based rewrite: every grammar rule is applied as a sticky regex
// anchored at the current position, blocks are dispatched on their first
// character, and table / setext rules are only attempted after a cheap
// look at the next line. Tokens are shaped exactly like marked's, and
// rendering is done by marked's own Parser/Renderer from the vendored
// build. A parse() call keeps nothing from any earlier call.
import { Parser } from './vendor/marked/marked.esm.js';

// ---------- small string helpers ----------

function rtrim(str, c, invert) {
  const l = str.length;
  if (l === 0) return '';
  let n = 0;
  while (n < l) {
    const ch = str.charAt(l - n - 1);
    if (ch === c && !invert) n++;
    else if (ch !== c && invert) n++;
    else break;
  }
  return str.slice(0, l - n);
}

function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && /^[ \t]*$/.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

function normalizeLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

function findClosingBracket(str, b) {
  if (str.indexOf(b[0]) === -1 && str.indexOf(b[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === b[0]) level++;
    else if (str[i] === b[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  if (level > 0) return -2;
  return -1;
}

function expandTabs(line, indent) {
  let col = indent || 0;
  let out = '';
  for (const ch of line) {
    if (ch === '\t') {
      const added = 4 - (col % 4);
      out += ' '.repeat(added);
      col += added;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

const FIND_PIPE = /\|/g;
const SPLIT_PIPE = / \|/;
const SLASH_PIPE = /\\\|/g;
function splitCells(tableRow, count) {
  const row = tableRow.replace(FIND_PIPE, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(SPLIT_PIPE);
  let i = 0;
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(SLASH_PIPE, '|');
  return cells;
}

const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
function decodeNumericCharacterReferences(text) {
  if (!NUM_REF.test(text)) return text;
  return text.replace(NUM_REF_OR_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? Number.parseInt(hex, 16) : Number.parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

// One scan of a masked inline source for the last emphasis, strong and
// strikethrough closers, shared by every opener in the pass.
function scanClosers(src) {
  let ast = -1;
  let und = -1;
  let del = -1;
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') del = i;
      else if (ch === '*') ast = i;
      else und = i;
    }
    i = j - 1;
  }
  return { src, ast, und, del };
}

// ---------- grammar: pattern sources ----------
// `rep` splices one pattern into another the way marked's edit() does:
// a leading ^ of the inserted pattern is dropped.
const CARET = /(^|[^\[])\^/g;
function rep(src, name, val) {
  const vs = typeof val === 'string' ? val : val.source;
  return src.replace(name, vs.replace(CARET, '$1'));
}
// Sticky version of a pattern: drop every start-of-string anchor (at the
// pattern start or after an alternation bar) and anchor at lastIndex.
function sticky(src, flags) {
  return new RegExp(src.replace(/(^|\|)\^/g, '$1'), (flags || '') + 'y');
}
function plain(src, flags) {
  return new RegExp(src, flags);
}

const TAG = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';
const COMMENT = '<!--(?:-?>|[\\s\\S]*?(?:-->|$))';
const BULLET = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const HR_SRC = '^ {0,3}((?:-[\\t ]*){3,}|(?:_[\\t ]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const HR_NC_SRC = " {0,3}(?:(?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\n+|$)";
const HEADING_SRC = ' {0,3}#{1,6}(?:\\s|$)';
const FENCES_SRC = ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)';
const BLOCKQUOTE_SRC = ' {0,3}>';
const CODE_SRC = '(?: {4}| {0,3}\\t)[^\\n]';
const HTML_START_SRC = ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';
const LIST_INT_TOP = ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]';
const LIST_INT_BQ = ' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)';

// Block grammar (GFM).
const NEWLINE_SRC = '^(?:[ \\t]*(?:\\n|$))+';
const BLOCK_CODE_SRC = '^((?: {4}| {0,3}\\t)[^\\n]+(?:\\n(?:[ \\t]*(?:\\n|$))*)?)+';
const FENCES_FULL_SRC = '^ {0,3}(`{3,}(?=[^`\\n]*(?:\\n|$))|~{3,})([^\\n]*)(?:\\n|$)(?:|([\\s\\S]*?)(?:\\n|$))(?: {0,3}(?:(?=`)\\1`*|(?=~)\\1~*) *(?=\\n|$)|$)';
const HEADING_FULL_SRC = '^ {0,3}(#{1,6})(?=\\s|$)(.*)(?:\\n+|$)';
const LHEADING_CORE = '^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\\n(?!\\s*?\\n|bull |fences|blockquote|heading|hr|html|table))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)';
const PARAGRAPH_CORE = '^([^\\n]+(?:\\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \\t]+\\n)[^\\n]+)*)';
const BLOCK_TEXT_SRC = '^[^\\n]+';
const BLOCK_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+';
const DEF_SRC = '^ {0,3}\\[(label)\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(title))? *(?:\\n+|$)';
const DEF_TITLE = '(?:\\"(?:\\\\[\\s\\S]|[^\\"\\\\])*\\"|\\\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\\\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))';
const LIST_SRC = '^(bull)([ \\t][^\\n]*?)?(?:\\n|$)';
const HTML_ATTR = ' +[a-zA-Z:_][\\w.:-]*(?: *= *\\"[^\\"\\n]*\\"| *= *\'[^\'\\n]*\'| *= *[^\\s\\"\'=<>`]+)?';
const HTML_SRC = '^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
  + '|comment[^\\n]*(\\n+|$)'
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
  + '|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + ')';
const TABLE_SRC = '^ *([^\\n ].*)\\n'
  + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
  + '(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)';

function buildParagraph(listInterrupt) {
  let s = PARAGRAPH_CORE;
  s = rep(s, 'hr', HR_SRC);
  s = rep(s, 'heading', HEADING_SRC);
  s = s.replace('|lheading', '');
  s = s.replace('|table', '');
  s = rep(s, 'blockquote', BLOCKQUOTE_SRC);
  s = rep(s, 'fences', FENCES_SRC);
  s = rep(s, 'list', listInterrupt);
  s = rep(s, 'html', rep(HTML_START_SRC, 'tag', TAG));
  return s;
}
const PARAGRAPH_SRC = (() => {
  let s = PARAGRAPH_CORE;
  s = rep(s, 'hr', HR_SRC);
  s = rep(s, 'heading', HEADING_SRC);
  s = s.replace('|lheading', '');
  s = rep(s, 'table', buildTable());
  s = rep(s, 'blockquote', BLOCKQUOTE_SRC);
  s = rep(s, 'fences', FENCES_SRC);
  s = rep(s, 'list', LIST_INT_TOP);
  s = rep(s, 'html', rep(HTML_START_SRC, 'tag', TAG));
  return s;
})();
function buildTable() {
  let s = TABLE_SRC;
  s = rep(s, 'hr', HR_SRC);
  s = rep(s, 'heading', HEADING_SRC);
  s = rep(s, 'blockquote', BLOCKQUOTE_SRC);
  s = rep(s, 'code', CODE_SRC);
  s = rep(s, 'fences', FENCES_SRC);
  s = rep(s, 'list', ' {0,3}(?:[*+-]|1[.)])[ \\t]');
  s = rep(s, 'html', rep(HTML_START_SRC, 'tag', TAG));
  return s;
}
const TABLE_FULL_SRC = buildTable();
const BLOCKQUOTE_PARA_SRC = buildParagraph(LIST_INT_BQ);
const BLOCKQUOTE_SRC_FULL = (() => {
  let s = '^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(paragraph)|[^\\n]*)(?:\\n|$))+';
  return rep(s, 'paragraph', BLOCKQUOTE_PARA_SRC);
})();
const LHEADING_SRC = (() => {
  let s = LHEADING_CORE;
  s = s.replace(/bull/g, BULLET);
  s = s.replace(/blockCode/g, '(?: {4}| {0,3}\\t)');
  s = s.replace(/fences/g, ' {0,3}(?:`{3,}|~{3,})');
  s = s.replace(/blockquote/g, ' {0,3}>');
  s = s.replace(/heading/g, HEADING_SRC);
  s = s.replace(/hr/g, HR_NC_SRC);
  s = s.replace(/html/g, ' {0,3}<[^\\n>]+>\\n');
  s = s.replace(/table/g, ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n');
  return s;
})();
const DEF_FULL_SRC = rep(rep(DEF_SRC, 'label', BLOCK_LABEL), 'title', DEF_TITLE);
const LIST_FULL_SRC = LIST_SRC.replace(/bull/g, BULLET);
const HTML_FULL_SRC = rep(rep(rep(HTML_SRC, 'comment', COMMENT), 'tag', TAG), 'attribute', HTML_ATTR);

// Sticky block regexes.
const RE_NEWLINE = sticky(NEWLINE_SRC);
const RE_BLOCK_CODE = sticky(BLOCK_CODE_SRC);
const RE_FENCES = sticky(FENCES_FULL_SRC);
const RE_HEADING = sticky(HEADING_FULL_SRC);
const RE_HR = sticky(HR_SRC);
const RE_BLOCKQUOTE = sticky(BLOCKQUOTE_SRC_FULL);
const RE_LIST = sticky(LIST_FULL_SRC);
const RE_HTML = sticky(HTML_FULL_SRC, 'i');
const RE_DEF = sticky(DEF_FULL_SRC);
const RE_TABLE = sticky(TABLE_FULL_SRC);
const RE_LHEADING = sticky(LHEADING_SRC);
const RE_PARAGRAPH = sticky(PARAGRAPH_SRC);
const RE_BLOCK_TEXT = sticky(BLOCK_TEXT_SRC);
// Plain (non-sticky) copies used for .test() on whole strings.
const RE_HR_PLAIN = plain(HR_SRC);
const RE_LHEADING_PLAIN = plain(LHEADING_SRC);

// ---------- inline grammar (GFM) ----------
const PUNCT = '[\\p{P}\\p{S}]';
const PUNCT_SPACE = '[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE = '[^\\s\\p{P}\\p{S}]';
const PUNCT_GFM = '(?!~)[\\p{P}\\p{S}]';
const PUNCT_SPACE_GFM = '(?!~)[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_GFM = '(?:[^\\s\\p{P}\\p{S}]|~)';
const SCHEME = '[a-zA-Z][a-zA-Z0-9+.-]{1,31}';
const EMAIL_BODY = '[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])';
const EMAIL_PROTO = '(?:mailto:email|xmpp:email(?:\\/[A-Za-z0-9@.]+)?)'.replace(/email/g, EMAIL_BODY);

const ESCAPE_SRC = '^\\\\([!\\"#$%&\'()*+,\\-./:;<=>?@\\[\\]\\\\^_`{|}~])';
const INLINE_CODE_SRC = '^(`+)([^`]|[^`][\\s\\S]*?[^`])\\1(?!`)';
const BR_SRC = '^( {2,}|\\\\)\\n(?!\\s*$)[ \\t]*';
const INLINE_TEXT_SRC = (() => {
  let s = '^(?:[^a-zA-Z0-9](?=emailProtocol)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\\n)|(?=[a-zA-Z0-9.!#$%&\'*+\\/=?_`{\\|}~-]+@)|[\\s\\S]*?(?:(?=[\\\\<!\\[`*~_]|\\b_|protocol:\\/\\/|wwwStart|$)|[^ ](?= {2,}\\n)|[^a-zA-Z0-9](?=emailProtocol)|[^a-zA-Z0-9.!#$%&\'*+\\/=?_`{\\|}~-](?=[a-zA-Z0-9.!#$%&\'*+\\/=?_`{\\|}~-]+@))))';
  s = s.replace('protocol', '[hH][tT][tT][pP][sS]?|[fF][tT][pP]');
  s = s.replace(/emailProtocol/g, '(?:mailto|xmpp):');
  s = s.replace('wwwStart', '(?<![^\\s*_~(])www\\.');
  return s;
})();
const BLOCK_SKIP_SRC = (() => {
  let s = 'link|precode-code|html';
  s = s.replace('link', '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)');
  s = s.replace('precode-', '(?<!`)()');
  s = s.replace('code', '(?<b>`+)[^`]+\\k<b>(?!`)');
  s = s.replace('html', '<(?! )[^<>]*?>');
  return s;
})();
const EM_LDELIM_SRC = (() => {
  let s = '^(?:\\*+(?:((?!\\*)punct)|([^\\s*]))?)|^_+(?:((?!_)punct)|([^\\s_]))?';
  return s.replace(/punct/g, PUNCT_GFM);
})();
const EM_RDELIM_AST_CORE = '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)'
  + '|[^*]+(?=[^*])'
  + '|(?!\\*)punct(\\*+)(?=[\\s]|$)'
  + '|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)'
  + '|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)'
  + '|[\\s](\\*+)(?!\\*)(?=punct)'
  + '|(?!\\*)punct(\\*+)(?!\\*)(?=punct)'
  + '|notPunctSpace(\\*+)(?=notPunctSpace)';
const EM_RDELIM_AST_SRC = EM_RDELIM_AST_CORE
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE_GFM)
  .replace(/punctSpace/g, PUNCT_SPACE_GFM)
  .replace(/punct/g, PUNCT_GFM);
const EM_RDELIM_UND_CORE = '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)'
  + '|[^_]+(?=[^_])'
  + '|(?!_)punct(_+)(?=[\\s]|$)'
  + '|notPunctSpace(_+)(?!_)(?=punctSpace|$)'
  + '|(?!_)punctSpace(_+)(?=notPunctSpace)'
  + '|[\\s](_+)(?!_)(?=punct)'
  + '|(?!_)punct(_+)(?!_)(?=punct)';
const EM_RDELIM_UND_SRC = EM_RDELIM_UND_CORE
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE)
  .replace(/punctSpace/g, PUNCT_SPACE)
  .replace(/punct/g, PUNCT);
const DEL_LDELIM_SRC = '^~~?(?:((?!~)punct)|[^\\s~])'.replace(/punct/g, PUNCT);
const DEL_RDELIM_CORE = '^[^~]+(?=[^~])'
  + '|(?!~)punct(~~?)(?=[\\s]|$)'
  + '|notPunctSpace(~~?)(?!~)(?=punctSpace|$)'
  + '|(?!~)punctSpace(~~?)(?=notPunctSpace)'
  + '|[\\s](~~?)(?!~)(?=punct)'
  + '|(?!~)punct(~~?)(?!~)(?=punct)'
  + '|notPunctSpace(~~?)(?=notPunctSpace)';
const DEL_RDELIM_SRC = DEL_RDELIM_CORE
  .replace(/notPunctSpace/g, NOT_PUNCT_SPACE)
  .replace(/punctSpace/g, PUNCT_SPACE)
  .replace(/punct/g, PUNCT);
const ANY_PUNCT_SRC = '\\\\(punct)'.replace(/punct/g, PUNCT);
const ANY_PUNCT_OUTSIDE_CODE_SRC = '(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\(punct)'.replace(/punct/g, PUNCT);
const AUTOLINK_SRC = (() => {
  let s = '^<(scheme:[^\\s\\x00-\\x1f<>]*|email)>';
  s = s.replace('scheme', SCHEME);
  s = s.replace('email', '[a-zA-Z0-9.!#$%&\'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])');
  return s;
})();
const INLINE_COMMENT = '<!--(?:-?>|[\\s\\S]*?-->)';
const TAG_INLINE_SRC = (() => {
  let s = '^comment'
    + '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>'
    + '|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>'
    + '|^<\\?[\\s\\S]*?\\?>'
    + '|^<![a-zA-Z]+\\s[\\s\\S]*?>'
    + '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>';
  s = s.replace('comment', INLINE_COMMENT);
  s = s.replace('attribute', '\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*\\"[^\\"]*\\"|\\s*=\\s*\'[^\']*\'|\\s*=\\s*[^\\s\\"\'=<>`]+)?');
  return s;
})();
const INLINE_LABEL_BRACKETS = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const INLINE_LABEL = ('(?:\\[(?:brackets|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?')
  .replace('brackets', INLINE_LABEL_BRACKETS);
const LINK_SRC = (() => {
  let s = '^!?\\[(label)\\]\\([ \\t\\n]*(href)(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(title))?[ \\t\\n]*\\)';
  s = s.replace('label', INLINE_LABEL);
  s = s.replace('href', '<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\))');
  s = s.replace('title', '\\"(?:\\\\[\\s\\S]|[^\\"\\\\])*\\"|\\\'(?:\\\\[\\s\\S]|[^\'\\\\])*\\\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)');
  return s;
})();
const REFLINK_SRC = '^!?\\[(label)\\]\\[(ref)\\]'.replace('label', INLINE_LABEL).replace('ref', BLOCK_LABEL);
const NOLINK_SRC = '^!?\\[(ref)\\](?:\\[\\])?'.replace('ref', BLOCK_LABEL);
const BOUNDED_BLOCK_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';
const BOUNDED_INLINE_LABEL = ('(?:[^\\[\\]\\\\`]*(?:\\[(?:brackets|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?')
  .replace('brackets', INLINE_LABEL_BRACKETS);
const REFLINK_SEARCH_SRC = (() => {
  const reflink = '^!?\\[(label)\\]\\[(ref)\\]'.replace('label', BOUNDED_INLINE_LABEL).replace('ref', BOUNDED_BLOCK_LABEL);
  const nolink = '^!?\\[(ref)\\](?:\\[\\])?'.replace('ref', BOUNDED_BLOCK_LABEL);
  return (reflink + '|' + nolink + '(?!\\()').replace(/(^|\|)\^/g, '$1');
})();
const URL_SRC = (() => {
  let s = '^emailProtocol|^((?:protocol):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|^email';
  s = s.replace('emailProtocol', EMAIL_PROTO);
  s = s.replace('protocol', '[hH][tT][tT][pP][sS]?|[fF][tT][pP]');
  s = s.replace('email', '[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])');
  return s;
})();
const BACKPEDAL_SRC = '(?:[^?!.,:;*_\\\'"~()&]+|\\([^)]*\\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_\\\'"~)]+(?!$))+';
const DEL_SRC = '^(~~?)(?=[^\\s~])((?:\\\\[\\s\\S]|[^\\\\])*?(?:\\\\[\\s\\S]|[^\\s~\\\\]))\\1(?=[^~]|$)';
const PUNCTUATION_SRC = '^((?![*_])punctSpace)'.replace(/punctSpace/g, PUNCT_SPACE);

// Sticky inline regexes.
const RE_ESCAPE = sticky(ESCAPE_SRC);
const RE_INLINE_CODE = sticky(INLINE_CODE_SRC);
const RE_BR = sticky(BR_SRC);
const RE_INLINE_TEXT = sticky(INLINE_TEXT_SRC);
const RE_EM_LDELIM = sticky(EM_LDELIM_SRC, 'u');
const RE_EM_RDELIM_AST = plain(EM_RDELIM_AST_SRC, 'gu');
const RE_EM_RDELIM_UND = plain(EM_RDELIM_UND_SRC, 'gu');
const RE_DEL_LDELIM = sticky(DEL_LDELIM_SRC, 'u');
const RE_DEL_RDELIM = plain(DEL_RDELIM_SRC, 'gu');
const RE_ANY_PUNCT = plain(ANY_PUNCT_SRC, 'gu');
const RE_ANY_PUNCT_OUTSIDE_CODE = plain(ANY_PUNCT_OUTSIDE_CODE_SRC, 'gu');
const RE_AUTOLINK = sticky(AUTOLINK_SRC);
const RE_TAG_INLINE = sticky(TAG_INLINE_SRC);
const RE_LINK = sticky(LINK_SRC);
const RE_REFLINK = sticky(REFLINK_SRC);
const RE_NOLINK = sticky(NOLINK_SRC);
const RE_URL = sticky(URL_SRC);
const RE_BACKPEDAL = plain(BACKPEDAL_SRC);
const RE_DEL = sticky(DEL_SRC);
const RE_PUNCTUATION = sticky(PUNCTUATION_SRC, 'u');
const RE_BLOCK_SKIP = plain(BLOCK_SKIP_SRC, 'g');
const RE_REFLINK_SEARCH = plain(REFLINK_SEARCH_SRC, 'g');

// Small `other` regexes used across the tokenizers.
const CODE_REMOVE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const OUTPUT_LINK_REPLACE = /\\([\[\]])/g;
const INDENT_CODE_COMP = /^(\s+)(?:```)/;
const BEGINNING_SPACE = /^\s+/;
const ENDING_HASH = /#$/;
const ENDING_SPACE_TAB = /[ \t]$/;
const NON_SPACE = /[^ ]/;
const NEWLINE_GLOBAL = /\n/g;
const TAB_GLOBAL = /\t/g;
const LEADING_SPACE_TAB = /^[ \t]+/;
const BLANK_LINE = /^[ \t]*$/;
const DOUBLE_BLANK_LINE = /\n[ \t]*\n[ \t]*$/;
const BLOCKQUOTE_START = /^ {0,3}>/;
const BQ_SETEXT_REPLACE = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const BQ_SETEXT_REPLACE2 = /^ {0,3}>[ \t]?/gm;
const BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const LIST_NESTING = /^ {1,4}(?=( {4})*[^ ])/g;
const LIST_IS_TASK = /^\[[ xX]\][ \t]+\S/;
const LIST_REPLACE_TASK = /^\[[ xX]\][ \t]+/;
const LIST_TASK_CHECKBOX = /\[[ xX]\]/;
const ANY_LINE = /\n.*\n/;
const HREF_BRACKETS = /^<(.*)>$/;
const TABLE_DELIMITER = /[:|]/;
const TABLE_ALIGN_CHARS = /^\||\| *$/g;
const TABLE_ALIGN_RIGHT = /^ *-+: *$/;
const TABLE_ALIGN_CENTER = /^ *:-+: *$/;
const TABLE_ALIGN_LEFT = /^ *:-+ *$/;
const TABLE_ROW_BLANK = /\n[ \t]*$/;
const START_A_TAG = /^<a /i;
const END_A_TAG = /^<\/a>/i;
const START_PRE_TAG = /^<(pre|code|kbd|script)(\s|>)/i;
const END_PRE_TAG = /^<\/(pre|code|kbd|script)(\s|>)/i;
const START_ANGLE = /^</;
const END_ANGLE = />$/;
const UNICODE_ALNUM = /[\p{L}\p{N}]/u;
const CARRIAGE_RETURN = /\r\n|\r/g;
const SETEXT_LINE = /^ {0,3}(=+|-+)[ \t]*$/;
const TABLE_DELIM_LINE = /^ *\|? *:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?$/;
const INLINE_FAST_SKIP = /[\\<\[!*_`~]|www\.|@|:\/\/|mailto:|xmpp:|  \n/;

function cachedIndentRegex(create) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) {
      re = create(idx);
      cache[idx] = re;
    }
    return re;
  };
}
const listItemRegex = (bull) => new RegExp(`^( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`);
const nextBulletRegex = cachedIndentRegex((n) => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`));
const hrRegexFor = cachedIndentRegex((n) => new RegExp(`^ {0,${n}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`));
const fencesBeginRegex = cachedIndentRegex((n) => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`));
const headingBeginRegex = cachedIndentRegex((n) => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`));
const htmlBeginRegex = cachedIndentRegex((n) => new RegExp(`^ {0,${n}}(?:</?(?:${TAG})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const blockquoteBeginRegex = cachedIndentRegex((n) => new RegExp(`^ {0,${n}}>`));

// ---------- lexer state ----------
function createLexer() {
  return {
    links: Object.create(null),
    queue: [],
    inLink: false,
    inRawBlock: false,
    linkEmitted: false,
    linkParenPossible: true,
    top: true,
    closerStack: [],
  };
}

function queueInline(L, text) {
  const tokens = [];
  L.queue.push({ src: text, tokens });
  return tokens;
}

function execAt(re, s, pos) {
  re.lastIndex = pos;
  return re.exec(s);
}

function indentCodeCompensation(raw, text) {
  const m = INDENT_CODE_COMP.exec(raw);
  if (m === null) return text;
  const indentToCode = m[1];
  return text.split('\n').map((node) => {
    const mi = BEGINNING_SPACE.exec(node);
    if (mi === null) return node;
    return node.slice(Math.min(mi[0].length, indentToCode.length));
  }).join('\n');
}

// ---------- block tokenizers ----------
// Each takes (L, s, pos) and returns a token, or undefined. The caller
// advances pos by token.raw.length, exactly like marked does.

function tokSpace(L, s, pos) {
  const cap = execAt(RE_NEWLINE, s, pos);
  if (cap && cap[0].length > 0) return { type: 'space', raw: cap[0] };
}

function tokCode(L, s, pos) {
  const cap = execAt(RE_BLOCK_CODE, s, pos);
  if (!cap) return undefined;
  const raw = trimTrailingBlankLines(cap[0]);
  return {
    type: 'code',
    raw,
    codeBlockStyle: 'indented',
    text: raw.replace(CODE_REMOVE_INDENT, ''),
  };
}

function tokFences(L, s, pos) {
  const cap = execAt(RE_FENCES, s, pos);
  if (!cap) return undefined;
  const raw = cap[0];
  return {
    type: 'code',
    raw,
    lang: cap[2] ? cap[2].trim().replace(RE_ANY_PUNCT, '$1') : cap[2],
    text: indentCodeCompensation(raw, cap[3] || ''),
  };
}

function tokHeading(L, s, pos) {
  const cap = execAt(RE_HEADING, s, pos);
  if (!cap) return undefined;
  let text = cap[2].trim();
  if (ENDING_HASH.test(text)) {
    const trimmed = rtrim(text, '#');
    if (!trimmed || ENDING_SPACE_TAB.test(trimmed)) text = trimmed.trim();
  }
  return {
    type: 'heading',
    raw: rtrim(cap[0], '\n'),
    depth: cap[1].length,
    text,
    tokens: queueInline(L, text),
  };
}

function tokHr(L, s, pos) {
  const cap = execAt(RE_HR, s, pos);
  if (!cap) return undefined;
  return { type: 'hr', raw: rtrim(cap[0], '\n') };
}

function tokBlockquote(L, s, pos) {
  const cap = execAt(RE_BLOCKQUOTE, s, pos);
  if (!cap) return undefined;
  let lines = rtrim(cap[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];
  while (lines.length > 0) {
    let inBlockquote = false;
    const currentLines = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (BLOCKQUOTE_START.test(lines[i])) {
        currentLines.push(lines[i]);
        inBlockquote = true;
      } else if (!inBlockquote) {
        currentLines.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);
    const currentRaw = currentLines.join('\n');
    const currentText = currentRaw
      .replace(BQ_MARKER_WS, (_, marker, whitespace) => marker + expandTabs(whitespace, marker.length))
      .replace(BQ_SETEXT_REPLACE, '\n    $1')
      .replace(BQ_SETEXT_REPLACE2, '');
    raw = raw ? `${raw}\n${currentRaw}` : currentRaw;
    text = text ? `${text}\n${currentText}` : currentText;
    const top = L.top;
    L.top = true;
    lexBlocks(L, currentText, tokens, true);
    L.top = top;
    if (lines.length === 0) break;
    const lastToken = tokens.at(-1);
    if (lastToken?.type === 'code' || lastToken?.type === 'heading' || lastToken?.type === 'hr' || lastToken?.type === 'html' || lastToken?.type === 'table') {
      break;
    } else if (lastToken?.type === 'blockquote') {
      const oldToken = lastToken;
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(BQ_SETEXT_REPLACE2, '');
      const newToken = tokBlockquote(L, newText, 0);
      if (!newToken) break;
      tokens[tokens.length - 1] = newToken;
      const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = `${raw}\n${consumed.join('\n')}`;
      text = text.substring(0, text.length - oldToken.text.length) + newToken.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && BLOCKQUOTE_START.test(lines[0])) continue;
      break;
    } else if (lastToken?.type === 'list') {
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const newToken = tokList(L, newText, 0);
      if (!newToken) break;
      tokens[tokens.length - 1] = newToken;
      const consumedCount = newToken.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
        : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw = `${raw}\n${consumed}`;
        text = `${text}\n${consumed}`;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
  }
  return { type: 'blockquote', raw, tokens, text };
}

function endsWithBlankLineCheck(str) {
  let i = str.length - 1;
  while (i >= 0 && (str[i] === ' ' || str[i] === '\t')) i--;
  if (i < 0 || str[i] !== '\n') return false;
  i--;
  while (i >= 0 && (str[i] === ' ' || str[i] === '\t')) i--;
  return i >= 0 && str[i] === '\n';
}

function tokList(L, s, pos) {
  let cap = execAt(RE_LIST, s, pos);
  if (!cap) return undefined;
  const end = s.length;
  let p = pos;
  let bull = cap[1].trim();
  const isordered = bull.length > 1;
  const list = {
    type: 'list',
    raw: '',
    ordered: isordered,
    start: isordered ? +bull.slice(0, -1) : '',
    loose: false,
    items: [],
  };
  bull = isordered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;
  const itemRegex = new RegExp(`( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`, 'y');
  let endsWithBlankLine = false;
  const lineAt = (from) => {
    const nl = s.indexOf('\n', from);
    return nl === -1 ? s.slice(from) : s.slice(from, nl);
  };
  const advanceLine = (from) => {
    const nl = s.indexOf('\n', from);
    return nl === -1 ? end : nl + 1;
  };
  while (p < end) {
    let endEarly = false;
    let itemContents = '';
    itemRegex.lastIndex = p;
    if (!(cap = itemRegex.exec(s))) break;
    if (execAt(RE_HR, s, p)) break;
    const itemStart = p;
    p += cap[0].length;
    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(LEADING_SPACE_TAB, (ws) => expandTabs(ws, bulletIndent));
    let nextLine = lineAt(p);
    let blankLine = !line.trim();
    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(NON_SPACE);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }
    if (blankLine && BLANK_LINE.test(nextLine)) {
      p = advanceLine(p);
      endEarly = true;
    }
    if (!endEarly) {
      const nextBulletRe = nextBulletRegex(indent);
      const hrRe = hrRegexFor(indent);
      const fencesBeginRe = fencesBeginRegex(indent);
      const headingBeginRe = headingBeginRegex(indent);
      const htmlBeginRe = htmlBeginRegex(indent);
      const blockquoteBeginRe = blockquoteBeginRegex(indent);
      const reIdx = Math.max(0, Math.min(3, indent - 1));
      const parts = [itemContents];
      while (p < end) {
        const lineStart = p;
        const rawLine = lineAt(p);
        nextLine = rawLine;
        const c0 = nextLine.charCodeAt(0);
        const nextLineWithoutTabs = (c0 === 32 || c0 === 9)
          ? nextLine.replace(LEADING_SPACE_TAB, (ws) => expandTabs(ws))
          : nextLine;
        let fns = 0;
        while (fns < nextLineWithoutTabs.length && nextLineWithoutTabs.charCodeAt(fns) === 32) fns++;
        const fc = fns < nextLineWithoutTabs.length ? nextLineWithoutTabs.charCodeAt(fns) : -1;
        const isBlank = fns === nextLineWithoutTabs.length;
        if (fns <= reIdx && fc !== -1) {
          if ((fc === 96 || fc === 126) && fencesBeginRe.test(nextLine)) break;
          if (fc === 35 && headingBeginRe.test(nextLine)) break;
          if (fc === 60 && htmlBeginRe.test(nextLine)) break;
          if (fc === 62 && blockquoteBeginRe.test(nextLine)) break;
          if ((fc === 42 || fc === 45 || fc === 43 || (fc >= 48 && fc <= 57)) && nextBulletRe.test(nextLine)) break;
          if ((fc === 45 || fc === 95 || fc === 42) && hrRe.test(nextLine)) break;
        }
        if (fns >= indent || isBlank) {
          parts.push('\n', nextLineWithoutTabs.slice(indent));
        } else {
          if (blankLine) break;
          const lineNoTabs = line.includes('\t') ? line.replace(TAB_GLOBAL, '    ') : line;
          let lfns = 0;
          while (lfns < lineNoTabs.length && lineNoTabs.charCodeAt(lfns) === 32) lfns++;
          if (lfns < lineNoTabs.length && lfns >= 4) break;
          const lc = lfns < lineNoTabs.length ? lineNoTabs.charCodeAt(lfns) : -1;
          if (lfns <= reIdx && lc !== -1) {
            if ((lc === 96 || lc === 126) && fencesBeginRe.test(line)) break;
            if (lc === 35 && headingBeginRe.test(line)) break;
            if (lc === 60 && htmlBeginRe.test(line)) break;
            if ((lc === 45 || lc === 95 || lc === 42) && hrRe.test(line)) break;
          }
          const setextContinuation = /^ {0,3}(?:=+|-+) *$/.test(nextLine)
            && RE_LHEADING_PLAIN.test(`${line}\n${nextLine}`);
          const continuation = setextContinuation
            ? `    ${nextLineWithoutTabs.replace(/^ {0,3}/, '')}`
            : nextLine;
          parts.push('\n', continuation);
        }
        blankLine = isBlank;
        p = advanceLine(lineStart);
        line = nextLineWithoutTabs.slice(indent);
      }
      itemContents = parts.join('');
    }
    const raw = s.slice(itemStart, p);
    if (!list.loose) {
      if (endsWithBlankLine) list.loose = true;
      else if (endsWithBlankLineCheck(raw)) endsWithBlankLine = true;
    }
    list.items.push({
      type: 'list_item',
      raw,
      task: LIST_IS_TASK.test(itemContents),
      loose: false,
      text: itemContents,
      tokens: [],
    });
  }
  const lastItem = list.items.at(-1);
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else {
    return undefined;
  }
  list.raw = s.slice(pos, p).trimEnd();
  for (const item of list.items) {
    L.top = false;
    item.tokens = lexBlocks(L, item.text, [], false);
    if (!list.loose) {
      const spacers = item.tokens.filter((t) => t.type === 'space');
      const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => ANY_LINE.test(t.raw));
      list.loose = hasMultipleLineBreaks;
    }
  }
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && (itemToken?.type === 'text' || itemToken?.type === 'paragraph')) {
      item.text = item.text.replace(LIST_REPLACE_TASK, '');
      itemToken.raw = itemToken.raw.replace(LIST_REPLACE_TASK, '');
      itemToken.text = itemToken.text.replace(LIST_REPLACE_TASK, '');
      for (let i = L.queue.length - 1; i >= 0; i--) {
        if (LIST_IS_TASK.test(L.queue[i].src)) {
          L.queue[i].src = L.queue[i].src.replace(LIST_REPLACE_TASK, '');
          break;
        }
      }
      const taskRaw = LIST_TASK_CHECKBOX.exec(item.raw);
      if (taskRaw) {
        const checkboxToken = {
          type: 'checkbox',
          raw: taskRaw[0] + ' ',
          checked: taskRaw[0] !== '[ ]',
        };
        item.checked = checkboxToken.checked;
        if (list.loose) {
          if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
            item.tokens[0].raw = checkboxToken.raw + item.tokens[0].raw;
            item.tokens[0].text = checkboxToken.raw + item.tokens[0].text;
            item.tokens[0].tokens.unshift(checkboxToken);
          } else {
            item.tokens.unshift({
              type: 'paragraph',
              raw: checkboxToken.raw,
              text: checkboxToken.raw,
              tokens: [checkboxToken],
            });
          }
        } else {
          item.tokens.unshift(checkboxToken);
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
  return list;
}

function tokHtml(L, s, pos) {
  const cap = execAt(RE_HTML, s, pos);
  if (!cap) return undefined;
  const raw = trimTrailingBlankLines(cap[0]);
  return {
    type: 'html',
    block: true,
    raw,
    pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
    text: raw,
  };
}

function tokDef(L, s, pos) {
  const cap = execAt(RE_DEF, s, pos);
  if (!cap) return undefined;
  if (!START_ANGLE.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) return undefined;
  const tag = normalizeLabel(cap[1]);
  const href = cap[2] ? cap[2].replace(HREF_BRACKETS, '$1').replace(RE_ANY_PUNCT, '$1') : '';
  const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(RE_ANY_PUNCT, '$1') : cap[3];
  return {
    type: 'def',
    tag,
    raw: rtrim(cap[0], '\n'),
    href,
    title,
  };
}

function tokTable(L, s, pos) {
  const cap = execAt(RE_TABLE, s, pos);
  if (!cap) return undefined;
  if (!TABLE_DELIMITER.test(cap[2])) return undefined;
  const headers = splitCells(cap[1]);
  const aligns = cap[2].replace(TABLE_ALIGN_CHARS, '').split('|');
  const rows = cap[3]?.trim() ? cap[3].replace(TABLE_ROW_BLANK, '').split('\n') : [];
  const item = {
    type: 'table',
    raw: rtrim(cap[0], '\n'),
    header: [],
    align: [],
    rows: [],
  };
  if (headers.length !== aligns.length) return undefined;
  for (const align of aligns) {
    if (TABLE_ALIGN_RIGHT.test(align)) item.align.push('right');
    else if (TABLE_ALIGN_CENTER.test(align)) item.align.push('center');
    else if (TABLE_ALIGN_LEFT.test(align)) item.align.push('left');
    else item.align.push(null);
  }
  for (let i = 0; i < headers.length; i++) {
    item.header.push({
      text: headers[i],
      tokens: queueInline(L, headers[i]),
      header: true,
      align: item.align[i],
    });
  }
  for (const row of rows) {
    item.rows.push(splitCells(row, item.header.length).map((cell, i) => ({
      text: cell,
      tokens: queueInline(L, cell),
      header: false,
      align: item.align[i],
    })));
  }
  return item;
}

function tokLheading(L, s, pos) {
  const cap = execAt(RE_LHEADING, s, pos);
  if (!cap) return undefined;
  const text = cap[1].trim();
  return {
    type: 'heading',
    raw: rtrim(cap[0], '\n'),
    depth: cap[2].charAt(0) === '=' ? 1 : 2,
    text,
    tokens: queueInline(L, text),
  };
}

function tokParagraph(L, s, pos) {
  const cap = execAt(RE_PARAGRAPH, s, pos);
  if (!cap) return undefined;
  const text = cap[1].charAt(cap[1].length - 1) === '\n' ? cap[1].slice(0, -1) : cap[1];
  return {
    type: 'paragraph',
    raw: cap[0],
    text,
    tokens: queueInline(L, text),
  };
}

function tokText(L, s, pos) {
  const cap = execAt(RE_BLOCK_TEXT, s, pos);
  if (!cap) return undefined;
  return {
    type: 'text',
    raw: cap[0],
    text: cap[0],
    tokens: queueInline(L, cap[0]),
  };
}

// A table can only start when the second line is a delimiter row.
function tablePrecheck(s, pos) {
  const nl1 = s.indexOf('\n', pos);
  if (nl1 === -1) return false;
  const line1 = s.slice(pos, nl1);
  if (!/^ *[^ ]/.test(line1)) return false;
  const nl2 = s.indexOf('\n', nl1 + 1);
  const line2 = nl2 === -1 ? s.slice(nl1 + 1) : s.slice(nl1 + 1, nl2);
  return TABLE_DELIM_LINE.test(line2);
}

// A setext heading can only start when some line before the next blank
// line is an underline.
function lheadingPrecheck(s, pos) {
  let i = s.indexOf('\n', pos);
  if (i === -1) return false;
  i++;
  while (i <= s.length) {
    const j = s.indexOf('\n', i);
    const line = j === -1 ? s.slice(i) : s.slice(i, j);
    if (/^[ \t]*$/.test(line)) return false;
    if (SETEXT_LINE.test(line)) return true;
    if (j === -1) return false;
    i = j + 1;
  }
  return false;
}

// ---------- block loop ----------
function lexBlocks(L, s, tokens, lastParagraphClipped) {
  let pos = 0;
  const len = s.length;
  let prevRemaining = Infinity;
  while (pos < len) {
    const remaining = len - pos;
    if (remaining >= prevRemaining) {
      throw new Error('Infinite loop on byte: ' + s.charCodeAt(pos));
    }
    prevRemaining = remaining;
    const c = s[pos];
    let tok;
    // newline
    if ((c === ' ' || c === '\t' || c === '\n') && (tok = tokSpace(L, s, pos))) {
      pos += tok.raw.length;
      const lastToken = tokens.at(-1);
      if (tok.raw.length === 1 && lastToken !== undefined) lastToken.raw += '\n';
      else tokens.push(tok);
      continue;
    }
    // indented code
    if ((c === ' ' || c === '\t') && (tok = tokCode(L, s, pos))) {
      pos += tok.raw.length;
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        lastToken.text += '\n' + tok.text;
        L.queue.at(-1).src = lastToken.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    // fenced code
    if ((c === ' ' || c === '`' || c === '~') && (tok = tokFences(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // ATX heading
    if ((c === ' ' || c === '#') && (tok = tokHeading(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // thematic break
    if ((c === ' ' || c === '-' || c === '_' || c === '*') && (tok = tokHr(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // blockquote
    if ((c === ' ' || c === '>') && (tok = tokBlockquote(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // list
    if ((c === ' ' || c === '*' || c === '+' || c === '-' || (c >= '0' && c <= '9')) && (tok = tokList(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // raw HTML block
    if ((c === ' ' || c === '<') && (tok = tokHtml(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // link reference definition
    if ((c === ' ' || c === '[') && (tok = tokDef(L, s, pos))) {
      pos += tok.raw.length;
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'paragraph' || lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        lastToken.text += '\n' + tok.raw;
        L.queue.at(-1).src = lastToken.text;
      } else {
        if (!Object.hasOwn(L.links, tok.tag)) {
          L.links[tok.tag] = { href: tok.href, title: tok.title };
        }
        tokens.push(tok);
      }
      continue;
    }
    // table
    if (c !== '\n' && tablePrecheck(s, pos) && (tok = tokTable(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // setext heading
    if (c !== '\n' && lheadingPrecheck(s, pos) && (tok = tokLheading(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    // top-level paragraph
    if (L.top && c !== '\n' && (tok = tokParagraph(L, s, pos))) {
      const lastToken = tokens.at(-1);
      if (lastParagraphClipped && lastToken?.type === 'paragraph') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        lastToken.text += '\n' + tok.text;
        L.queue.pop();
        L.queue.at(-1).src = lastToken.text;
      } else {
        tokens.push(tok);
      }
      lastParagraphClipped = false;
      pos += tok.raw.length;
      continue;
    }
    // text
    if (c !== '\n' && (tok = tokText(L, s, pos))) {
      pos += tok.raw.length;
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        lastToken.text += '\n' + tok.text;
        L.queue.pop();
        L.queue.at(-1).src = lastToken.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + s.charCodeAt(pos));
  }
  L.top = true;
  return tokens;
}

// ---------- inline helpers ----------
function cachedEmStrong(L, masked, delim) {
  const frame = L.closerStack.at(-1);
  if (frame && frame.src === masked) return delim === '*' ? frame.ast : frame.und;
  const scanned = scanClosers(masked);
  return delim === '*' ? scanned.ast : scanned.und;
}

function cachedDel(L, masked) {
  const frame = L.closerStack.at(-1);
  if (frame && frame.src === masked) return frame.del;
  return scanClosers(masked).del;
}

function linkInText(L, text) {
  if (!text.includes('[')) return false;
  for (const match of text.matchAll(RE_BLOCK_SKIP)) {
    RE_LINK.lastIndex = 0;
    if (RE_LINK.test(match[0]) && text.charAt(match.index - 1) !== '!') return true;
  }
  for (const match of text.matchAll(RE_REFLINK_SEARCH)) {
    const match0 = match[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(L.links, normalizeLabel(match0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(L, match0.slice(1, refStart - 1))) continue;
    return true;
  }
  return false;
}

// Mask links, code, html and escapes so emStrong and del do not see
// their delimiters inside them. Every mask keeps the length it replaces.
function maskSrc(L, src) {
  let maskedSrc = src;
  if (src.includes('[')) {
    const maskReflink = (match0) => {
      const refStart = match0.lastIndexOf('[');
      if (!Object.hasOwn(L.links, normalizeLabel(match0.slice(refStart + 1, -1)))) return match0;
      if (refStart > 1 && match0.charAt(0) !== '!') {
        const text = match0.slice(1, refStart - 1);
        if (linkInText(L, text)) {
          return '[' + text.replace(plain(REFLINK_SEARCH_SRC, 'g'), maskReflink)
            + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match0.length - 2) + ']';
    };
    maskedSrc = maskedSrc.replace(plain(REFLINK_SEARCH_SRC, 'g'), maskReflink);
  }
  if (maskedSrc.includes('\\') || maskedSrc.includes('`')) {
    maskedSrc = maskedSrc.replace(plain(ANY_PUNCT_OUTSIDE_CODE_SRC, 'gu'), (match0, code, punct) => {
      if (punct) return '+'.repeat(match0.length);
      if (code) return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
      return match0;
    });
  }
  if (maskedSrc.includes('[') || maskedSrc.includes('<') || maskedSrc.includes('`')) {
    maskedSrc = maskedSrc.replace(plain(BLOCK_SKIP_SRC, 'g'), (match0, _link, context) => {
      const offset = context ? context.length : 0;
      return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
    });
  }
  return maskedSrc;
}

function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') {
      i++;
      continue;
    }
    if (label[i] === '`') {
      const code = execAt(RE_INLINE_CODE, label, i);
      if (code) {
        i += code[0].length - 1;
        continue;
      }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const token = execAt(RE_TAG_INLINE, tokenSrc, 0) || execAt(RE_AUTOLINK, tokenSrc, 0);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

function outputLink(L, cap, link, raw) {
  const href = link.href;
  const title = link.title || null;
  const text = cap[1].replace(OUTPUT_LINK_REPLACE, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const outerInLink = L.inLink;
  const outerLinkEmitted = L.linkEmitted;
  const outerInRawBlock = L.inRawBlock;
  L.inLink = true;
  L.linkEmitted = false;
  const tokens = lexInline(L, text, []);
  const textHasLink = L.linkEmitted;
  L.linkEmitted = outerLinkEmitted;
  L.inLink = outerInLink;
  if (!isImage) {
    if (textHasLink) {
      L.inRawBlock = outerInRawBlock;
      return undefined;
    }
    L.linkEmitted = true;
  }
  return {
    type: isImage ? 'image' : 'link',
    raw,
    href,
    title,
    text,
    tokens,
  };
}

// ---------- inline tokenizers ----------
function tokEscape(L, s, pos) {
  const cap = execAt(RE_ESCAPE, s, pos);
  if (!cap) return undefined;
  return { type: 'escape', raw: cap[0], text: cap[1] };
}

function tokTag(L, s, pos) {
  const cap = execAt(RE_TAG_INLINE, s, pos);
  if (!cap) return undefined;
  if (!L.inLink && START_A_TAG.test(cap[0])) L.inLink = true;
  else if (L.inLink && END_A_TAG.test(cap[0])) L.inLink = false;
  if (!L.inRawBlock && START_PRE_TAG.test(cap[0])) L.inRawBlock = true;
  else if (L.inRawBlock && END_PRE_TAG.test(cap[0])) L.inRawBlock = false;
  return {
    type: 'html',
    raw: cap[0],
    inLink: L.inLink,
    inRawBlock: L.inRawBlock,
    block: false,
    text: cap[0],
  };
}

function tokLink(L, s, pos) {
  if (L.linkParenPossible === false) return undefined;
  const cap = execAt(RE_LINK, s, pos);
  if (!cap) return undefined;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(s.slice(pos), cap[1], labelStart)) return undefined;
  const trimmedUrl = cap[2].trim();
  if (START_ANGLE.test(trimmedUrl)) {
    if (!END_ANGLE.test(trimmedUrl)) return undefined;
    const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return undefined;
  } else {
    const lastParenIndex = findClosingBracket(cap[2], '()');
    if (lastParenIndex === -2) return undefined;
    if (lastParenIndex > -1) {
      const start = cap[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + cap[1].length + lastParenIndex;
      cap[2] = cap[2].substring(0, lastParenIndex);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  const unescaped = rtrim(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return undefined;
  let href = cap[2];
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (START_ANGLE.test(href)) href = href.slice(1, -1);
  return outputLink(L, cap, {
    href: href ? href.replace(RE_ANY_PUNCT, '$1') : href,
    title: title ? title.replace(RE_ANY_PUNCT, '$1') : title,
  }, cap[0]);
}

function tokReflink(L, s, pos) {
  const cap = execAt(RE_REFLINK, s, pos) || execAt(RE_NOLINK, s, pos);
  if (!cap) return undefined;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(s.slice(pos), cap[1], labelStart)) return undefined;
  const link = L.links[normalizeLabel(cap[2] || cap[1])];
  if (!link) {
    const text = cap[0].charAt(0);
    return { type: 'text', raw: text, text };
  }
  return outputLink(L, cap, link, cap[0]);
}

function tokEmStrong(L, s, pos, masked, prevChar) {
  let match = execAt(RE_EM_LDELIM, s, pos);
  if (!match) return undefined;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return undefined;
  const delimChar = match[0][0];
  const midRun = prevChar === delimChar;
  const srcStart = pos;
  let runStart = srcStart;
  while (runStart > 0 && masked[runStart - 1] === delimChar) runStart--;
  const runPrevChar = [...masked.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!execAt(RE_PUNCTUATION, runPrevChar, 0);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!execAt(RE_PUNCTUATION, prevChar, 0);
  if (match[4] && UNICODE_ALNUM.test(prevChar)) return undefined;
  const nextChar = match[1] || match[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const afterDelim = match[1] || match[2] || match[3] || match[4] || '';
    const runLen = match[0].length - afterDelim.length;
    const lLength = afterDelim ? runLen : runLen - 1;
    let rDelim;
    let rLength;
    let delimTotal = lLength;
    let midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim()
      && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return undefined;
    const endReg = delimChar === '*' ? RE_EM_RDELIM_AST : RE_EM_RDELIM_UND;
    const lastPossible = cachedEmStrong(L, masked, delimChar);
    const windowStart = pos + lLength;
    if (lastPossible < windowStart) return undefined;
    const clipped = masked.slice(windowStart);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(clipped)) !== null) {
      if (match.index > lastInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = rDelim.length;
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
      const lastCharLength = match[0].codePointAt(0) > 0xFFFF ? 2 : 1;
      const raw = s.slice(pos, pos + lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: lexInline(L, text, []) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: lexInline(L, text, []) };
    }
  }
  return undefined;
}

function tokCodespan(L, s, pos) {
  const cap = execAt(RE_INLINE_CODE, s, pos);
  if (!cap) return undefined;
  let text = cap[2].replace(NEWLINE_GLOBAL, ' ');
  const hasNonSpaceChars = NON_SPACE.test(text);
  const hasSpaceCharsOnBothEnds = text.charAt(0) === ' ' && text.charAt(text.length - 1) === ' ';
  if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) text = text.substring(1, text.length - 1);
  return { type: 'codespan', raw: cap[0], text };
}

function tokBr(L, s, pos) {
  const cap = execAt(RE_BR, s, pos);
  if (!cap) return undefined;
  return { type: 'br', raw: cap[0] };
}

function tokDel(L, s, pos, masked, prevChar) {
  const match0 = execAt(RE_DEL_LDELIM, s, pos);
  if (!match0) return undefined;
  const nextChar = match0[1] || '';
  if (!nextChar || !prevChar || execAt(RE_PUNCTUATION, prevChar, 0)) {
    const delRunLen = s[pos + 1] === '~' ? 2 : 1;
    const lLength = match0[0].length > delRunLen ? delRunLen : delRunLen - 1;
    let rDelim;
    let rLength;
    let delimTotal = lLength;
    const lastPossible = cachedDel(L, masked);
    const windowStart = pos + lLength;
    if (lastPossible < windowStart) return undefined;
    const clipped = masked.slice(windowStart);
    const lastInWindow = lastPossible - windowStart;
    RE_DEL_RDELIM.lastIndex = 0;
    let match;
    while ((match = RE_DEL_RDELIM.exec(clipped)) !== null) {
      if (match.index > lastInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = rDelim.length;
      if (rLength !== lLength) continue;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal);
      const lastCharLength = match[0].codePointAt(0) > 0xFFFF ? 2 : 1;
      const raw = s.slice(pos, pos + lLength + match.index + lastCharLength + rLength);
      const text = raw.slice(lLength, -lLength);
      return { type: 'del', raw, text, tokens: lexInline(L, text, []) };
    }
  }
  return undefined;
}

function tokAutolink(L, s, pos) {
  const cap = execAt(RE_AUTOLINK, s, pos);
  if (!cap) return undefined;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  return {
    type: 'link',
    raw: cap[0],
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
  };
}

function tokUrl(L, s, pos) {
  const cap = execAt(RE_URL, s, pos);
  if (!cap) return undefined;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + text;
  } else {
    let prevCapZero;
    let c0 = cap[0];
    do {
      prevCapZero = c0;
      RE_BACKPEDAL.lastIndex = 0;
      const m = RE_BACKPEDAL.exec(c0);
      c0 = m?.[0] ?? '';
    } while (prevCapZero !== c0);
    text = c0;
    href = cap[1] === 'www.' ? 'http://' + c0 : c0;
  }
  return {
    type: 'link',
    raw: text,
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
  };
}

function tokInlineText(L, s, pos) {
  const cap = execAt(RE_INLINE_TEXT, s, pos);
  if (!cap) return undefined;
  const escaped = L.inRawBlock;
  return {
    type: 'text',
    raw: cap[0],
    text: escaped ? cap[0] : decodeNumericCharacterReferences(cap[0]),
    escaped,
  };
}

// An extended autolink can only start at `www.`, `mailto:`, `xmpp:`, a
// known scheme followed by `://`, or an email-looking run ending in `@`.
function urlPrecheck(s, pos) {
  const c = s[pos];
  if (c === 'w' && s.startsWith('www.', pos)) return true;
  if (c === 'm' && s.startsWith('mailto:', pos)) return true;
  if (c === 'x' && s.startsWith('xmpp:', pos)) return true;
  if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
    let i = pos + 1;
    while (i < s.length && i - pos < 33) {
      const ch = s[i];
      if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch === '+' || ch === '-' || ch === '.') {
        i++;
        continue;
      }
      break;
    }
    if (s[i] === ':' && s[i + 1] === '/' && s[i + 2] === '/') {
      const scheme = s.slice(pos, i).toLowerCase();
      if (scheme === 'http' || scheme === 'https' || scheme === 'ftp') return true;
    }
    let j = pos;
    while (j < s.length) {
      const ch = s[j];
      if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch === '.' || ch === '_' || ch === '+' || ch === '-') {
        j++;
        continue;
      }
      break;
    }
    if (j > pos && s[j] === '@') return true;
  }
  return false;
}

// ---------- inline loop ----------
function lexInline(L, s, tokens) {
  const prevLinkParenPossible = L.linkParenPossible;
  L.linkParenPossible = prevLinkParenPossible && s.includes(')');
  try {
    return lexInlineInner(L, s, tokens);
  } finally {
    L.linkParenPossible = prevLinkParenPossible;
  }
}

function lexInlineInner(L, s, tokens) {
  // Plain text with no inline syntax at all becomes one text token.
  if (!INLINE_FAST_SKIP.test(s)) {
    tokens.push({
      type: 'text',
      raw: s,
      text: L.inRawBlock ? s : decodeNumericCharacterReferences(s),
      escaped: L.inRawBlock,
    });
    return tokens;
  }
  const hasEm = s.includes('*') || s.includes('_') || s.includes('~');
  const masked = hasEm ? maskSrc(L, s) : s;
  if (hasEm) L.closerStack.push(scanClosers(masked));
  try {
    return tokenizeInlines(L, s, masked, tokens);
  } finally {
    if (hasEm) L.closerStack.pop();
  }
}

function tokenizeInlines(L, s, masked, tokens) {
  let pos = 0;
  const len = s.length;
  let keepPrevChar = false;
  let prevChar = '';
  let prevRemaining = Infinity;
  while (pos < len) {
    const remaining = len - pos;
    if (remaining >= prevRemaining) {
      throw new Error('Infinite loop on byte: ' + s.charCodeAt(pos));
    }
    prevRemaining = remaining;
    if (!keepPrevChar) prevChar = '';
    keepPrevChar = false;
    const c = s[pos];
    let tok;
    if (c === '\\' && (tok = tokEscape(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (c === '<' && (tok = tokTag(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if ((c === '[' || c === '!') && (tok = tokLink(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if ((c === '[' || c === '!') && (tok = tokReflink(L, s, pos))) {
      pos += tok.raw.length;
      const lastToken = tokens.at(-1);
      if (tok.type === 'text' && lastToken?.type === 'text') {
        lastToken.raw += tok.raw;
        lastToken.text += tok.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    if ((c === '*' || c === '_') && (tok = tokEmStrong(L, s, pos, masked, prevChar))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (c === '`' && (tok = tokCodespan(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if ((c === ' ' || c === '\\') && (tok = tokBr(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (c === '~' && (tok = tokDel(L, s, pos, masked, prevChar))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (c === '<' && (tok = tokAutolink(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (!L.inLink && urlPrecheck(s, pos) && (tok = tokUrl(L, s, pos))) {
      pos += tok.raw.length;
      tokens.push(tok);
      continue;
    }
    if (tok = tokInlineText(L, s, pos)) {
      pos += tok.raw.length;
      if (tok.raw.slice(-1) !== '_') prevChar = tok.raw.slice(-1);
      keepPrevChar = true;
      const lastToken = tokens.at(-1);
      if (lastToken?.type === 'text') {
        lastToken.raw += tok.raw;
        lastToken.text += tok.text;
      } else {
        tokens.push(tok);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + s.charCodeAt(pos));
  }
  return tokens;
}

// ---------- entry point ----------
export function parse(markdown) {
  const L = createLexer();
  const src = markdown.replace(CARRIAGE_RETURN, '\n');
  const tokens = [];
  lexBlocks(L, src, tokens, false);
  for (let i = 0; i < L.queue.length; i++) {
    const next = L.queue[i];
    L.inRawBlock = false;
    lexInline(L, next.src, next.tokens);
  }
  L.queue.length = 0;
  return Parser.parse(tokens);
}

// TEMP DEBUG EXPORT - remove before submit
export const __regexes = {
  blockquote: RE_BLOCKQUOTE, code: RE_BLOCK_CODE, def: RE_DEF, fences: RE_FENCES,
  heading: RE_HEADING, hr: RE_HR, html: RE_HTML, lheading: RE_LHEADING,
  list: RE_LIST, newline: RE_NEWLINE, paragraph: RE_PARAGRAPH, table: RE_TABLE,
  text: RE_BLOCK_TEXT,
  _backpedal: RE_BACKPEDAL, anyPunctuation: RE_ANY_PUNCT,
  anyPunctuationOutsideCode: RE_ANY_PUNCT_OUTSIDE_CODE, autolink: RE_AUTOLINK,
  blockSkip: RE_BLOCK_SKIP, br: RE_BR, codeInline: RE_INLINE_CODE, del: RE_DEL,
  delLDelim: RE_DEL_LDELIM, delRDelim: RE_DEL_RDELIM, emStrongLDelim: RE_EM_LDELIM,
  emStrongRDelimAst: RE_EM_RDELIM_AST, emStrongRDelimUnd: RE_EM_RDELIM_UND,
  escape: RE_ESCAPE, link: RE_LINK, nolink: RE_NOLINK, punctuation: RE_PUNCTUATION,
  reflink: RE_REFLINK, reflinkSearch: RE_REFLINK_SEARCH, tag: RE_TAG_INLINE,
  textInline: RE_INLINE_TEXT, url: RE_URL,
};
