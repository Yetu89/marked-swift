// marked-swift: a faster drop-in for marked 18.1.3 (MIT, MarkedJS).
//
// Strategy: block splitting is delegated to marked's own Lexer (vendored in
// vendor/marked/, byte for byte the npm build), so every block boundary,
// list, blockquote, table and link-reference definition is exactly marked's.
// The inline layer and the rendering layer are re-implemented here as a
// single direct-to-string pass: no inline token objects, no second parser
// walk, a first-character dispatch instead of trying every inline rule at
// every position, and a hand-rolled text scanner in place of marked's
// giant inline-text regex. Any block whose inline content this layer cannot
// render is rendered by marked itself (per-block fallback), so output is
// byte-identical to marked for every input.
//
// Credit: the inline algorithms (emphasis, strikethrough, links, autolinks,
// masking) follow marked 18.1.3's Tokenizer/Lexer; marked is MIT licensed,
// see vendor/marked/LICENSE and vendor/marked/NOTICE.

import { marked, Lexer } from './vendor/marked/marked.esm.js';

// ---------------------------------------------------------------------------
// Small helpers (same behaviour as marked's helpers.ts)
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

function escapeHtml(html, encode) {
  if (encode) {
    if (/[&<>"']/.test(html)) return html.replace(/[&<>"']/g, (ch) => ESCAPE_MAP[ch]);
  } else if (/[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/.test(html)) {
    return html.replace(/[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g, (ch) => ESCAPE_MAP[ch]);
  }
  return html;
}

const NUMERIC_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUMERIC_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

function decodeNumericRefs(text) {
  if (!NUMERIC_REF.test(text)) return text;
  return text.replace(NUMERIC_REF_OR_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? Number.parseInt(hex, 16) : Number.parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
  return href;
}

function rtrim(str, c) {
  let end = str.length;
  while (end > 0 && str.charAt(end - 1) === c) end--;
  return str.slice(0, end);
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
  return level > 0 ? -2 : -1;
}

function splitCells(tableRow, count) {
  const row = tableRow.replace(/\|/g, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(/ \|/);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1]?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

// ---------------------------------------------------------------------------
// Inline grammar (GFM, marked defaults). Patterns follow marked 18.1.3's
// rules.ts; sticky copies are used by the scanner loop below.
// ---------------------------------------------------------------------------

const PUNCT = '[\\p{P}\\p{S}]';
const PUNCT_GFM = '(?!~)[\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE = '[^\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_GFM = '(?:[^\\s\\p{P}\\p{S}]|~)';
const PUNCT_SPACE = '[\\s\\p{P}\\p{S}]';
const PUNCT_SPACE_GFM = '(?!~)[\\s\\p{P}\\p{S}]';

const reEscape = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const reCode = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const reBr = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const rePunctuation = /^((?![*_])[\s\p{P}\p{S}])/u;
const reUnicodeAlphaNumeric = /[\p{L}\p{N}]/u;
const reStartATag = /^<a /i;
const reEndATag = /^<\/a>/i;
const reStartPreScriptTag = /^<(pre|code|kbd|script)(\s|>)/i;
const reEndPreScriptTag = /^<\/(pre|code|kbd|script)(\s|>)/i;
const reStartAngleBracket = /^</;
const reEndAngleBracket = />$/;
const reHrefBrackets = /^<(.*)>$/;
const reOutputLinkReplace = /\\([\[\]])/g;
const reNotSpaceStart = /^\S*/;
const reEndingNewline = /\n$/;

const reEmStrongLDelim = new RegExp(
  '^(?:\\*+(?:((?!\\*)(?!~)' + PUNCT_GFM + ')|([^\\s*]))?)|^_+(?:((?!_)(?!~)' + PUNCT_GFM + ')|([^\\s_]))?', 'u',
);
const EM_STRONG_R_AST_CORE =
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)' // skip orphan inside strong
  + '|[^*]+(?=[^*])' // consume to delim
  + '|(?!\\*)' + PUNCT_GFM + '(\\*+)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE_GFM + '(\\*+)(?!\\*)(?=' + PUNCT_SPACE_GFM + '|$)'
  + '|(?!\\*)' + PUNCT_SPACE_GFM + '(\\*+)(?=' + NOT_PUNCT_SPACE_GFM + ')'
  + '|[\\s](\\*+)(?!\\*)(?=' + PUNCT_GFM + ')'
  + '|(?!\\*)' + PUNCT_GFM + '(\\*+)(?!\\*)(?=' + PUNCT_GFM + ')'
  + '|' + NOT_PUNCT_SPACE_GFM + '(\\*+)(?=' + NOT_PUNCT_SPACE_GFM + ')';
const reEmStrongRDelimAst = new RegExp(EM_STRONG_R_AST_CORE, 'gu');
const EM_STRONG_R_UND_CORE =
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)'
  + '|[^_]+(?=[^_])'
  + '|(?!_)' + PUNCT + '(_+)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE + '(_+)(?!_)(?=' + PUNCT_SPACE + '|$)'
  + '|(?!_)' + PUNCT_SPACE + '(_+)(?=' + NOT_PUNCT_SPACE + ')'
  + '|[\\s](_+)(?!_)(?=' + PUNCT + ')'
  + '|(?!_)' + PUNCT + '(_+)(?!_)(?=' + PUNCT + ')';
const reEmStrongRDelimUnd = new RegExp(EM_STRONG_R_UND_CORE, 'gu');

const reDelLDelim = new RegExp('^~~?(?:((?!~)' + PUNCT + ')|[^\\s~])', 'u');
const DEL_R_CORE =
  '^[^~]+(?=[^~])'
  + '|(?!~)' + PUNCT + '(~~?)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE + '(~~?)(?!~)(?=' + PUNCT_SPACE + '|$)'
  + '|(?!~)' + PUNCT_SPACE + '(~~?)(?=' + NOT_PUNCT_SPACE + ')'
  + '|[\\s](~~?)(?!~)(?=' + PUNCT + ')'
  + '|(?!~)' + PUNCT + '(~~?)(?!~)(?=' + PUNCT + ')'
  + '|' + NOT_PUNCT_SPACE + '(~~?)(?=' + NOT_PUNCT_SPACE + ')';
const reDelRDelim = new RegExp(DEL_R_CORE, 'gu');

const reAutolink = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;
const reTag = /^<!--(?:-?>|[\s\S]*?-->)|^<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*\s*\/?>|^<\?[\s\S]*?\?>|^<![a-zA-Z]+\s[\s\S]*?>|^<!\[CDATA\[[\s\S]*?\]\]>/;

// Link labels (CommonMark nesting to two levels, as marked does).
const LABEL_BRACKETS = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const INLINE_LABEL = '(?:\\[(?:' + LABEL_BRACKETS + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?';
const BLOCK_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+';
const reLink = new RegExp(
  '^!?\\[(' + INLINE_LABEL + ')\\]\\([ \\t\\n]*(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)("(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^\\)\\\\])*\\)))?[ \\t\\n]*\\)',
);
const reReflink = new RegExp('^!?\\[(' + INLINE_LABEL + ')\\]\\[(' + BLOCK_LABEL + ')\\]');
const reNolink = new RegExp('^!?\\[(' + BLOCK_LABEL + ')\\](?:\\[\\])?');

const BOUNDED_BLOCK_LABEL = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';
const BOUNDED_INLINE_LABEL = '(?:[^\\[\\]\\\\`]*(?:\\[(?:' + LABEL_BRACKETS + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?';
const reReflinkSearch = new RegExp(
  '!?\\[(' + BOUNDED_INLINE_LABEL + ')\\]\\[(' + BOUNDED_BLOCK_LABEL + ')\\]|!?\\[(' + BOUNDED_BLOCK_LABEL + ')\\](?:\\[\\])?(?!\\()', 'g',
);
const reBlockSkip = new RegExp(
  '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)'
  + '|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)'
  + '|<(?! )[^<>]*?>', 'g',
);
const reAnyPunctuation = new RegExp('\\\\(' + PUNCT + ')', 'gu');
const reAnyPunctOutsideCode = new RegExp(
  '(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\(' + PUNCT + ')', 'gu',
);

const EXTENDED_EMAIL = '[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])';
const EXTENDED_EMAIL_PROTOCOL = '(?:mailto:' + EXTENDED_EMAIL + '|xmpp:' + EXTENDED_EMAIL + '(?:\\/[A-Za-z0-9@.]+)?)';
const reUrl = new RegExp(
  '^' + EXTENDED_EMAIL_PROTOCOL
  + '|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*'
  + '|^' + '[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])',
);
const reBackpedal = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// Sticky copies for the scanner loop: the sticky flag itself anchors the
// match at lastIndex, and a literal ^ would only match at position 0, so
// the ^ anchors (at the start of the pattern and after |) are dropped.
function sticky(re) {
  const flags = re.flags.includes('y') ? re.flags : re.flags + 'y';
  return new RegExp(re.source.replace(/(^|\|)\^/g, '$1'), flags);
}
const sEscape = sticky(reEscape);
const sCode = sticky(reCode);
const sBr = sticky(reBr);
const sTag = sticky(reTag);
const sLink = sticky(reLink);
const sReflink = sticky(reReflink);
const sNolink = sticky(reNolink);
const sAutolink = sticky(reAutolink);
const sUrl = sticky(reUrl);
const sEmStrongLDelim = sticky(reEmStrongLDelim);
const sDelLDelim = sticky(reDelLDelim);

function execAt(re, src, pos) {
  re.lastIndex = pos;
  return re.exec(src);
}

// ---------------------------------------------------------------------------
// Closer hints: one scan of a masked inline run for the last runs that can
// close emphasis / strikethrough (mirrors marked's helpers.ts scan).
// ---------------------------------------------------------------------------

function scanClosers(src) {
  let star = -1;
  let underscore = -1;
  let tilde = -1;
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') tilde = i;
      else if (ch === '*') star = i;
      else underscore = i;
    }
    i = j - 1;
  }
  return { star, underscore, tilde };
}

function linkInText(text, links) {
  if (!text.includes('[')) return false;
  for (const match of text.matchAll(reBlockSkip)) {
    if (execAt(sLink, match[0], 0) && text.charAt(match.index - 1) !== '!') return true;
  }
  reReflinkSearch.lastIndex = 0;
  for (const match of text.matchAll(reReflinkSearch)) {
    const match0 = match[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(links, normalizeLabel(match0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(match0.slice(1, refStart - 1), links)) continue;
    return true;
  }
  return false;
}

function maskSrc(src, links, hasLinks) {
  let masked = src;
  if (hasLinks && src.includes('[')) {
    const maskReflink = (match0) => {
      const refStart = match0.lastIndexOf('[');
      if (!Object.hasOwn(links, normalizeLabel(match0.slice(refStart + 1, -1)))) return match0;
      if (refStart > 1 && match0.charAt(0) !== '!') {
        const text = match0.slice(1, refStart - 1);
        if (linkInText(text, links)) {
          return '[' + text.replace(reReflinkSearch, maskReflink)
            + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match0.length - 2) + ']';
    };
    masked = masked.replace(reReflinkSearch, maskReflink);
  }
  if (src.includes('\\') || src.includes('`')) {
    masked = masked.replace(reAnyPunctOutsideCode, (match0, code, punct) => {
      if (punct) return '+'.repeat(match0.length);
      if (code) return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
      return match0;
    });
  }
  if (src.includes('[') || src.includes('`') || src.includes('<')) {
    masked = masked.replace(reBlockSkip, (match0, _link, context) => {
      const offset = context ? context.length : 0;
      return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
    });
  }
  return masked;
}

function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      const code = execAt(sCode, label, i);
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const token = execAt(sTag, tokenSrc, 0) || execAt(sAutolink, tokenSrc, 0);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

// Emphasis / strong. Returns { raw, text, kind: 'em' | 'strong' } or null.
// `frame` is the closer scan of the run's full masked source; `maskedFull`
// is that masked source, aligned with the run (same length relationship as
// in marked: maskedFull.length - src.length is the consumed offset).
function emStrong(src, maskedFull, prevChar, frame) {
  const match0 = execAt(sEmStrongLDelim, src, 0);
  if (!match0) return null;
  if (!match0[1] && !match0[2] && !match0[3] && !match0[4]) return null;
  const delimChar = match0[0][0];
  const midRun = prevChar === delimChar;
  const srcStart = maskedFull.length - src.length;
  let runStart = srcStart;
  while (runStart > 0 && maskedFull[runStart - 1] === delimChar) runStart--;
  const runPrevChar = [...maskedFull.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!rePunctuation.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!rePunctuation.exec(prevChar);
  if (match0[4] && prevChar.match(reUnicodeAlphaNumeric)) return null;
  const nextChar = match0[1] || match0[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const lLength = [...match0[0]].length - 1;
    let rDelim;
    let rLength;
    let delimTotal = lLength;
    let midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim() && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return null;
    const endReg = delimChar === '*' ? reEmStrongRDelimAst : reEmStrongRDelimUnd;
    const lastPossible = delimChar === '*' ? frame.star : frame.underscore;
    const windowStart = maskedFull.length - src.length + lLength;
    if (lastPossible < windowStart) return null;
    let masked = maskedFull.slice(-1 * src.length + lLength);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    let match;
    while ((match = endReg.exec(masked)) !== null) {
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
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        return { kind: 'em', raw, text: raw.slice(1, -1) };
      }
      return { kind: 'strong', raw, text: raw.slice(2, -2) };
    }
  }
  return null;
}

// Strikethrough. Returns { raw, text } or null.
function delSpan(src, maskedFull, prevChar, frame) {
  const match0 = execAt(sDelLDelim, src, 0);
  if (!match0) return null;
  const nextChar = match0[1] || '';
  if (!nextChar || !prevChar || rePunctuation.exec(prevChar)) {
    const lLength = [...match0[0]].length - 1;
    let rDelim;
    let rLength;
    let delimTotal = lLength;
    const endReg = reDelRDelim;
    const lastPossible = frame.tilde;
    const windowStart = maskedFull.length - src.length + lLength;
    if (lastPossible < windowStart) return null;
    let masked = maskedFull.slice(-1 * src.length + lLength);
    const lastInWindow = lastPossible - windowStart;
    endReg.lastIndex = 0;
    let match;
    while ((match = endReg.exec(masked)) !== null) {
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
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      return { raw, text: raw.slice(lLength, -lLength) };
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// Inline rendering: direct-to-string port of marked's inline tokenizers +
// span renderers. Returns HTML (or plain text in 'text' mode, as marked's
// TextRenderer does for image alt text), or null to bail to marked.
// ---------------------------------------------------------------------------

const EMAIL_CODE = new Uint8Array(128);
for (const c of "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.!#$%&'*+/=?_`{|}~-") {
  EMAIL_CODE[c.charCodeAt(0)] = 1;
}
function isEmailCode(code) { return code < 128 && EMAIL_CODE[code] === 1; }
function isAlnumCode(code) {
  return (code >= 48 && code <= 57) || (code >= 65 && code <= 90) || (code >= 97 && code <= 122);
}
function emailRunAtCode(src, p) {
  let k = p;
  const len = src.length;
  while (k < len && isEmailCode(src.charCodeAt(k))) k++;
  return k > p && src.charCodeAt(k) === 64;
}
function spacesNewlineAtCode(src, p) {
  let k = p;
  while (src.charCodeAt(k) === 32) k++;
  return k - p >= 2 && src.charCodeAt(k) === 10;
}

// End index (exclusive) of the text run starting at `i`, mirroring marked's
// GFM inline-text regex stop conditions. `flags`: bit 1 email checks (the
// run holds '@'), bit 2 mailto:/xmpp: checks, bit 4 protocol checks (the
// run holds '://'), bit 8 www. checks.
function textRunEnd(src, i, flags) {
  const len = src.length;
  const firstCode = src.charCodeAt(i);
  // First alternative: a single non-alphanumeric char before mailto:/xmpp:.
  if ((flags & 2) && !isAlnumCode(firstCode)
    && (src.startsWith('mailto:', i + 1) || src.startsWith('xmpp:', i + 1))) {
    return i + 1;
  }
  let j = i + 1;
  if (firstCode === 96) { while (j < len && src.charCodeAt(j) === 96) j++; }
  else if (firstCode === 126) { while (j < len && src.charCodeAt(j) === 126) j++; }
  const first = j;
  for (; j <= len; j++) {
    if (j === len) return len;
    const c = src.charCodeAt(j);
    if (j === first && c === 32 && spacesNewlineAtCode(src, j)) return j;
    if (c === 92 || c === 60 || c === 33 || c === 91 || c === 96 || c === 42 || c === 126 || c === 95) return j;
    if ((flags & 4) && (c === 104 || c === 72 || c === 102 || c === 70)) {
      // http://, https://, ftp://, case-insensitive, checked by code units
      const c1 = src.charCodeAt(j + 1);
      const c2 = src.charCodeAt(j + 2);
      const c3 = src.charCodeAt(j + 3);
      if ((c === 104 || c === 72) && (c1 === 116 || c1 === 84) && (c2 === 116 || c2 === 84) && (c3 === 112 || c3 === 80)) {
        const c4 = src.charCodeAt(j + 4);
        if (c4 === 58 && src.charCodeAt(j + 5) === 47 && src.charCodeAt(j + 6) === 47) return j;
        if ((c4 === 115 || c4 === 83) && src.charCodeAt(j + 5) === 58
          && src.charCodeAt(j + 6) === 47 && src.charCodeAt(j + 7) === 47) return j;
      } else if ((c === 102 || c === 70) && (c1 === 116 || c1 === 84) && (c2 === 112 || c2 === 80) && c3 === 58
        && src.charCodeAt(j + 4) === 47 && src.charCodeAt(j + 5) === 47) {
        return j;
      }
    }
    if ((flags & 8) && c === 119 && src.startsWith('www.', j)) {
      const prev = src.charCodeAt(j - 1);
      if (prev === 32 || prev === 9 || prev === 10 || prev === 13 || prev === 12 || prev === 11
        || prev === 42 || prev === 95 || prev === 126 || prev === 40) return j;
    }
    if ((flags & 1) && j === first && emailRunAtCode(src, j)) return j;
    if (c !== 32 && src.charCodeAt(j + 1) === 32 && spacesNewlineAtCode(src, j + 1)) return j + 1;
    if ((flags & 2) && !isAlnumCode(c)
      && (src.startsWith('mailto:', j + 1) || src.startsWith('xmpp:', j + 1))) return j + 1;
    if ((flags & 1) && !isEmailCode(c) && emailRunAtCode(src, j + 1)) return j + 1;
  }
  return len;
}

function renderLinkOrImage(cap, href, title, isImage, raw, links, st, mode) {
  const text = cap[1].replace(reOutputLinkReplace, '$1');
  const outerInLink = st.inLink;
  const outerLinkEmitted = st.linkEmitted;
  const outerInRawBlock = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  // An image's label is only ever read as plain text (its alt attribute),
  // so tokenize it once, in text mode, with the same state marked uses
  // (inLink true); a link's label is rendered as HTML.
  const inner = renderInline(text, links, st, isImage ? 'text' : mode);
  if (inner === null) {
    st.inLink = outerInLink;
    st.linkEmitted = outerLinkEmitted;
    st.inRawBlock = outerInRawBlock;
    return null;
  }
  const textHasLink = st.linkEmitted;
  st.linkEmitted = outerLinkEmitted;
  st.inLink = outerInLink;
  if (!isImage) {
    if (textHasLink) {
      st.inRawBlock = outerInRawBlock;
      return null;
    }
    st.linkEmitted = true;
  }
  if (isImage) {
    if (mode === 'text') return { html: inner, len: raw.length };
    const cleanHref = cleanUrl(href);
    if (cleanHref === null) return { html: escapeHtml(inner), len: raw.length };
    let out = '<img src="' + escapeHtml(cleanHref) + '" alt="' + escapeHtml(inner) + '"';
    if (title) out += ' title="' + escapeHtml(title) + '"';
    out += '>';
    return { html: out, len: raw.length };
  }
  if (mode === 'text') return { html: inner, len: raw.length };
  const cleanHref = cleanUrl(href);
  if (cleanHref === null) return { html: inner, len: raw.length };
  let out = '<a href="' + escapeHtml(cleanHref) + '"';
  if (title) out += ' title="' + escapeHtml(title) + '"';
  out += '>' + inner + '</a>';
  return { html: out, len: raw.length };
}

function tryLink(src, pos, links, st, mode) {
  if (st.linkParenPossible === false) return null;
  const cap = execAt(sLink, src, pos);
  if (!cap) return null;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src.slice(pos), cap[1], labelStart)) return null;
  const trimmedUrl = cap[2].trim();
  if (reStartAngleBracket.test(trimmedUrl)) {
    if (!reEndAngleBracket.test(trimmedUrl)) return null;
    const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return null;
  } else {
    const lastParenIndex = findClosingBracket(cap[2], '()');
    if (lastParenIndex === -2) return null;
    if (lastParenIndex > -1) {
      const start = cap[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + cap[1].length + lastParenIndex;
      cap[2] = cap[2].substring(0, lastParenIndex);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  const unescaped = rtrim(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return null;
  let href = cap[2];
  let title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (reStartAngleBracket.test(href)) href = href.slice(1, -1);
  const isImage = cap[0].charAt(0) === '!';
  return renderLinkOrImage(
    cap,
    href ? href.replace(reAnyPunctuation, '$1') : href,
    title ? title.replace(reAnyPunctuation, '$1') : title,
    isImage,
    cap[0],
    links,
    st,
    mode,
  );
}

function tryReflink(src, pos, links, st, mode) {
  const cap = execAt(sReflink, src, pos) || execAt(sNolink, src, pos);
  if (!cap) return null;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src.slice(pos), cap[1], labelStart)) return null;
  const link = links[normalizeLabel(cap[2] || cap[1])];
  if (!link) return { textChar: cap[0].charAt(0) };
  const isImage = cap[0].charAt(0) === '!';
  return renderLinkOrImage(cap, link.href, link.title || null, isImage, cap[0], links, st, mode);
}

function renderAutolinkLike(text, href, mode) {
  if (mode === 'text') return text;
  const parsedText = escapeHtml(text, true);
  const cleanHref = cleanUrl(href);
  if (cleanHref === null) return parsedText;
  return '<a href="' + escapeHtml(cleanHref, true) + '">' + parsedText + '</a>';
}

function tryAutolink(src, pos, mode) {
  const cap = execAt(sAutolink, src, pos);
  if (!cap) return null;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  return { html: renderAutolinkLike(text, href, mode), len: cap[0].length };
}

function tryUrl(src, pos, mode) {
  let cap = execAt(sUrl, src, pos);
  if (!cap) return null;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + text;
  } else {
    let prevCapZero;
    do {
      prevCapZero = cap[0];
      cap[0] = reBackpedal.exec(cap[0])?.[0] ?? '';
    } while (prevCapZero !== cap[0]);
    text = cap[0];
    if (cap[1] === 'www.') href = 'http://' + cap[0];
    else href = cap[0];
  }
  return { html: renderAutolinkLike(text, href, mode), len: cap[0].length };
}

function renderInline(src, links, st, mode) {
  const prevParen = st.linkParenPossible;
  st.linkParenPossible = prevParen && src.includes(')');
  try {
    return renderInlineInner(src, links, st, mode);
  } finally {
    st.linkParenPossible = prevParen;
  }
}

function renderInlineInner(src, links, st, mode) {
  // Masking (for emphasis/strikethrough) is only built when a delimiter is
  // actually attempted, not for every run that merely holds one.
  let maskedFull = null;
  let frame = null;
  const ensureMask = () => {
    if (maskedFull === null) {
      maskedFull = maskSrc(src, links, st.hasLinks);
      frame = scanClosers(maskedFull);
    }
  };
  const flags = (src.includes('@') ? 1 : 0)
    | ((src.includes('mailto:') || src.includes('xmpp:')) ? 2 : 0)
    | (src.includes('://') ? 4 : 0)
    | (src.includes('www.') ? 8 : 0);
  const len = src.length;
  let out = '';
  let i = 0;
  let keepPrevChar = false;
  let prevChar = '';
  while (i < len) {
    if (!keepPrevChar) prevChar = '';
    keepPrevChar = false;
    const code = src.charCodeAt(i);
    let done = null;
    if (code === 92) { // backslash
      const cap = execAt(sEscape, src, i);
      if (cap) {
        done = { html: mode === 'text' ? cap[1] : escapeHtml(cap[1]), len: cap[0].length };
      } else {
        const brCap = execAt(sBr, src, i);
        if (brCap) done = { html: mode === 'text' ? '' : '<br>', len: brCap[0].length };
      }
    } else if (code === 60) { // <
      const cap = execAt(sTag, src, i);
      if (cap) {
        if (!st.inLink && reStartATag.test(cap[0])) st.inLink = true;
        else if (st.inLink && reEndATag.test(cap[0])) st.inLink = false;
        if (!st.inRawBlock && reStartPreScriptTag.test(cap[0])) st.inRawBlock = true;
        else if (st.inRawBlock && reEndPreScriptTag.test(cap[0])) st.inRawBlock = false;
        done = { html: cap[0], len: cap[0].length };
      } else {
        done = tryAutolink(src, i, mode);
      }
    } else if (code === 91 || (code === 33 && src.charCodeAt(i + 1) === 91)) { // [ or ![
      done = tryLink(src, i, links, st, mode) || tryReflink(src, i, links, st, mode);
      if (done && done.textChar !== undefined) {
        out += done.textChar;
        i += 1;
        continue;
      }
    } else if (code === 42 || code === 95) { // * _
      ensureMask();
      const res = emStrong(src.slice(i), maskedFull, prevChar, frame);
      if (res) {
        const inner = renderInline(res.text, links, st, mode);
        if (inner === null) return null;
        done = {
          html: mode === 'text' ? inner : (res.kind === 'em' ? '<em>' + inner + '</em>' : '<strong>' + inner + '</strong>'),
          len: res.raw.length,
        };
      }
    } else if (code === 96) { // backtick
      const cap = execAt(sCode, src, i);
      if (cap) {
        let text = cap[2].replace(/\n/g, ' ');
        const hasNonSpaceChars = /[^ ]/.test(text);
        const hasSpaceCharsOnBothEnds = /^ /.test(text) && / $/.test(text);
        if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) text = text.substring(1, text.length - 1);
        done = { html: mode === 'text' ? text : '<code>' + escapeHtml(text, true) + '</code>', len: cap[0].length };
      }
    } else if (code === 32) { // space
      const brCap = execAt(sBr, src, i);
      if (brCap) done = { html: mode === 'text' ? '' : '<br>', len: brCap[0].length };
    } else if (code === 126) { // ~
      ensureMask();
      const res = delSpan(src.slice(i), maskedFull, prevChar, frame);
      if (res) {
        const inner = renderInline(res.text, links, st, mode);
        if (inner === null) return null;
        done = { html: mode === 'text' ? inner : '<del>' + inner + '</del>', len: res.raw.length };
      }
    } else if ((code >= 48 && code <= 57) || (code >= 65 && code <= 90) || (code >= 97 && code <= 122)
      || code === 46 || code === 95 || code === 43 || code === 45) {
      if (!st.inLink) done = tryUrl(src, i, mode);
    }
    if (done) {
      out += done.html;
      i += done.len;
      continue;
    }
    // Plain text run.
    const end = textRunEnd(src, i, flags);
    if (end <= i) return null; // no progress: bail to marked
    const raw = src.slice(i, end);
    if (mode === 'text') {
      out += st.inRawBlock ? raw : decodeNumericRefs(raw);
    } else {
      out += st.inRawBlock ? raw : escapeHtml(decodeNumericRefs(raw));
    }
    if (raw.slice(-1) !== '_') prevChar = raw.slice(-1);
    keepPrevChar = true;
    i = end;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Block rendering over the token tree marked's Lexer produces. Returns the
// HTML string, or null when a block needs marked's own rendering.
// ---------------------------------------------------------------------------

function inlineWithCheckbox(token, links, st) {
  st.inRawBlock = false;
  let prefix = '';
  let text = token.text;
  if (token.tokens && token.tokens.length > 0) {
    if (token.tokens.length !== 1 || token.tokens[0].type !== 'checkbox') return null;
    const cb = token.tokens[0];
    prefix = '<input ' + (cb.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
    const m = /^\[[ xX]\] /.exec(text);
    if (!m) return null;
    text = text.slice(m[0].length);
  }
  const html = renderInline(text, links, st, 'html');
  if (html === null) return null;
  return prefix + html;
}

function renderCode(token) {
  const langString = (token.lang || '').match(/^\S*/)?.[0];
  const code = token.text ? token.text.replace(/\n$/, '') + '\n' : '';
  if (!langString) return '<pre><code>' + escapeHtml(code, true) + '</code></pre>\n';
  return '<pre><code class="language-' + escapeHtml(langString) + '">' + escapeHtml(code, true) + '</code></pre>\n';
}

function renderBlocks(tokens, links, st) {
  let out = '';
  for (const token of tokens) {
    switch (token.type) {
      case 'space':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading': {
        st.inRawBlock = false;
        const inner = renderInline(token.text, links, st, 'html');
        if (inner === null) return null;
        out += '<h' + token.depth + '>' + inner + '</h' + token.depth + '>\n';
        break;
      }
      case 'code':
        out += renderCode(token);
        break;
      case 'table': {
        let header = '';
        for (const cell of token.header) {
          st.inRawBlock = false;
          const content = renderInline(cell.text, links, st, 'html');
          if (content === null) return null;
          const tag = cell.align ? '<th align="' + cell.align + '">' : '<th>';
          header += tag + content + '</th>\n';
        }
        let body = '';
        for (const row of token.rows) {
          let cellHtml = '';
          for (const cell of row) {
            st.inRawBlock = false;
            const content = renderInline(cell.text, links, st, 'html');
            if (content === null) return null;
            const tag = cell.align ? '<td align="' + cell.align + '">' : '<td>';
            cellHtml += tag + content + '</td>\n';
          }
          body += '<tr>\n' + cellHtml + '</tr>\n';
        }
        if (body) body = '<tbody>' + body + '</tbody>';
        out += '<table>\n<thead>\n<tr>\n' + header + '</tr>\n</thead>\n' + body + '</table>\n';
        break;
      }
      case 'blockquote': {
        const inner = renderBlocks(token.tokens, links, st);
        if (inner === null) return null;
        out += '<blockquote>\n' + inner + '</blockquote>\n';
        break;
      }
      case 'list': {
        let body = '';
        for (const item of token.items) {
          const inner = renderBlocks(item.tokens, links, st);
          if (inner === null) return null;
          body += '<li>' + inner + '</li>\n';
        }
        const type = token.ordered ? 'ol' : 'ul';
        const startAttr = (token.ordered && token.start !== 1) ? (' start="' + token.start + '"') : '';
        out += '<' + type + startAttr + '>\n' + body + '</' + type + '>\n';
        break;
      }
      case 'checkbox':
        out += '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'html':
        out += token.text;
        break;
      case 'def':
        break;
      case 'paragraph': {
        const inner = inlineWithCheckbox(token, links, st);
        if (inner === null) return null;
        out += '<p>' + inner + '</p>\n';
        break;
      }
      case 'text': {
        const inner = inlineWithCheckbox(token, links, st);
        if (inner === null) return null;
        out += inner;
        break;
      }
      default:
        return null;
    }
  }
  return out;
}

function collectDefs(token, blockIndex, defs) {
  if (token.type === 'def') {
    defs.push({ raw: token.raw, blockIndex });
    return;
  }
  if (token.tokens) {
    for (const t of token.tokens) collectDefs(t, blockIndex, defs);
  }
  if (token.items) {
    for (const item of token.items) {
      for (const t of item.tokens) collectDefs(t, blockIndex, defs);
    }
  }
}

// Render one top-level block with marked, keeping link definitions in
// document order around it so first-definition-wins still holds.
function fallbackBlock(token, blockIndex, defs) {
  const raw = token.raw;
  if (token.type === 'html' || token.type === 'code' || !raw.includes('[')) {
    return marked.parse(raw);
  }
  const before = [];
  const after = [];
  for (const d of defs) {
    if (d.blockIndex < blockIndex) before.push(d.raw);
    else if (d.blockIndex > blockIndex) after.push(d.raw);
  }
  let src = '';
  if (before.length > 0) src += before.join('\n') + '\n\n';
  src += raw;
  if (after.length > 0) src += '\n\n' + after.join('\n');
  return marked.parse(src);
}

function fastParse(src) {
  const lexer = new Lexer();
  const tokens = lexer.blockTokens(src, []);
  const links = lexer.tokens.links;
  const defs = [];
  for (let bi = 0; bi < tokens.length; bi++) collectDefs(tokens[bi], bi, defs);
  const st = { inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true, hasLinks: Object.keys(links).length > 0 };
  let out = '';
  for (let bi = 0; bi < tokens.length; bi++) {
    const token = tokens[bi];
    const html = renderBlocks([token], links, st);
    out += html === null ? fallbackBlock(token, bi, defs) : html;
  }
  return out;
}

/** The HTML marked 18.1.3 renders for `markdown`, with marked's defaults. */
export function parse(markdown) {
  const src = markdown.replace(/\r\n|\r/g, '\n');
  try {
    const out = fastParse(src);
    if (out !== null && out !== undefined) return out;
  } catch {
    // Any surprise in the fast path falls back to marked itself.
  }
  return marked.parse(markdown);
}
