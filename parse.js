// marked-swift: a faster drop-in for marked 18.1.3 (MIT, MarkedJS).
//
// Strategy: the block layer is a direct port of marked's Lexer.blockTokens
// and Tokenizer block methods, written index-based with sticky regexes and
// a first-character dispatch, so no per-block substring churn. It produces
// the same token tree marked's Lexer does; if it ever bails or disagrees
// with itself, marked's own Lexer (vendored in vendor/marked/, byte for
// byte the npm build) takes over for that case. The inline layer and the
// rendering layer are re-implemented here as a single direct-to-string
// pass: no inline token objects, no second parser walk, a first-character
// dispatch instead of trying every inline rule at every position, and a
// hand-rolled text scanner in place of marked's giant inline-text regex.
// Any block whose inline content this layer cannot render is rendered by
// marked itself (per-block fallback), so output is byte-identical to
// marked for every input.
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
  let tokens;
  let links;
  try {
    const splitter = new Splitter();
    const myTokens = [];
    const endPos = splitter.blockTokens(src, 0, src.length, myTokens, false);
    if (endPos !== src.length) throw new Error('splitter incomplete');
    tokens = myTokens;
    links = splitter.links;
  } catch {
    // Splitter bailed: marked's own Lexer for the block tree (V1 path).
    const lexer = new Lexer();
    tokens = lexer.blockTokens(src, []);
    links = lexer.tokens.links;
  }
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

// ---------------------------------------------------------------------------
// V2 block splitter: a direct port of marked's block layer (Lexer.blockTokens
// + Tokenizer block methods), written index-based with sticky regexes and a
// first-character dispatch, so no per-block substring churn. It produces the
// same token tree marked's Lexer does; renderBlocks above consumes it.
// ---------------------------------------------------------------------------

// marked's edit() strips ^ anchors from an inserted pattern (its caret rule).
function stripCaret(s) {
  return s.replace(/(^|[^\[])\^/g, '$1');
}
// Build a sticky regex from a source string: ^ anchors are dropped because
// the sticky flag itself anchors the match at lastIndex.
function by(src, flags) {
  return new RegExp(stripCaret(src), (flags || '') + 'y');
}

function expandTabs(line, indent) {
  let col = indent || 0;
  let expanded = '';
  for (const char of line) {
    if (char === '\t') {
      const added = 4 - (col % 4);
      expanded += ' '.repeat(added);
      col += added;
    } else {
      expanded += char;
      col++;
    }
  }
  return expanded;
}

function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && /^[ \t]*$/.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

const TAG_LIST = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';
const COMMENT_SRC = '<!--(?:-?>|[\\s\\S]*?(?:-->|$))';
const BULLET_SRC = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const HR_SRC = ' {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const HEADING_START_SRC = ' {0,3}#{1,6}(?:\\s|$)';
const BLOCK_CODE_SRC = '(?: {4}| {0,3}\\t)';
const FENCES_START_SRC = ' {0,3}(?:`{3,}|~{3,})';
const BLOCKQUOTE_START_SRC = ' {0,3}>';
const HTML_LINE_SRC = ' {0,3}<[^\\n>]+>\\n';
const HTML_INTERRUPT_SRC = ' {0,3}(?:</?(?:' + TAG_LIST + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';
const FENCES_INTERRUPT_SRC = ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)';
// marked's inline.anyPunctuation: backslash + punctuation -> the punctuation
const anyPunctRe = /\\([\p{P}\p{S}])/gu;

// Block grammar (GFM), sticky, as marked's rules.ts builds it.
const bNewline = by('^(?:[ \\t]*(?:\\n|$))+');
const bCode = by('^((?: {4}| {0,3}\\t)[^\\n]+(?:\\n(?:[ \\t]*(?:\\n|$))*)?)+');
const bFences = by('^ {0,3}(`{3,}(?=[^`\\n]*(?:\\n|$))|~{3,})([^\\n]*)(?:\\n|$)(?:|([\\s\\S]*?)(?:\\n|$))(?: {0,3}(?:(?=`)\\1`*|(?=~)\\1~*) *(?=\\n|$)|$)');
const bHr = by('^' + HR_SRC);
const bHeading = by('^ {0,3}(#{1,6})(?=\\s|$)(.*)(?:\\n+|$)');
const bList = by('^(' + BULLET_SRC + ')([ \\t][^\\n]*?)?(?:\\n|$)');
const bText = by('^[^\\n]+');
const bDef = by('^ {0,3}\\[(' + BLOCK_LABEL + ')\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)("(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\)))? *(?:\\n+|$)');
const bHtml = by('^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
  + '|' + COMMENT_SRC + '[^\\n]*(\\n+|$)'
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
  + '|</?(' + TAG_LIST + ')(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + ')', 'i');

// Setext heading (GFM): the table alternative is the GFM one.
const LHEADING_CORE = '^(?!BULLET |BLOCKCODE|FENCES|BLOCKQUOTE|HEADING|HR|HTML|TABLE)((?:.|\\n(?!\\s*?\\n|BULLET |FENCES|BLOCKQUOTE|HEADING|HR|HTML|TABLE))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)';
// In the setext pattern marked inserts a NON-capturing hr variant (the hr
// regex's capturing group would shift the underline to group 3).
const LH_HR_SRC = ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const bLheading = by(LHEADING_CORE
  .replace(/BULLET/g, BULLET_SRC)
  .replace(/BLOCKCODE/g, BLOCK_CODE_SRC)
  .replace(/FENCES/g, FENCES_START_SRC)
  .replace(/BLOCKQUOTE/g, BLOCKQUOTE_START_SRC)
  .replace(/HEADING/g, HEADING_START_SRC)
  .replace(/HR/g, LH_HR_SRC)
  .replace(/HTML/g, HTML_LINE_SRC)
  .replace(/TABLE/g, ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n'));

// GFM table.
const bTable = by('^ *([^\\n ].*)\\n'
  + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
  + '(?:\\n((?:(?! *\\n|HR|HEADING|BLOCKQUOTE|CODE|FENCES|LIST|HTML).*(?:\\n|$))*)\\n*|$)'
  .replace(/HR/g, HR_SRC)
  .replace(/HEADING/g, HEADING_START_SRC)
  .replace(/BLOCKQUOTE/g, BLOCKQUOTE_START_SRC)
  .replace(/CODE/g, BLOCK_CODE_SRC + '[^\\n]')
  .replace(/FENCES/g, FENCES_INTERRUPT_SRC)
  .replace(/LIST/g, ' {0,3}(?:[*+-]|1[.)])[ \\t]')
  .replace(/HTML/g, HTML_INTERRUPT_SRC));

// Paragraph variants (used inside the blockquote pattern).
function buildParagraph(listInterruptSrc) {
  return '^([^\\n]+(?:\\n(?!'
    + HR_SRC + '|'
    + HEADING_START_SRC + '|'
    + BLOCKQUOTE_START_SRC + '|'
    + FENCES_INTERRUPT_SRC + '|'
    + listInterruptSrc + '|'
    + HTML_INTERRUPT_SRC
    + '|[ \\t]+\\n)[^\\n]+)*)';
}
const bBlockquoteParagraph = by(buildParagraph(' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)'));
const bBlockquote = by('^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(' + stripCaret(bBlockquoteParagraph.source) + ')|[^\\n]*)(?:\\n|$))+');

// Line-level interrupt checks for the manual paragraph scanner (GFM).
const pHr = by(HR_SRC);
const pHeading = by(HEADING_START_SRC);
const pBlockquote = by(BLOCKQUOTE_START_SRC);
const pFences = by(FENCES_INTERRUPT_SRC);
const pList = by(' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]');
const pHtml = by(HTML_INTERRUPT_SRC);

function indentCodeCompensation(raw, text) {
  const m = /^(\s+)(?:```)/.exec(raw);
  if (m === null) return text;
  const indentToCode = m[1];
  return text.split('\n').map((node) => {
    const mm = /^\s+/.exec(node);
    if (mm === null) return node;
    return node.slice(Math.min(mm[0].length, indentToCode.length));
  }).join('\n');
}

// Cheap pre-checks used by the main dispatch (supersets: they never exclude
// a real match, they only skip regexes that cannot match).
function secondLineIsTableDelimiter(src, lineStart) {
  // The line after the current one must look like a table delimiter row.
  const nl = src.indexOf('\n', lineStart);
  if (nl === -1) return false;
  let s = nl + 1;
  let spaces = 0;
  while (src.charCodeAt(s) === 32 && spaces < 3) { s++; spaces++; }
  let hasDash = false;
  let i = s;
  for (; i < src.length; i++) {
    const c = src.charCodeAt(i);
    if (c === 10) break;
    if (c === 45) hasDash = true;
    else if (c !== 32 && c !== 124 && c !== 58 && c !== 9) return false;
  }
  return hasDash && i > s;
}
// Is the line starting at ls a setext underline (<=3 spaces, then only =
// or only -, then spaces/tabs to end of line)?
function lineIsSetext(src, ls) {
  let s = ls;
  let spaces = 0;
  while (src.charCodeAt(s) === 32 && spaces < 3) { s++; spaces++; }
  const c0 = src.charCodeAt(s);
  if (c0 !== 61 && c0 !== 45) return false;
  let i = s + 1;
  for (; i < src.length; i++) {
    const c = src.charCodeAt(i);
    if (c === 10) break;
    if (c !== c0 && c !== 32 && c !== 9) return false;
  }
  return i > s;
}
function secondLineIsSetext(src, lineStart) {
  const nl = src.indexOf('\n', lineStart);
  if (nl === -1) return false;
  return lineIsSetext(src, nl + 1);
}
// A setext underline may sit several lines down (the heading text can span
// lines), so scan forward until a blank line: if any line before it is a
// setext underline, the lheading regex is worth trying.
function hasSetextAhead(src, p) {
  let ls = src.indexOf('\n', p);
  if (ls === -1) return false;
  let scanned = 0;
  while (ls !== -1 && scanned < 200) {
    const lineStart = ls + 1;
    if (lineStart >= src.length) return false;
    if (lineIsSetext(src, lineStart)) return true;
    // blank line ends the possible heading text
    let le = src.indexOf('\n', lineStart);
    if (le === -1) le = src.length;
    let blank = true;
    for (let i = lineStart; i < le; i++) {
      const c = src.charCodeAt(i);
      if (c !== 32 && c !== 9) { blank = false; break; }
    }
    if (blank) return false;
    ls = le;
    scanned++;
  }
  return false;
}

// Manual paragraph scanner: replicates the GFM paragraph regex
// ^([^\n]+(?:\n(?!hr|heading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)
// without running the regex itself. Returns the raw text, or null.
function paragraphAt(src, p) {
  const n = src.length;
  let lineEnd = src.indexOf('\n', p);
  if (lineEnd === -1) lineEnd = n;
  let end = lineEnd; // end of the last consumed line (no trailing \n)
  while (end < n && src.charCodeAt(end) === 10) {
    const ls = end + 1;
    if (ls >= n) break;
    const le = src.indexOf('\n', ls);
    const lineEnd2 = le === -1 ? n : le;
    // blank line: all spaces/tabs then \n (an empty line counts too)
    let blank = src.charCodeAt(lineEnd2) === 10;
    if (blank) {
      for (let i = ls; i < lineEnd2; i++) {
        const c = src.charCodeAt(i);
        if (c !== 32 && c !== 9) { blank = false; break; }
      }
    }
    if (blank) break;
    // first significant char of the next line (<=3 spaces of indent): only
    // the interrupt whose pattern can start with it is worth trying
    let k = ls;
    while (k < lineEnd2 && src.charCodeAt(k) === 32 && k - ls < 3) k++;
    const fc = src.charCodeAt(k);
    if ((fc === 45 || fc === 95 || fc === 42) && execAt(pHr, src, ls)) break;
    if (fc === 35 && execAt(pHeading, src, ls)) break;
    if (fc === 62 && execAt(pBlockquote, src, ls)) break;
    if ((fc === 96 || fc === 126) && execAt(pFences, src, ls)) break;
    if ((fc === 42 || fc === 43 || fc === 45 || fc === 49) && execAt(pList, src, ls)) break;
    if (fc === 60 && execAt(pHtml, src, ls)) break;
    // table interrupt: header line + delimiter line (gated cheaply)
    if (secondLineIsTableDelimiter(src, ls) && execAt(bTable, src, ls)) break;
    end = lineEnd2;
  }
  return src.slice(p, end);
}

// Index-based splitter producing marked's block token tree.
class Splitter {
  constructor() {
    this.links = {};
    this.top = true;
  }

  blockTokens(src, p, end, tokens, lastParagraphClipped) {
    let srcLength = Infinity;
    let lastParagraphClippedLocal = lastParagraphClipped;
    while (p < end) {
      const len = end - p;
      if (len < srcLength) srcLength = len;
      else break; // infinite loop guard: a token consumed nothing

      const c0 = src.charCodeAt(p);
      // first significant character after at most 3 leading spaces (block
      // rules allow up to 3 spaces of indent)
      let s = p;
      while (s < end && src.charCodeAt(s) === 32 && s - p < 3) s++;
      const cs = src.charCodeAt(s);

      // space: blank lines / trailing newlines
      if (c0 === 10 || c0 === 32 || c0 === 9) {
        const cap = execAt(bNewline, src, p);
        if (cap) {
          p += cap[0].length;
          if (cap[0].length === 1 && tokens.length > 0) {
            tokens[tokens.length - 1].raw += '\n';
          } else {
            tokens.push({ type: 'space', raw: cap[0] });
          }
          continue;
        }
      }

      // indented code
      if (c0 === 32 || c0 === 9) {
        const cap = execAt(bCode, src, p);
        if (cap) {
          const raw = trimTrailingBlankLines(cap[0]);
          const text = raw.replace(/^(?: {0,3}\t| {1,4})/gm, '');
          p += raw.length;
          const last = tokens[tokens.length - 1];
          if (last && (last.type === 'paragraph' || last.type === 'text')) {
            last.raw += (last.raw.endsWith('\n') ? '' : '\n') + raw;
            last.text += '\n' + text;
          } else {
            tokens.push({ type: 'code', raw, codeBlockStyle: 'indented', text });
          }
          continue;
        }
      }

      // fences
      if (cs === 96 || cs === 126) {
        const cap = execAt(bFences, src, p);
        if (cap) {
          const raw = cap[0];
          const text = indentCodeCompensation(raw, cap[3] || '');
          p += raw.length;
          tokens.push({ type: 'code', raw, lang: cap[2] ? cap[2].trim().replace(anyPunctRe, '$1') : cap[2], text });
          continue;
        }
      }

      // ATX heading
      if (cs === 35) {
        const cap = execAt(bHeading, src, p);
        if (cap) {
          let text = cap[2].trim();
          if (/#$/.test(text)) {
            const trimmed = rtrim(text, '#');
            if (!trimmed || /[ \t]$/.test(trimmed)) {
              text = trimmed.trim();
            }
          }
          const raw = rtrim(cap[0], '\n');
          p += raw.length;
          tokens.push({ type: 'heading', raw, depth: cap[1].length, text, tokens: [] });
          continue;
        }
      }

      // hr
      if (cs === 45 || cs === 95 || cs === 42) {
        const cap = execAt(bHr, src, p);
        if (cap) {
          const raw = rtrim(cap[0], '\n');
          p += raw.length;
          tokens.push({ type: 'hr', raw });
          continue;
        }
      }

      // blockquote
      if (cs === 62) {
        const r = this.blockquote(src, p, end);
        if (r) {
          p = r.end;
          tokens.push(r.token);
          continue;
        }
      }

      // list
      if (cs === 42 || cs === 43 || cs === 45 || (cs >= 48 && cs <= 57)) {
        const r = this.list(src, p, end);
        if (r) {
          p = r.end;
          tokens.push(r.token);
          continue;
        }
      }

      // html block
      if (cs === 60) {
        const cap = execAt(bHtml, src, p);
        if (cap) {
          const raw = trimTrailingBlankLines(cap[0]);
          p += raw.length;
          tokens.push({ type: 'html', block: true, raw, pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style', text: raw });
          continue;
        }
      }

      // link-ref definition
      if (cs === 91) {
        const cap = execAt(bDef, src, p);
        if (cap) {
          // outside angle brackets a link destination holds only balanced parens
          if (cap[2].charAt(0) !== '<' && findClosingBracket(cap[2], '()') !== -1) {
            // fall through to paragraph/text below
          } else {
            const tag = normalizeLabel(cap[1]);
            const href = cap[2] ? cap[2].replace(/^<(.*)>$/, '$1').replace(anyPunctRe, '$1') : '';
            const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(anyPunctRe, '$1') : cap[3];
            const raw = rtrim(cap[0], '\n');
            p += raw.length;
            const last = tokens[tokens.length - 1];
            if (last && (last.type === 'paragraph' || last.type === 'text')) {
              last.raw += (last.raw.endsWith('\n') ? '' : '\n') + raw;
              last.text += '\n' + raw;
            } else {
              if (!this.links[tag]) this.links[tag] = { href, title };
              tokens.push({ type: 'def', tag, raw, href, title });
            }
            continue;
          }
        }
      }

      // table
      if (secondLineIsTableDelimiter(src, p)) {
        const cap = execAt(bTable, src, p);
        if (cap && /[:|]/.test(cap[2])) {
          const aligns = cap[2].replace(/^\||\| *$/g, '').split('|');
          const headers = splitCells(cap[1]);
          if (headers.length === aligns.length) {
            const align = aligns.map((d) => {
              if (/^ *-+: *$/.test(d)) return 'right';
              if (/^ *:-+: *$/.test(d)) return 'center';
              if (/^ *:-+ *$/.test(d)) return 'left';
              return null;
            });
            const header = headers.map((cell, i) => ({ text: cell, tokens: [], header: true, align: align[i] }));
            const rows = cap[3] && cap[3].trim() ? cap[3].replace(/\n[ \t]*$/, '').split('\n').map((row) => splitCells(row, header.length).map((cell, i) => ({ text: cell, tokens: [], header: false, align: align[i] }))) : [];
            const raw = rtrim(cap[0], '\n');
            p += raw.length;
            tokens.push({ type: 'table', raw, header, align, rows });
            continue;
          }
        }
      }

      // setext heading
      if (hasSetextAhead(src, p)) {
        const cap = execAt(bLheading, src, p);
        if (cap) {
          const raw = rtrim(cap[0], '\n');
          p += raw.length;
          tokens.push({ type: 'heading', raw, depth: cap[2].charAt(0) === '=' ? 1 : 2, text: cap[1].trim(), tokens: [] });
          continue;
        }
      }

      // paragraph (only when state.top)
      if (this.top) {
        const raw = paragraphAt(src, p);
        if (raw) {
          const text = raw.endsWith('\n') ? raw.slice(0, -1) : raw;
          p += raw.length;
          const last = tokens[tokens.length - 1];
          if (lastParagraphClippedLocal && last && last.type === 'paragraph') {
            last.raw += (last.raw.endsWith('\n') ? '' : '\n') + raw;
            last.text += '\n' + text;
          } else {
            tokens.push({ type: 'paragraph', raw, text, tokens: [] });
          }
          lastParagraphClippedLocal = false;
          continue;
        }
      }

      // text (fallback: one line)
      const cap = execAt(bText, src, p);
      if (cap) {
        const raw = cap[0];
        p += raw.length;
        const last = tokens[tokens.length - 1];
        if (last && last.type === 'text') {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + raw;
          last.text += '\n' + raw;
        } else {
          tokens.push({ type: 'text', raw, text: raw, tokens: [] });
        }
        continue;
      }

      break; // nothing matched: bail to marked fallback
    }
    this.top = true;
    return p;
  }
}


// --- blockquote + list (ported from marked's Tokenizer; index-based) ---

const bqStart = /^ {0,3}>/;
const bqMarkerWhitespace = /^( {0,3}>)([ \t]+)/gm;
const bqSetextReplace = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const bqSetextReplace2 = /^ {0,3}>[ \t]?/gm;

function cachedIndentRegex(create) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) { re = create(idx); cache[idx] = re; }
    return re;
  };
}
const nextBulletRegexFn = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`));
const hrRegexFn = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`));
const fencesBeginRegexFn = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`));
const headingBeginRegexFn = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`));
const htmlBeginRegexFn = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}(?:</?(?:${TAG_LIST})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const blockquoteBeginRegexFn = cachedIndentRegex((i) => new RegExp(`^ {0,${i}}>`));

function nextLineAt(src, p, end) {
  const nl = src.indexOf('\n', p);
  if (nl === -1 || nl >= end) return src.slice(p, end);
  return src.slice(p, nl);
}

Splitter.prototype.blockquote = function (src, p, end) {
  const cap = execAt(bBlockquote, src, p);
  if (!cap) return null;
  let lines = rtrim(cap[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];
  while (lines.length > 0) {
    let inBlockquote = false;
    const currentLines = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (bqStart.test(lines[i])) {
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
      .replace(bqMarkerWhitespace, (_, marker, whitespace) => marker + expandTabs(whitespace, marker.length))
      .replace(bqSetextReplace, '\n    $1')
      .replace(bqSetextReplace2, '');
    raw = raw ? raw + '\n' + currentRaw : currentRaw;
    text = text ? text + '\n' + currentText : currentText;
    const top = this.top;
    this.top = true;
    this.blockTokens(currentText, 0, currentText.length, tokens, true);
    this.top = top;
    if (lines.length === 0) break;
    const lastToken = tokens[tokens.length - 1];
    if (lastToken && (lastToken.type === 'code' || lastToken.type === 'heading' || lastToken.type === 'hr' || lastToken.type === 'html' || lastToken.type === 'table')) {
      break;
    } else if (lastToken && lastToken.type === 'blockquote') {
      const oldToken = lastToken;
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(bqSetextReplace2, '');
      const newToken = this.blockquote(newText, 0, newText.length);
      if (!newToken) throw new Error('blockquote recurse failed');
      tokens[tokens.length - 1] = newToken.token;
      const leftover = newText.substring(newToken.token.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = raw + '\n' + consumed.join('\n');
      text = text.substring(0, text.length - oldToken.text.length) + newToken.token.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && bqStart.test(lines[0])) continue;
      break;
    } else if (lastToken && lastToken.type === 'list') {
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const newToken = this.list(newText, 0, newText.length);
      if (!newToken) throw new Error('list recurse failed');
      tokens[tokens.length - 1] = newToken.token;
      const consumedCount = newToken.token.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.token.raw.length).split('\n').length
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
  return { token: { type: 'blockquote', raw, tokens, text }, end: p + raw.length };
};

Splitter.prototype.list = function (src, p, end) {
  const startPos = p;
  let cap = execAt(bList, src, p);
  if (!cap) return null;
  const taken = () => p - startPos;
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
  const itemRegex = by(`^( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`);
  let endsWithBlankLine = false;
  while (p < end) {
    let endEarly = false;
    let itemContents = '';
    cap = execAt(itemRegex, src, p);
    if (!cap) break;
    if (execAt(bHr, src, p)) break; // bullet was actually an hr
    const itemStart = taken();
    p += cap[0].length;
    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(/^[ \t]+/, (whitespace) => expandTabs(whitespace, bulletIndent));
    let nextLine = nextLineAt(src, p, end);
    let blankLine = !line.trim();
    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(/[^ ]/);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }
    if (blankLine && /^[ \t]*$/.test(nextLine)) {
      p += nextLine.length + 1;
      endEarly = true;
    }
    if (!endEarly) {
      const nextBulletRegex = nextBulletRegexFn(indent);
      const hrRegex = hrRegexFn(indent);
      const fencesBeginRegex = fencesBeginRegexFn(indent);
      const headingBeginRegex = headingBeginRegexFn(indent);
      const htmlBeginRegex = htmlBeginRegexFn(indent);
      const blockquoteBeginRegex = blockquoteBeginRegexFn(indent);
      while (p < end) {
        const rawLine = nextLineAt(src, p, end);
        nextLine = rawLine;
        const nextLineWithoutTabs = nextLine.replace(/^[ \t]+/, (whitespace) => expandTabs(whitespace));
        if (fencesBeginRegex.test(nextLine)) break;
        if (headingBeginRegex.test(nextLine)) break;
        if (htmlBeginRegex.test(nextLine)) break;
        if (blockquoteBeginRegex.test(nextLine)) break;
        if (nextBulletRegex.test(nextLine)) break;
        if (hrRegex.test(nextLine)) break;
        if (nextLineWithoutTabs.search(/[^ ]/) >= indent || !nextLine.trim()) {
          itemContents += '\n' + nextLineWithoutTabs.slice(indent);
        } else {
          if (blankLine) break;
          if (line.replace(/\t/g, '    ').search(/[^ ]/) >= 4) break;
          if (fencesBeginRegex.test(line)) break;
          if (headingBeginRegex.test(line)) break;
          if (htmlBeginRegex.test(line)) break;
          if (hrRegex.test(line)) break;
          const setextContinuation = /^ {0,3}(?:=+|-+) *$/.test(nextLine)
            && execAt(bLheading, line + '\n' + nextLine, 0);
          const continuation = setextContinuation
            ? '    ' + nextLineWithoutTabs.replace(/^ {0,3}/, '')
            : nextLine;
          itemContents += '\n' + continuation;
        }
        blankLine = !nextLine.trim();
        p += rawLine.length + 1;
        line = nextLineWithoutTabs.slice(indent);
      }
    }
    const raw = src.slice(startPos + itemStart, startPos + taken());
    if (!list.loose) {
      if (endsWithBlankLine) list.loose = true;
      else if (/\n[ \t]*\n[ \t]*$/.test(raw)) endsWithBlankLine = true;
    }
    list.items.push({
      type: 'list_item',
      raw,
      task: /^\[[ xX]\][ \t]+\S/.test(itemContents),
      loose: false,
      text: itemContents,
      tokens: [],
    });
  }
  const lastItem = list.items[list.items.length - 1];
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else {
    return null;
  }
  list.raw = src.slice(startPos, startPos + taken()).trimEnd();
  for (const item of list.items) {
    this.top = false;
    item.tokens = [];
    this.blockTokens(item.text, 0, item.text.length, item.tokens, false);
    if (!list.loose) {
      const spacers = item.tokens.filter((t) => t.type === 'space');
      const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => /\n.*\n/.test(t.raw));
      list.loose = hasMultipleLineBreaks;
    }
  }
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && (itemToken && (itemToken.type === 'text' || itemToken.type === 'paragraph'))) {
      item.text = item.text.replace(/^\[[ xX]\][ \t]+/, '');
      itemToken.raw = itemToken.raw.replace(/^\[[ xX]\][ \t]+/, '');
      itemToken.text = itemToken.text.replace(/^\[[ xX]\][ \t]+/, '');
      const taskRaw = /\[[ xX]\]/.exec(item.raw);
      if (taskRaw) {
        const checkboxToken = { type: 'checkbox', raw: taskRaw[0] + ' ', checked: taskRaw[0] !== '[ ]' };
        item.checked = checkboxToken.checked;
        if (list.loose) {
          if (item.tokens[0] && (item.tokens[0].type === 'paragraph' || item.tokens[0].type === 'text') && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
            item.tokens[0].raw = checkboxToken.raw + item.tokens[0].raw;
            item.tokens[0].text = checkboxToken.raw + item.tokens[0].text;
            item.tokens[0].tokens.unshift(checkboxToken);
          } else {
            item.tokens.unshift({ type: 'paragraph', raw: checkboxToken.raw, text: checkboxToken.raw, tokens: [checkboxToken] });
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
  return { token: list, end: startPos + list.raw.length };
};

// Test-only export: the bench compares the splitter's token tree with
// marked's Lexer directly.
export { Splitter };
