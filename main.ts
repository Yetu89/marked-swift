// MarkedSwift driver: renders every case in the harness input file
// with parse() and writes the HTML strings, in order, to the output
// file. The harness mounts the cases at /input/cases.json and expects
// /output/html.json; both locations can be overridden for local runs.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inDir, 'cases.json'), 'utf8'));
const html = [];
for (const c of cases) {
  html.push(parse(c.markdown));
}
mkdirSync(outDir, { recursive: true });
writeFileSync(join(outDir, 'html.json'), JSON.stringify(html));
