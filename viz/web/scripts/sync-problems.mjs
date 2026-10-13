// Copies ../../problems into public/problems for the site and writes an index.
// Run with `npm run sync-problems`. The copies are not committed (see .gitignore).
import { readdirSync, readFileSync, writeFileSync, mkdirSync, copyFileSync, existsSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const src = join(here, '../../../problems');
const dst = join(here, '../public/problems');
mkdirSync(dst, { recursive: true });

const index = [];
for (const name of readdirSync(src)) {
  const dir = join(src, name);
  if (!existsSync(join(dir, 'testcase.vsm')) || !existsSync(join(dir, 'main.vsm'))) continue;
  mkdirSync(join(dst, name), { recursive: true });
  for (const f of ['testcase.vsm', 'main.vsm', 'problem.md']) {
    if (existsSync(join(dir, f))) copyFileSync(join(dir, f), join(dst, name, f));
  }
  const md = existsSync(join(dir, 'problem.md')) ? readFileSync(join(dir, 'problem.md'), 'utf8') : '';
  const title = (md.match(/^#\s+(.+)$/m) || [, name])[1].trim();
  index.push({ name, title, number: parseInt(name, 10) || 0 });
}
index.sort((a, b) => a.number - b.number);
writeFileSync(join(dst, 'index.json'), JSON.stringify(index, null, 1));
console.log(`copied ${index.length} problems to public/problems`);
