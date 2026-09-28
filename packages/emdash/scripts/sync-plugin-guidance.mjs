import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../..');
const source = await fs.readFile(path.join(root, 'docs/EMDASH_PLUGIN_MATHEMATICAL_GUIDANCE.md'), 'utf8');
const check = process.argv.slice(2).includes('--check');
for (const name of ['emdash', 'emdash-cloud']) {
  const target = path.join(root, 'plugins', name, 'skills', name, 'references/mathematical-contract.md');
  if (check) {
    if (await fs.readFile(target, 'utf8') !== source) throw new Error(`Stale packaged mathematical guidance: ${name}`);
  } else {
    await fs.mkdir(path.dirname(target), { recursive: true }); await fs.writeFile(target, source);
  }
}
console.log(check ? 'Shared plugin mathematical guidance matches.' : 'Shared plugin mathematical guidance packaged.');
