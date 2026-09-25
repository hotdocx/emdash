import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { copyFile, mkdir, mkdtemp, readFile, readdir, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const packageRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const repositoryRoot = path.resolve(packageRoot, '../..');
const pnpm = path.join(repositoryRoot, 'scripts/pnpmw');
const fixture = path.join(packageRoot, 'fixtures/polynomial-vega');
const args = process.argv.slice(2);
let suppliedTarball, output;
for (let index = 0; index < args.length; index += 2) {
  const value = args[index + 1];
  if (!value) throw new Error('Usage: prepare-polynomial-vega.mjs [--tarball FILE] [--output NEW_DIRECTORY]');
  if (args[index] === '--tarball' && !suppliedTarball) suppliedTarball = path.resolve(value);
  else if (args[index] === '--output' && !output) output = path.resolve(value);
  else throw new Error(`Unknown or repeated option: ${args[index]}`);
}
const run = (command, arguments_, capture = false) => execFileSync(command, arguments_, {
  cwd: repositoryRoot, encoding: 'utf8', stdio: capture ? ['ignore', 'pipe', 'inherit'] : 'inherit', timeout: 120_000,
});
if (output) {
  const relative = path.relative(repositoryRoot, output);
  if (relative === '' || (!relative.startsWith(`..${path.sep}`) && !path.isAbsolute(relative))) {
    throw new Error('The external consumer directory must be outside this contributor checkout.');
  }
}
if (!suppliedTarball) run(pnpm, ['run', 'package:build']);
if (output) await mkdir(output); // Deliberately fail instead of overwriting an existing consumer.
else output = await mkdtemp(path.join(os.tmpdir(), 'emdash-polynomial-vega-'));
const fixtureSha256 = {};
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
for (const entry of await readdir(fixture, { withFileTypes: true })) {
  assert.ok(entry.isFile(), `Only source files belong in the consumer fixture: ${entry.name}`);
  await copyFile(path.join(fixture, entry.name), path.join(output, entry.name));
  fixtureSha256[entry.name] = sha256(await readFile(path.join(output, entry.name)));
}
let tarball = suppliedTarball;
if (!tarball) {
  const packed = JSON.parse(run(pnpm, ['--dir', packageRoot, 'pack', '--json', '--pack-destination', output], true));
  const record = Array.isArray(packed) ? packed[0] : packed;
  tarball = path.resolve(output, record.filename ?? record.path);
}
await copyFile(tarball, path.join(output, 'emdash.tgz'));
const artifact = {
  revision: 'emdash-polynomial-vega-artifact-v1',
  checkoutHead: run('git', ['rev-parse', 'HEAD'], true).trim(),
  checkoutDirty: Boolean(run('git', ['status', '--porcelain'], true).trim()),
  tarballSha256: sha256(await readFile(path.join(output, 'emdash.tgz'))),
  fixtureSha256,
};
await writeFile(path.join(output, 'artifact.json'), JSON.stringify(artifact, null, 2) + '\n');
run(pnpm, ['--dir', output, 'install', '--ignore-workspace', '--offline', '--ignore-scripts']);
run(pnpm, ['--dir', output, 'run', 'build']);
run(pnpm, ['--dir', output, 'test']);
artifact.lockfileSha256 = sha256(await readFile(path.join(output, 'pnpm-lock.yaml')));
artifact.browserBundleSha256 = sha256(await readFile(path.join(output, 'dist/app.js')));
await writeFile(path.join(output, 'artifact.json'), JSON.stringify(artifact, null, 2) + '\n');
console.log(JSON.stringify({ consumerDirectory: output, ...artifact }, null, 2));
console.log(`Serve with: ${pnpm} --dir ${output} start`);
