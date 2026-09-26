import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { cp, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repositoryRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../..');
const temporary = await mkdtemp(path.join(os.tmpdir(), 'emdash-goal-portable-'));
const supplied = process.argv.slice(2);
if (supplied.length && (supplied.length !== 2 || supplied[0] !== '--runtime')) throw new Error('Usage: verify-goal-runtime.mjs [--runtime DIRECTORY]');
const original = supplied.length ? path.resolve(supplied[1]) : path.join(repositoryRoot, 'plugins/emdash/dist');
try {
  await cp(original, path.join(temporary, 'runtime'), { recursive: true });
  const executable = path.join(temporary, 'runtime/emdash-agent.cjs');
  const workspace = path.join(temporary, 'mathematics');
  const run = (args, input) => {
    const result = spawnSync(process.execPath, [executable, ...args], {
      cwd: temporary, encoding: 'utf8', timeout: 30_000, maxBuffer: 4 * 1024 * 1024,
      env: { ...process.env, NODE_PATH: '' }, input,
    });
    if (result.error) throw result.error;
    return { status: result.status, response: JSON.parse(result.stdout) };
  };
  const good = (args, input) => {
    const result = run(args, input);
    assert.equal(result.status, 0, JSON.stringify(result.response));
    assert.equal(result.response.ok, true);
    return result.response.result;
  };
  const capabilities = good(['capabilities']);
  assert.equal(capabilities.executesUserModules, false);
  const initialized = good(['init', '--root', workspace]);
  const computed = good(['compute', '--root', workspace]);
  assert.equal(computed.member, true);
  assert.equal(computed.sourceRevision, initialized.sourceRevision);
  assert.equal(computed.coefficients.length, 2);
  const rendered = good(['render', '--root', workspace]);
  assert.match(await readFile(rendered.svgPath, 'utf8'), /<svg/u);
  const resumed = good(['inspect', '--root', workspace]);
  assert.equal(resumed.artifacts.computation.status, 'current');
  assert.equal(resumed.artifacts.view.status, 'current');

  // A normal TypeScript host program creates the inert input. The server never imports it.
  await writeFile(path.join(temporary, 'author.mts'), `
import {
  RATIONAL_DOMAIN, algebraPolynomialRing, algebraPolynomialVariable,
  algebraPolynomialConstant, algebraPolynomialPower, algebraPolynomialMultiply,
  algebraPolynomialSubtract, algebraPolynomialIdeal, createAlgebraGoalSource,
  serializeAlgebraGoalSource, type AlgebraGoalSource,
} from './runtime/authoring.cjs';
const R = algebraPolynomialRing(RATIONAL_DOMAIN, ['x','y'], 'lex');
const x = algebraPolynomialVariable(R, 0), y = algebraPolynomialVariable(R, 1);
const c = algebraPolynomialConstant(R, '1/2');
const source: AlgebraGoalSource = createAlgebraGoalSource({
  ideal: algebraPolynomialIdeal(R, [
    algebraPolynomialSubtract(y, algebraPolynomialPower(x, 2n)),
    algebraPolynomialSubtract(algebraPolynomialMultiply(x,y), c),
  ]),
  polynomial: algebraPolynomialSubtract(algebraPolynomialPower(x, 3n), c),
}, { title: 'A rational parameter authored in TypeScript' });
console.log(serializeAlgebraGoalSource(source));
`);
  execFileSync(path.join(repositoryRoot, 'node_modules/.bin/tsc'), [
    '--strict', '--noEmit', '--target', 'ES2020', '--module', 'NodeNext',
    '--moduleResolution', 'NodeNext', 'author.mts',
  ], { cwd: temporary, stdio: 'inherit', timeout: 30_000 });
  const source = JSON.parse(execFileSync(process.execPath, ['author.mts'], {
    cwd: temporary, encoding: 'utf8', timeout: 30_000, env: { ...process.env, NODE_PATH: '' },
  }));
  const updated = good(['request'], JSON.stringify({ command: 'update', root: workspace,
    expectedRevision: resumed.sourceRevision, source }));
  assert.equal(updated.artifacts.computation.status, 'stale');
  assert.equal(good(['compute', '--root', workspace]).member, true);
  const stale = run(['request'], JSON.stringify({ command: 'update', root: workspace,
    expectedRevision: initialized.sourceRevision, source }));
  assert.equal(stale.status, 1);
  assert.equal(stale.response.error.code, 'STALE_SOURCE');
  const denied = run(['request'], JSON.stringify({ command: 'inspect', root: workspace, module: 'untrusted.ts' }));
  assert.equal(denied.status, 1);
  console.log('Portable goal runtime: CLI, fresh-process resume, TypeScript authoring/declarations, updates, stale controls and derived view passed.');
} finally {
  await rm(temporary, { recursive: true, force: true });
}
