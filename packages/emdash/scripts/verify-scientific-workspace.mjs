import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import ts from 'typescript';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../../..');
const temporary = await fs.mkdtemp(path.join(os.tmpdir(), 'emdash-scientific-consumer-'));
const workspace = path.join(temporary, 'project');
try {
  const build = spawnSync(process.execPath, [path.join(root, 'packages/emdash/scripts/build-scientific-workspace.mjs'), '--out', workspace, '--node-version', process.version], { cwd: temporary, encoding: 'utf8', timeout: 90_000 });
  assert.equal(build.status, 0, build.stderr + build.stdout);
  const read = async (name) => JSON.parse(await fs.readFile(path.join(workspace, name), 'utf8'));
  const original = await read('input.json');
  const retained = await read('retained.json');
  const library = await import(pathToFileURL(path.join(workspace, 'vendor/emdash.mjs')).href);
  const receipt = await read('vendor/build.json');
  assert.equal(receipt.bundles['emdash.mjs'], createHash('sha256').update(await fs.readFile(path.join(workspace, 'vendor/emdash.mjs'))).digest('hex'));
  for (const name of ['compute.ts', 'reuse.ts', 'study.ts']) {
    assert(!(await fs.readFile(path.join(workspace, name), 'utf8')).includes(root));
  }
  await fs.writeFile(path.join(workspace, 'type-probe.ts'), `import { RATIONAL_DOMAIN, algebraPolynomialRing, algebraPolynomialConstant } from './vendor/emdash.mjs';
const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x']);
algebraPolynomialConstant(ring, '1/2');
// @ts-expect-error approximate JavaScript numbers are not exact rational inputs.
algebraPolynomialConstant(ring, 0.5);
`);
  const program = ts.createProgram(['compute.ts', 'reuse.ts', 'study.ts', 'type-probe.ts'].map(name => path.join(workspace, name)), {
    noEmit: true, strict: true, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext, allowImportingTsExtensions: true,
    types: ['node'], typeRoots: [path.join(root, 'node_modules/@types')], skipLibCheck: false,
  });
  const diagnostics = ts.getPreEmitDiagnostics(program);
  assert.equal(diagnostics.length, 0, ts.formatDiagnosticsWithColorAndContext(diagnostics, {
    getCanonicalFileName: p => p, getCurrentDirectory: () => temporary, getNewLine: () => '\n',
  }));
  async function run(task, name, parameters = {}, success = true) {
    const output = path.join(temporary, name);
    const result = spawnSync(process.execPath, [path.join(workspace, 'run-local.mjs'), task, output, JSON.stringify(parameters)], { cwd: temporary, encoding: 'utf8', timeout: 30_000 });
    if (!success) { assert.notEqual(result.status, 0); return null; }
    assert.equal(result.status, 0, result.stderr + result.stdout);
    return JSON.parse(await fs.readFile(path.join(output, 'result.json'), 'utf8'));
  }
  const computed = await run('compute', 'computed');
  assert.equal(computed.exact.member, true);
  assert.deepEqual(computed.exact.coefficients, ['-1*x', '1']);
  assert.deepEqual(computed.native.ranks, [1, 3, 1]);
  assert.equal(computed.native.compositeIsZero, true);
  assert.equal(computed.internal, null);
  assert.match(await fs.readFile(path.join(temporary, 'computed/plot.svg'), 'utf8'), /<svg/);
  const reused = await run('reuse', 'reused');
  assert.deepEqual(reused.native, computed.native);
  const internal = await run('compute', 'internal', { internal: true, adoptionReason: 'Explicitly adopt this computed equation for the acceptance example.' });
  assert.equal(internal.internal.adoptedEquationCount, 1);
  const internalArtifact = JSON.parse(await fs.readFile(path.join(temporary, 'internal/internal.json'), 'utf8'));
  assert(internalArtifact.assumptions.every(item => item.hasProofBody === false));
  assert(internalArtifact.definitions.every(item => item.body && item.transparency === 'transparent'));
  await run('compute', 'no-adoption', { internal: true }, false);

  const staleSource = structuredClone(original);
  staleSource.query.terms = [{ coefficient: '1', exponents: ['1', '0'] }];
  await fs.writeFile(path.join(workspace, 'input.json'), JSON.stringify(staleSource));
  await run('reuse', 'stale', {}, false);
  const nonmember = await run('compute', 'nonmember');
  assert.equal(nonmember.exact.member, false); assert.equal(nonmember.native, null);
  assert(nonmember.exact.remainder.length > 0);
  await fs.writeFile(path.join(workspace, 'input.json'), JSON.stringify(original));
  const invalid = structuredClone(retained); invalid.coefficients[0] = [];
  await fs.writeFile(path.join(workspace, 'retained.json'), JSON.stringify(invalid));
  await run('reuse', 'invalid-relation', {}, false);

  const input = library.algebraGoalInput(original);
  const relation = library.checkAlgebraGoalRelation(original, retained);
  const alternate = [library.algebraPolynomialAdd(relation.coefficients[0], input.ideal.generators[1]),
    library.algebraPolynomialSubtract(relation.coefficients[1], input.ideal.generators[0])];
  const alternateRetained = { ...retained, coefficients: alternate.map(value => JSON.parse(library.serializeAlgebraPolynomial(value)).terms) };
  await fs.writeFile(path.join(workspace, 'retained.json'), JSON.stringify(alternateRetained));
  const alternative = await run('reuse', 'alternative');
  assert.deepEqual(alternative.exact.coefficients, alternate.map(library.algebraPolynomialText));
  assert.notDeepEqual(alternative.native.upperColumn, computed.native.upperColumn);
  assert.equal(alternative.native.compositeIsZero, true);

  await fs.writeFile(path.join(workspace, 'extension.ts'), `import { writeFileSync } from 'node:fs';
import { RATIONAL_DOMAIN, algebraPolynomialRing, algebraPolynomialVariable, algebraPolynomialPower, algebraPolynomialText } from './vendor/emdash.mjs';
const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x']);
writeFileSync(process.env.WORKSPACE_EXECUTION_OUTPUT_DIR + '/result.json', JSON.stringify({ power: algebraPolynomialText(algebraPolynomialPower(algebraPolynomialVariable(ring, 0), 5n)) }));
`);
  const manifest = await read('workspace.program.json');
  manifest.files.push('extension.ts'); manifest.tasks.extension = { entrypoint: 'extension.ts' };
  await fs.writeFile(path.join(workspace, 'workspace.program.json'), JSON.stringify(manifest));
  assert.equal((await run('extension', 'extension')).power, '1*x^5');
  console.log('Portable scientific consumer passed: declarations, exact relation, native/internal reuse, stale/invalid/alternate coefficients, nonmember result, plot and authored extension.');
} finally { await fs.rm(temporary, { recursive: true, force: true }); }
