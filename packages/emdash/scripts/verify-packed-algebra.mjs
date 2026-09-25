import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';

/** Checks the installed tarball through public exports in the clean consumer. */
export async function verifyPackedAlgebra({ consumerDirectory, repositoryRoot, packageRoot }) {
  const run = (command, args) => execFileSync(command, args, {
    cwd: consumerDirectory, stdio: 'inherit', timeout: 90_000,
  });
  await writeFile(path.join(consumerDirectory, 'algebra-consumer.mjs'), `
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import * as esm from '@hotdocx/emdash/algebra';
const cjs = createRequire(import.meta.url)('@hotdocx/emdash/algebra');
for (const a of [esm, cjs]) {
  const ring = a.algebraPolynomialRing(a.RATIONAL_DOMAIN, ['x', 'y'], 'lex');
  const x = a.algebraPolynomialVariable(ring, 0), y = a.algebraPolynomialVariable(ring, 1);
  const c = a.algebraPolynomialConstant(ring, '1/2');
  const input = {
    ideal: a.algebraPolynomialIdeal(ring, [
      a.algebraPolynomialSubtract(y, a.algebraPolynomialPower(x, 2n)),
      a.algebraPolynomialSubtract(a.algebraPolynomialMultiply(x, y), c),
    ]),
    polynomial: a.algebraPolynomialSubtract(a.algebraPolynomialPower(x, 3n), c),
  };
  const source = a.algebraIdealWitnessSource(input);
  const result = a.algebraIdealMembership(input.polynomial, a.algebraGroebnerBasis(input.ideal));
  assert.equal(result.member, true);
  const checked = a.checkAlgebraIdealWitness(input, { source, coefficients: result.coefficients });
  assert.equal(checked.authority, 'exact-polynomial-arithmetic');
  const view = a.sampleAlgebraPolynomialCurves(input, { ...a.ALGEBRA_CURVE_VIEWPORT, cells: 16 });
  assert.equal(view.source, source);
  assert.ok(view.curves.every(curve => curve.segments.length > 0));
  assert.throws(() => a.checkAlgebraIdealWitness({ ...input, polynomial: x }, checked));
  assert.throws(() => a.algebraPolynomialConstant(ring, 0.5));
  for (const forbidden of ['CoreChecker', 'computeSingularIdealWitness',
    'adoptAlgebraFormalTrustedComputation', 'renderAlgebraPolynomialCurveSvg']) {
    assert.equal(forbidden in a, false);
  }
}
console.log('Packed algebra ESM/CJS computation and source controls passed.');
`);
  await writeFile(path.join(consumerDirectory, 'algebra-consumer.ts'), `
import {
  RATIONAL_DOMAIN, algebraPolynomialRing, algebraPolynomialConstant,
  algebraPolynomialIdeal, algebraIdealMembership, algebraGroebnerBasis,
  sampleAlgebraPolynomialCurves,
  type AlgebraRationalPolynomial, type AlgebraIdealWitnessInput,
} from '@hotdocx/emdash/algebra';
const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y']);
const polynomial: AlgebraRationalPolynomial = algebraPolynomialConstant(ring, '1/2');
const input: AlgebraIdealWitnessInput = { polynomial, ideal: algebraPolynomialIdeal(ring, [polynomial]) };
const member: boolean = algebraIdealMembership(polynomial, algebraGroebnerBasis(input.ideal)).member;
const source: string = sampleAlgebraPolynomialCurves(input).source;
void member; void source;
// @ts-expect-error JavaScript numbers are not exact rational inputs.
algebraPolynomialConstant(ring, 0.5);
// @ts-expect-error The computational entry does not expose a formal checker.
import { CoreChecker } from '@hotdocx/emdash/algebra';
`);
  await writeFile(path.join(consumerDirectory, 'browser-algebra-entry.js'), `
import * as algebra from '@hotdocx/emdash/algebra';
globalThis.emdashPackedAlgebra = algebra;
`);
  run(process.execPath, ['algebra-consumer.mjs']);
  run(path.join(repositoryRoot, 'node_modules/.bin/tsc'), [
    '--noEmit', '--strict', '--target', 'ES2020', '--module', 'NodeNext',
    '--moduleResolution', 'NodeNext', 'algebra-consumer.ts',
  ]);
  run(path.join(packageRoot, 'node_modules/.bin/esbuild'), [
    'browser-algebra-entry.js', '--bundle', '--format=esm', '--platform=browser',
    '--target=es2020', '--outfile=browser-algebra-bundle.js',
  ]);
  const bundle = await readFile(path.join(consumerDirectory, 'browser-algebra-bundle.js'), 'utf8');
  assert.match(bundle, /emdash-algebra-polynomial-v1/u);
  assert.doesNotMatch(bundle, /node:|CoreChecker|comm_ring_|Singular|vega|emdash-lf-/u,
    'the computational browser closure must not acquire Core, formal or host-library owners');
  const declarationDirectory = path.join(consumerDirectory, 'node_modules/@hotdocx/emdash/dist/types');
  const pending = ['package_algebra'];
  const seen = new Set();
  while (pending.length) {
    const name = pending.pop();
    if (seen.has(name)) continue;
    seen.add(name);
    assert.match(name, /^(?:package_algebra|algebra_(?:parent|engine|exact|polynomial|ideal|ideal_witness|polynomial_plot))$/u,
      `unexpected computational declaration dependency: ${name}`);
    const declaration = await readFile(path.join(declarationDirectory, `${name}.d.ts`), 'utf8');
    for (const match of declaration.matchAll(/from ['"]\.\/([^'"]+)['"]/gu)) pending.push(match[1]);
    assert.doesNotMatch(declaration, /from ['"](?:node:|[^.])/u);
  }
  console.log(`Packed algebra declarations: ${seen.size} computational modules; browser bundle: ${Buffer.byteLength(bundle)} bytes.`);
}
