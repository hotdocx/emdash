import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import path from 'node:path';
import {
  normalizeAlgebraGoalSource, algebraGoalInput, computeAlgebraGoal, checkAlgebraGoalRelation,
  createAlgebraRelationComplex, algebraPolynomialText, algebraPolynomialZero,
  sampleAlgebraPolynomialCurves, ALGEBRA_CURVE_VIEWPORT, renderAlgebraPolynomialCurveSvg,
  prepareAlgebraRelationModuleData, adoptAlgebraRelationModuleComplex,
  serializeAlgebraPolynomial, serializeCoreLfWorkspaceCanonicalJson,
  serializeCoreExpression, createCoreProofArtifactFingerprint, FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE,
} from './vendor/emdash.mjs';

/** An ordinary authored program: several library operations in one run. */
export async function runStudy(reuse: boolean) {
  const parameters = JSON.parse(readFileSync(0, 'utf8') || '{}') as { internal?: boolean; adoptionReason?: string };
  const output = process.env.WORKSPACE_EXECUTION_OUTPUT_DIR;
  if (!output || !path.isAbsolute(output)) throw new Error('Select an absolute output directory.');
  const source = normalizeAlgebraGoalSource(JSON.parse(readFileSync(new URL('./input.json', import.meta.url), 'utf8')));
  const input = algebraGoalInput(source);
  const computation = reuse
    ? JSON.parse(readFileSync(new URL('./retained.json', import.meta.url), 'utf8'))
    : computeAlgebraGoal(source);
  // This checks retained coefficients against the actual input; reuse does
  // not rerun membership or replace the chosen coefficient vector.
  const relation = reuse || computation.member ? checkAlgebraGoalRelation(source, computation) : null;
  const complex = relation ? createAlgebraRelationComplex(input, relation) : null;
  const coefficients = relation ? relation.coefficients.map(algebraPolynomialText) : [];
  const native = complex ? {
    ranks: complex.complex.terms.map(term => term.module.rank),
    upperColumn: complex.column.components.map(algebraPolynomialText),
    imageOfOne: complex.unitImage.components.map(algebraPolynomialText),
    compositeIsZero: complex.complex.isComplex,
    authority: 'exact-polynomial-arithmetic',
  } : null;
  let internal: { status: string; adoptedEquationCount: number; adoptionReason: string; qualification: string } | null = null;
  if (parameters.internal) {
    if (!relation) throw new Error('Internal reuse requires a positive exact relation.');
    if (typeof parameters.adoptionReason !== 'string' || !parameters.adoptionReason.trim()) {
      throw new Error('Internal construction requires an explicit computed-equation adoption reason.');
    }
    const sourceData = serializeCoreLfWorkspaceCanonicalJson({
      mathematicalSource: relation.source, coefficients: relation.coefficients.map(serializeAlgebraPolynomial),
    }, 'scientificProgram.source');
    const data = prepareAlgebraRelationModuleData({ ideal: input.ideal, left: input.polynomial, right: algebraPolynomialZero(input.ideal.ring) }, relation, sourceData);
    const hash = (value: string) => 'sha256:' + createHash('sha256').update(value).digest('hex');
    const checked = await adoptAlgebraRelationModuleComplex({
      data, decision: { kind: 'trust-exact-algebra-computation', evidence: parameters.adoptionReason },
      names: { moduleId: 'scientific.example', sourceId: 'generated/scientific-assumptions.ts', prefix: 'study', provenance: 'retained scientific program relation' },
      assertCurrent: () => { checkAlgebraGoalRelation(source, computation); },
      fingerprint: (text, profile) => createCoreProofArtifactFingerprint({ source: { id: 'scientific-computed-law', sha256: hash(text) }, profileSha256: hash(profile) }),
    });
    const assumptions = checked.adopted.source.entries.map(entry => ({
      name: entry.declaration.name, type: serializeCoreExpression(entry.declaration.type),
      classification: entry.classification, hasProofBody: entry.declaration.body !== undefined,
      authority: entry.adoptionArtifact.authority,
    }));
    internal = { status: checked.status, adoptedEquationCount: assumptions.length, adoptionReason: parameters.adoptionReason,
      qualification: 'Core checks construction and action types relative to the explicit computed equation; no new standalone projection reduction is qualified.' };
    writeFileSync(path.join(output, 'internal.json'), JSON.stringify({
      ...internal, profile: FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE, assumptions,
      definitions: ['study_complex', 'study_image'].map(name => {
        const declaration = checked.environment.lookup(name)!;
        return { name, type: serializeCoreExpression(declaration.type), body: serializeCoreExpression(declaration.body!), transparency: declaration.transparency };
      }),
      action: { argument: serializeCoreExpression(checked.argument), image: serializeCoreExpression(checked.image) },
    }, null, 2) + '\n');
  }
  const view = input.ideal.ring.variables.length === 2
    ? sampleAlgebraPolynomialCurves(input, { ...ALGEBRA_CURVE_VIEWPORT, cells: 32 }) : null;
  const result = {
    revision: 'emdash-scientific-result-v1', title: source.title,
    source, mathematicalSource: computation.mathematicalSource, mode: reuse ? 'retained-reuse' : 'compute-and-reuse',
    exact: { member: computation.member, coefficients, remainder: computation.remainder,
      generators: input.ideal.generators.map(algebraPolynomialText), query: algebraPolynomialText(input.polynomial) },
    native, internal, view: view
      ? { authority: view.authority, limitation: view.limitation, artifact: 'plot.svg' }
      : { authority: 'unavailable', limitation: 'The current curve view requires two variables.', artifact: null },
  };
  writeFileSync(path.join(output, 'result.json'), JSON.stringify(result, null, 2) + '\n');
  writeFileSync(path.join(output, 'retained.json'), JSON.stringify(computation, null, 2) + '\n');
  if (view) writeFileSync(path.join(output, 'plot.svg'), renderAlgebraPolynomialCurveSvg(view));
  console.log(JSON.stringify({ member: result.exact.member, coefficients, native, internal }));
}
