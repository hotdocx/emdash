/** Complete native H-arrow realization for the nonsplit multiplication-by-x map. */
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { describe, it, mock } from 'node:test';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { binderMode, kernelFree, kernelExpressionEquals, provenance, sourceSpan } from '../src/v3_2/kernel';
import { runAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { defineAlgebraFormalFreydNativeRationalBackend, prepareAlgebraFormalFreydNativeRationalModelContext } from '../src/v3_2/algebra_formal_freyd_native_rational_model_context';
import { trustAlgebraFormalFreydNativeHomologyMap } from '../src/v3_2/algebra_formal_freyd_native_map_workflow';
import { algebraFormalFreydNativeModelType } from '../src/v3_2/algebra_formal_freyd_native_model_signatures';
import { algebraFormalFreydNativeModelMapObservationBundle, algebraFormalFreydModelMapObservationBundle } from '../src/v3_2/algebra_formal_freyd_model_map_observation';
import { algebraFormalFreydNativeModelHomologyObservationBundle } from '../src/v3_2/algebra_formal_freyd_model_observation';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { algebraPolynomialPresentationMorphismCongruence, algebraPolynomialPresentationMorphismIdentity } from '../src/v3_2/algebra_polynomial_freyd_category';
import { polynomialFreydHomologyFixture, isPolynomialFreydMorphismZero } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { freydNativeModelProbe } from './v3_2_algebra_formal_freyd_native_model_fixtures';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as nativeMaps from '../src/v3_2/algebra_polynomial_freyd_functorial_homology';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';

const p = provenance('surface', 'native complete arrow', sourceSpan('tests/native-complete-arrow.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({ id: 'tests.native-complete-arrow', revision: 'v1',
    coefficientContract: 'Interpret the ring and coefficient names in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native whole P/Q; selected-arrow realization is separately explicit.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality of that native model.' });
const prepare = () => prepareAlgebraFormalFreydNativeRationalModelContext({ backend, namePrefix: 'native_arrow',
    selected: algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(
        polynomialFreydHomologyFixture('one'))) });
let setup: ReturnType<typeof prepare>;
const context = () => setup ??= prepare();
const adoptEquations = async () => {
    const v = context(), goalId = 'native-arrow-replay', type = v.bundle.realization.claimType;
    const run = await runAlgebraFormalWorkflow({ goalId, adapter: v.bundle.adapter, realization: v.bundle.realization,
        engine: v.bundle.engine, document: { moduleId: v.initialSource.moduleId, declarationId: goalId,
            environment: v.environment, type, provenance: p, fingerprint: fingerprint(goalId),
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: type } }) } });
    return trustAlgebraFormalFreydLongExact({ artifactId: 'native-arrow-equations', bundle: v.bundle, run,
        source: v.initialSource, fingerprint, decisionEvidence: id => 'Explicitly adopt the original matrix equation ' + id });
};
let equationsPromise: ReturnType<typeof adoptEquations>;
const equations = () => equationsPromise ??= adoptEquations();
const realize = async () => {
    const v = context(), adopted = await equations();
    const entry = v.preparedModel.inventory.maps.find(x => x.key === 'degree/0/inclusion')!;
    const decisions: string[] = [];
    const input = { artifactId: 'native-arrow-model', modelId: 'native-scalar-model', observationId: 'degree/0/inclusion',
        formalModel: v.formalModel, prepared: entry.prepared, source: adopted.source, fingerprint,
        decisionEvidence: (id: string) => { decisions.push(id); return 'Explicit matrix computation or complete native arrow interpretation: ' + id; } };
    const result = await trustAlgebraFormalFreydNativeHomologyMap(input);
    return { v, adopted, entry, input, result, decisions };
};
let realizationPromise: ReturnType<typeof realize>;
const consumer = () => realizationPromise ??= realize();

describe('v3.2 complete native H arrows', () => {
    it('realizes the nonzero nonidentity x arrow with one interpretation and automatic matrix inputs', async t => {
        await equations();
        const forbid = () => { throw new Error('Native arrow realization must retain the original H, map and universals'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeMaps, 'algebraPolynomialFreydInducedHomologyMap', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { v, adopted, entry, result } = await consumer();
            const map = entry.prepared.selected.homologyMap;
            assert.equal(isPolynomialFreydMorphismZero(map), false);
            assert.equal(algebraPolynomialPresentationMorphismCongruence(map,
                algebraPolynomialPresentationMorphismIdentity(map.source)).agrees, false);
            assert.equal(result.observation.realization.prepared.selected, entry.prepared.selected);
            assert.equal(result.observation.realization.source.actual.selected, entry.prepared.selected.chainMap.source);
            assert.equal(result.observation.realization.target.actual.selected, entry.prepared.selected.chainMap.target);
            assert.equal(result.counts.interpretationClaims, 1);
            assert.equal(result.counts.homologyReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            assert.equal(result.source.entries.filter(x => x.classification === 'trusted-presentation-semantics').length, 1);
            assert.ok(result.source.entries.slice(0, -1).every(x => x.classification === 'computed-equation'));
            assert.equal(result.source.environment.lookup('bridge_FreydHomologyModel'), undefined);
            assert.equal(result.observation.profile.requiresLegacyModel, false);
            assert.equal(result.observation.profile.endpointTransport, false);
            const checker = createCoreProofChecker(result.source.environment), r = result.observation.realization;
            checker.check(checker.rootContext, r.formalArrow, r.observationType);
            checker.check(checker.rootContext, r.nativeArrow, r.observationType);
            checker.check(checker.rootContext, result.proof, r.claimType);
            assert.match(serializeCoreExpression(r.formalArrow), /bridge_freyd_adjunction_model_arrow_observation/u);
            assert.equal(adopted.source.entries.length, v.bundle.equations.claims.length);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
            t.diagnostic(JSON.stringify(result.counts));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('reuses every matrix prerequisite and the complete-arrow agreement without another decision', async () => {
        const { input, result } = await consumer();
        const again = await trustAlgebraFormalFreydNativeHomologyMap({ ...input, source: result.source,
            artifactId: 'native-arrow-reuse', decisionEvidence: () => { assert.fail('All thirteen requests must reuse their proofs'); } });
        assert.equal(again.source, result.source);
        assert.equal(again.counts.reused, 13);
        assert.equal(again.counts.newAssumptions, 0);
        assert.ok(kernelExpressionEquals(again.proof, result.proof));
        assert.equal(again.observation.realization.formalData, result.observation.realization.formalData);
    });

    it('rejects legacy or mixed models, forged preparations and a wrongly typed native model', async () => {
        const { v, input, result } = await consumer();
        assert.throws(() => algebraFormalFreydModelMapObservationBundle(result.observationInput), /profiles/iu);
        assert.throws(() => result.observation.adapter.normalizeRealization({ ...result.observation.realization }, 'test'), /Foreign/iu);
        await assert.rejects(trustAlgebraFormalFreydNativeHomologyMap({ ...input, prepared: { ...input.prepared } }), /issued/iu);
        await assert.rejects(trustAlgebraFormalFreydNativeHomologyMap({ ...input, formalModel: v.normality,
            decisionEvidence: () => { assert.fail('Reject the model type before adopting any claim'); } }));
        const s = result.observationInput.source.realization, otherM = kernelFree('other_native_arrow_model', p);
        const environment = result.source.environment.extend({ name: otherM.name,
            type: algebraFormalFreydNativeModelType(v.formalRing), mode: binderMode('explicit', 'functorial'), provenance: p });
        const other = algebraFormalFreydNativeModelHomologyObservationBundle({ modelId: s.modelId, observationId: 'foreign-source',
            formalModel: otherM, environment, actual: s.actual,
            aboveLaw: s.inputLaws.above, belowLaw: s.inputLaws.below, chainLaw: s.inputLaws.chain });
        assert.throws(() => algebraFormalFreydNativeModelMapObservationBundle({ ...result.observationInput, environment, source: other }),
            /same supplied model/iu);
    });

    it('emits the native arrow, computed arrow and explicit realization for Lambdapi', async () => {
        const { result } = await consumer(), r = result.observation.realization;
        const source = freydNativeModelProbe(result.source.environment, [
            { label: 'complete native H arrow', term: r.formalArrow, type: r.observationType, span: p.span! },
            { label: 'computed x arrow with original endpoints', term: r.nativeArrow, type: r.observationType, span: p.span! },
            { label: 'explicit complete-arrow realization', term: result.proof, type: r.claimType, span: p.span! }
        ]);
        assert.doesNotMatch(source, /FreydHomologyModel|freyd_homology_model/u);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_ARROW_PROBE_OUTPUT) {
            writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_ARROW_PROBE_OUTPUT, source);
        }
    });
});
