/** Direct native δ realization for the middle window of the nonsplit sequence. */
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
import { trustAlgebraFormalFreydNativeConnecting } from '../src/v3_2/algebra_formal_freyd_native_connecting_workflow';
import { algebraFormalFreydNativeModelType } from '../src/v3_2/algebra_formal_freyd_native_model_signatures';
import { algebraFormalFreydNativeConnectingObservationBundle } from '../src/v3_2/algebra_formal_freyd_model_connecting_observation';
import { algebraFormalFreydNativeModelHomologyObservationBundle } from '../src/v3_2/algebra_formal_freyd_model_observation';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { polynomialFreydHomologyFixture, isPolynomialFreydMorphismZero } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { freydNativeModelProbe } from './v3_2_algebra_formal_freyd_native_model_fixtures';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as nativeConnecting from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';

const p = provenance('surface', 'native connecting window', sourceSpan('tests/native-connecting-window.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({ id: 'tests.native-connecting-window', revision: 'v1',
    coefficientContract: 'Interpret the ring and coefficient names in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native whole P/Q; selected-arrow realization is separately explicit.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality of that native model.' });
const prepare = () => prepareAlgebraFormalFreydNativeRationalModelContext({ backend, namePrefix: 'native_delta',
    selected: algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(
        polynomialFreydHomologyFixture('two'))) });
let setup: ReturnType<typeof prepare>;
const context = () => setup ??= prepare();
const adoptEquations = async () => {
    const v = context(), goalId = 'native-delta-replay', type = v.bundle.realization.claimType;
    const run = await runAlgebraFormalWorkflow({ goalId, adapter: v.bundle.adapter, realization: v.bundle.realization,
        engine: v.bundle.engine, document: { moduleId: v.initialSource.moduleId, declarationId: goalId,
            environment: v.environment, type, provenance: p, fingerprint: fingerprint(goalId),
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: type } }) } });
    return trustAlgebraFormalFreydLongExact({ artifactId: 'native-delta-equations', bundle: v.bundle, run,
        source: v.initialSource, fingerprint, decisionEvidence: id => 'Explicitly adopt the original matrix equation ' + id });
};
let equationsPromise: ReturnType<typeof adoptEquations>;
const equations = () => equationsPromise ??= adoptEquations();
const realize = async () => {
    const v = context(), adopted = await equations();
    const entry = v.preparedModel.inventory.connectings.find(x => x.key === 'degree/1/connecting')!;
    const decisions: string[] = [];
    const input = { artifactId: 'native-delta-model', modelId: 'native-scalar-model', observationId: 'degree/1/connecting',
        formalModel: v.formalModel, normality: v.normality, prepared: entry.prepared, source: adopted.source, fingerprint,
        decisionEvidence: (id: string) => { decisions.push(id); return 'Explicit matrix computation or complete native arrow interpretation: ' + id; } };
    const result = await trustAlgebraFormalFreydNativeConnecting(input);
    return { v, adopted, entry, input, result, decisions };
};
let realizationPromise: ReturnType<typeof realize>;
const consumer = () => realizationPromise ??= realize();

describe('v3.2 direct native connecting realization', () => {
    it('realizes the nonzero middle δ with native row contracts and automatic matrix inputs', async t => {
        await equations();
        const forbid = () => { throw new Error('Native arrow realization must retain the original H, map and universals'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { v, adopted, entry, result } = await consumer();
            const map = entry.prepared.selected.homologyMap;
            assert.equal(isPolynomialFreydMorphismZero(map), false);
            assert.equal(result.observation.realization.prepared.selected, entry.prepared.selected);
            assert.equal(result.observation.realization.source.actual.selected, entry.prepared.selected.source);
            assert.equal(result.observation.realization.target.actual.selected, entry.prepared.selected.target);
            assert.ok(result.counts.interpretationClaims >= 2);
            assert.equal(result.counts.connectingReplays, 0);
            assert.equal(result.counts.homologyReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            const semantic = result.source.entries.filter(x => x.classification === 'trusted-presentation-semantics');
            assert.equal(semantic.length, result.counts.interpretationClaims);
            assert.ok(semantic.slice(0, -1).every(x => serializeCoreExpression(x.declaration.type).includes('bridge_FreydAdjunctionModelRowShortExact')));
            assert.ok(serializeCoreExpression(semantic.at(-1)!.declaration.type).includes('bridge_FreydArrowObservation'));
            assert.equal(result.rows.length, 4);
            assert.equal(result.source.environment.lookup('bridge_FreydHomologyModel'), undefined);
            assert.equal(result.observation.profile.requiresLegacyModel, false);
            assert.equal(result.observation.profile.endpointCasts, false);
            const checker = createCoreProofChecker(result.source.environment), r = result.observation.realization;
            checker.check(checker.rootContext, r.formalArrow, r.observationType);
            checker.check(checker.rootContext, r.nativeArrow, r.observationType);
            checker.check(checker.rootContext, result.proof, r.claimType);
            assert.match(serializeCoreExpression(r.formalArrow), /bridge_freyd_adjunction_model_connecting_observation/u);
            assert.equal(adopted.source.entries.length, v.bundle.equations.claims.length);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
            t.diagnostic(JSON.stringify(result.counts));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('reuses every matrix prerequisite and the complete-arrow agreement without another decision', async () => {
        const { input, result } = await consumer();
        const again = await trustAlgebraFormalFreydNativeConnecting({ ...input, source: result.source,
            artifactId: 'native-delta-reuse', decisionEvidence: () => { assert.fail('All thirty-seven requests must reuse their proofs'); } });
        assert.equal(again.source, result.source);
        assert.equal(again.counts.reused, 37);
        assert.equal(again.counts.newAssumptions, 0);
        assert.ok(kernelExpressionEquals(again.proof, result.proof));
        assert.equal(again.observation.realization.formalData, result.observation.realization.formalData);
    });

    it('rejects foreign profiles, mixed models, forged preparations and a wrongly typed native model', async () => {
        const { v, input, result } = await consumer();
        const foreignSource = { ...result.observationInput.source, profile: {
            ...result.observationInput.source.profile, revision: 'foreign-point-profile'
        } } as unknown as typeof result.observationInput.source;
        assert.throws(() => algebraFormalFreydNativeConnectingObservationBundle({ ...result.observationInput, source: foreignSource }),
            /point observation profiles/iu);
        assert.throws(() => result.observation.adapter.normalizeRealization({ ...result.observation.realization }, 'test'), /Foreign/iu);
        assert.throws(() => algebraFormalFreydNativeConnectingObservationBundle({ ...result.observationInput,
            rows: result.rows.map((row, i) => i === 0 ? { ...row, exact: row.chain } : row) }));
        await assert.rejects(trustAlgebraFormalFreydNativeConnecting({ ...input, prepared: { ...input.prepared } }), /issued/iu);
        await assert.rejects(trustAlgebraFormalFreydNativeConnecting({ ...input, normality: v.formalModel,
            decisionEvidence: () => { assert.fail('Reject the model type before adopting any claim'); } }));
        const s = result.observationInput.source.realization, otherM = kernelFree('other_native_delta_model', p);
        const environment = result.source.environment.extend({ name: otherM.name,
            type: algebraFormalFreydNativeModelType(v.formalRing), mode: binderMode('explicit', 'functorial'), provenance: p });
        const other = algebraFormalFreydNativeModelHomologyObservationBundle({ modelId: s.modelId, observationId: 'foreign-source',
            formalModel: otherM, environment, actual: s.actual,
            aboveLaw: s.inputLaws.above, belowLaw: s.inputLaws.below, chainLaw: s.inputLaws.chain });
        assert.throws(() => algebraFormalFreydNativeConnectingObservationBundle({ ...result.observationInput, environment, source: other }),
            /one model/iu);
    });

    it('emits the native arrow, computed arrow and explicit realization for Lambdapi', async () => {
        const { result } = await consumer(), r = result.observation.realization;
        const source = freydNativeModelProbe(result.source.environment, [
            { label: 'complete native δ', term: r.formalArrow, type: r.observationType, span: p.span! },
            { label: 'computed middle δ with original endpoints', term: r.nativeArrow, type: r.observationType, span: p.span! },
            { label: 'explicit native δ realization', term: result.proof, type: r.claimType, span: p.span! }
        ]);
        assert.doesNotMatch(source, /FreydHomologyModel|freyd_homology_model/u);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_CONNECTING_PROBE_OUTPUT) {
            writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_CONNECTING_PROBE_OUTPUT, source);
        }
    });
});
