/** One actual interior homology and exactness term, not an opaque exactness claim. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it, mock } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS, AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN, affineFormalCommRingType, affineFormalRingElementType,
    algebraPolynomialIdeal, algebraPolynomialQuotientRing, algebraPresentedAlgebra,
    binderMode, checkLambdapiProbe, createAlgebraFormalAssumptionSource,
    createCoreProofArtifactFingerprint, createCoreProofChecker, defineAffineFormalPolynomialReifier,
    kernelExpressionEquals, kernelFree, provenance, serializeCoreLfKernelProbe, sourceSpan
} from '../src/v3_2';
import { AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption } from '../src/v3_2/algebra_formal_assumption_source';
import { AlgebraFormalWorkflowInput, runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { KernelExpression } from '../src/v3_2/kernel';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import { createAlgebraPolynomialFreydKernelChoiceProviders } from '../src/v3_2/algebra_polynomial_selected_weak_pullback_provider';
import { prepareAlgebraFormalFreydKernelChoiceProviders, trustAlgebraFormalFreydKernelChoiceProviders } from '../src/v3_2/algebra_formal_freyd_kernel_choice_providers';
import { delegateAlgebraFormalPresentationMorphismEquations } from '../src/v3_2/algebra_formal_presentation_morphism_batch';
import { algebraFormalFreydChainPairDelegationBundle, algebraFormalFreydChainPairTerm } from '../src/v3_2/algebra_formal_freyd_chain_pair';
import { createAlgebraPolynomialFreydHomologyEngine } from '../src/v3_2/algebra_polynomial_freyd_homology_category';
import { algebraFormalFreydEpimorphismBlockDelegationBundle, algebraFormalFreydEpimorphismTerm } from '../src/v3_2/algebra_formal_freyd_epimorphism';
import { createAlgebraPolynomialFreydAbelianEngine } from '../src/v3_2/algebra_polynomial_freyd_abelian_category';
import { algebraFormalFreydActualHomologyReconstructionBundle, algebraFormalFreydActualHomologyTerm, defineAlgebraFormalFreydActualHomologyRealization } from '../src/v3_2/algebra_formal_freyd_actual_homology';
import { FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_actual_homology_signatures';
import { algebraFormalFreydModelType, createFormalFreydModelProofEnvironment, FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_model_signatures';
import { algebraFormalFreydModelHomologyObservationBundle, algebraFormalFreydRetainedHomologyPresentation } from '../src/v3_2/algebra_formal_freyd_model_observation';
import { defineAlgebraFormalComputationGoal } from '../src/v3_2/algebra_formal_delegation';
import { FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_kernel_choice_provider_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_spine_signatures';

const p = provenance('surface', 'actual interior homology', sourceSpan('tests/actual-interior-homology.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const decisionEvidence = (id: string) => 'Explicitly adopt the selected equation/provider semantics: ' + id;

const adopt = async <R, I, O>(source: AlgebraFormalAssumptionSource, id: string, claimType: KernelExpression,
    input: Pick<AlgebraFormalWorkflowInput<R, I, O>, 'adapter' | 'realization' | 'engine'>) => {
    const run = await runAlgebraFormalWorkflow({ ...input, goalId: id, document: {
        moduleId: source.moduleId, declarationId: id, environment: source.environment, type: claimType,
        plan: coreProofPlanHole(id, { provenance: p, expectation: { contextDepth: 0, target: claimType } }),
        provenance: p, fingerprint: fingerprint(id)
    } });
    const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: id.replace(/-/gu, '_'),
        decision: { kind: 'trust-exact-algebra-computation', evidence: decisionEvidence(id) } });
    const next = appendAlgebraFormalAssumption({ source, adoption, classification: 'computed-equation' });
    return { source: next, proof: next.entries[next.entries.length - 1].reference };
};

const construct = async () => {
    const whole = algebraPolynomialFreydBoundedLongExactHomology(polynomialFreydHomologyFixture('two'));
    const point = whole.interior[2];
    const selected = point.exactness.homology;
    const ring = whole.sequence.ring;
    const R = kernelFree('actual_homology_R', p), x = kernelFree('actual_homology_x', p);
    // Given coherent models; the test does not construct them from raw providers.
    const formalModel = kernelFree('actual_homology_model', p);
    const otherModel = kernelFree('actual_homology_other_model', p);
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra: algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))),
        formalRing: R, generatorTerms: [x], coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(key);
            if (!term) { term = kernelFree('actual_homology_c_' + [...key].map(c => c.codePointAt(0)!.toString(16)).join('_'), p); coefficients.set(key, term); }
            return term;
        }, status: 'trusted-computation'
    });
    const prepared = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier,
        selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'actual-homology-cycles', ring, kernel: selected.cycles }) });
    const reconstruction = algebraFormalFreydActualHomologyReconstructionBundle({ reifier, selected, providers: prepared });
    algebraFormalFreydRetainedHomologyPresentation(reconstruction.realization);
    const chain = algebraFormalFreydChainPairDelegationBundle({ reifier, selected: selected.pair });
    const epi = algebraFormalFreydEpimorphismBlockDelegationBundle({ reifier, selected: point.exactness.epimorphism! });
    const element = affineFormalRingElementType(R);
    const environment = createFormalFreydModelProofEnvironment([
        { name: R.name, type: affineFormalCommRingType() }, { name: x.name, type: element },
        { name: formalModel.name, type: algebraFormalFreydModelType(R) },
        { name: otherModel.name, type: algebraFormalFreydModelType(R) },
        ...[...coefficients.values()].map(term => ({ name: term.name, type: element }))
    ]);
    const initial = createAlgebraFormalAssumptionSource({ moduleId: 'proof.cas.actual-homology', sourceId: 'tests/actual-homology.assumptions', baseEnvironment: environment });
    const forbid = () => { throw new Error('Actual homology reconstruction must not reselect universal objects'); };
    const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
        mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid), mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
    try {
        const providers = await trustAlgebraFormalFreydKernelChoiceProviders({ artifactId: 'actual-homology-providers', prepared, source: initial, fingerprint, decisionEvidence });
        const maps = await delegateAlgebraFormalPresentationMorphismEquations({ artifactId: 'actual-homology-maps', reifier,
            morphisms: [selected.pair.dNext, selected.boundaryMorphism], agreements: [], chainSquares: [], source: providers.source, fingerprint, decisionEvidence });
        const aboveLaw = maps.source.entries[providers.source.entries.length].reference;
        const boundaryLaw = maps.source.entries[providers.source.entries.length + 1].reference;
        const chainLaw = await adopt(maps.source, 'actual-homology-chain', chain.realization.claimType,
            { adapter: chain.adapter, realization: chain.realization, engine: createAlgebraPolynomialFreydHomologyEngine(chain.model) });
        const pair = algebraFormalFreydChainPairTerm(chain.realization, aboveLaw, providers.morphismLaw, chainLaw.proof);
        const reconstructed = await adopt(chainLaw.source, 'actual-homology-reconstruction', reconstruction.realization.claimType, reconstruction);
        const epicity = await adopt(reconstructed.source, 'actual-homology-epicity', epi.realization.claimType,
            { adapter: epi.adapter, realization: epi.realization, engine: createAlgebraPolynomialFreydAbelianEngine(epi.model) });
        const epic = algebraFormalFreydEpimorphismTerm(epi.realization, boundaryLaw, epicity.proof);
        const result = algebraFormalFreydActualHomologyTerm(reconstruction.realization, { providers, aboveLaw,
            belowLaw: providers.morphismLaw, chain: pair.term, boundaryLaw, reconstructionLaw: reconstructed.proof, epic: epic.term });
        spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        return { whole, point, selected, reifier, prepared, providers, reconstruction, initial, source: epicity.source, result, epic,
            formalModel, otherModel, aboveLaw, belowLaw: providers.morphismLaw, chainLaw: chainLaw.proof };
    } finally { spies.forEach(spy => spy.mock.restore()); }
};
let value: ReturnType<typeof construct> | undefined;
const consumer = () => value ??= construct();

const observeModel = async () => {
    const v = await consumer();
    const bundle = algebraFormalFreydModelHomologyObservationBundle({ modelId: 'actual-homology-model', observationId: 'interior-2',
        formalModel: v.formalModel, environment: v.source.environment, actual: v.reconstruction.realization,
        aboveLaw: v.aboveLaw, belowLaw: v.belowLaw, chainLaw: v.chainLaw });
    const id = 'actual-model-whole-H';
    const run = await runAlgebraFormalWorkflow({ ...bundle, goalId: id, document: {
        moduleId: v.source.moduleId, declarationId: id, environment: v.source.environment, type: bundle.realization.claimType,
        plan: coreProofPlanHole(id, { provenance: p, expectation: { contextDepth: 0, target: bundle.realization.claimType } }),
        provenance: p, fingerprint: fingerprint(id)
    } });
    const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: 'actual_model_whole_H',
        decision: { kind: 'trust-exact-algebra-computation', evidence: 'Explicitly interpret the supplied coherent model at this retained native homology point' } });
    const source = appendAlgebraFormalAssumption({ source: v.source, adoption, classification: bundle.profile.assumptionClassification });
    return { v, bundle, source };
};
let observed: ReturnType<typeof observeModel> | undefined;
const modelConsumer = () => observed ??= observeModel();

describe('v3.2 actual formal interior homology', () => {
    it('constructs homology and exactness at the original native boundary', async () => {
        const v = await consumer();
        const checker = createCoreProofChecker(v.source.environment);
        checker.validateEnvironment();
        checker.check(checker.rootContext, v.result.term, v.result.type);
        checker.check(checker.rootContext, v.result.exactness, v.result.exactnessType);
        assert.equal(v.result.selected, v.selected);
        assert.equal(v.providers.native, v.selected.cycles);
        assert.ok(kernelExpressionEquals(v.result.boundary, v.epic.morphism));
        assert.equal(v.initial.entries.length, 0);
        assert.equal(v.source.entries.filter(entry => entry.classification === 'trusted-presentation-semantics').length, 2);
    });

    it('rejects replacing the selected pair, cycle choices or raw boundary', async () => {
        const v = await consumer();
        for (const selected of [
            { ...v.selected, pair: v.whole.interior[1].pair },
            { ...v.selected, cycleObject: v.selected.pair.d.source },
            { ...v.selected, boundaryMorphism: v.selected.pair.dNext }
        ]) assert.throws(() => defineAlgebraFormalFreydActualHomologyRealization({ reifier: v.reifier, providers: v.prepared, selected }), /actual|original|retain|disagree/iu);
    });

    it('uses the whole-H owner with an explicit model interpretation and no reselection', async () => {
        await consumer();
        const forbid = () => { throw new Error('Model observation must retain the already computed universals and homology'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { v, bundle, source } = await modelConsumer();
            const checker = createCoreProofChecker(source.environment);
            checker.validateEnvironment();
            checker.check(checker.rootContext, bundle.realization.formalPoint, bundle.realization.pointType);
            checker.check(checker.rootContext, bundle.realization.nativePoint, bundle.realization.pointType);
            assert.equal(bundle.realization.actual.selected, v.selected);
            assert.equal(bundle.profile.constructsModel, false);
            assert.equal(source.entries.length, v.source.entries.length + 1);
            assert.equal(source.entries.at(-1)!.classification, 'trusted-presentation-semantics');
            assert.ok(kernelExpressionEquals(source.entries.at(-1)!.declaration.type, bundle.realization.claimType));
            assert.deepEqual(source.entries.slice(0, -1), v.source.entries);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('rejects foreign model queries, forged bindings and stale choices', async () => {
        const { v, bundle } = await modelConsumer();
        const common = { modelId: 'other-model', observationId: 'interior-2', environment: v.source.environment, actual: v.reconstruction.realization,
            aboveLaw: v.aboveLaw, belowLaw: v.belowLaw, chainLaw: v.chainLaw };
        const other = algebraFormalFreydModelHomologyObservationBundle({ ...common, formalModel: v.otherModel });
        const goal = defineAlgebraFormalComputationGoal({ goalId: 'foreign-model', document: {
            moduleId: v.source.moduleId, declarationId: 'foreign-model', environment: v.source.environment, type: other.realization.claimType,
            plan: coreProofPlanHole('foreign-model', { provenance: p, expectation: { contextDepth: 0, target: other.realization.claimType } }),
            provenance: p, fingerprint: fingerprint('foreign-model')
        } });
        assert.throws(() => bundle.adapter.acquire(goal, bundle.realization), /exact model point/iu);
        assert.throws(() => bundle.adapter.normalizeRealization({ ...bundle.realization }, 'test'), /Foreign/iu);
        assert.throws(() => algebraFormalFreydModelHomologyObservationBundle({ ...common, formalModel: v.formalModel,
            actual: { ...common.actual, formalData: 'stale' } }), /Stale/iu);
        assert.throws(() => algebraFormalFreydModelHomologyObservationBundle({ ...common, formalModel: v.reifier.formalRing }), /type|convert|unif/iu);
        const defined = kernelFree('defined_homology_model', p);
        const definedEnvironment = v.source.environment.extend({ name: defined.name, type: algebraFormalFreydModelType(v.reifier.formalRing),
            body: v.formalModel, transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
        assert.throws(() => algebraFormalFreydModelHomologyObservationBundle({ ...common, environment: definedEnvironment,
            formalModel: defined }), /reinterpret a defined model/iu);
    });

    it('checks the constructed homology and exactness together in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_ACTUAL_HOMOLOGY !== '1'
    }, async () => {
        const { v, bundle, source } = await modelConsumer();
        let environment = source.environment;
        const terms: readonly [string, KernelExpression, KernelExpression][] = [
            ['actual_interior_homology', v.result.term, v.result.type],
            ['actual_interior_exactness', v.result.exactness, v.result.exactnessType],
            ['actual_model_formal_point', bundle.realization.formalPoint, bundle.realization.pointType],
            ['actual_model_native_point', bundle.realization.nativePoint, bundle.realization.pointType]
        ];
        const assertions = terms.map(([name, term, type]) => {
            environment = environment.extend({ name, type, body: term,
                transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
            return { label: name, term: kernelFree(name, p), type, span: sourceSpan('generated/actual-homology.ts', 1, 1) };
        });
        const serialized = serializeCoreLfKernelProbe({ environment, externalFreeReferences: {
            ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
            ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
            ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
            ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
            ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS
        }, assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;\nrequire open emdash.emdash3_2_commutative_algebra_freyd_homology_models;') },
        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});
