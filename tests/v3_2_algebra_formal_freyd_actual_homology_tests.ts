/** One actual interior homology and exactness term, not an opaque exactness claim. */

import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it, mock } from 'node:test';
import { AFFINE_FORMAL_FINITE_MODULE_BINDINGS } from '../src/v3_2/algebra_formal_finite_module';
import { AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS } from '../src/v3_2/algebra_formal_localization_signatures';
import { AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS } from '../src/v3_2/algebra_formal_presentation_morphism';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { affineFormalCommRingType, affineFormalRingElementType } from '../src/v3_2/algebra_formal_conformance';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import { algebraPolynomialQuotientRing } from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { binderMode, kernelExpressionEquals, kernelFree, provenance, sourceSpan } from '../src/v3_2/kernel';
import { checkLambdapiProbe } from '../src/v3_2/probe';
import { createAlgebraFormalAssumptionSource } from '../src/v3_2/algebra_formal_assumption_source';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { defineAffineFormalPolynomialReifier } from '../src/v3_2/algebra_formal_reifier';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';
import { CoreLfScopedBuilder } from '../src/v3_2/lf_builder';
import { formalFreydSpineLanguage } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption } from '../src/v3_2/algebra_formal_assumption_source';
import { AlgebraFormalWorkflowInput, runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { KernelExpression } from '../src/v3_2/kernel';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { isPolynomialFreydMorphismZero, polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { algebraPolynomialPresentationMorphismAdd, algebraPolynomialPresentationMorphismCongruence } from '../src/v3_2/algebra_polynomial_freyd_category';
import * as nativeFunctorialHomology from '../src/v3_2/algebra_polynomial_freyd_functorial_homology';
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
import { algebraFormalFreydModelType, FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_model_signatures';
import { createFormalFreydModelMapProofEnvironment, FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_model_map_signatures';
import { prepareAlgebraFormalFreydModelMap, algebraFormalFreydModelMapSquareBundle } from '../src/v3_2/algebra_formal_freyd_model_map_preparation';
import { algebraFormalFreydModelMapObservationBundle } from '../src/v3_2/algebra_formal_freyd_model_map_observation';
import { algebraFormalFreydModelHomologyObservationBundle, algebraFormalFreydRetainedHomologyPresentation } from '../src/v3_2/algebra_formal_freyd_model_observation';
import {
    algebraFormalFreydModelConnectingObservationTerm, algebraFormalFreydModelNormalityType,
    createFormalFreydModelConnectingProofEnvironment, FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS,
    FREYD_MODEL_CONNECTING_ARGUMENTS, FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_PROFILE
} from '../src/v3_2/algebra_formal_freyd_model_connecting_signatures';
import { kernelInstantiate } from '../src/v3_2/kernel';
import { prepareAlgebraFormalFreydModelConnecting, assertAlgebraFormalFreydModelConnectingPreparationCurrent }
    from '../src/v3_2/algebra_formal_freyd_model_connecting_preparation';
import * as nativeConnecting from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import { trustAlgebraFormalFreydModelConnecting } from '../src/v3_2/algebra_formal_freyd_model_connecting_workflow';
import { algebraFormalPresentationMorphismDelegationBundle } from '../src/v3_2/algebra_formal_presentation_morphism_delegation';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
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
    const unscaled = whole.degrees[1].projection;
    const oldMap = unscaled.chainMap;
    const scaledChain = nativeFunctorialHomology.algebraPolynomialFreydHomologyChainMap({ source: oldMap.source, target: oldMap.target,
        fNext: algebraPolynomialPresentationMorphismAdd(oldMap.fNext, oldMap.fNext),
        f: algebraPolynomialPresentationMorphismAdd(oldMap.f, oldMap.f),
        fPrev: algebraPolynomialPresentationMorphismAdd(oldMap.fPrev, oldMap.fPrev) });
    const selectedMap = nativeFunctorialHomology.algebraPolynomialFreydInducedHomologyMap(scaledChain);
    const mapPrepared = prepareAlgebraFormalFreydModelMap({ reifier, selected: selectedMap });
    const actualPoint = (which: 'source' | 'target') => {
        const selected = selectedMap.chainMap[which];
        const providers = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier,
            selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'map-' + which + '-cycles', ring, kernel: selected.cycles }) });
        const actual = defineAlgebraFormalFreydActualHomologyRealization({ reifier, selected, providers });
        algebraFormalFreydRetainedHomologyPresentation(actual);
        return actual;
    };
    const mapSourceActual = actualPoint('source'), mapTargetActual = actualPoint('target');
    const chain = algebraFormalFreydChainPairDelegationBundle({ reifier, selected: selected.pair });
    const epi = algebraFormalFreydEpimorphismBlockDelegationBundle({ reifier, selected: point.exactness.epimorphism! });
    const element = affineFormalRingElementType(R);
    const environment = createFormalFreydModelMapProofEnvironment([
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
            formalModel, otherModel, aboveLaw, belowLaw: providers.morphismLaw, chainLaw: chainLaw.proof,
            unscaled, selectedMap, mapPrepared, mapSourceActual, mapTargetActual };
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

const observeMap = async () => {
    const v = await consumer();
    const start = v.source.entries.length;
    const batch = await delegateAlgebraFormalPresentationMorphismEquations({ artifactId: 'model-map-inputs', reifier: v.reifier,
        morphisms: [...v.mapPrepared.maps.map(m => m.selected), v.selectedMap.homologyMap], agreements: [], chainSquares: [],
        source: v.source, fingerprint, decisionEvidence });
    const laws = batch.source.entries.slice(start).map(e => e.reference);
    const chainSBundle = algebraFormalFreydChainPairDelegationBundle({ reifier: v.reifier, selected: v.selectedMap.chainMap.source.pair });
    const chainTBundle = algebraFormalFreydChainPairDelegationBundle({ reifier: v.reifier, selected: v.selectedMap.chainMap.target.pair });
    const chainS = await adopt(batch.source, 'model-map-source-chain', chainSBundle.realization.claimType,
        { adapter: chainSBundle.adapter, realization: chainSBundle.realization, engine: createAlgebraPolynomialFreydHomologyEngine(chainSBundle.model) });
    const chainT = await adopt(chainS.source, 'model-map-target-chain', chainTBundle.realization.claimType,
        { adapter: chainTBundle.adapter, realization: chainTBundle.realization, engine: createAlgebraPolynomialFreydHomologyEngine(chainTBundle.model) });
    const upperBundle = algebraFormalFreydModelMapSquareBundle(v.mapPrepared, 'upper');
    const lowerBundle = algebraFormalFreydModelMapSquareBundle(v.mapPrepared, 'lower');
    const upper = await adopt(chainT.source, 'model-map-upper', upperBundle.realization.claimType, upperBundle);
    const lower = await adopt(upper.source, 'model-map-lower', lowerBundle.realization.claimType, lowerBundle);
    const sourcePoint = algebraFormalFreydModelHomologyObservationBundle({ modelId: 'actual-homology-model', observationId: 'degree0-B',
        formalModel: v.formalModel, environment: lower.source.environment, actual: v.mapSourceActual,
        aboveLaw: laws[0], belowLaw: laws[1], chainLaw: chainS.proof });
    const targetPoint = algebraFormalFreydModelHomologyObservationBundle({ modelId: 'actual-homology-model', observationId: 'degree0-C',
        formalModel: v.formalModel, environment: lower.source.environment, actual: v.mapTargetActual,
        aboveLaw: laws[2], belowLaw: laws[3], chainLaw: chainT.proof });
    const bundle = algebraFormalFreydModelMapObservationBundle({ observationId: 'twice-projection', source: sourcePoint, target: targetPoint,
        prepared: v.mapPrepared, environment: lower.source.environment, componentLaws: [laws[4], laws[5], laws[6]],
        upperLaw: upper.proof, lowerLaw: lower.proof, resultLaw: laws[7] });
    const id = 'model-map-arrow';
    const run = await runAlgebraFormalWorkflow({ ...bundle, goalId: id, document: { moduleId: lower.source.moduleId,
        declarationId: id, environment: lower.source.environment, type: bundle.realization.claimType,
        plan: coreProofPlanHole(id, { provenance: p, expectation: { contextDepth: 0, target: bundle.realization.claimType } }),
        provenance: p, fingerprint: fingerprint(id) } });
    const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: 'model_map_arrow', decision: {
        kind: 'trust-exact-algebra-computation', evidence: 'Interpret the supplied model at the retained complete homology arrow, with its original endpoints' } });
    const source = appendAlgebraFormalAssumption({ source: lower.source, adoption, classification: bundle.profile.assumptionClassification });
    return { v, sourcePoint, targetPoint, bundle, source, lower, laws, upper };
};
let observedMap: ReturnType<typeof observeMap> | undefined;
const mapConsumer = () => observedMap ??= observeMap();

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

    it('binds a nonzero nonidentity homology map as one complete arrow without reselection', async () => {
        const v = await consumer();
        assert.equal(isPolynomialFreydMorphismZero(v.selectedMap.homologyMap), false);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(v.selectedMap.homologyMap, v.unscaled.homologyMap).agrees, false);
        const forbid = () => { throw new Error('Map observation must use the already computed map and universals'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeFunctorialHomology, 'algebraPolynomialFreydInducedHomologyMap', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid), mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { bundle, source } = await mapConsumer();
            const checker = createCoreProofChecker(source.environment);
            checker.validateEnvironment();
            checker.check(checker.rootContext, bundle.realization.chain.term, bundle.realization.chain.type);
            checker.check(checker.rootContext, bundle.realization.formalArrow, bundle.realization.observationType);
            checker.check(checker.rootContext, bundle.realization.nativeArrow, bundle.realization.observationType);
            assert.equal(bundle.realization.prepared.selected, v.selectedMap);
            assert.equal(bundle.profile.endpointTransport, false);
            assert.equal(source.entries.at(-1)!.classification, 'trusted-presentation-semantics');
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('rejects mixed models, replaced map selections, forged preparations and unrelated laws', async () => {
        const { v, sourcePoint, targetPoint, bundle, lower, upper, laws } = await mapConsumer();
        const args = { observationId: 'map-negative', source: sourcePoint, target: targetPoint, prepared: v.mapPrepared,
            environment: lower.source.environment, componentLaws: [laws[4], laws[5], laws[6]] as const,
            upperLaw: upper.proof, lowerLaw: lower.proof, resultLaw: laws[7] };
        const otherTarget = algebraFormalFreydModelHomologyObservationBundle({ modelId: 'other-model', observationId: 'degree0-C',
            formalModel: v.otherModel, environment: lower.source.environment, actual: v.mapTargetActual,
            aboveLaw: targetPoint.realization.inputLaws.above, belowLaw: targetPoint.realization.inputLaws.below,
            chainLaw: targetPoint.realization.inputLaws.chain });
        assert.throws(() => algebraFormalFreydModelMapObservationBundle({ ...args, target: otherTarget }), /same supplied model/iu);
        assert.throws(() => algebraFormalFreydModelMapObservationBundle({ ...args, source: targetPoint }), /original source\/target/iu);
        assert.throws(() => algebraFormalFreydModelMapObservationBundle({ ...args, prepared: { ...v.mapPrepared } }), /issued/iu);
        assert.throws(() => algebraFormalFreydModelMapSquareBundle({ ...v.mapPrepared,
            upper: { ...v.mapPrepared.upper, claimType: v.mapPrepared.lower.claimType } }, 'upper'), /issued/iu);
        assert.throws(() => algebraFormalFreydModelMapObservationBundle({ ...args, resultLaw: upper.proof }), /type|convert|unif/iu);
        for (const selected of [
            { ...v.selectedMap, homologyMap: v.unscaled.homologyMap },
            { ...v.selectedMap, cyclesMap: { ...v.selectedMap.cyclesMap, kernel: v.selectedMap.chainMap.source.cycles } },
            { ...v.selectedMap, chainMap: { ...v.selectedMap.chainMap, upperAgreement: v.selectedMap.chainMap.lowerAgreement } }
        ]) assert.throws(() => prepareAlgebraFormalFreydModelMap({ reifier: v.reifier, selected }), /original|semantic products/iu);
        assert.throws(() => bundle.adapter.normalizeRealization({ ...bundle.realization }, 'test'), /Foreign/iu);
        const claim = sourcePoint.realization.claimType;
        const goal = defineAlgebraFormalComputationGoal({ goalId: 'foreign-map-query', document: {
            moduleId: lower.source.moduleId, declarationId: 'foreign-map-query', environment: lower.source.environment, type: claim,
            plan: coreProofPlanHole('foreign-map-query', { provenance: p, expectation: { contextDepth: 0, target: claim } }),
            provenance: p, fingerprint: fingerprint('foreign-map-query')
        } });
        assert.throws(() => bundle.adapter.acquire(goal, bundle.realization), /complete model arrow/iu);
    });

    it('checks the constructed homology and exactness together in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_ACTUAL_HOMOLOGY !== '1'
    }, async () => {
        const { v, bundle } = await modelConsumer();
        const map = await mapConsumer();
        let environment = map.source.environment;
        const terms: readonly [string, KernelExpression, KernelExpression][] = [
            ['actual_interior_homology', v.result.term, v.result.type],
            ['actual_interior_exactness', v.result.exactness, v.result.exactnessType],
            ['actual_model_formal_point', bundle.realization.formalPoint, bundle.realization.pointType],
            ['actual_model_native_point', bundle.realization.nativePoint, bundle.realization.pointType],
            ['actual_model_chain_map', map.bundle.realization.chain.term, map.bundle.realization.chain.type],
            ['actual_model_formal_arrow', map.bundle.realization.formalArrow, map.bundle.realization.observationType],
            ['actual_model_native_arrow', map.bundle.realization.nativeArrow, map.bundle.realization.observationType]
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
            ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS
        }, assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;\nrequire open emdash.emdash3_2_commutative_algebra_freyd_homology_models;\nrequire open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;\nrequire open emdash.emdash3_2_commutative_algebra_freyd_homology_model_maps;') },
        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});


describe('v3.2 model connecting signatures', () => {
    it('adopts a retained nonsplit connecting arrow with explicit row semantics and no reselection', async testContext => {
        const v = await consumer(), selected = v.whole.windows[1].connecting;
        assert.equal(isPolynomialFreydMorphismZero(selected.homologyMap), false);
        const R = kernelFree('connecting_R', p), x = kernelFree('connecting_x', p);
        const M = kernelFree('connecting_model', p), N = kernelFree('connecting_normality', p);
        const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
        const reifier = defineAffineFormalPolynomialReifier({
            algebra: algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(selected.sequence.ring, []))),
            formalRing: R, generatorTerms: [x], coefficientReifier: coefficient => {
                const key = RATIONAL_DOMAIN.text(coefficient);
                let term = coefficients.get(key);
                if (!term) { term = kernelFree('connecting_c_' + [...key].map(c => c.codePointAt(0)!.toString(16)).join('_'), p); coefficients.set(key, term); }
                return term;
            }, status: 'trusted-computation'
        });
        const prepared = prepareAlgebraFormalFreydModelConnecting({ reifier, selected });
        const actual = (which: 'source' | 'target') => {
            const H = selected[which];
            const providers = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier,
                selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'connecting/' + which,
                    ring: selected.sequence.ring, kernel: H.cycles }) });
            const result = defineAlgebraFormalFreydActualHomologyRealization({ reifier, selected: H, providers });
            algebraFormalFreydRetainedHomologyPresentation(result);
            return result;
        };
        const sourceActual = actual('source'), targetActual = actual('target');
        const environment = createFormalFreydModelConnectingProofEnvironment([
            { name: R.name, type: affineFormalCommRingType() }, { name: x.name, type: affineFormalRingElementType(R) },
            { name: M.name, type: algebraFormalFreydModelType(R) }, { name: N.name, type: algebraFormalFreydModelNormalityType(R, M) },
            ...[...coefficients.values()].map(term => ({ name: term.name, type: affineFormalRingElementType(R) }))
        ]);
        let source = createAlgebraFormalAssumptionSource({ moduleId: 'proof.cas.connecting', sourceId: 'tests/connecting.assumptions', baseEnvironment: environment });
        const known = new Map<string, KernelExpression>();
        const append = async <Q, A, B>(id: string, claimType: KernelExpression,
            classification: 'computed-equation' | 'trusted-presentation-semantics',
            bundle: Pick<AlgebraFormalWorkflowInput<Q, A, B>, 'adapter' | 'realization' | 'engine'>) => {
            const key = serializeCoreExpression(claimType), old = known.get(key);
            if (old) return old;
            const run = await runAlgebraFormalWorkflow({ ...bundle, goalId: id, document: {
                moduleId: source.moduleId, declarationId: id, environment: source.environment, type: claimType,
                plan: coreProofPlanHole(id, { provenance: p, expectation: { contextDepth: 0, target: claimType } }),
                provenance: p, fingerprint: fingerprint(id)
            } });
            const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: id,
                decision: { kind: 'trust-exact-algebra-computation', evidence: 'Explicit connecting model/equation interpretation ' + id } });
            source = appendAlgebraFormalAssumption({ source, adoption, classification });
            const proof = source.entries.at(-1)!.reference;
            known.set(key, proof); return proof;
        };
        const point = async (a: typeof sourceActual, name: string) => {
            const morph = async (value: typeof a.chain.above, which: string) => {
                const bundle = algebraFormalPresentationMorphismDelegationBundle({ reifier, selected: value.selected });
                return append(name + '_' + which, value.claimType, 'computed-equation', { ...bundle,
                    engine: createAlgebraTypeScriptReferenceEngine({ id: name + '/' + which, revision: 'v1', implementations: bundle.operations.implementations }) });
            };
            const aboveLaw = await morph(a.chain.above, 'above'), belowLaw = await morph(a.chain.below, 'below');
            const chain = algebraFormalFreydChainPairDelegationBundle({ reifier, selected: a.selected.pair });
            const chainLaw = await append(name + '_chain', a.chain.claimType, 'computed-equation', { ...chain,
                engine: createAlgebraPolynomialFreydHomologyEngine(chain.model) });
            const result = algebraFormalFreydModelHomologyObservationBundle({ modelId: 'connecting-model', observationId: name,
                formalModel: M, environment: source.environment, actual: a, aboveLaw, belowLaw, chainLaw });
            await append(name + '_model', result.realization.claimType, 'trusted-presentation-semantics', result);
            return result;
        };
        const modelSource = await point(sourceActual, 'connecting_source'), modelTarget = await point(targetActual, 'connecting_target');
        const before = source.entries.length;
        const forbid = () => { throw new Error('Connecting interpretation must retain the original computation'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const result = await trustAlgebraFormalFreydModelConnecting({ artifactId: 'connecting-retained', prepared,
                modelSource, modelTarget, normality: N, source, fingerprint, decisionEvidence });
            assert.equal(result.prepared.selected, selected);
            assert.equal(result.observation.realization.source.actual.selected, selected.source);
            assert.equal(result.observation.realization.target.actual.selected, selected.target);
            assert.equal(result.observation.profile.nativeWholeConnectingObservation, true);
            assert.equal(result.observation.profile.endpointCasts, false);
            assert.match(serializeCoreExpression(result.observation.realization.formalArrow),
                /bridge_freyd_homology_model_native_connecting_observation/u);
            assert.equal(result.observation.realization.values.source_chain, modelSource.realization.pair.term);
            assert.equal(result.observation.realization.values.target_chain, modelTarget.realization.pair.term);
            assert.equal(result.rows.length, 4);
            assert.equal(result.counts.homologyReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            assert.equal(result.counts.connectingReplays, 0);
            assert.ok(result.source.entries.length > before);
            assert.equal(result.source.entries.at(-1)!.classification, 'trusted-presentation-semantics');
            assert.ok(result.source.entries.slice(before).some(entry => entry.classification === 'computed-equation'));
            const checker = createCoreProofChecker(result.source.environment);
            checker.check(checker.rootContext, result.proof, result.observation.realization.claimType);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
            const decisions: string[] = [];
            const replay = await trustAlgebraFormalFreydModelConnecting({ artifactId: 'connecting-reuse', prepared,
                modelSource, modelTarget, normality: N, source: result.source, fingerprint,
                decisionEvidence: id => { decisions.push(id); return 'Unexpected duplicate decision'; } });
            assert.equal(replay.counts.newAssumptions, 0);
            assert.deepEqual(decisions, []);
            assert.equal(replay.proof, result.proof);
            await assert.rejects(() => trustAlgebraFormalFreydModelConnecting({ artifactId: 'connecting-bad-normality', prepared,
                modelSource, modelTarget, normality: modelSource.realization.pair.term, source, fingerprint,
                decisionEvidence: id => { decisions.push(id); return 'Unexpected invalid-input decision'; } }));
            assert.deepEqual(decisions, []);
            assert.throws(() => result.observation.adapter.normalizeRealization({ ...result.observation.realization }, 'forged'), /Foreign/iu);
            const wrongType = modelSource.realization.claimType;
            const wrongGoal = defineAlgebraFormalComputationGoal({ goalId: 'wrong_connecting_claim', document: {
                moduleId: result.source.moduleId, declarationId: 'wrong_connecting_claim', environment: result.source.environment,
                type: wrongType, plan: coreProofPlanHole('wrong_connecting_claim', { provenance: p,
                    expectation: { contextDepth: 0, target: wrongType } }), provenance: p, fingerprint: fingerprint('wrong_connecting_claim')
            } });
            assert.throws(() => result.observation.adapter.acquire(wrongGoal, result.observation.realization), /Goal differs/iu);
            if (process.env.EMDASH_RUN_PROOF_CAS_FREYD_MODEL_CONNECTING_ADOPTION === '1') {
                const value = result.observation.realization;
                const assertions = [
                    ...Object.keys(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS).map(name => ({
                        label: name, term: kernelFree(name, p), type: result.source.environment.lookup(name)!.type,
                        span: sourceSpan('generated/retained-connecting-signatures.ts', 1, 1)
                    })),
                    { label: 'retained_formal_connecting', term: value.formalArrow, type: value.observationType, span: sourceSpan('generated/retained-connecting.ts', 1, 1) },
                    { label: 'retained_native_connecting', term: value.nativeArrow, type: value.observationType, span: sourceSpan('generated/retained-connecting.ts', 2, 1) },
                    { label: 'connecting_interpretation', term: result.proof, type: value.claimType, span: sourceSpan('generated/retained-connecting.ts', 3, 1) },
                    ...value.rowMaps.map((map, i) => ({ label: 'connecting_row_map_' + i, term: map.term, type: map.type,
                        span: sourceSpan('generated/retained-connecting.ts', 4 + i, 1) }))
                ];
                const serialized = serializeCoreLfKernelProbe({ environment: result.source.environment, externalFreeReferences: {
                    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
                    ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
                    ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
                    ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS,
                    ...FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS
                }, assertions });
                const imports = [
                    'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;',
                    'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;',
                    'require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_native_connecting;'
                ].join('\n');
                let source = serialized.source.replace('require open emdash.emdash3_2;', imports);
                for (const name of Object.values(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS)) {
                    source = source.replace('assert ⊢ ' + name + ' :', 'assert ⊢ @' + name + ' :');
                }
                const output = process.env.EMDASH_PROOF_CAS_NATIVE_CONNECTING_PROBE_OUTPUT;
                if (output) {
                    writeFileSync(output, source, 'utf8');
                    testContext.diagnostic('Emitted the retained native connecting probe; Lambdapi validation is a separate bounded stage.');
                } else {
                    const checked = checkLambdapiProbe({ ...serialized, source },
                        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
                    assert.equal(checked.timedOut, false, checked.diagnostics.slice(-8000));
                    assert.equal(checked.accepted, true, checked.diagnostics.slice(-12000));
                }
            }
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('prepares the retained connecting window without homology or universal reselection', async () => {
        const v = await consumer(), selected = v.whole.windows[1].connecting;
        const forbid = () => { throw new Error('Connecting preparation must not re-run selected universal algorithms'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(nativeFunctorialHomology, 'algebraPolynomialFreydInducedHomologyMap', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const prepared = prepareAlgebraFormalFreydModelConnecting({ reifier: v.reifier, selected });
            assert.equal(prepared.selected, selected);
            assert.equal(prepared.source.selected, selected.source.pair);
            assert.equal(prepared.target.selected, selected.target.pair);
            assert.equal(prepared.result.selected, selected.homologyMap);
            assert.deepEqual(prepared.rows.map(row => row.degree), [2, 1, 0, -1]);
            assert.equal(prepared.rowMaps.length, 3);
            assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
            assert.throws(() => assertAlgebraFormalFreydModelConnectingPreparationCurrent({ ...prepared }), /issued/iu);
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('rejects changed connecting endpoints or an arrow inconsistent with the retained trace', async () => {
        const v = await consumer(), selected = v.whole.windows[1].connecting;
        const changed = algebraPolynomialPresentationMorphismAdd(selected.homologyMap, selected.homologyMap);
        assert.throws(() => prepareAlgebraFormalFreydModelConnecting({ reifier: v.reifier,
            selected: { ...selected, homologyMap: changed } }), /reconstruction/iu);
        assert.throws(() => prepareAlgebraFormalFreydModelConnecting({ reifier: v.reifier,
            selected: { ...selected, source: selected.target } }), /original H/iu);
        let active = selected;
        const proxy = new Proxy({ ...selected }, { get: (_target, key) => Reflect.get(active, key) });
        const prepared = prepareAlgebraFormalFreydModelConnecting({ reifier: v.reifier, selected: proxy });
        active = { ...selected, homologyMap: changed };
        assert.throws(() => assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared), /Stale|reconstruction/iu);
    });

    const fixture = () => {
        let environment = createFormalFreydModelConnectingProofEnvironment([]);
        let target = environment.lookup('bridge_freyd_homology_model_native_connecting_observation')!.type;
        const values: Record<string, KernelExpression> = {};
        for (const field of FREYD_MODEL_CONNECTING_ARGUMENTS) {
            assert.equal(target.tag, 'pi');
            if (target.tag !== 'pi') throw new Error('Connecting telescope ended early');
            assert.equal(target.binder.mode.plicity, field.implicit ? 'implicit' : 'explicit');
            const value = kernelFree('connecting_input_' + field.name, p);
            environment = environment.extend({ name: value.name, type: target.binder.type,
                mode: binderMode('explicit', 'functorial'), provenance: p });
            values[field.name] = value;
            target = kernelInstantiate(target.body, value);
        }
        return { environment, values, target, term: algebraFormalFreydModelConnectingObservationTerm(values) };
    };

    it('constructs the exact conditional connecting call without changing Core owners', () => {
        const v = fixture(), checker = createCoreProofChecker(v.environment);
        assert.equal(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_PROFILE.sourceOperations,
            'native-whole-delta-at-retained-H-endpoints');
        assert.equal(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS.bridge_freyd_homology_model_native_connecting_observation,
            'freyd_homology_model_native_connecting_observation');
        assert.equal(FREYD_MODEL_CONNECTING_ARGUMENTS.length, 47);
        assert.equal(new Set(FREYD_MODEL_CONNECTING_ARGUMENTS.map(field => field.name)).size, 47);
        checker.check(checker.rootContext, v.term, v.target);
        checker.check(checker.rootContext, v.values.N, algebraFormalFreydModelNormalityType(v.values.R, v.values.M));
        for (const name of Object.keys(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS)) {
            assert.equal(v.environment.lookup(name)!.body, undefined);
        }
    });

    it('rejects legacy normality and row contracts at the native connecting interface', () => {
        const v = fixture();
        let environment = v.environment;
        for (const [native, legacy] of [
            ['bridge_FreydHomologyModelNativeNormality', 'bridge_FreydHomologyModelNormality'],
            ['bridge_FreydHomologyModelNativeShortExact', 'bridge_FreydHomologyModelShortExact']
        ]) {
            assert.equal(environment.lookup(legacy), undefined);
            environment = environment.extend({ ...environment.lookup(native)!, name: legacy });
        }
        const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
        const oldNormalityType = b.lower(L.tau(L.call('bridge_FreydHomologyModelNormality',
            [b.embed(v.values.R), b.embed(v.values.M)], 1)));
        const rowValues = ['R', 'M', 'A0', 'B0', 'D0', 'i0', 'p0', 'c0'].map(name => b.embed(v.values[name]));
        const oldRowType = b.lower(L.tau(b.call(b.free('bridge_FreydHomologyModelShortExact'),
            rowValues.map((value, i) => ({ value,
                plicity: [0, 2, 3, 4].includes(i) ? 'implicit' as const : 'explicit' as const })))));
        const oldNormality = kernelFree('legacy_normality', p), oldRow = kernelFree('legacy_row', p);
        for (const [reference, type] of [[oldNormality, oldNormalityType], [oldRow, oldRowType]] as const) {
            environment = environment.extend({ name: reference.name, type,
                mode: binderMode('explicit', 'functorial'), provenance: p });
        }
        const checker = createCoreProofChecker(environment);
        checker.check(checker.rootContext, oldNormality, oldNormalityType);
        checker.check(checker.rootContext, oldRow, oldRowType);
        assert.throws(() => checker.check(checker.rootContext,
            algebraFormalFreydModelConnectingObservationTerm({ ...v.values, N: oldNormality }), v.target));
        assert.throws(() => checker.check(checker.rootContext,
            algebraFormalFreydModelConnectingObservationTerm({ ...v.values, x0: oldRow }), v.target));
    });

    it('rejects missing normality, foreign fields and raw-zero evidence in place of short exactness', () => {
        const v = fixture(), checker = createCoreProofChecker(v.environment);
        const { N: _N, ...missing } = v.values;
        assert.throws(() => algebraFormalFreydModelConnectingObservationTerm(missing), /every exact/iu);
        assert.throws(() => algebraFormalFreydModelConnectingObservationTerm({ ...v.values, foreign: v.values.R }), /foreign/iu);
        assert.throws(() => checker.check(checker.rootContext,
            algebraFormalFreydModelConnectingObservationTerm({ ...v.values, N: v.values.cm }), v.target));
        assert.throws(() => checker.check(checker.rootContext,
            algebraFormalFreydModelConnectingObservationTerm({ ...v.values, x0: v.values.c0 }), v.target));
    });

    it('checks the exact connecting signatures and conditional call in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_MODEL_CONNECTING_SIGNATURES !== '1'
    }, () => {
        const v = fixture();
        const assertions: { label: string; term: KernelExpression; type: KernelExpression;
            span: ReturnType<typeof sourceSpan> }[] = Object.keys(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS).map(name => ({
            label: name, term: kernelFree(name, p), type: v.environment.lookup(name)!.type,
            span: sourceSpan('generated/model-connecting-signatures.ts', 1, 1)
        }));
        assertions.push({ label: 'conditional_connecting', term: v.term, type: v.target,
            span: sourceSpan('generated/model-connecting-signatures.ts', 2, 1) });
        const serialized = serializeCoreLfKernelProbe({ environment: v.environment, externalFreeReferences: {
            ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
            ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
            ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
            ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
            ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS,
            ...FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS
        }, assertions });
        const imports = 'require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_native_connecting;';
        // Bare LF names insert leading implicits. These three assertions
        // intentionally inspect the full unsaturated external signature.
        let source = serialized.source.replace('require open emdash.emdash3_2;', imports);
        for (const name of Object.values(FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS)) {
            const assertion = 'assert ⊢ ' + name + ' :';
            assert.ok(source.includes(assertion), 'Expected the unsaturated signature assertion for ' + name);
            source = source.replace(assertion, 'assert ⊢ @' + name + ' :');
        }
        const checked = checkLambdapiProbe({ ...serialized,
            source
        }, { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics.slice(-8000));
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-12000));
    });
});
