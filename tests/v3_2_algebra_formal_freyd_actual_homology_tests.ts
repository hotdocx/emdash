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
import { createFormalFreydActualHomologyProofEnvironment, FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_actual_homology_signatures';
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
    const chain = algebraFormalFreydChainPairDelegationBundle({ reifier, selected: selected.pair });
    const epi = algebraFormalFreydEpimorphismBlockDelegationBundle({ reifier, selected: point.exactness.epimorphism! });
    const element = affineFormalRingElementType(R);
    const environment = createFormalFreydActualHomologyProofEnvironment([
        { name: R.name, type: affineFormalCommRingType() }, { name: x.name, type: element },
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
        return { whole, point, selected, reifier, prepared, providers, reconstruction, initial, source: epicity.source, result, epic };
    } finally { spies.forEach(spy => spy.mock.restore()); }
};
let value: ReturnType<typeof construct> | undefined;
const consumer = () => value ??= construct();

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

    it('checks the constructed homology and exactness together in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_ACTUAL_HOMOLOGY !== '1'
    }, async () => {
        const v = await consumer();
        let environment = v.source.environment;
        const terms: readonly [string, KernelExpression, KernelExpression][] = [
            ['actual_interior_homology', v.result.term, v.result.type],
            ['actual_interior_exactness', v.result.exactness, v.result.exactnessType]
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
            ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS
        }, assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;') },
        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});
