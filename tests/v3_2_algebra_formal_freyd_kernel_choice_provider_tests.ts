/** Actual selected cycle choices; universal law trust is not a finite sample proof. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it, mock } from 'node:test';
import { KernelExpression } from '../src/v3_2/kernel';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS, AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN, affineFormalCommRingType, affineFormalRingElementType,
    algebraPolynomialIdeal, algebraPolynomialQuotientRing, algebraPolynomialVariable, algebraPolynomialZero, algebraPresentedAlgebra,
    binderMode, checkLambdapiProbe, createAlgebraFormalAssumptionSource,
    createCoreProofArtifactFingerprint, createCoreProofChecker, defineAffineFormalPolynomialReifier,
    isCoreKind, kernelExpressionEquals, kernelFree, provenance, serializeCoreLfKernelProbe, sourceSpan
} from '../src/v3_2';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { createAlgebraPolynomialFreydKernelChoiceProviders } from '../src/v3_2/algebra_polynomial_selected_weak_pullback_provider';
import {
    FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS,
    createFormalFreydKernelChoiceProviderProofEnvironment
} from '../src/v3_2/algebra_formal_freyd_kernel_choice_provider_signatures';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, createFormalFreydSpineProofEnvironment } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import {
    ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE,
    prepareAlgebraFormalFreydKernelChoiceProviders, trustAlgebraFormalFreydKernelChoiceProviders
} from '../src/v3_2/algebra_formal_freyd_kernel_choice_providers';

const p = provenance('surface', 'actual cycle kernel providers', sourceSpan('tests/selected-kernel-providers.ts', 1, 1));
const fingerprint = (goalId: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + goalId + '.ts', sha256: 'sha256:' + '1'.repeat(64) },
    profileSha256: 'sha256:' + '2'.repeat(64)
});

const fixture = (ideal: 'zero' | 'nonzero' | 'redundant-zero' = 'zero') => {
    const whole = algebraPolynomialFreydBoundedLongExactHomology(polynomialFreydHomologyFixture('two'));
    const homology = whole.interior[2].exactness.homology;
    const ring = whole.sequence.ring;
    const selected = createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'actual-interior-cycles', ring, kernel: homology.cycles });
    const R = kernelFree('selected_provider_R', p);
    const x = kernelFree('selected_provider_x', p);
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const relations = ideal === 'nonzero' ? [algebraPolynomialVariable(ring, 0)] :
        ideal === 'redundant-zero' ? [algebraPolynomialZero(ring), algebraPolynomialZero(ring)] : [];
    const algebra = algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, relations)));
    const reifier = defineAffineFormalPolynomialReifier({ algebra, formalRing: R, generatorTerms: [x],
        coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(key);
            if (!term) {
                term = kernelFree('selected_provider_c_' + [...key].map(c => c.codePointAt(0)!.toString(16)).join('_'), p);
                coefficients.set(key, term);
            }
            return term;
        }, status: 'trusted-computation' });
    const prepared = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier, selected });
    const elementType = affineFormalRingElementType(R);
    const inputs = [{ name: R.name, type: affineFormalCommRingType() }, { name: x.name, type: elementType },
        ...[...coefficients.values()].map(term => ({ name: term.name, type: elementType }))];
    const environment = createFormalFreydKernelChoiceProviderProofEnvironment(inputs);
    const source = createAlgebraFormalAssumptionSource({ moduleId: 'proof.cas.selected-kernel-providers',
        sourceId: 'tests/selected-kernel-providers.assumptions', baseEnvironment: environment });
    return { whole, homology, ring, selected, reifier, prepared, inputs, source };
};

const construct = async () => {
    const value = fixture();
    const decisions: string[] = [];
    const forbid = () => { throw new Error('Formal selected provider binding must not reselect weak kernels or pullbacks'); };
    const spies = [mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
        mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
    try {
        const result = await trustAlgebraFormalFreydKernelChoiceProviders({ artifactId: 'actual-selected-kernel',
            prepared: value.prepared, source: value.source, fingerprint,
            decisionEvidence: id => { decisions.push(id); return 'Explicit trust for the represented native ring: ' + id; } });
        spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        return { ...value, result, decisions };
    } finally { spies.forEach(spy => spy.mock.restore()); }
};
let constructed: ReturnType<typeof construct> | undefined;
const consumer = () => constructed ??= construct();

describe('v3.2 formal selected kernel provider binding', () => {
    it('constructs original choices with separately classified universal provider trust', async () => {
        const value = await consumer();
        const { result } = value;
        assert.equal(result.native, value.homology.cycles);
        assert.equal(result.prepared.selected.first.selected, value.homology.cycles.firstWeakPullback);
        assert.equal(result.prepared.selected.second.selected, value.homology.cycles.secondWeakPullback);
        assert.equal(value.source.entries.length, 0);
        assert.deepEqual(result.source.entries.map(entry => entry.classification),
            ['computed-equation', 'computed-equation', 'trusted-presentation-semantics', 'computed-equation', 'trusted-presentation-semantics']);
        assert.equal(result.bindings.length, 2);
        result.bindings.forEach((binding, index) => {
            assert.equal(result.source.entries[binding.providerIndex].reference, binding.provider);
            assert.equal(result.source.entries[binding.compatibilityIndex].reference, binding.compatibility);
            assert.ok(value.decisions.includes('actual-selected-kernel-' + index + '-provider'));
        });
        const checker = createCoreProofChecker(result.source.environment);
        checker.validateEnvironment();
        checker.check(checker.rootContext, result.term, result.type);
        assert.ok(result.first.factor && result.first.law && result.second.factor && result.second.law);
        assert.equal(ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE.finiteSamplesEstablishUniversality, false);
        assert.equal(ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE.suppliesGlobalWeakKernels, false);
        assert.equal(ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE.claimsFormalExactness, false);
    });

    it('rejects wrong provider evidence, missing signature environments, and forged preparations', async () => {
        const value = await consumer();
        const result = value.result;
        const checker = createCoreProofChecker(result.source.environment);
        const first = result.bindings[0];
        const second = result.bindings[1];
        assert.throws(() => checker.check(checker.rootContext, first.provider,
            result.source.entries[second.providerIndex].declaration.type));
        assert.throws(() => checker.check(checker.rootContext, first.compatibility,
            result.source.entries[first.providerIndex].declaration.type));
        const base = { artifactId: 'invalid-selected-kernel', prepared: value.prepared, source: value.source, fingerprint,
            decisionEvidence: () => { throw new Error('No trust action should occur before validation'); } };
        await assert.rejects(() => trustAlgebraFormalFreydKernelChoiceProviders({ ...base, prepared: { ...value.prepared } }), /issued whole/u);
        const missing = createAlgebraFormalAssumptionSource({ moduleId: value.source.moduleId, sourceId: value.source.sourceId,
            baseEnvironment: createFormalFreydSpineProofEnvironment(value.inputs) });
        await assert.rejects(() => trustAlgebraFormalFreydKernelChoiceProviders({ ...base, source: missing }), /signature/u);
    });

    it('reuses only the exact existing original-morphism law', async () => {
        const value = await consumer();
        const result = await trustAlgebraFormalFreydKernelChoiceProviders({ artifactId: 'reused-selected-kernel',
            prepared: value.prepared, source: value.result.source, fingerprint, decisionEvidence: id => 'Explicit repeated provider trust: ' + id });
        assert.equal(result.morphismLaw, value.result.morphismLaw);
        assert.equal(result.source.entries.length, value.result.source.entries.length + 4);
        assert.ok(kernelExpressionEquals(result.morphism, value.result.morphism));
    });

    it('rejects changed native projections before any proof assumption is adopted', async () => {
        const value = fixture();
        const mutableFirst = { ...value.homology.cycles.firstWeakPullback };
        const mutableKernel = { ...value.homology.cycles, firstWeakPullback: mutableFirst };
        const handles = createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'mutable-actual-kernel', ring: value.ring, kernel: mutableKernel });
        const prepared = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier: value.reifier, selected: handles });
        mutableFirst.projectionLeft = { ...mutableFirst.projectionLeft };
        let decisions = 0;
        await assert.rejects(() => trustAlgebraFormalFreydKernelChoiceProviders({ artifactId: 'stale-selected-kernel', prepared,
            source: value.source, fingerprint, decisionEvidence: () => { decisions++; return 'should not be adopted'; } }), /changed|drift|another/u);
        assert.equal(decisions, 0);
        assert.equal(value.source.entries.length, 0);
    });

    it('rejects nonzero quotient semantics and accepts redundant generators of the zero ideal', async () => {
        assert.throws(() => fixture('nonzero'), /zero quotient ideal/u);
        const redundant = fixture('redundant-zero');
        assert.equal(redundant.reifier.algebra.quotient.ideal.generators.length, 2);
        assert.equal(redundant.reifier.algebra.quotient.basis.basis.length, 0);
        const result = await trustAlgebraFormalFreydKernelChoiceProviders({ artifactId: 'redundant-zero-ideal-providers',
            prepared: redundant.prepared, source: redundant.source, fingerprint,
            decisionEvidence: id => 'Explicit provider semantics over the unchanged polynomial ring: ' + id });
        assert.equal(result.native, redundant.homology.cycles);
        assert.equal(result.source.entries.filter(entry => entry.classification === 'trusted-presentation-semantics').length, 2);
    });

    it('checks the constructed actual choice term against Lambdapi source signatures', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_KERNEL_CHOICE_PROVIDERS !== '1'
    }, async () => {
        const { result } = await consumer();
        const name = 'actual_selected_cycle_choices';
        const environment = result.source.environment.extend({ name, type: result.type, body: result.term,
            transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
        const checker = createCoreProofChecker(environment);
        const assertions: { label: string; term: KernelExpression; type: KernelExpression; span: ReturnType<typeof sourceSpan> }[] = [
            { label: 'actual selected cycle kernel choices', term: kernelFree(name, p), type: result.type,
            span: sourceSpan('generated/selected-cycle-choices.ts', 1, 1) }];
        for (const [index, stage] of [result.first, result.second].entries()) {
            for (const [label, term] of [['whole', stage.whole], ['factor', stage.factor], ['law', stage.law]] as const) {
                assert.ok(term);
                const inferred = checker.infer(checker.rootContext, term);
                if (isCoreKind(inferred.type)) throw new Error('Provider projection unexpectedly has KIND type');
                assertions.push({ label: 'selected provider ' + index + ' ' + label, term, type: inferred.type,
                    span: sourceSpan('generated/selected-cycle-choices.ts', assertions.length + 1, 1) });
            }
        }
        const serialized = serializeCoreLfKernelProbe({ environment,
            externalFreeReferences: { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
                ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS },
            assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choice_providers;') },
        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});
