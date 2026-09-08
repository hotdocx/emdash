/** Selected-provider binding tests; samples do not prove an all-test law. */

import assert from 'node:assert/strict';
import { describe, it, mock } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialOne, algebraPolynomialRing, algebraPolynomialVariable } from '../src/v3_2/algebra_polynomial';
import { algebraPolynomialFreeModule, algebraPolynomialModuleVector } from '../src/v3_2/algebra_polynomial_module';
import { algebraPolynomialModuleMap, algebraPolynomialModuleMapCompose, algebraPolynomialModuleMapZero } from '../src/v3_2/algebra_polynomial_presentation';
import { algebraPolynomialModuleMapEquals } from '../src/v3_2/algebra_polynomial_presentation_morphism';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import {
    ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE,
    AlgebraSelectedWeakPullbackProviderError,
    assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent,
    createAlgebraPolynomialFreydKernelChoiceProviders,
    createAlgebraPolynomialSelectedWeakPullbackProvider
} from '../src/v3_2/algebra_polynomial_selected_weak_pullback_provider';

const whole = algebraPolynomialFreydBoundedLongExactHomology(polynomialFreydHomologyFixture('two'));
const homology = whole.interior[2].exactness.homology;
const kernel = homology.cycles;
const ring = whole.sequence.ring;
const selected = createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'test-selected-cycles', ring, kernel });
const providerError = (code: AlgebraSelectedWeakPullbackProviderError['code']) => (error: unknown) =>
    error instanceof AlgebraSelectedWeakPullbackProviderError && error.code === code;

describe('v3.2 selected weak-pullback provider handles', () => {
    it('retains an interior homology cycle kernel and both literal choices', () => {
        assert.equal(selected.kernel, homology.cycles);
        assert.equal(selected.first.selected, kernel.firstWeakPullback);
        assert.equal(selected.second.selected, kernel.secondWeakPullback);
        assert.equal(kernel.object, homology.cycleObject);
        assert.equal(kernel.object.ambient, selected.first.selected.object);
        assert.equal(kernel.object.relations.generators.length, selected.second.selected.object.rank);
        assert.equal(kernel.embedding, homology.cycleEmbedding);
        selected.assertCurrent();
        assert.ok(Object.isFrozen(selected));
        assert.ok(Object.isFrozen(selected.first));
        assert.equal(ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE.reselectsWeakKernels, false);
        assert.equal(ALGEBRA_POLYNOMIAL_SELECTED_WEAK_PULLBACK_PROVIDER_PROFILE.resourceFailuresAreNegativeMathematics, false);
    });

    it('factors fresh combined and pair tests without selecting another kernel or pullback', () => {
        const forbid = () => { throw new Error('A selected provider must not reselect a kernel or weak pullback'); };
        const spies = [mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            for (const provider of [selected.first, selected.second]) {
                const choice = provider.selected;
                const source = algebraPolynomialFreeModule(ring, 3);
                const seed = algebraPolynomialModuleMap(source, choice.object, Array.from({ length: 3 }, (_, column) =>
                    algebraPolynomialModuleVector(choice.object, Array.from({ length: choice.object.rank }, (_, row) =>
                        (row + column) % 2 === 0 ? algebraPolynomialVariable(ring, 0) : algebraPolynomialOne(ring)))));
                const test = algebraPolynomialModuleMapCompose(choice.combinedMorphism, seed);
                const combined = provider.factorCombined(test);
                assert.equal(combined.weakKernel, choice.weakKernel);
                assert.equal(combined.test, test);
                assert.equal(combined.lift.target, choice.object);
                assert.ok(algebraPolynomialModuleMapEquals(combined.reconstruction, test));
                const left = algebraPolynomialModuleMapCompose(choice.projectionLeft, seed);
                const right = algebraPolynomialModuleMapCompose(choice.projectionRight, seed);
                const pair = provider.factorPair(left, right);
                assert.equal(pair.weakPullback, choice);
                assert.equal(pair.testLeft, left);
                assert.equal(pair.testRight, right);
                assert.ok(algebraPolynomialModuleMapEquals(pair.reconstructionLeft, left));
                assert.ok(algebraPolynomialModuleMapEquals(pair.reconstructionRight, right));
                const empty = algebraPolynomialModuleMapZero(algebraPolynomialFreeModule(ring, 0), choice.biproduct.object);
                assert.equal(provider.factorCombined(empty).lift.source.rank, 0);
            }
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally {
            spies.forEach(spy => spy.mock.restore());
        }
    });

    it('rejects a foreign ring, choice, forged handle, and changed literal rank or projection', () => {
        const choice = selected.first.selected;
        assert.throws(() => createAlgebraPolynomialSelectedWeakPullbackProvider({ id: 'foreign-ring',
            ring: algebraPolynomialRing(RATIONAL_DOMAIN, ['other'], 'lex'), selected: choice }), providerError('FOREIGN_RING'));
        assert.throws(() => assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent(selected.first, selected.second.selected),
            providerError('FOREIGN_CHOICE'));
        assert.throws(() => assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent({ ...selected.first }), providerError('UNKNOWN_PROVIDER'));
        assert.throws(() => createAlgebraPolynomialSelectedWeakPullbackProvider({ id: 'wrong-rank', ring,
            selected: { ...choice, object: { ...choice.object, rank: choice.object.rank + 1 } } }), providerError('INVALID_SELECTION'));
        assert.throws(() => createAlgebraPolynomialSelectedWeakPullbackProvider({ id: 'wrong-projection', ring,
            selected: { ...choice, projectionLeft: choice.projectionRight } }),
        (error: unknown) => error instanceof Error);
    });

    it('rejects a changed selected snapshot before invoking the factor algorithm', () => {
        const mutable = { ...selected.first.selected };
        const provider = createAlgebraPolynomialSelectedWeakPullbackProvider({ id: 'mutable-selected-snapshot', ring, selected: mutable });
        mutable.projectionLeft = { ...mutable.projectionLeft };
        assert.throws(() => assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent(provider), providerError('STALE_PROVIDER'));
        assert.throws(() => provider.factorCombined(mutable.combinedMorphism), providerError('STALE_PROVIDER'));
        const changedKernel = { ...kernel, secondWeakPullback: selected.first.selected };
        assert.throws(() => createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'foreign-stage', ring, kernel: changedKernel }),
            providerError('FOREIGN_CHOICE'));
    });

    it('propagates resource failures instead of reporting mathematical nonexistence', () => {
        assert.throws(() => selected.first.factorCombined(selected.first.selected.combinedMorphism, { maximumReductionSteps: 0 }),
            (error: unknown) => error instanceof weakKernel.AlgebraPolynomialWeakKernelError && error.code === 'INVALID_FACTORIZATION_LIMIT');
    });
});
