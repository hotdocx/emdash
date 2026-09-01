/** Focused polynomial weak pullbacks derived from weak kernels. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapZero
} from '../src/v3_2/algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from '../src/v3_2/algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialWeakPullbackError,
    algebraPolynomialModuleMapWeakPullback,
    algebraPolynomialWeakPullbackFactor
} from '../src/v3_2/algebra_polynomial_weak_pullback';

const weakPullbackError = (code: AlgebraPolynomialWeakPullbackError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialWeakPullbackError);
        assert.equal(error.code, code);
        return true;
    };

describe('v3.2 polynomial computational weak pullbacks', () => {
    it('derives a nontrivial weak pullback and factors a compatible pair', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const leftSource = algebraPolynomialFreeModule(ring, 2);
        const rightSource = algebraPolynomialFreeModule(ring, 1);
        const target = algebraPolynomialFreeModule(ring, 1);
        const left = algebraPolynomialModuleMap(leftSource, target, [
            algebraPolynomialModuleVector(target, [x]),
            algebraPolynomialModuleVector(target, [y])
        ]);
        const right = algebraPolynomialModuleMap(rightSource, target, [
            algebraPolynomialModuleVector(target, [x])
        ]);
        const weakPullback = algebraPolynomialModuleMapWeakPullback(left, right);
        assert.equal(weakPullback.compatible, true);
        assert.equal(weakPullback.claimsUniqueLifts, false);
        assert.equal(algebraPolynomialModuleMapEquals(
            weakPullback.compatibilityLeft,
            weakPullback.compatibilityRight
        ), true);

        const testSource = algebraPolynomialFreeModule(ring, 1);
        const testLeft = algebraPolynomialModuleMap(testSource, leftSource, [
            algebraPolynomialModuleVector(leftSource, [one, zero])
        ]);
        const testRight = algebraPolynomialModuleMap(testSource, rightSource, [
            algebraPolynomialModuleVector(rightSource, [one])
        ]);
        const progress: string[] = [];
        const factor = algebraPolynomialWeakPullbackFactor(
            weakPullback,
            testLeft,
            testRight,
            { context: { onProgress: event => progress.push(event.phase) } }
        );
        assert.equal(factor.reconstructs, true);
        assert.equal(factor.claimsUniqueLift, false);
        assert.deepEqual(progress, ['algebra.polynomial-weak-kernel.factor']);
        assert.equal(algebraPolynomialModuleMapEquals(
            factor.reconstructionLeft,
            testLeft
        ), true);
        assert.equal(algebraPolynomialModuleMapEquals(
            factor.reconstructionRight,
            testRight
        ), true);
        assert.ok(Object.isFrozen(weakPullback));
        assert.ok(Object.isFrozen(factor));
    });

    it('handles identity and zero cospan boundaries', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const module = algebraPolynomialFreeModule(ring, 2);
        const identity = algebraPolynomialModuleMapIdentity(module);
        const identityPullback = algebraPolynomialModuleMapWeakPullback(
            identity,
            identity
        );
        const identityFactor = algebraPolynomialWeakPullbackFactor(
            identityPullback,
            identity,
            identity
        );
        assert.equal(identityFactor.reconstructs, true);

        const target = algebraPolynomialFreeModule(ring, 1);
        const zeroPullback = algebraPolynomialModuleMapWeakPullback(
            algebraPolynomialModuleMapZero(module, target),
            algebraPolynomialModuleMapZero(module, target)
        );
        assert.equal(zeroPullback.object.rank, 4);
        assert.equal(zeroPullback.compatible, true);
    });

    it('rejects malformed cospans and incompatible test pairs', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const source = algebraPolynomialFreeModule(ring, 1);
        const target = algebraPolynomialFreeModule(ring, 1);
        const foreignTarget = algebraPolynomialFreeModule(ring, 2);
        const left = algebraPolynomialModuleMapIdentity(source);
        assert.throws(
            () => algebraPolynomialModuleMapWeakPullback(
                left,
                algebraPolynomialModuleMapZero(source, foreignTarget)
            ),
            weakPullbackError('INVALID_COSPAN')
        );

        const zero = algebraPolynomialModuleMapZero(source, target);
        const weakPullback = algebraPolynomialModuleMapWeakPullback(left, zero);
        assert.throws(
            () => algebraPolynomialWeakPullbackFactor(
                weakPullback,
                algebraPolynomialModuleMapIdentity(source),
                algebraPolynomialModuleMapIdentity(source)
            ),
            weakPullbackError('INCOMPATIBLE_TEST_PAIR')
        );
        const wrongSource = algebraPolynomialFreeModule(ring, 2);
        assert.throws(
            () => algebraPolynomialWeakPullbackFactor(
                weakPullback,
                algebraPolynomialModuleMapIdentity(source),
                algebraPolynomialModuleMapZero(wrongSource, source)
            ),
            weakPullbackError('INVALID_TEST_PAIR')
        );
    });

    it('is deterministic and retains the combined reconstruction', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const source = algebraPolynomialFreeModule(ring, 1);
        const target = algebraPolynomialFreeModule(ring, 1);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [x])
        ]);
        const first = algebraPolynomialModuleMapWeakPullback(map, map);
        const second = algebraPolynomialModuleMapWeakPullback(map, map);
        assert.equal(algebraPolynomialModuleMapEquals(
            first.combinedMorphism,
            second.combinedMorphism
        ), true);
        const factor = algebraPolynomialWeakPullbackFactor(
            first,
            algebraPolynomialModuleMapIdentity(source),
            algebraPolynomialModuleMapIdentity(source)
        );
        assert.equal(algebraPolynomialModuleMapEquals(
            algebraPolynomialModuleMapCompose(
                first.combinedMorphism,
                factor.lift
            ),
            factor.pairedTest
        ), true);
    });
});
