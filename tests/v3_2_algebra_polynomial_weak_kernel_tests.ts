/** Focused computational weak-kernel and selected-lift tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { INTEGER_DOMAIN, RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleVector,
    algebraPolynomialModuleZero
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapIsZero,
    algebraPolynomialModuleMapZero
} from '../src/v3_2/algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from '../src/v3_2/algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialWeakKernelError,
    algebraPolynomialModuleMapWeakKernel,
    algebraPolynomialWeakKernelFactor
} from '../src/v3_2/algebra_polynomial_weak_kernel';

const weakKernelError = (code: AlgebraPolynomialWeakKernelError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialWeakKernelError);
        assert.equal(error.code, code);
        return true;
    };

describe('v3.2 polynomial finite-free computational weak kernels', () => {
    it('computes a nontrivial weak kernel and factors two test columns', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const negativeOne = algebraPolynomialSubtract(zero, one);
        const source = algebraPolynomialFreeModule(ring, 3);
        const target = algebraPolynomialFreeModule(ring, 1);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [x]),
            algebraPolynomialModuleVector(target, [y]),
            algebraPolynomialModuleVector(target, [algebraPolynomialAdd(x, y)])
        ]);
        const weakKernel = algebraPolynomialModuleMapWeakKernel(map);
        assert.equal(weakKernel.annihilates, true);
        assert.equal(weakKernel.claimsUniqueLifts, false);
        assert.equal(algebraPolynomialModuleMapIsZero(
            algebraPolynomialModuleMapCompose(map, weakKernel.morphism)
        ), true);
        assert.ok(weakKernel.object.rank > 0);

        const testSource = algebraPolynomialFreeModule(ring, 2);
        const test = algebraPolynomialModuleMap(testSource, source, [
            algebraPolynomialModuleVector(source, [
                algebraPolynomialSubtract(zero, y), x, zero
            ]),
            algebraPolynomialModuleVector(source, [negativeOne, negativeOne, one])
        ]);
        const progress: string[] = [];
        const factorization = algebraPolynomialWeakKernelFactor(
            weakKernel,
            test,
            { context: { onProgress: event => progress.push(event.phase) } }
        );
        assert.equal(factorization.reconstructs, true);
        assert.equal(factorization.divisions.length, 2);
        assert.deepEqual(progress, [
            'algebra.polynomial-weak-kernel.factor',
            'algebra.polynomial-weak-kernel.factor'
        ]);
        assert.equal(algebraPolynomialModuleMapEquals(
            algebraPolynomialModuleMapCompose(
                weakKernel.morphism,
                factorization.lift
            ),
            test
        ), true);
        assert.ok(Object.isFrozen(weakKernel));
        assert.ok(Object.isFrozen(factorization));
    });

    it('handles zero, identity, and rank-zero boundaries', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const source = algebraPolynomialFreeModule(ring, 2);
        const target = algebraPolynomialFreeModule(ring, 1);
        const zeroMap = algebraPolynomialModuleMapZero(source, target);
        const zeroWeakKernel = algebraPolynomialModuleMapWeakKernel(zeroMap);
        assert.equal(zeroWeakKernel.object.rank, 2);
        const zeroFactor = algebraPolynomialWeakKernelFactor(
            zeroWeakKernel,
            algebraPolynomialModuleMapIdentity(source)
        );
        assert.equal(zeroFactor.reconstructs, true);

        const identity = algebraPolynomialModuleMapIdentity(source);
        const identityWeakKernel = algebraPolynomialModuleMapWeakKernel(identity);
        assert.equal(identityWeakKernel.object.rank, 0);
        assert.equal(identityWeakKernel.morphism.columns.length, 0);
        const emptyTestSource = algebraPolynomialFreeModule(ring, 0);
        const emptyTest = algebraPolynomialModuleMapZero(emptyTestSource, source);
        const emptyFactor = algebraPolynomialWeakKernelFactor(
            identityWeakKernel,
            emptyTest
        );
        assert.equal(emptyFactor.lift.columns.length, 0);
        assert.equal(emptyFactor.reconstructs, true);
    });

    it('rejects non-annihilated, foreign, and invalid-limit tests', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const source = algebraPolynomialFreeModule(ring, 2);
        const target = algebraPolynomialFreeModule(ring, 1);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [x]),
            algebraPolynomialModuleVector(target, [algebraPolynomialOne(ring)])
        ]);
        const weakKernel = algebraPolynomialModuleMapWeakKernel(map);
        assert.throws(
            () => algebraPolynomialWeakKernelFactor(
                weakKernel,
                algebraPolynomialModuleMapIdentity(source)
            ),
            weakKernelError('NON_ANNIHILATED_TEST')
        );
        const foreignTarget = algebraPolynomialFreeModule(ring, 3);
        assert.throws(
            () => algebraPolynomialWeakKernelFactor(
                weakKernel,
                algebraPolynomialModuleMapZero(source, foreignTarget)
            ),
            weakKernelError('FOREIGN_TEST_MAP')
        );
        assert.throws(
            () => algebraPolynomialWeakKernelFactor(
                weakKernel,
                algebraPolynomialModuleMapZero(target, source),
                { maximumReductionSteps: 0 }
            ),
            weakKernelError('INVALID_FACTORIZATION_LIMIT')
        );
        assert.throws(
            () => algebraPolynomialWeakKernelFactor(
                weakKernel,
                algebraPolynomialModuleMapZero(target, source),
                { context: { cancellation: { requested: () => true } } }
            ),
            weakKernelError('CANCELLED')
        );
    });

    it('inherits the field-only Groebner capability boundary', () => {
        const ring = algebraPolynomialRing(INTEGER_DOMAIN, ['x'], 'lex');
        const module = algebraPolynomialFreeModule(ring, 1);
        const map = algebraPolynomialModuleMap(module, module, [
            algebraPolynomialModuleVector(module, [algebraPolynomialVariable(ring, 0)])
        ]);
        assert.throws(() => algebraPolynomialModuleMapWeakKernel(map));
    });

    it('retains exact zero remainders for selected lifts', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const source = algebraPolynomialFreeModule(ring, 2);
        const target = algebraPolynomialFreeModule(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [algebraPolynomialVariable(ring, 0)]),
            algebraPolynomialModuleVector(target, [zero])
        ]);
        const weakKernel = algebraPolynomialModuleMapWeakKernel(map);
        const testSource = algebraPolynomialFreeModule(ring, 1);
        const test = algebraPolynomialModuleMap(testSource, source, [
            algebraPolynomialModuleVector(source, [zero, algebraPolynomialOne(ring)])
        ]);
        const factorization = algebraPolynomialWeakKernelFactor(
            weakKernel,
            test
        );
        factorization.divisions.forEach(division => assert.ok(
            algebraPolynomialModuleEquals(
                division.remainder,
                algebraPolynomialModuleZero(weakKernel.syzygies.module)
            )
        ));
    });
});
