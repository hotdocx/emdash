/** Focused AFFINE-TENSOR-3A tensor-product and fiber-product tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientZero
} from '../src/v3_2/algebra_quotient';
import {
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapEquals,
    algebraPresentedAlgebraMapIdentity
} from '../src/v3_2/algebra_presented_algebra';
import {
    algebraAffineMorphism,
    algebraAffineMorphismEquals,
    algebraAffineScheme
} from '../src/v3_2/algebra_affine_scheme';
import {
    ALGEBRA_TENSOR_PROFILE,
    AlgebraTensorError,
    algebraAffineFiberProduct,
    algebraPresentedTensorFactor,
    algebraPresentedTensorProduct
} from '../src/v3_2/algebra_tensor';

const tensorError = (code: AlgebraTensorError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraTensorError);
        assert.equal(error.code, code);
        return true;
    };

const freeAlgebra = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variable ? [variable] : [], 'lex');
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    return {
        ring,
        quotient,
        algebra: algebraPresentedAlgebra(quotient),
        generator: variable ? algebraPolynomialVariable(ring, 0) : undefined
    };
};

const cuspFixture = () => {
    const base = freeAlgebra('t');
    const left = freeAlgebra('x');
    const right = freeAlgebra('y');
    const leftMap = algebraPresentedAlgebraMap(base.algebra, left.algebra, [
        algebraQuotientElement(left.quotient, algebraPolynomialPower(left.generator!, 2n))
    ]);
    const rightMap = algebraPresentedAlgebraMap(base.algebra, right.algebra, [
        algebraQuotientElement(right.quotient, algebraPolynomialPower(right.generator!, 3n))
    ]);
    return { base, left, right, leftMap, rightMap };
};

describe('v3.2 presented tensor products and affine fiber products', () => {
    it('presents Q[x] tensor_Q[t] Q[y] as x^2 equals y^3', () => {
        const value = cuspFixture();
        const tensor = algebraPresentedTensorProduct(
            value.base.algebra,
            value.leftMap,
            value.rightMap
        );
        assert.deepEqual(tensor.polynomialRing.variables, ['left_x', 'right_y']);
        assert.equal(tensor.compatibility.length, 1);
        assert.equal(tensor.compatibility[0].equal, true);
        const leftX = algebraPolynomialVariable(tensor.polynomialRing, 0);
        const rightY = algebraPolynomialVariable(tensor.polynomialRing, 1);
        const relation = algebraPolynomialSubtract(
            algebraPolynomialPower(leftX, 2n),
            algebraPolynomialPower(rightY, 3n)
        );
        assert.ok(algebraQuotientEquals(
            algebraQuotientElement(tensor.algebra.quotient, relation),
            algebraQuotientZero(tensor.algebra.quotient)
        ));
        assert.equal(ALGEBRA_TENSOR_PROFILE.variableLayout,
            'left-block-then-right-block');
        assert.ok(Object.isFrozen(tensor));
    });

    it('constructs the universal factor from compatible maps', () => {
        const value = cuspFixture();
        const tensor = algebraPresentedTensorProduct(
            value.base.algebra,
            value.leftMap,
            value.rightMap
        );
        const factor = algebraPresentedTensorFactor(
            tensor,
            tensor.leftMap,
            tensor.rightMap
        );
        assert.ok(algebraPresentedAlgebraMapEquals(
            factor.map,
            algebraPresentedAlgebraMapIdentity(tensor.algebra)
        ));
        assert.equal(factor.compatibility.every(item => item.equal), true);
    });

    it('rejects candidate factor maps that disagree on the base', () => {
        const value = cuspFixture();
        const tensor = algebraPresentedTensorProduct(
            value.base.algebra,
            value.leftMap,
            value.rightMap
        );
        const badLeft = algebraPresentedAlgebraMap(
            value.left.algebra,
            tensor.algebra,
            [algebraQuotientZero(tensor.algebra.quotient)]
        );
        assert.throws(
            () => algebraPresentedTensorFactor(tensor, badLeft, tensor.rightMap),
            tensorError('INCOMPATIBLE_TENSOR_MAPS')
        );
    });

    it('constructs affine fiber products with compatible projections', () => {
        const value = cuspFixture();
        const baseScheme = algebraAffineScheme(value.base.algebra);
        const leftScheme = algebraAffineScheme(value.left.algebra);
        const rightScheme = algebraAffineScheme(value.right.algebra);
        const left = algebraAffineMorphism(leftScheme, baseScheme, value.leftMap);
        const right = algebraAffineMorphism(rightScheme, baseScheme, value.rightMap);
        const product = algebraAffineFiberProduct(left, right);
        assert.equal(product.compatible, true);
        assert.ok(algebraAffineMorphismEquals(
            product.leftComposite,
            product.rightComposite
        ));
        assert.equal(product.leftProjection.source, product.scheme);
        assert.equal(product.rightProjection.source, product.scheme);
    });

    it('handles tensor products over the coefficient field and rejects nonparallel maps', () => {
        const base = freeAlgebra('');
        const left = freeAlgebra('x');
        const right = freeAlgebra('y');
        const tensor = algebraPresentedTensorProduct(
            base.algebra,
            algebraPresentedAlgebraMap(base.algebra, left.algebra, []),
            algebraPresentedAlgebraMap(base.algebra, right.algebra, [])
        );
        assert.deepEqual(tensor.polynomialRing.variables, ['left_x', 'right_y']);
        assert.equal(tensor.compatibility.length, 0);
        const otherBase = freeAlgebra('s');
        assert.throws(
            () => algebraAffineFiberProduct(
                algebraAffineMorphism(
                    algebraAffineScheme(left.algebra),
                    algebraAffineScheme(base.algebra),
                    algebraPresentedAlgebraMap(base.algebra, left.algebra, [])
                ),
                algebraAffineMorphism(
                    algebraAffineScheme(right.algebra),
                    algebraAffineScheme(otherBase.algebra),
                    algebraPresentedAlgebraMap(otherBase.algebra, right.algebra, [
                        algebraQuotientElement(right.quotient, right.generator!)
                    ])
                )
            ),
            tensorError('NON_PARALLEL_FIBER_PRODUCT')
        );
    });
});
