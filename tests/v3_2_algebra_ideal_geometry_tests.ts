/** Focused CAS-CONSTRUCTIBLE-8A1 elimination ideal tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraGroebnerBasis,
    algebraIdealMembership,
    algebraPolynomialIdeal
} from '../src/v3_2/algebra_ideal';
import {
    ALGEBRA_IDEAL_GEOMETRY_PROFILE,
    AlgebraIdealGeometryError,
    algebraIdealIntersection,
    algebraIdealProduct,
    algebraIdealRadicalEquivalence,
    algebraIdealRadicalMembership,
    algebraIdealSaturate,
    algebraIdealSum
} from '../src/v3_2/algebra_ideal_geometry';
import {
    algebraPolynomialMultiply,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';

const geometryError = (code: AlgebraIdealGeometryError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraIdealGeometryError);
        assert.equal(error.code, code);
        return true;
    };

const member = (
    polynomial: ReturnType<typeof algebraPolynomialVariable>,
    ideal: ReturnType<typeof algebraPolynomialIdeal>
) => algebraIdealMembership(polynomial, algebraGroebnerBasis(ideal)).member;

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const xIdeal = algebraPolynomialIdeal(ring, [x]);
    const yIdeal = algebraPolynomialIdeal(ring, [y]);
    return { ring, x, y, xIdeal, yIdeal };
};

describe('v3.2 elimination ideal geometry', () => {
    it('constructs ideal sums and products in one ring', () => {
        const { x, y, xIdeal, yIdeal } = fixture();
        const sum = algebraIdealSum(xIdeal, yIdeal);
        const product = algebraIdealProduct(xIdeal, yIdeal);
        const xy = algebraPolynomialMultiply(x, y);
        assert.equal(member(x, sum), true);
        assert.equal(member(y, sum), true);
        assert.equal(member(xy, product), true);
        assert.equal(member(x, product), false);
    });

    it('computes intersections by eliminating one retained variable', () => {
        const { x, y, xIdeal, yIdeal } = fixture();
        const result = algebraIdealIntersection(xIdeal, yIdeal);
        const xy = algebraPolynomialMultiply(x, y);
        assert.equal(member(xy, result.ideal), true);
        assert.equal(member(x, result.ideal), false);
        assert.equal(member(y, result.ideal), false);
        assert.equal(result.extendedRing.variables[0], result.eliminationVariable);
        assert.ok(result.basis.basis.length > 0);
        assert.ok(Object.isFrozen(result));
    });

    it('computes principal saturation through the Rabinowitsch ideal', () => {
        const { ring, x, y } = fixture();
        const xyIdeal = algebraPolynomialIdeal(ring, [
            algebraPolynomialMultiply(x, y)
        ]);
        const saturation = algebraIdealSaturate(xyIdeal, x);
        assert.equal(member(y, saturation.ideal), true);
        assert.equal(member(x, saturation.ideal), false);
        const whole = algebraIdealSaturate(
            algebraPolynomialIdeal(ring, [x]),
            x
        );
        assert.equal(
            member(algebraPolynomialPower(x, 0n), whole.ideal),
            true
        );
        assert.equal(ALGEBRA_IDEAL_GEOMETRY_PROFILE.saturation,
            'rabinowitsch-principal-saturation');
    });

    it('retains positive and negative radical membership computations', () => {
        const { ring, x, y } = fixture();
        const square = algebraPolynomialIdeal(ring, [
            algebraPolynomialPower(x, 2n)
        ]);
        const positive = algebraIdealRadicalMembership(square, x);
        const negative = algebraIdealRadicalMembership(square, y);
        assert.equal(positive.member, true);
        assert.equal(positive.unitMembership.member, true);
        assert.equal(negative.member, false);
        assert.equal(negative.unitMembership.member, false);
        assert.ok(positive.elimination.basis.transformations.length > 0);
    });

    it('decides radical equivalence and rejects foreign rings', () => {
        const { ring, x, y, xIdeal } = fixture();
        const square = algebraPolynomialIdeal(ring, [
            algebraPolynomialPower(x, 2n)
        ]);
        assert.equal(
            algebraIdealRadicalEquivalence(xIdeal, square).equivalent,
            true
        );
        assert.equal(
            algebraIdealRadicalEquivalence(
                xIdeal,
                algebraPolynomialIdeal(ring, [y])
            ).equivalent,
            false
        );
        const foreignRing = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grevlex'
        );
        assert.throws(
            () => algebraIdealIntersection(
                xIdeal,
                algebraPolynomialIdeal(foreignRing, [
                    algebraPolynomialVariable(foreignRing, 0)
                ]) as never
            ),
            geometryError('FOREIGN_IDEAL_RING')
        );
    });
});
