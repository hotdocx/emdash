/** Focused AFFINE-COVERS-4A affine-cover and Cech-nerve tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientAdd,
    algebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientOne,
    algebraQuotientZero
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra, algebraPresentedAlgebraMapApply } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import {
    ALGEBRA_CECH_PROFILE,
    AlgebraCechError,
    algebraAffineCover
} from '../src/v3_2/algebra_cech';

const cechError = (code: AlgebraCechError['code']) => (error: unknown) => {
    assert.ok(error instanceof AlgebraCechError);
    assert.equal(error.code, code);
    return true;
};

const affine = (variables: readonly string[], unit = false) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(
        ring,
        unit ? [algebraPolynomialOne(ring)] : []
    ));
    const algebra = algebraPresentedAlgebra(quotient);
    return { ring, quotient, algebra, scheme: algebraAffineScheme(algebra) };
};

describe('v3.2 finite affine covers and Cech data', () => {
    it('turns x and 1-x into two charts and their overlap', () => {
        const ambient = affine(['x']);
        const xPolynomial = algebraPolynomialVariable(ambient.ring, 0);
        const x = algebraQuotientElement(ambient.quotient, xPolynomial);
        const oneMinusX = algebraQuotientElement(
            ambient.quotient,
            algebraPolynomialSubtract(algebraPolynomialOne(ambient.ring), xPolynomial)
        );
        const cover = algebraAffineCover(ambient.scheme, [x, oneMinusX], 1);
        assert.equal(cover.unimodular.unimodular, true);
        assert.equal(cover.charts.length, 2);
        assert.deepEqual(cover.simplices.map(value => [value.degree, value.indices]), [
            [0, [0]],
            [0, [1]],
            [1, [0, 1]]
        ]);
        const overlap = cover.simplices.find(value => value.degree === 1)!;
        assert.equal(overlap.faces.length, 2);
        assert.deepEqual(overlap.faces.map(face => face.sign), [1, -1]);
        assert.equal(ALGEBRA_CECH_PROFILE.overlap, 'localization-at-product');
        assert.ok(Object.isFrozen(cover));
        assert.ok(Object.isFrozen(overlap.faces));
    });

    it('retains restriction maps satisfying the face inverse equations', () => {
        const ambient = affine(['x']);
        const xPolynomial = algebraPolynomialVariable(ambient.ring, 0);
        const elements = [
            algebraQuotientElement(ambient.quotient, xPolynomial),
            algebraQuotientElement(
                ambient.quotient,
                algebraPolynomialSubtract(algebraPolynomialOne(ambient.ring), xPolynomial)
            )
        ];
        const cover = algebraAffineCover(ambient.scheme, elements, 1);
        const overlap = cover.simplices.find(value => value.degree === 1)!;
        overlap.faces.forEach(face => {
            const target = cover.simplices.find(value =>
                value.indices.join(',') === face.targetIndices.join(',')
            )!;
            const localizedElement = algebraPresentedAlgebraMapApply(
                face.restrictionMap,
                target.chart.chart.localization.elementImage
            );
            const inverse = face.restrictionMap.generatorImages.at(-1)!;
            assert.ok(algebraQuotientEquals(
                algebraQuotientMultiply(localizedElement, inverse),
                algebraQuotientOne(overlap.chart.chart.coordinateAlgebra.quotient)
            ));
        });
    });

    it('retains unimodular coefficients in the ambient quotient', () => {
        const ambient = affine(['x']);
        const xPolynomial = algebraPolynomialVariable(ambient.ring, 0);
        const elements = [
            algebraQuotientElement(ambient.quotient, xPolynomial),
            algebraQuotientElement(
                ambient.quotient,
                algebraPolynomialSubtract(algebraPolynomialOne(ambient.ring), xPolynomial)
            )
        ];
        const cover = algebraAffineCover(ambient.scheme, elements, 1);
        const combination = elements.reduce(
            (sum, element, index) => algebraQuotientAdd(
                sum,
                algebraQuotientMultiply(cover.elementCoefficients[index], element)
            ),
            algebraQuotientZero(ambient.quotient)
        );
        assert.ok(algebraQuotientEquals(
            combination,
            algebraQuotientOne(ambient.quotient)
        ));
    });

    it('builds the ordered two-skeleton of a three-chart cover', () => {
        const ambient = affine(['x', 'y']);
        const x = algebraPolynomialVariable(ambient.ring, 0);
        const y = algebraPolynomialVariable(ambient.ring, 1);
        const third = algebraPolynomialSubtract(
            algebraPolynomialOne(ambient.ring),
            algebraPolynomialAdd(x, y)
        );
        const cover = algebraAffineCover(ambient.scheme, [x, y, third].map(value =>
            algebraQuotientElement(ambient.quotient, value)
        ), 2);
        assert.deepEqual(cover.cochainDegrees.map(value => value.simplices.length), [
            3,
            3,
            1
        ]);
        assert.equal(cover.simplices.filter(value => value.degree === 1)
            .flatMap(value => value.faces).length, 6);
        assert.equal(cover.simplices.find(value => value.degree === 2)!.faces.length, 3);
    });

    it('rejects noncovers and accepts the empty cover of the zero scheme', () => {
        const ambient = affine(['x']);
        const x = algebraQuotientElement(
            ambient.quotient,
            algebraPolynomialVariable(ambient.ring, 0)
        );
        assert.throws(
            () => algebraAffineCover(ambient.scheme, [x]),
            cechError('NOT_A_COVER')
        );
        const emptyAmbient = affine(['x'], true);
        const emptyCover = algebraAffineCover(emptyAmbient.scheme, []);
        assert.equal(emptyCover.charts.length, 0);
        assert.equal(emptyCover.simplices.length, 0);
        assert.equal(emptyCover.maximumDegree, -1);
        assert.throws(
            () => algebraAffineCover(ambient.scheme, [x], -1),
            cechError('INVALID_MAXIMUM_DEGREE')
        );
    });
});
