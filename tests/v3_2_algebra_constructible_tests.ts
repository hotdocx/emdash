/** Focused CAS-CONSTRUCTIBLE-8A2 locally closed Boolean tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraGroebnerBasis,
    algebraIdealMembership,
    algebraPolynomialIdeal
} from '../src/v3_2/algebra_ideal';
import {
    ALGEBRA_CONSTRUCTIBLE_PROFILE,
    AlgebraConstructibleError,
    algebraConstructibleComplement,
    algebraConstructibleDifference,
    algebraConstructibleEquivalence,
    algebraConstructibleFull,
    algebraConstructibleIntersection,
    algebraConstructibleSet,
    algebraConstructibleUnion,
    algebraLocallyClosedPiece
} from '../src/v3_2/algebra_constructible';
import {
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';

const constructibleError = (code: AlgebraConstructibleError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraConstructibleError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const one = algebraPolynomialOne(ring);
    const zeroIdeal = algebraPolynomialIdeal(ring, []);
    const xIdeal = algebraPolynomialIdeal(ring, [x]);
    const closedXPiece = algebraLocallyClosedPiece(xIdeal, one);
    const openXPiece = algebraLocallyClosedPiece(zeroIdeal, x);
    const closedX = algebraConstructibleSet(ring, [closedXPiece]);
    const openX = algebraConstructibleSet(ring, [openXPiece]);
    return { ring, x, y, one, zeroIdeal, xIdeal, closedXPiece, openXPiece,
        closedX, openX };
};

describe('v3.2 locally closed constructible sets', () => {
    it('normalizes V(xy) intersect D(x) by principal saturation', () => {
        const { ring, x, y } = fixture();
        const piece = algebraLocallyClosedPiece(
            algebraPolynomialIdeal(ring, [algebraPolynomialMultiply(x, y)]),
            x
        );
        assert.equal(piece.empty, false);
        assert.equal(
            algebraIdealMembership(y, algebraGroebnerBasis(piece.closedIdeal)).member,
            true
        );
        assert.equal(
            algebraIdealMembership(x, algebraGroebnerBasis(piece.closedIdeal)).member,
            false
        );
        assert.equal(ALGEBRA_CONSTRUCTIBLE_PROFILE.piece,
            'saturation-normalized-V-I-intersect-D-f');
        assert.ok(Object.isFrozen(piece));
    });

    it('recognizes empty locally closed pieces through radical membership', () => {
        const { ring, x, xIdeal } = fixture();
        const emptyPiece = algebraLocallyClosedPiece(xIdeal, x);
        const emptySet = algebraConstructibleSet(ring, [emptyPiece]);
        assert.equal(emptyPiece.emptiness.member, true);
        assert.equal(emptyPiece.empty, true);
        assert.equal(emptySet.empty, true);
        assert.equal(emptySet.pieces.length, 0);
    });

    it('computes complements, intersections, unions, and differences', () => {
        const { ring, closedX, openX } = fixture();
        const full = algebraConstructibleFull(ring);
        assert.equal(
            algebraConstructibleEquivalence(
                algebraConstructibleDifference(full, closedX),
                openX
            ).equivalent,
            true
        );
        assert.equal(
            algebraConstructibleEquivalence(
                algebraConstructibleDifference(full, openX),
                closedX
            ).equivalent,
            true
        );
        assert.equal(
            algebraConstructibleIntersection(closedX, openX).empty,
            true
        );
        assert.equal(
            algebraConstructibleEquivalence(
                algebraConstructibleUnion(closedX, openX),
                full
            ).equivalent,
            true
        );
        assert.equal(
            algebraConstructibleEquivalence(
                algebraConstructibleComplement(closedX),
                openX
            ).equivalent,
            true
        );
    });

    it('retains mutual differences and rejects cross-ring unions', () => {
        const { ring, closedX, openX } = fixture();
        const comparison = algebraConstructibleEquivalence(closedX, openX);
        assert.equal(comparison.equivalent, false);
        assert.equal(comparison.leftMinusRight.empty, false);
        assert.equal(comparison.rightMinusLeft.empty, false);
        const foreign = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grevlex'
        );
        assert.throws(
            () => algebraConstructibleUnion(
                closedX,
                algebraConstructibleFull(foreign) as never
            ),
            constructibleError('FOREIGN_RING')
        );
        assert.equal(ring.variables.length, 2);
    });
});
