import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN, ALGEBRA_CURVE_VIEWPORT,
    algebraPolynomialRing, algebraPolynomialVariable, algebraPolynomialConstant,
    algebraPolynomialPower, algebraPolynomialMultiply, algebraPolynomialSubtract,
    algebraPolynomialIdeal, algebraGroebnerBasis, algebraIdealMembership,
    algebraIdealWitnessSource, checkAlgebraIdealWitness, sampleAlgebraPolynomialCurves,
    AlgebraIdealWitnessInput
} from '../src/v3_2/package_algebra';

function family(parameter: string): AlgebraIdealWitnessInput {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0), y = algebraPolynomialVariable(ring, 1);
    const c = algebraPolynomialConstant(ring, parameter);
    return {
        ideal: algebraPolynomialIdeal(ring, [
            algebraPolynomialSubtract(y, algebraPolynomialPower(x, 2n)),
            algebraPolynomialSubtract(algebraPolynomialMultiply(x, y), c)
        ]),
        polynomial: algebraPolynomialSubtract(algebraPolynomialPower(x, 3n), c)
    };
}

describe('curated computational package entry', () => {
    it('computes and samples a rational family through the public surface without a formal environment', () => {
        for (const parameter of ['1', '8', '1/2', '-1/2', '0']) {
            const input = family(parameter);
            const result = algebraIdealMembership(input.polynomial, algebraGroebnerBasis(input.ideal));
            assert.equal(result.member, true);
            const checked = checkAlgebraIdealWitness(input, {
                source: algebraIdealWitnessSource(input), coefficients: result.coefficients
            });
            const view = sampleAlgebraPolynomialCurves(input, { ...ALGEBRA_CURVE_VIEWPORT, cells: 16 });
            assert.equal(view.source, checked.source);
            assert.equal(view.authority, 'approximate-real-locus-view');
            assert.equal(checked.authority, 'exact-polynomial-arithmetic');
        }
    });

    it('keeps source edits distinct from viewport edits and rejects stale exact results', () => {
        const input = family('1'), changed = family('1/2');
        const result = algebraIdealMembership(input.polynomial, algebraGroebnerBasis(input.ideal));
        const witness = { source: algebraIdealWitnessSource(input), coefficients: result.coefficients };
        assert.throws(() => checkAlgebraIdealWitness(changed, witness), /exact ordered generators/u);
        const original = sampleAlgebraPolynomialCurves(input, { ...ALGEBRA_CURVE_VIEWPORT, cells: 16 });
        const wider = sampleAlgebraPolynomialCurves(input, { ...ALGEBRA_CURVE_VIEWPORT, cells: 16, xMax: 4 });
        assert.equal(original.source, wider.source);
        assert.notDeepEqual(original.curves[0].segments, wider.curves[0].segments);
        assert.notEqual(sampleAlgebraPolynomialCurves(changed).source, original.source);
    });

    it('retains exact computation when the numeric view is unsupported', () => {
        const input = family('1' + '0'.repeat(400));
        const result = algebraIdealMembership(input.polynomial, algebraGroebnerBasis(input.ideal));
        const checked = checkAlgebraIdealWitness(input, {
            source: algebraIdealWitnessSource(input), coefficients: result.coefficients
        });
        assert.equal(checked.source, algebraIdealWitnessSource(input));
        assert.throws(() => sampleAlgebraPolynomialCurves(input), /numerical interpretation/u);
        assert.throws(() => family('0.5'), /canonical|rational/iu);
    });
});
