/** Focused AFFINE-SINGULAR-6A injected and real differential tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialMultiply,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientOne,
    algebraQuotientZero
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra, algebraPresentedAlgebraMap } from '../src/v3_2/algebra_presented_algebra';
import { algebraPrincipalLocalization } from '../src/v3_2/algebra_localization';
import { algebraPresentedTensorProduct } from '../src/v3_2/algebra_tensor';
import {
    ALGEBRA_AFFINE_SINGULAR_PROFILE,
    compareQuotientEqualityWithSingular,
    compareSaturationMembershipWithSingular,
    singularIdealMembershipScript,
    singularSaturationMembershipScript
} from '../src/v3_2/algebra_affine_singular';
import { AlgebraOracleTransport } from '../src/v3_2/algebra_oracle';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';

const transport = (member: boolean): AlgebraOracleTransport => ({
    async execute() {
        return {
            exitCode: 0,
            stdout: `EMDASH_IDEAL_MEMBER:${member ? '1' : '0'}\n`,
            stderr: ''
        };
    }
});

const nilpotentFixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const x2 = algebraPolynomialPower(x, 2n);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, [x2]));
    return { ring, x, x2, quotient };
};

describe('v3.2 real and injected Singular affine comparisons', () => {
    it('retains quotient agreement and disagreement from injected transports', async () => {
        const { x, x2, quotient } = nilpotentFixture();
        const left = algebraQuotientElement(
            quotient,
            algebraPolynomialAdd(x, x2)
        );
        const right = algebraQuotientElement(quotient, x);
        const agreement = await compareQuotientEqualityWithSingular(
            quotient,
            left,
            right,
            transport(true)
        );
        assert.equal(agreement.native, true);
        assert.equal(agreement.singular, true);
        assert.equal(agreement.agrees, true);
        const disagreement = await compareQuotientEqualityWithSingular(
            quotient,
            left,
            right,
            transport(false)
        );
        assert.equal(disagreement.native, true);
        assert.equal(disagreement.singular, false);
        assert.equal(disagreement.agrees, false);
        assert.equal(ALGEBRA_AFFINE_SINGULAR_PROFILE.authority,
            'non-authoritative-differential-comparison');
    });

    it('builds deterministic quotient and saturation scripts', () => {
        const { ring, x, x2 } = nilpotentFixture();
        const ideal = algebraPolynomialIdeal(ring, [x2]);
        assert.equal(
            singularIdealMembershipScript(ideal, x2),
            singularIdealMembershipScript(ideal, x2)
        );
        const saturation = singularSaturationMembershipScript(ideal, x, x);
        assert.match(saturation, /1-emdash_t\*imap\(emdash_r,emdash_f\)/u);
        assert.match(saturation, /EMDASH_IDEAL_MEMBER:1/u);
    });

    it('compares saturation membership through an injected oracle', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const result = await compareSaturationMembershipWithSingular(
            algebraPolynomialIdeal(ring, [algebraPolynomialMultiply(x, y)]),
            x,
            y,
            transport(true)
        );
        assert.equal(result.native, true);
        assert.equal(result.agrees, true);
        assert.equal(result.subject, 'saturation-membership');
    });

    it('runs quotient, saturation, localization, and fiber checks in real Singular', {
        skip: process.env.EMDASH_RUN_SINGULAR_AFFINE_ORACLE !== '1'
    }, async () => {
        const node = createAlgebraOracleNodeTransport();
        const nilpotent = nilpotentFixture();
        const quotient = await compareQuotientEqualityWithSingular(
            nilpotent.quotient,
            algebraQuotientElement(
                nilpotent.quotient,
                algebraPolynomialAdd(nilpotent.x, nilpotent.x2)
            ),
            algebraQuotientElement(nilpotent.quotient, nilpotent.x),
            node
        );
        assert.equal(quotient.agrees, true);

        const xyRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(xyRing, 0);
        const y = algebraPolynomialVariable(xyRing, 1);
        const saturation = await compareSaturationMembershipWithSingular(
            algebraPolynomialIdeal(xyRing, [algebraPolynomialMultiply(x, y)]),
            x,
            y,
            node
        );
        assert.equal(saturation.agrees, true);

        const lineRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['u'], 'lex');
        const u = algebraPolynomialVariable(lineRing, 0);
        const lineQuotient = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(lineRing, [])
        );
        const localization = algebraPrincipalLocalization(
            algebraPresentedAlgebra(lineQuotient),
            algebraQuotientElement(lineQuotient, u)
        );
        const localizationComparison = await compareQuotientEqualityWithSingular(
            localization.algebra.quotient,
            localization.inverseProduct,
            algebraQuotientOne(localization.algebra.quotient),
            node
        );
        assert.equal(localizationComparison.agrees, true);

        const baseRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['t'], 'lex');
        const leftRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['a'], 'lex');
        const rightRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['b'], 'lex');
        const baseQ = algebraPolynomialQuotientRing(algebraPolynomialIdeal(baseRing, []));
        const leftQ = algebraPolynomialQuotientRing(algebraPolynomialIdeal(leftRing, []));
        const rightQ = algebraPolynomialQuotientRing(algebraPolynomialIdeal(rightRing, []));
        const base = algebraPresentedAlgebra(baseQ);
        const left = algebraPresentedAlgebra(leftQ);
        const right = algebraPresentedAlgebra(rightQ);
        const tensor = algebraPresentedTensorProduct(
            base,
            algebraPresentedAlgebraMap(base, left, [
                algebraQuotientElement(leftQ, algebraPolynomialPower(
                    algebraPolynomialVariable(leftRing, 0), 2n
                ))
            ]),
            algebraPresentedAlgebraMap(base, right, [
                algebraQuotientElement(rightQ, algebraPolynomialPower(
                    algebraPolynomialVariable(rightRing, 0), 3n
                ))
            ])
        );
        const relation = algebraPolynomialSubtract(
            algebraPolynomialPower(algebraPolynomialVariable(tensor.polynomialRing, 0), 2n),
            algebraPolynomialPower(algebraPolynomialVariable(tensor.polynomialRing, 1), 3n)
        );
        const fiber = await compareQuotientEqualityWithSingular(
            tensor.algebra.quotient,
            algebraQuotientElement(tensor.algebra.quotient, relation),
            algebraQuotientZero(tensor.algebra.quotient),
            node
        );
        assert.equal(fiber.agrees, true);
    });
});
