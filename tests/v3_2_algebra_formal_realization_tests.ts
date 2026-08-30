/** Focused BRIDGE-CONTRACT-1B realization-boundary tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { provenance, kernelFree } from '../src/v3_2/kernel';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientText
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import {
    ALGEBRA_FORMAL_REALIZATION_PROFILE,
    AlgebraFormalRealizationError,
    defineAffineFormalAlgebraRealization,
    defineAffineFormalCoverRealization
} from '../src/v3_2/algebra_formal_realization';

const because = (detail: string) => provenance('derived', detail);

const bridgeError = (code: AlgebraFormalRealizationError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalRealizationError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = (variable = 'x') => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    const scheme = algebraAffineScheme(algebra);
    const elements = [
        algebraQuotientElement(quotient, x),
        algebraQuotientElement(
            quotient,
            algebraPolynomialSubtract(algebraPolynomialOne(ring), x)
        )
    ];
    const cover = algebraAffineCover(scheme, elements, 1);
    const termByText = new Map<string, ReturnType<typeof kernelFree>>();
    [...cover.elements, ...cover.elementCoefficients].forEach((element, index) => {
        const text = algebraQuotientText(element);
        if (!termByText.has(text)) {
            termByText.set(text, kernelFree(`formal_element_${index}`, because(text)));
        }
    });
    const realization = defineAffineFormalAlgebraRealization({
        algebra,
        formalRing: kernelFree('formal_R', because('formal ring')),
        status: 'explicit-data',
        reifyElement: element => termByText.get(algebraQuotientText(element)) ??
            kernelFree('formal_unmapped', because('unmapped'))
    });
    return { ring, x, quotient, algebra, scheme, cover, realization };
};

describe('v3.2 affine computational-to-formal realization contract', () => {
    it('retains an explicit law-bearing binary cover realization', () => {
        const value = fixture();
        const law = kernelFree('formal_cover_law', because('cover law'));
        const formal = defineAffineFormalCoverRealization({
            cover: value.cover,
            algebra: value.realization,
            status: 'explicit-data',
            lawTerm: law
        });
        assert.equal(formal.generatorTerms.length, 2);
        assert.equal(formal.coefficientTerms.length, 2);
        assert.equal(formal.lawTerm, law);
        assert.equal(formal.computationalEquationHolds, true);
        assert.equal(formal.formalCoverAvailable, true);
        assert.equal(ALGEBRA_FORMAL_REALIZATION_PROFILE.trustedProducesFormalLaw,
            false);
        assert.ok(Object.isFrozen(formal));
        assert.ok(Object.isFrozen(formal.generatorTerms));
    });

    it('permits checked status only with an actual formal law term', () => {
        const value = fixture();
        const formal = defineAffineFormalCoverRealization({
            cover: value.cover,
            algebra: value.realization,
            status: 'checked',
            lawTerm: kernelFree('checked_cover_law', because('checked law'))
        });
        assert.equal(formal.status, 'checked');
        assert.equal(formal.formalCoverAvailable, true);
        assert.throws(
            () => defineAffineFormalCoverRealization({
                cover: value.cover,
                algebra: value.realization,
                status: 'checked'
            }),
            bridgeError('MISSING_FORMAL_LAW')
        );
    });

    it('keeps trusted computation as non-formal metadata', () => {
        const value = fixture();
        const trusted = defineAffineFormalCoverRealization({
            cover: value.cover,
            algebra: value.realization,
            status: 'trusted-computation'
        });
        assert.equal(trusted.formalCoverAvailable, false);
        assert.equal(trusted.lawTerm, undefined);
        assert.throws(
            () => defineAffineFormalCoverRealization({
                cover: value.cover,
                algebra: value.realization,
                status: 'trusted-computation',
                lawTerm: kernelFree('forbidden_law', because('forbidden'))
            }),
            bridgeError('TRUSTED_FORMAL_LAW')
        );
    });

    it('rejects foreign cover and element parents', () => {
        const first = fixture('x');
        const second = fixture('y');
        assert.throws(
            () => defineAffineFormalCoverRealization({
                cover: second.cover as never,
                algebra: first.realization,
                status: 'explicit-data',
                lawTerm: kernelFree('law', because('foreign cover'))
            }),
            bridgeError('FOREIGN_AFFINE_COVER')
        );
        assert.throws(
            () => first.realization.reifyElement(second.cover.elements[0] as never),
            bridgeError('FOREIGN_QUOTIENT_ELEMENT')
        );
    });

    it('rejects nondeterministic element reification', () => {
        const value = fixture();
        let next = 0;
        const unstable = defineAffineFormalAlgebraRealization({
            algebra: value.algebra,
            formalRing: kernelFree('formal_R', because('formal ring')),
            status: 'explicit-data',
            reifyElement: () => kernelFree(
                `unstable_${next++}`,
                because('unstable')
            )
        });
        assert.throws(
            () => defineAffineFormalCoverRealization({
                cover: value.cover,
                algebra: unstable,
                status: 'explicit-data',
                lawTerm: kernelFree('law', because('law'))
            }),
            bridgeError('NONDETERMINISTIC_REIFIER')
        );
    });

    it('produces deterministic closed explicit Core terms', () => {
        const value = fixture();
        const first = value.realization.reifyElement(value.cover.elements[0]);
        const second = value.realization.reifyElement(value.cover.elements[0]);
        assert.equal(serializeCoreExpression(first), serializeCoreExpression(second));
        assert.match(serializeCoreExpression(value.realization.formalRing), /formal_R/u);
    });
});
