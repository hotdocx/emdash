/** Focused BRIDGE-REIFY-2A polynomial/quotient Core reification tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { kernelFree, provenance } from '../src/v3_2/kernel';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { serializeKernelExpression } from '../src/v3_2/lambdapi';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import { defineAffineFormalCoverRealization } from '../src/v3_2/algebra_formal_realization';
import {
    AFFINE_FORMAL_RING_BINDINGS,
    ALGEBRA_FORMAL_REIFIER_PROFILE,
    AlgebraFormalReifierError,
    defineAffineFormalPolynomialReifier
} from '../src/v3_2/algebra_formal_reifier';

const because = (detail: string) => provenance('derived', detail);

const reifierError = (code: AlgebraFormalReifierError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalReifierError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = (withRelation = true) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(
        ring,
        withRelation ? [algebraPolynomialPower(x, 2n)] : []
    ));
    const algebra = algebraPresentedAlgebra(quotient);
    const formalRing = kernelFree('formal_R', because('formal ring'));
    const formalX = kernelFree('formal_x', because('formal x'));
    const coefficientReifier = (coefficient: typeof RATIONAL_DOMAIN.zero) =>
        kernelFree(
            `formal_coefficient_${Array.from(new TextEncoder().encode(
                RATIONAL_DOMAIN.text(coefficient)
            )).map(byte => byte.toString(16)).join('')}`,
            because('coefficient')
        );
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX],
        coefficientReifier,
        status: 'explicit-data'
    });
    return { ring, x, quotient, algebra, formalRing, formalX, reifier };
};

describe('v3.2 canonical polynomial and quotient reification', () => {
    it('emits identical Core for equivalent quotient representatives', () => {
        const value = fixture();
        const first = algebraQuotientElement(value.quotient, value.x);
        const second = algebraQuotientElement(
            value.quotient,
            algebraPolynomialAdd(value.x, algebraPolynomialPower(value.x, 2n))
        );
        assert.equal(
            serializeCoreExpression(value.reifier.reifyElement(first)),
            serializeCoreExpression(value.reifier.reifyElement(second))
        );
        assert.equal(
            serializeCoreExpression(value.reifier.realization.reifyElement(first)),
            serializeCoreExpression(value.reifier.reifyElement(first))
        );
    });

    it('uses reviewed external ring-operation names only at emission', () => {
        const value = fixture(false);
        const element = algebraQuotientElement(
            value.quotient,
            algebraPolynomialAdd(value.x, algebraPolynomialPower(value.x, 2n))
        );
        const core = value.reifier.reifyElement(element);
        const portable = serializeCoreExpression(core);
        const lambdapi = serializeKernelExpression(core, {
            externalFreeReferences: AFFINE_FORMAL_RING_BINDINGS
        });
        assert.match(portable, /bridge_comm_ring_add/u);
        assert.match(portable, /bridge_comm_ring_mul/u);
        assert.doesNotMatch(portable, /\(free "comm_ring_add"\)/u);
        assert.match(lambdapi, /comm_ring_add/u);
        assert.match(lambdapi, /comm_ring_mul/u);
        assert.equal(ALGEBRA_FORMAL_REIFIER_PROFILE.addsCoreOwner, false);
    });

    it('constructs a cover realization through the canonical reifier', () => {
        const value = fixture(false);
        const cover = algebraAffineCover(
            algebraAffineScheme(value.algebra),
            [
                algebraQuotientElement(value.quotient, value.x),
                algebraQuotientElement(
                    value.quotient,
                    algebraPolynomialSubtract(
                        algebraPolynomialOne(value.ring),
                        value.x
                    )
                )
            ],
            1
        );
        const formal = defineAffineFormalCoverRealization({
            cover,
            algebra: value.reifier.realization,
            status: 'explicit-data',
            lawTerm: kernelFree('formal_cover_law', because('cover law'))
        });
        assert.equal(formal.generatorTerms.length, cover.elements.length);
    });

    it('rejects generator arity and exponent overflow', () => {
        const value = fixture(false);
        assert.throws(
            () => defineAffineFormalPolynomialReifier({
                algebra: value.algebra,
                formalRing: value.formalRing,
                generatorTerms: [],
                coefficientReifier: coefficient => kernelFree(
                    `coefficient_${RATIONAL_DOMAIN.text(coefficient)}`,
                    because('coefficient')
                ),
                status: 'explicit-data'
            }),
            reifierError('GENERATOR_ARITY_MISMATCH')
        );
        const bounded = defineAffineFormalPolynomialReifier({
            algebra: value.algebra,
            formalRing: value.formalRing,
            generatorTerms: [value.formalX],
            coefficientReifier: () => kernelFree('formal_coefficient', because('c')),
            status: 'explicit-data',
            maximumExponent: 2n
        });
        assert.throws(
            () => bounded.reifyElement(algebraQuotientElement(
                value.quotient,
                algebraPolynomialPower(value.x, 3n)
            )),
            reifierError('EXPONENT_LIMIT_EXCEEDED')
        );
    });

    it('rejects nondeterministic coefficients and foreign elements', () => {
        const value = fixture(false);
        let next = 0;
        const unstable = defineAffineFormalPolynomialReifier({
            algebra: value.algebra,
            formalRing: value.formalRing,
            generatorTerms: [value.formalX],
            coefficientReifier: () => kernelFree(`coefficient_${next++}`, because('c')),
            status: 'explicit-data'
        });
        assert.throws(
            () => unstable.reifyElement(algebraQuotientElement(value.quotient, value.x)),
            reifierError('NONDETERMINISTIC_COEFFICIENT')
        );
        const foreign = fixture(false);
        const foreignRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['y'], 'lex');
        const foreignQuotient = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(foreignRing, [])
        );
        assert.throws(
            () => foreign.reifier.reifyElement(algebraQuotientElement(
                foreignQuotient,
                algebraPolynomialVariable(foreignRing, 0)
            ) as never),
            reifierError('FOREIGN_QUOTIENT_ELEMENT')
        );
    });
});
