/** Focused BRIDGE-COVER-3A exact formal-cover Core tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { kernelFree, provenance } from '../src/v3_2/kernel';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { serializeKernelExpression } from '../src/v3_2/lambdapi';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import { algebraPolynomialQuotientRing, algebraQuotientElement } from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import {
    defineAffineFormalCoverRealization
} from '../src/v3_2/algebra_formal_realization';
import {
    AFFINE_FORMAL_RING_BINDINGS,
    defineAffineFormalPolynomialReifier
} from '../src/v3_2/algebra_formal_reifier';
import {
    AFFINE_FORMAL_COVER_BINDINGS,
    ALGEBRA_FORMAL_COVER_PROFILE,
    AlgebraFormalCoverError,
    buildAffineFormalCoverTerms,
    buildAffineFormalFamily
} from '../src/v3_2/algebra_formal_cover';

const because = (detail: string) => provenance('derived', detail);

const coverError = (code: AlgebraFormalCoverError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalCoverError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    const cover = algebraAffineCover(algebraAffineScheme(algebra), [
        algebraQuotientElement(quotient, x),
        algebraQuotientElement(
            quotient,
            algebraPolynomialSubtract(algebraPolynomialOne(ring), x)
        )
    ], 1);
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing: kernelFree('formal_R', because('formal ring')),
        generatorTerms: [kernelFree('formal_x', because('formal x'))],
        coefficientReifier: coefficient => kernelFree(
            `formal_coefficient_${Array.from(new TextEncoder().encode(
                RATIONAL_DOMAIN.text(coefficient)
            )).map(byte => byte.toString(16)).join('')}`,
            because('coefficient')
        ),
        status: 'explicit-data'
    });
    const realization = defineAffineFormalCoverRealization({
        cover,
        algebra: reifier.realization,
        status: 'explicit-data',
        lawTerm: kernelFree('formal_cover_law', because('formal law'))
    });
    return { ring, x, quotient, algebra, cover, reifier, realization };
};

describe('v3.2 exact algebraic Zariski-cover Core construction', () => {
    it('builds the existing formal cover constructor without new Core owners', () => {
        const terms = buildAffineFormalCoverTerms(fixture().realization);
        const core = serializeCoreExpression(terms.cover);
        assert.match(core, /bridge_comm_ring_zariski_cover_intro/u);
        assert.match(core, /bridge_comm_ring_unimodular_intro/u);
        assert.match(core, /bridge_finite_family_cons/u);
        assert.equal(
            serializeCoreExpression(terms.generators)
                .match(/bridge_finite_family_cons/gu)?.length,
            2
        );
        assert.equal(
            serializeCoreExpression(terms.coefficients)
                .match(/bridge_finite_family_cons/gu)?.length,
            2
        );
        assert.equal(ALGEBRA_FORMAL_COVER_PROFILE.addsCoreOwner, false);
        assert.ok(Object.isFrozen(terms));
    });

    it('emits exact active Lambdapi owner names and preserves order', () => {
        const terms = buildAffineFormalCoverTerms(fixture().realization);
        const lambdapi = serializeKernelExpression(terms.cover, {
            externalFreeReferences: {
                ...AFFINE_FORMAL_RING_BINDINGS,
                ...AFFINE_FORMAL_COVER_BINDINGS
            }
        });
        assert.match(lambdapi, /@comm_ring_zariski_cover_intro/u);
        assert.match(lambdapi, /@comm_ring_unimodular_intro/u);
        assert.match(lambdapi, /@finite_family_cons/u);
        assert.ok(lambdapi.indexOf('formal_x') < lambdapi.indexOf('formal_cover_law'));
        assert.equal(
            lambdapi,
            serializeKernelExpression(terms.cover, {
                externalFreeReferences: {
                    ...AFFINE_FORMAL_RING_BINDINGS,
                    ...AFFINE_FORMAL_COVER_BINDINGS
                }
            })
        );
    });

    it('constructs empty and three-element family lengths structurally', () => {
        const carrier = kernelFree('formal_carrier', because('carrier'));
        const empty = buildAffineFormalFamily(carrier, []);
        const triple = buildAffineFormalFamily(carrier, [
            kernelFree('a', because('a')),
            kernelFree('b', because('b')),
            kernelFree('c', because('c'))
        ]);
        assert.match(serializeCoreExpression(empty.length), /bridge_nat_zero/u);
        assert.equal(
            serializeCoreExpression(triple.length).match(/bridge_nat_succ/gu)?.length,
            3
        );
        assert.equal(
            serializeCoreExpression(triple.family).match(/bridge_finite_family_cons/gu)
                ?.length,
            3
        );
    });

    it('rejects trusted realizations without a formal law', () => {
        const value = fixture();
        const trustedAlgebra = defineAffineFormalPolynomialReifier({
            algebra: value.algebra,
            formalRing: value.reifier.formalRing,
            generatorTerms: value.reifier.generatorTerms,
            coefficientReifier: coefficient => kernelFree(
                `trusted_coefficient_${RATIONAL_DOMAIN.text(coefficient).replace(/\W/gu, '')}`,
                because('trusted coefficient')
            ),
            status: 'trusted-computation'
        });
        const trusted = defineAffineFormalCoverRealization({
            cover: value.cover,
            algebra: trustedAlgebra.realization,
            status: 'trusted-computation'
        });
        assert.throws(
            () => buildAffineFormalCoverTerms(trusted),
            coverError('FORMAL_COVER_UNAVAILABLE')
        );
    });
});
