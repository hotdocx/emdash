/** Focused AFFINE-SCHEMES-2B contravariant affine-scheme tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientOne,
    algebraQuotientZero
} from '../src/v3_2/algebra_quotient';
import {
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapApply
} from '../src/v3_2/algebra_presented_algebra';
import {
    ALGEBRA_AFFINE_SCHEME_PROFILE,
    AlgebraAffineSchemeError,
    algebraAffineMorphism,
    algebraAffineMorphismCompose,
    algebraAffineMorphismEquals,
    algebraAffineMorphismIdentity,
    algebraAffineScheme,
    algebraAffineSchemeComputableCategory,
    algebraAffineSchemeEquals,
    algebraBasicOpenAffineSubscheme,
    algebraClosedAffineSubscheme
} from '../src/v3_2/algebra_affine_scheme';

const schemeError = (code: AlgebraAffineSchemeError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraAffineSchemeError);
        assert.equal(error.code, code);
        return true;
    };

const line = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const generator = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    return { ring, generator, quotient, algebra, scheme: algebraAffineScheme(algebra) };
};

describe('v3.2 affine schemes and contravariant morphisms', () => {
    it('represents Spec(B) to Spec(A) by the coordinate map A to B', () => {
        const a = line('x');
        const b = line('y');
        const coordinateMap = algebraPresentedAlgebraMap(
            a.algebra,
            b.algebra,
            [algebraQuotientElement(
                b.quotient,
                algebraPolynomialPower(b.generator, 2n)
            )]
        );
        const morphism = algebraAffineMorphism(b.scheme, a.scheme, coordinateMap);
        assert.equal(morphism.source, b.scheme);
        assert.equal(morphism.target, a.scheme);
        assert.equal(morphism.coordinateMap.source, a.algebra);
        assert.equal(morphism.coordinateMap.target, b.algebra);
        assert.equal(ALGEBRA_AFFINE_SCHEME_PROFILE.variance,
            'Spec-B-to-Spec-A-is-algebra-map-A-to-B');
    });

    it('reverses algebra-map composition and preserves identities', () => {
        const a = line('x');
        const b = line('y');
        const c = line('z');
        const f = algebraAffineMorphism(
            b.scheme,
            a.scheme,
            algebraPresentedAlgebraMap(a.algebra, b.algebra, [
                algebraQuotientElement(b.quotient, algebraPolynomialPower(b.generator, 2n))
            ])
        );
        const g = algebraAffineMorphism(
            c.scheme,
            b.scheme,
            algebraPresentedAlgebraMap(b.algebra, c.algebra, [
                algebraQuotientElement(c.quotient, c.generator)
            ])
        );
        const composite = algebraAffineMorphismCompose(f, g);
        assert.ok(algebraQuotientEquals(
            composite.coordinateMap.generatorImages[0],
            algebraQuotientElement(c.quotient, algebraPolynomialPower(c.generator, 2n))
        ));
        assert.ok(algebraAffineMorphismEquals(
            algebraAffineMorphismCompose(f, algebraAffineMorphismIdentity(b.scheme)),
            f
        ));
    });

    it('constructs closed subschemes by adjoining ambient equations', () => {
        const ambient = line('x');
        const equation = algebraQuotientElement(
            ambient.quotient,
            algebraPolynomialPower(ambient.generator, 2n)
        );
        const closed = algebraClosedAffineSubscheme(ambient.scheme, [equation]);
        assert.equal(closed.immersion.source, closed.scheme);
        assert.equal(closed.immersion.target, ambient.scheme);
        assert.ok(algebraQuotientEquals(
            algebraPresentedAlgebraMapApply(closed.immersion.coordinateMap, equation),
            algebraQuotientZero(closed.coordinateRing)
        ));
        const unchanged = algebraClosedAffineSubscheme(ambient.scheme, []);
        assert.ok(algebraAffineSchemeEquals(unchanged.scheme, ambient.scheme));
    });

    it('constructs basic-open immersions from localization maps', () => {
        const ambient = line('x');
        const x = algebraQuotientElement(ambient.quotient, ambient.generator);
        const open = algebraBasicOpenAffineSubscheme(ambient.scheme, x);
        assert.equal(open.immersion.source, open.scheme);
        assert.equal(open.immersion.target, ambient.scheme);
        assert.equal(open.chart.localization.inverseEquation, true);
        assert.ok(algebraQuotientEquals(
            algebraPresentedAlgebraMapApply(open.immersion.coordinateMap, x),
            open.chart.localization.elementImage
        ));
    });

    it('instantiates a strict computable category of affine schemes', () => {
        const a = line('x');
        const category = algebraAffineSchemeComputableCategory<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >().category;
        const identity = category.identityMorphism(a.scheme);
        assert.ok(category.equalObjects(category.source(identity), a.scheme));
        assert.ok(category.equalMorphisms(
            category.compose(identity, identity),
            identity
        ));
    });

    it('rejects coordinate maps with covariant or unrelated endpoints', () => {
        const a = line('x');
        const b = line('y');
        const wrong = algebraPresentedAlgebraMap(
            a.algebra,
            b.algebra,
            [algebraQuotientElement(b.quotient, b.generator)]
        );
        assert.throws(
            () => algebraAffineMorphism(a.scheme, b.scheme, wrong),
            schemeError('INVALID_COORDINATE_MAP')
        );
        assert.ok(algebraQuotientEquals(
            algebraQuotientOne(a.quotient),
            algebraQuotientOne(a.quotient)
        ));
    });
});
