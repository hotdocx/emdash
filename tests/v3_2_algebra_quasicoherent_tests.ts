/** Focused PAM-QCOH-6A affine quasi-coherent presentation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
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
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import {
    algebraAffineScheme,
    algebraBasicOpenAffineSubscheme
} from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleIsZero,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import {
    ALGEBRA_AFFINE_QUASICOHERENT_PROFILE,
    AlgebraAffineQuasiCoherentError,
    algebraAffineQuasiCoherentBasicOpen,
    algebraAffineQuasiCoherentOnBasicOpen,
    algebraAffineQuasiCoherentPresentation,
    algebraAffineQuasiCoherentPresentationSchema,
    serializeAlgebraAffineQuasiCoherentChart,
    serializeAlgebraAffineQuasiCoherentPresentation
} from '../src/v3_2/algebra_quasicoherent';

const quasicoherentError = (code: AlgebraAffineQuasiCoherentError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraAffineQuasiCoherentError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = (variable = 'x') => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const scheme = algebraAffineScheme(algebra);
    const free = algebraPresentedAlgebraFreeModule(algebra, 1);
    const module = algebraPresentedAlgebraModule(free, [
        algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(quotient, x)
        ])
    ]);
    const presentation = algebraAffineQuasiCoherentPresentation(scheme, module);
    return { ring, x, quotient, algebra, scheme, free, module, presentation };
};

describe('v3.2 affine quasi-coherent module presentations', () => {
    it('derives basic-open values by module base change', () => {
        const value = fixture();
        const atX = algebraAffineQuasiCoherentBasicOpen(
            value.presentation,
            algebraQuotientElement(value.quotient, value.x)
        );
        const atOneMinusX = algebraAffineQuasiCoherentBasicOpen(
            value.presentation,
            algebraQuotientElement(
                value.quotient,
                algebraPolynomialSubtract(
                    algebraPolynomialOne(value.ring),
                    value.x
                )
            )
        );
        assert.equal(algebraPresentedAlgebraModuleIsZero(atX.module), true);
        assert.equal(algebraPresentedAlgebraModuleIsZero(atOneMinusX.module),
            false);
        assert.equal(atX.baseChange.scalarMap,
            atX.chart.chart.localization.canonicalMap);
    });

    it('retains exact cover-chart and product-overlap identities', () => {
        const value = fixture();
        const cover = algebraAffineCover(value.scheme, [
            algebraQuotientElement(value.quotient, value.x),
            algebraQuotientElement(
                value.quotient,
                algebraPolynomialSubtract(
                    algebraPolynomialOne(value.ring),
                    value.x
                )
            )
        ], 1);
        const first = algebraAffineQuasiCoherentOnBasicOpen(
            value.presentation,
            cover.charts[0]
        );
        const overlap = algebraAffineQuasiCoherentOnBasicOpen(
            value.presentation,
            cover.simplices.find(simplex => simplex.degree === 1)!.chart
        );
        assert.equal(first.chart, cover.charts[0]);
        assert.equal(overlap.chart,
            cover.simplices.find(simplex => simplex.degree === 1)!.chart);
        assert.deepEqual(
            overlap.module.freeModule.algebra.quotient.identity,
            overlap.chart.chart.localization.algebra.quotient.identity
        );
    });

    it('roundtrips schemas and deterministic presentation/chart serialization', () => {
        const value = fixture();
        const schema = algebraAffineQuasiCoherentPresentationSchema(
            value.scheme,
            value.module
        );
        const normalized = schema.normalize(value.presentation, 'presentation');
        assert.equal(normalized.module, value.module);
        const chart = algebraAffineQuasiCoherentBasicOpen(
            value.presentation,
            algebraQuotientElement(value.quotient, value.x)
        );
        assert.equal(
            serializeAlgebraAffineQuasiCoherentPresentation(value.presentation),
            serializeAlgebraAffineQuasiCoherentPresentation(value.presentation)
        );
        assert.equal(
            serializeAlgebraAffineQuasiCoherentChart(chart),
            serializeAlgebraAffineQuasiCoherentChart(chart)
        );
        assert.equal(ALGEBRA_AFFINE_QUASICOHERENT_PROFILE.claimsSheafEquivalence,
            false);
        assert.equal(ALGEBRA_AFFINE_QUASICOHERENT_PROFILE
            .claimsDescentEffectiveness, false);
    });

    it('rejects a module or basic-open chart over a foreign affine scheme', () => {
        const first = fixture('x');
        const second = fixture('y');
        assert.throws(
            () => algebraAffineQuasiCoherentPresentation(
                first.scheme,
                second.module as never
            ),
            quasicoherentError('FOREIGN_MODULE_ALGEBRA')
        );
        const foreignChart = algebraBasicOpenAffineSubscheme(
            second.scheme,
            algebraQuotientElement(second.quotient, second.x)
        );
        assert.throws(
            () => algebraAffineQuasiCoherentOnBasicOpen(
                first.presentation,
                foreignChart as never
            ),
            quasicoherentError('FOREIGN_BASIC_OPEN_CHART')
        );
    });
});
