/** Focused QCC-DIFFERENTIAL-3A whole alternating differential tests. */

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
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementZero
} from '../src/v3_2/algebra_presented_module';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import { algebraAffineQuasiCoherentCechDiagram } from
    '../src/v3_2/algebra_quasicoherent_cech';
import {
    algebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainEquals,
    algebraAffineQuasiCoherentCochainFromGlobalElement,
    algebraAffineQuasiCoherentCochainIsZero,
    algebraAffineQuasiCoherentCochainZero
} from '../src/v3_2/algebra_quasicoherent_cochain';
import {
    ALGEBRA_QUASICOHERENT_DIFFERENTIAL_PROFILE,
    AlgebraQuasiCoherentDifferentialError,
    algebraAffineQuasiCoherentDifferential,
    algebraAffineQuasiCoherentDifferentialAdditivity,
    algebraAffineQuasiCoherentDifferentialOfNegate,
    algebraAffineQuasiCoherentDifferentialOfZeroIsZero,
    serializeAlgebraAffineQuasiCoherentDifferential
} from '../src/v3_2/algebra_quasicoherent_differential';

const differentialError = (
    code: AlgebraQuasiCoherentDifferentialError['code']
) => (error: unknown) => {
    assert.ok(error instanceof AlgebraQuasiCoherentDifferentialError);
    assert.equal(error.code, code);
    return true;
};

const fixture = (arity: 2 | 3 = 2) => {
    const variables = arity === 2 ? ['x'] : ['x', 'y'];
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const generators = variables.map((_, index) =>
        algebraPolynomialVariable(ring, index)
    );
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const scheme = algebraAffineScheme(algebra);
    const free = algebraPresentedAlgebraFreeModule(algebra, 1);
    const module = algebraPresentedAlgebraModule(free, []);
    const globalBasis = algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
    );
    const presentation = algebraAffineQuasiCoherentPresentation(scheme, module);
    const coverPolynomials = arity === 2
        ? [
            generators[0],
            algebraPolynomialSubtract(algebraPolynomialOne(ring), generators[0])
        ]
        : [
            generators[0],
            generators[1],
            algebraPolynomialSubtract(
                algebraPolynomialSubtract(
                    algebraPolynomialOne(ring),
                    generators[0]
                ),
                generators[1]
            )
        ];
    const cover = algebraAffineCover(
        scheme,
        coverPolynomials.map(polynomial =>
            algebraQuotientElement(quotient, polynomial)
        ),
        arity - 1
    );
    const diagram = algebraAffineQuasiCoherentCechDiagram(presentation, cover);
    return {
        ring,
        generators,
        quotient,
        algebra,
        scheme,
        free,
        module,
        globalBasis,
        presentation,
        cover,
        diagram
    };
};

describe('v3.2 whole alternating quasi-coherent Cech differential', () => {
    it('uses the retained binary orientation res(a1) minus res(a0)', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const diagonal = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const asymmetric = algebraAffineQuasiCoherentCochain(degree, [
            algebraPresentedAlgebraModuleElementZero(
                degree.data.simplices[0].value.module
            ),
            diagonal.components[1]
        ]);
        const differential = algebraAffineQuasiCoherentDifferential(asymmetric);
        assert.equal(differential.targets.length, 1);
        assert.deepEqual(
            differential.targets[0].contributions.map(value => ({
                source: value.face.domain.simplex.indices,
                sourcePosition: value.sourcePosition,
                sign: value.sign
            })),
            [
                { source: [1], sourcePosition: 1, sign: 1 },
                { source: [0], sourcePosition: 0, sign: -1 }
            ]
        );
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            differential.output.components[0],
            differential.targets[0].contributions[0].image
        ));
        assert.equal(algebraAffineQuasiCoherentCochainIsZero(
            differential.output
        ), false);
    });

    it('annihilates the diagonal cochain induced by a global section', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const diagonal = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const differential = algebraAffineQuasiCoherentDifferential(diagonal);
        assert.equal(algebraAffineQuasiCoherentCochainIsZero(
            differential.output
        ), true);
        assert.equal(differential.targets[0].contributions.length, 2);
    });

    it('computes additivity, zero, and negation through module arithmetic', () => {
        const value = fixture(3);
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const global = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const zero = algebraAffineQuasiCoherentCochainZero(degree);
        const additivity = algebraAffineQuasiCoherentDifferentialAdditivity(
            global,
            zero
        );
        assert.equal(additivity.holds, true);
        assert.equal(algebraAffineQuasiCoherentCochainEquals(
            additivity.sum.output,
            additivity.outputSum
        ), true);
        assert.equal(algebraAffineQuasiCoherentDifferentialOfZeroIsZero(degree),
            true);
        assert.equal(algebraAffineQuasiCoherentDifferentialOfNegate(global), true);
    });

    it('retains every ternary target contribution and serializes deterministically',
        () => {
            const value = fixture(3);
            const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
            const global = algebraAffineQuasiCoherentCochainFromGlobalElement(
                degree,
                value.globalBasis
            );
            const differential = algebraAffineQuasiCoherentDifferential(global);
            assert.deepEqual(
                differential.targets.map(target =>
                    target.contributions.map(value => value.sign)
                ),
                [[1, -1], [1, -1], [1, -1]]
            );
            assert.equal(
                serializeAlgebraAffineQuasiCoherentDifferential(differential),
                serializeAlgebraAffineQuasiCoherentDifferential(differential)
            );
            assert.equal(
                ALGEBRA_QUASICOHERENT_DIFFERENTIAL_PROFILE.wholeContributions,
                true
            );
        });

    it('does not invent a differential beyond the retained top degree', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 1);
        const cochain = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        assert.throws(
            () => algebraAffineQuasiCoherentDifferential(cochain),
            differentialError('NO_SUCCESSOR_DEGREE')
        );
        assert.equal(
            ALGEBRA_QUASICOHERENT_DIFFERENTIAL_PROFILE
                .finalTruncationDifferential,
            false
        );
    });
});
