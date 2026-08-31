/** Focused QCC-SQUARE-4A structural and evaluated d-squared tests. */

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
    algebraPresentedAlgebraModuleElementZero
} from '../src/v3_2/algebra_presented_module';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import { algebraAffineQuasiCoherentCechDiagram } from
    '../src/v3_2/algebra_quasicoherent_cech';
import {
    algebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainFromGlobalElement,
    algebraAffineQuasiCoherentCochainIsZero
} from '../src/v3_2/algebra_quasicoherent_cochain';
import {
    ALGEBRA_QUASICOHERENT_DIFFERENTIAL_SQUARE_PROFILE,
    AlgebraQuasiCoherentDifferentialSquareError,
    algebraAffineQuasiCoherentDifferentialSquare,
    serializeAlgebraAffineQuasiCoherentDifferentialSquare
} from '../src/v3_2/algebra_quasicoherent_differential_square';

const squareError = (
    code: AlgebraQuasiCoherentDifferentialSquareError['code']
) => (error: unknown) => {
    assert.ok(error instanceof AlgebraQuasiCoherentDifferentialSquareError);
    assert.equal(error.code, code);
    return true;
};

const fixture = (arity: 2 | 3 = 3) => {
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

describe('v3.2 structural and evaluated Cech differential square', () => {
    it('pairs every ternary repeated face with opposite total signs', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const global = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const input = algebraAffineQuasiCoherentCochain(degree, [
            global.components[0],
            algebraPresentedAlgebraModuleElementZero(
                degree.data.simplices[1].value.module
            ),
            global.components[2]
        ]);
        const square = algebraAffineQuasiCoherentDifferentialSquare(input);
        assert.equal(square.cancellations.length, 3);
        assert.deepEqual(square.cancellations.map(cancellation => ({
            removed: cancellation.comparison.removedPositions,
            first: cancellation.firstSign,
            second: cancellation.secondSign
        })), [
            { removed: [0, 1], first: 1, second: -1 },
            { removed: [0, 2], first: -1, second: 1 },
            { removed: [1, 2], first: 1, second: -1 }
        ]);
        assert.equal(square.cancellations.every(cancellation =>
            cancellation.unsignedImagesEqual &&
            cancellation.signsOpposite &&
            cancellation.cancels
        ), true);
    });

    it('computes d1(d0(s)) as the canonical zero cochain', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const input = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const square = algebraAffineQuasiCoherentDifferentialSquare(input);
        assert.equal(square.outputIsZero, true);
        assert.equal(square.holds, true);
        assert.equal(algebraAffineQuasiCoherentCochainIsZero(
            square.second.output
        ), true);
        assert.equal(square.first.sourceDegree.degree, 0);
        assert.equal(square.first.targetDegree.degree, 1);
        assert.equal(square.second.targetDegree.degree, 2);
    });

    it('serializes all paths, signs, images, and cancellations deterministically',
        () => {
            const value = fixture();
            const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
            const square = algebraAffineQuasiCoherentDifferentialSquare(
                algebraAffineQuasiCoherentCochainFromGlobalElement(
                    degree,
                    value.globalBasis
                )
            );
            const first = serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                square
            );
            const second = serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                square
            );
            assert.equal(first, second);
            assert.match(first, /"removedPositions":\[0,1\]/u);
            assert.match(first, /"firstSign":1,"secondSign":-1/u);
            assert.equal(
                ALGEBRA_QUASICOHERENT_DIFFERENTIAL_SQUARE_PROFILE.proofClaim,
                false
            );
        });

    it('rejects a binary diagram without a second successor degree', () => {
        const value = fixture(2);
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const input = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        assert.throws(
            () => algebraAffineQuasiCoherentDifferentialSquare(input),
            squareError('NO_SECOND_SUCCESSOR_DEGREE')
        );
    });

    it('rejects incomplete structural cancellation coverage', () => {
        const value = fixture();
        const forgedDiagram = Object.freeze({
            ...value.diagram,
            comparisons: Object.freeze([])
        });
        const degree = algebraAffineQuasiCoherentCochainDegree(forgedDiagram, 0);
        const input = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        assert.throws(
            () => algebraAffineQuasiCoherentDifferentialSquare(input),
            squareError('CANCELLATION_COUNT_MISMATCH')
        );
    });
});
