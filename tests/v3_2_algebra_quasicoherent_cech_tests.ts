/** Focused PAM-CECH-7A varying-ring quasi-coherent Cech tests. */

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
    algebraPresentedAlgebraModuleIsZero,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import { algebraPresentedAlgebraModuleSemilinearMapEquals } from
    '../src/v3_2/algebra_presented_module_map';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import {
    ALGEBRA_QUASICOHERENT_CECH_PROFILE,
    AlgebraQuasiCoherentCechError,
    algebraAffineQuasiCoherentCechDiagram,
    algebraAffineQuasiCoherentCechDiagramSchema,
    serializeAlgebraAffineQuasiCoherentCechDiagram
} from '../src/v3_2/algebra_quasicoherent_cech';

const cechError = (code: AlgebraQuasiCoherentCechError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraQuasiCoherentCechError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = (arity: 2 | 3) => {
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
    const module = algebraPresentedAlgebraModule(
        free,
        generators.map(generator => algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(quotient, generator)
        ]))
    );
    const presentation = algebraAffineQuasiCoherentPresentation(scheme, module);
    const coverElements = arity === 2
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
        coverElements.map(element => algebraQuotientElement(quotient, element)),
        arity - 1
    );
    return {
        ring,
        generators,
        quotient,
        algebra,
        scheme,
        free,
        module,
        presentation,
        cover,
        diagram: algebraAffineQuasiCoherentCechDiagram(presentation, cover)
    };
};

describe('v3.2 varying-ring quasi-coherent Cech diagrams', () => {
    it('retains binary chart/overlap modules, face maps, and signs', () => {
        const value = fixture(2);
        assert.deepEqual(
            value.diagram.simplices.map(simplex => simplex.simplex.indices),
            [[0], [1], [0, 1]]
        );
        assert.deepEqual(
            value.diagram.simplices.map(simplex =>
                algebraPresentedAlgebraModuleIsZero(simplex.value.module)
            ),
            [true, false, true]
        );
        assert.equal(value.diagram.faces.length, 2);
        assert.deepEqual(value.diagram.faces.map(face => face.face.sign), [1, -1]);
        assert.equal(value.diagram.faces.every(face =>
            face.map.relationImages.every(relation =>
                relation.image.representative.components.length === 1
            )
        ), true);
        assert.equal(value.diagram.comparisons.length, 0);
    });

    it('constructs the ternary two-skeleton and all repeated-face comparisons',
        () => {
            const value = fixture(3);
            assert.deepEqual(
                value.diagram.degrees.map(degree => degree.simplices.length),
                [3, 3, 1]
            );
            assert.deepEqual(
                value.diagram.degrees.map(degree => degree.incomingFaces.length),
                [6, 3, 0]
            );
            assert.equal(value.diagram.simplices.length, 7);
            assert.equal(value.diagram.faces.length, 9);
            assert.equal(value.diagram.comparisons.length, 3);
            assert.equal(value.diagram.comparisons.every(comparison =>
                comparison.holds &&
                algebraPresentedAlgebraModuleSemilinearMapEquals(
                    comparison.firstComposite,
                    comparison.secondComposite
                )
            ), true);
            const degreeZero = value.diagram.degrees[0].simplices;
            assert.deepEqual(degreeZero.map(simplex =>
                algebraPresentedAlgebraModuleIsZero(simplex.value.module)
            ), [true, true, false]);
        });

    it('accepts the empty cover of the zero affine scheme uniformly', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const quotient = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(ring, [algebraPolynomialOne(ring)])
        );
        const algebra = algebraPresentedAlgebra(quotient);
        const scheme = algebraAffineScheme(algebra);
        const free = algebraPresentedAlgebraFreeModule(algebra, 1);
        const module = algebraPresentedAlgebraModule(free, []);
        const presentation = algebraAffineQuasiCoherentPresentation(scheme, module);
        const cover = algebraAffineCover(scheme, [], 0);
        const diagram = algebraAffineQuasiCoherentCechDiagram(
            presentation,
            cover
        );
        assert.equal(algebraPresentedAlgebraModuleIsZero(module), true);
        assert.equal(diagram.simplices.length, 0);
        assert.equal(diagram.faces.length, 0);
        assert.equal(diagram.degrees.length, 0);
    });

    it('roundtrips schemas and deterministic serialization without overclaims',
        () => {
            const value = fixture(2);
            const schema = algebraAffineQuasiCoherentCechDiagramSchema(
                value.presentation,
                value.cover
            );
            const normalized = schema.normalize(value.diagram, 'diagram');
            assert.equal(normalized.simplices.length, value.diagram.simplices.length);
            assert.equal(
                serializeAlgebraAffineQuasiCoherentCechDiagram(value.diagram),
                serializeAlgebraAffineQuasiCoherentCechDiagram(value.diagram)
            );
            assert.equal(ALGEBRA_QUASICOHERENT_CECH_PROFILE.claimsChainComplex,
                false);
            assert.equal(ALGEBRA_QUASICOHERENT_CECH_PROFILE.claimsCohomology,
                false);
        });

    it('rejects an affine cover over a foreign scheme', () => {
        const first = fixture(2);
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['z'], 'lex');
        const z = algebraPolynomialVariable(ring, 0);
        const quotient = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(ring, [])
        );
        const algebra = algebraPresentedAlgebra(quotient);
        const scheme = algebraAffineScheme(algebra);
        const foreignCover = algebraAffineCover(scheme, [
            algebraQuotientElement(quotient, z),
            algebraQuotientElement(
                quotient,
                algebraPolynomialSubtract(algebraPolynomialOne(ring), z)
            )
        ], 1);
        assert.throws(
            () => algebraAffineQuasiCoherentCechDiagram(
                first.presentation,
                foreignCover as never
            ),
            cechError('FOREIGN_AFFINE_COVER')
        );
    });
});
