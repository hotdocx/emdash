/** Focused QCC-COCHAIN-2A heterogeneous affine Cech cochain tests. */

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
    algebraPresentedAlgebraModuleElementEquals
} from '../src/v3_2/algebra_presented_module';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import { algebraAffineQuasiCoherentCechDiagram } from
    '../src/v3_2/algebra_quasicoherent_cech';
import {
    ALGEBRA_QUASICOHERENT_COCHAIN_PROFILE,
    AlgebraQuasiCoherentCochainError,
    algebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainAdd,
    algebraAffineQuasiCoherentCochainComponentAt,
    algebraAffineQuasiCoherentCochainComponentAtIndices,
    algebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainEquals,
    algebraAffineQuasiCoherentCochainFromGlobalElement,
    algebraAffineQuasiCoherentCochainIsZero,
    algebraAffineQuasiCoherentCochainNegate,
    algebraAffineQuasiCoherentCochainSchema,
    algebraAffineQuasiCoherentCochainSubtract,
    algebraAffineQuasiCoherentCochainZero,
    serializeAlgebraAffineQuasiCoherentCochain
} from '../src/v3_2/algebra_quasicoherent_cochain';

const cochainError = (code: AlgebraQuasiCoherentCochainError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraQuasiCoherentCochainError);
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

describe('v3.2 heterogeneous affine Cech cochains', () => {
    it('retains exact ordered binary and ternary degree parents', () => {
        const binary = fixture(2);
        const ternary = fixture(3);
        const binaryZero = algebraAffineQuasiCoherentCochainDegree(
            binary.diagram,
            0
        );
        const ternaryOne = algebraAffineQuasiCoherentCochainDegree(
            ternary.diagram,
            1
        );
        assert.deepEqual(
            binaryZero.data.simplices.map(simplex => simplex.simplex.indices),
            [[0], [1]]
        );
        assert.deepEqual(
            ternaryOne.data.simplices.map(simplex => simplex.simplex.indices),
            [[0, 1], [0, 2], [1, 2]]
        );
        assert.notDeepEqual(binaryZero.identity, ternaryOne.identity);
        assert.equal(ALGEBRA_QUASICOHERENT_COCHAIN_PROFILE.commonScalarParent,
            false);
    });

    it('maps a global element into every retained simplex module', () => {
        const value = fixture(3);
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 1);
        const cochain = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        assert.equal(cochain.components.length, 3);
        cochain.components.forEach((component, index) => assert.equal(
            component.parent,
            degree.data.simplices[index].value.module
        ));
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraAffineQuasiCoherentCochainComponentAtIndices(
                cochain,
                [0, 2]
            ),
            cochain.components[1]
        ));
    });

    it('computes zero, addition, negation, subtraction, and equality', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const diagonal = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const zero = algebraAffineQuasiCoherentCochainZero(degree);
        const negative = algebraAffineQuasiCoherentCochainNegate(diagonal);
        assert.equal(algebraAffineQuasiCoherentCochainIsZero(zero), true);
        assert.equal(algebraAffineQuasiCoherentCochainIsZero(
            algebraAffineQuasiCoherentCochainAdd(diagonal, negative)
        ), true);
        assert.equal(algebraAffineQuasiCoherentCochainEquals(
            algebraAffineQuasiCoherentCochainSubtract(diagonal, diagonal),
            zero
        ), true);
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraAffineQuasiCoherentCochainComponentAt(diagonal, 0),
            diagonal.components[0]
        ));
    });

    it('roundtrips its schema and deterministic serialization', () => {
        const value = fixture();
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const cochain = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const schema = algebraAffineQuasiCoherentCochainSchema(degree);
        assert.equal(
            algebraAffineQuasiCoherentCochainEquals(
                schema.normalize(cochain, 'cochain'),
                cochain
            ),
            true
        );
        assert.equal(
            serializeAlgebraAffineQuasiCoherentCochain(cochain),
            serializeAlgebraAffineQuasiCoherentCochain(cochain)
        );
    });

    it('rejects degree, arity, component, lookup, and global-parent drift', () => {
        const first = fixture();
        const second = fixture(3);
        assert.throws(
            () => algebraAffineQuasiCoherentCochainDegree(first.diagram, 2),
            cochainError('INVALID_DEGREE')
        );
        const degree = algebraAffineQuasiCoherentCochainDegree(first.diagram, 0);
        const diagonal = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            first.globalBasis
        );
        assert.throws(
            () => algebraAffineQuasiCoherentCochain(degree, []),
            cochainError('INVALID_COMPONENT_ARITY')
        );
        assert.throws(
            () => algebraAffineQuasiCoherentCochain(degree, [
                diagonal.components[1],
                diagonal.components[0]
            ]),
            cochainError('FOREIGN_COMPONENT')
        );
        assert.throws(
            () => algebraAffineQuasiCoherentCochainComponentAt(diagonal, 2),
            cochainError('INVALID_COMPONENT_POSITION')
        );
        assert.throws(
            () => algebraAffineQuasiCoherentCochainComponentAtIndices(
                diagonal,
                [0, 1]
            ),
            cochainError('UNKNOWN_SIMPLEX')
        );
        assert.throws(
            () => algebraAffineQuasiCoherentCochainFromGlobalElement(
                degree,
                second.globalBasis as never
            ),
            cochainError('FOREIGN_GLOBAL_ELEMENT')
        );
        const secondDegree = algebraAffineQuasiCoherentCochainDegree(
            second.diagram,
            0
        );
        assert.throws(
            () => algebraAffineQuasiCoherentCochainAdd(
                diagonal,
                algebraAffineQuasiCoherentCochainZero(secondDegree) as never
            ),
            cochainError('FOREIGN_COCHAIN')
        );
    });
});
