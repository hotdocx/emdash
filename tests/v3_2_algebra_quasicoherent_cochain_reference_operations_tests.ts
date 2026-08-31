/** Focused QCC-GRAPH-5A fixed-degree differential graph tests. */

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
    algebraAffineQuasiCoherentCochainFromGlobalElement
} from '../src/v3_2/algebra_quasicoherent_cochain';
import {
    algebraAffineQuasiCoherentDifferential,
    serializeAlgebraAffineQuasiCoherentDifferential
} from '../src/v3_2/algebra_quasicoherent_differential';
import {
    algebraAffineQuasiCoherentDifferentialSquare,
    serializeAlgebraAffineQuasiCoherentDifferentialSquare
} from '../src/v3_2/algebra_quasicoherent_differential_square';
import {
    ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE,
    AlgebraQuasiCoherentCochainReferenceError,
    algebraQuasiCoherentCochainReferenceOperations,
    createAlgebraQuasiCoherentCochainEngine
} from '../src/v3_2/algebra_quasicoherent_cochain_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';

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

describe('v3.2 native fixed-degree Cech cochain operations', () => {
    it('executes the binary asymmetric differential in a graph', async () => {
        const value = fixture(2);
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const global = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const inputCochain = algebraAffineQuasiCoherentCochain(degree, [
            algebraPresentedAlgebraModuleElementZero(
                degree.data.simplices[0].value.module
            ),
            global.components[1]
        ]);
        const operations = algebraQuasiCoherentCochainReferenceOperations(degree);
        assert.equal(operations.squareAvailable, false);
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.quasicoherent.binary-differential',
            'v1'
        );
        const input = builder.input('input', operations.inputSchema);
        const output = builder.operation(
            'differential',
            operations.differential,
            input
        );
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: output }]),
            engine: createAlgebraQuasiCoherentCochainEngine(operations),
            inputs: [{ id: 'input', value: inputCochain }]
        });
        const differential = execution.outputs[0].value as never;
        assert.equal(
            serializeAlgebraAffineQuasiCoherentDifferential(differential),
            serializeAlgebraAffineQuasiCoherentDifferential(
                algebraAffineQuasiCoherentDifferential(inputCochain)
            )
        );
    });

    it('executes the ternary differential square in a graph', async () => {
        const value = fixture(3);
        const degree = algebraAffineQuasiCoherentCochainDegree(value.diagram, 0);
        const cochain = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degree,
            value.globalBasis
        );
        const operations = algebraQuasiCoherentCochainReferenceOperations(degree);
        assert.equal(operations.squareAvailable, true);
        assert.ok(operations.square);
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.quasicoherent.ternary-square',
            'v1'
        );
        const input = builder.input('input', operations.inputSchema);
        const output = builder.operation('square', operations.square, input);
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: output }]),
            engine: createAlgebraQuasiCoherentCochainEngine(operations),
            inputs: [{ id: 'input', value: cochain }]
        });
        const square = execution.outputs[0].value as {
            holds: boolean;
            cancellations: readonly unknown[];
        };
        assert.equal(square.holds, true);
        assert.equal(square.cancellations.length, 3);
        assert.equal(
            serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                execution.outputs[0].value as never
            ),
            serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                algebraAffineQuasiCoherentDifferentialSquare(cochain)
            )
        );
        assert.equal(
            ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.fixedDegreeSchema,
            true
        );
    });

    it('rejects a foreign-degree cochain at the operation schema', () => {
        const value = fixture(3);
        const degreeZero = algebraAffineQuasiCoherentCochainDegree(
            value.diagram,
            0
        );
        const degreeOne = algebraAffineQuasiCoherentCochainDegree(
            value.diagram,
            1
        );
        const operations = algebraQuasiCoherentCochainReferenceOperations(
            degreeZero
        );
        const foreign = algebraAffineQuasiCoherentCochainFromGlobalElement(
            degreeOne,
            value.globalBasis
        );
        assert.throws(
            () => operations.inputSchema.normalize(foreign, 'input'),
            /does not satisfy schema/u
        );
    });

    it('rejects an operation bundle at the retained top degree', () => {
        const value = fixture(2);
        const top = algebraAffineQuasiCoherentCochainDegree(value.diagram, 1);
        assert.throws(
            () => algebraQuasiCoherentCochainReferenceOperations(top),
            (error: unknown) => {
                assert.ok(error instanceof AlgebraQuasiCoherentCochainReferenceError);
                assert.equal(error.code, 'NO_SUCCESSOR_DEGREE');
                return true;
            }
        );
    });
});
