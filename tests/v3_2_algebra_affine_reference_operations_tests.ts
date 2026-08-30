/** Focused AFFINE-GRAPH-5A native affine-operation graph tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
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
import { algebraPresentedAlgebra, algebraPresentedAlgebraMap } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineMorphism, algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineReferenceOperations } from '../src/v3_2/algebra_affine_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';

const free = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variable ? [variable] : [], 'lex');
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    return {
        ring,
        quotient,
        algebra,
        scheme: algebraAffineScheme(algebra),
        generator: variable ? algebraPolynomialVariable(ring, 0) : undefined
    };
};

describe('v3.2 native affine whole-operation graphs', () => {
    it('executes a relative tensor and affine fiber product', async () => {
        const base = free('t');
        const left = free('x');
        const right = free('y');
        const leftMap = algebraPresentedAlgebraMap(base.algebra, left.algebra, [
            algebraQuotientElement(left.quotient, algebraPolynomialPower(left.generator!, 2n))
        ]);
        const rightMap = algebraPresentedAlgebraMap(base.algebra, right.algebra, [
            algebraQuotientElement(right.quotient, algebraPolynomialPower(right.generator!, 3n))
        ]);
        const operations = algebraAffineReferenceOperations<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const tensorBuilder = createAlgebraComputationGraphBuilder(
            'fixture.affine.tensor',
            'v1'
        );
        const tensorInput = tensorBuilder.input('input', operations.tensorInputSchema);
        const tensorOutput = tensorBuilder.operation('tensor', operations.tensor, tensorInput);
        const tensorExecution = await executeAlgebraComputationGraph({
            graph: tensorBuilder.build([{ id: 'result', value: tensorOutput }]),
            engine,
            inputs: [{ id: 'input', value: { base: base.algebra, leftMap, rightMap } }]
        });
        assert.deepEqual(
            (tensorExecution.outputs[0].value as { polynomialRing: { variables: string[] } })
                .polynomialRing.variables,
            ['left_x', 'right_y']
        );

        const fiberBuilder = createAlgebraComputationGraphBuilder(
            'fixture.affine.fiber',
            'v1'
        );
        const fiberInput = fiberBuilder.input('input', operations.fiberInputSchema);
        const fiberOutput = fiberBuilder.operation(
            'fiber',
            operations.fiberProduct,
            fiberInput
        );
        const fiberExecution = await executeAlgebraComputationGraph({
            graph: fiberBuilder.build([{ id: 'result', value: fiberOutput }]),
            engine,
            inputs: [{
                id: 'input',
                value: {
                    left: algebraAffineMorphism(left.scheme, base.scheme, leftMap),
                    right: algebraAffineMorphism(right.scheme, base.scheme, rightMap)
                }
            }]
        });
        assert.equal(
            (fiberExecution.outputs[0].value as { compatible: boolean }).compatible,
            true
        );
    });

    it('executes a finite affine-cover Cech graph', async () => {
        const ambient = free('x');
        const x = algebraQuotientElement(ambient.quotient, ambient.generator!);
        const oneMinusX = algebraQuotientElement(
            ambient.quotient,
            algebraPolynomialSubtract(
                algebraPolynomialOne(ambient.ring),
                ambient.generator!
            )
        );
        const operations = algebraAffineReferenceOperations<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.affine.cover',
            'v1'
        );
        const input = builder.input('input', operations.coverInputSchema);
        const output = builder.operation('cover', operations.cover, input);
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: output }]),
            engine: createAlgebraTypeScriptReferenceEngine({
                implementations: operations.implementations
            }),
            inputs: [{
                id: 'input',
                value: {
                    ambient: ambient.scheme,
                    elements: [x, oneMinusX],
                    maximumDegree: 1
                }
            }]
        });
        const cover = execution.outputs[0].value as {
            charts: readonly unknown[];
            simplices: readonly unknown[];
        };
        assert.equal(cover.charts.length, 2);
        assert.equal(cover.simplices.length, 3);
    });
});
