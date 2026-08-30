/** Focused CAS-MODULE-4B2D native graph-operation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPolynomialModuleReferenceOperations
} from '../src/v3_2/algebra_polynomial_module_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const zero = algebraPolynomialZero(ring);
    const module = algebraPolynomialFreeModule(ring, 2, 'position-over-term');
    const relations = algebraPolynomialSubmodule(module, [
        algebraPolynomialModuleVector(module, [x, y]),
        algebraPolynomialModuleVector(module, [y, zero])
    ]);
    return { module, relations };
};

describe('v3.2 native polynomial-module operations', () => {
    it('chains module Groebner and Schreyer nodes in one graph', async () => {
        const { module, relations } = fixture();
        const operations = algebraPolynomialModuleReferenceOperations(module);
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.polynomial-module.syzygies',
            'v1'
        );
        const input = builder.input('relations', operations.submoduleSchema);
        const basis = builder.operation('basis', operations.groebner, input);
        const syzygies = builder.operation('syzygies', operations.syzygies, basis);
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: syzygies }]),
            engine: createAlgebraTypeScriptReferenceEngine({
                implementations: operations.implementations
            }),
            inputs: [{ id: 'relations', value: relations }]
        });
        const result = execution.outputs[0].value as {
            readonly generators: readonly unknown[];
            readonly module: { readonly termOrder: string };
        };
        assert.equal(result.generators.length, 1);
        assert.equal(result.module.termOrder, 'schreyer');
    });

    it('executes a complete bounded Schreyer resolution as a graph node', async () => {
        const { module, relations } = fixture();
        const operations = algebraPolynomialModuleReferenceOperations(module);
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.polynomial-module.resolution',
            'v1'
        );
        const input = builder.input('input', operations.resolution.input);
        const resolution = builder.operation(
            'resolution',
            operations.resolution,
            input
        );
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: resolution }]),
            engine: createAlgebraTypeScriptReferenceEngine({
                implementations: operations.implementations
            }),
            inputs: [{ id: 'input', value: { relations, maximumLength: 4 } }]
        });
        const result = execution.outputs[0].value as {
            readonly complete: boolean;
            readonly length: number;
            readonly freeModules: readonly { readonly rank: number }[];
        };
        assert.equal(result.complete, true);
        assert.equal(result.length, 2);
        assert.deepEqual(result.freeModules.map(value => value.rank), [2, 3, 1]);
    });
});
