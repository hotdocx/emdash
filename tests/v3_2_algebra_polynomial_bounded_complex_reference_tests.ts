/** Focused operation/graph tests for polynomial bounded complexes. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialBoundedComplexReferenceOperations,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    computeAlgebraOperation,
    createAlgebraComputationGraphBuilder,
    createAlgebraTypeScriptReferenceEngine,
    executeAlgebraComputationGraph,
    serializeAlgebraPolynomialBoundedFreeComplex
} from '../src/v3_2';

describe('FBC native operations and graph execution', () => {
    it('preserves a whole negative complex byte-for-byte through a graph',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const module = algebraPolynomialFreeModule(ring, 1);
            const map = algebraPolynomialModuleMap(module, module, [
                algebraPolynomialModuleVector(module, [x])
            ]);
            const input = Object.freeze({
                terms: Object.freeze([module, module, module]),
                differentials: Object.freeze([map, map])
            });
            const operations = algebraPolynomialBoundedComplexReferenceOperations<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const engine = createAlgebraTypeScriptReferenceEngine({
                id: 'polynomial-bounded-complex-reference',
                revision: 'v1',
                implementations: operations.implementations
            });
            const direct = await computeAlgebraOperation({
                engine,
                operation: operations.complex,
                input
            });
            const builder = createAlgebraComputationGraphBuilder(
                'polynomial-bounded-complex-graph',
                'v1'
            );
            const graphInput = builder.input('candidate', operations.complexInputSchema);
            const result = builder.operation('complex', operations.complex, graphInput);
            const graph = builder.build([{ id: 'result', value: result }]);
            const executed = await executeAlgebraComputationGraph({
                graph,
                engine,
                inputs: [{ id: 'candidate', value: input }]
            });

            assert.equal(direct.value.isComplex, false);
            assert.equal(
                serializeAlgebraPolynomialBoundedFreeComplex(direct.value),
                serializeAlgebraPolynomialBoundedFreeComplex(
                    executed.outputs[0].value as typeof direct.value
                )
            );
            assert.equal(
                algebraPolynomialBoundedFreeComplex(input).conditions[0].zero,
                false
            );
        }
    );
});
