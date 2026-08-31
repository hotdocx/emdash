/** Focused operation/graph tests for presentation-morphism computations. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphismReferenceOperations,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule,
    computeAlgebraOperation,
    createAlgebraComputationGraphBuilder,
    createAlgebraTypeScriptReferenceEngine,
    executeAlgebraComputationGraph,
    serializeAlgebraPolynomialPresentationMorphism
} from '../src/v3_2';

describe('FPMAP native operations and graph execution', () => {
    it('agrees byte-for-byte between direct operation and graph execution',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const ambient = algebraPolynomialFreeModule(ring, 1);
            const presentation = algebraPresentedPolynomialModule(
                algebraPolynomialSubmodule(ambient, [
                    algebraPolynomialModuleVector(ambient, [x])
                ])
            );
            const map = algebraPolynomialModuleMap(ambient, ambient, [
                algebraPolynomialModuleVector(ambient, [y])
            ]);
            const input = Object.freeze({
                source: presentation,
                target: presentation,
                map
            });
            const operations =
                algebraPolynomialPresentationMorphismReferenceOperations<
                    typeof RATIONAL_DOMAIN.parent,
                    typeof RATIONAL_DOMAIN.zero,
                    string | bigint
                >();
            const engine = createAlgebraTypeScriptReferenceEngine({
                id: 'presentation-morphism-reference',
                revision: 'v1',
                implementations: operations.implementations
            });
            const direct = await computeAlgebraOperation({
                engine,
                operation: operations.morphism,
                input
            });
            const builder = createAlgebraComputationGraphBuilder(
                'presentation-morphism-graph',
                'v1'
            );
            const graphInput = builder.input(
                'candidate',
                operations.morphismInputSchema
            );
            const result = builder.operation(
                'witness',
                operations.morphism,
                graphInput
            );
            const graph = builder.build([{ id: 'result', value: result }]);
            const executed = await executeAlgebraComputationGraph({
                graph,
                engine,
                inputs: [{ id: 'candidate', value: input }]
            });

            assert.equal(direct.value.preservesRelations, true);
            assert.equal(
                serializeAlgebraPolynomialPresentationMorphism(direct.value),
                serializeAlgebraPolynomialPresentationMorphism(
                    executed.outputs[0].value as typeof direct.value
                )
            );
        }
    );
});
