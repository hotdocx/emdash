/** Focused category/compiler tests for polynomial bounded complexes. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedChainMapEquals,
    algebraPolynomialBoundedChainMapIdentity,
    algebraPolynomialBoundedComplexCategoryModel,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    compileAlgebraPolynomialBoundedComplexProgram,
    createAlgebraPolynomialBoundedComplexEngine,
    createCategoricalProgramBuilder,
    executeAlgebraComputationGraph,
    serializeAlgebraPolynomialBoundedChainMap
} from '../src/v3_2';

describe('FBC direct category and categorical compilation', () => {
    it('retains identity/composition and lowers whole chain-map validation',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const module = algebraPolynomialFreeModule(ring, 1);
            const map = (value: typeof x) => algebraPolynomialModuleMap(
                module,
                module,
                [algebraPolynomialModuleVector(module, [value])]
            );
            const complex = algebraPolynomialBoundedFreeComplex({
                terms: [module, module],
                differentials: [map(x)]
            });
            const scalar = algebraPolynomialBoundedChainMap({
                source: complex,
                target: complex,
                components: [map(y), map(y)]
            });
            const model = algebraPolynomialBoundedComplexCategoryModel(ring);
            assert.equal(model.category.equalMorphisms(
                model.category.compose(
                    scalar,
                    model.category.identityMorphism(complex)
                ),
                scalar
            ), true);
            assert.equal(algebraPolynomialBoundedChainMapEquals(
                model.category.identityMorphism(complex),
                algebraPolynomialBoundedChainMapIdentity(complex)
            ), true);

            const builder = createCategoricalProgramBuilder(
                'polynomial-bounded-complex.chain-map-program',
                'v1'
            );
            const input = builder.input('input', model.native.chainMapInputSchema);
            const output = builder.operation(
                'validate',
                model.chainMapOperation,
                input
            );
            const compilation = compileAlgebraPolynomialBoundedComplexProgram(
                model,
                builder.build([{ id: 'result', value: output }])
            );
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph,
                engine: createAlgebraPolynomialBoundedComplexEngine(model),
                inputs: [{
                    id: 'input',
                    value: {
                        source: complex,
                        target: complex,
                        components: scalar.components.map(entry => entry.map)
                    }
                }]
            });
            assert.equal(
                serializeAlgebraPolynomialBoundedChainMap(
                    execution.outputs[0].value as typeof scalar
                ),
                serializeAlgebraPolynomialBoundedChainMap(scalar)
            );
            assert.equal(
                compilation.nodes[0].selectedMethodId,
                'algebra.polynomial-bounded-complex.chain-map.primitive'
            );
            assert.equal(compilation.reinterpretationRules.length, 1);
        }
    );
});
