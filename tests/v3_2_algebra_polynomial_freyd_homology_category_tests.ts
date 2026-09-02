/** Focused category, native-operation, compiler, and graph homology tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydHomologyCategoryModel,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule,
    compileAlgebraPolynomialFreydHomologyProgram,
    createAlgebraPolynomialFreydHomologyEngine,
    createCategoricalProgramBuilder,
    executeAlgebraComputationGraph,
    executeCategoryOperation,
    planCategoryOperation,
    serializeAlgebraPolynomialFreydExactnessAt,
    serializeAlgebraPolynomialFreydHomologyAt,
    serializeAlgebraPolynomialFreydHomologyChainMap,
    serializeAlgebraPolynomialFreydInducedHomologyMap
} from '../src/v3_2';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const free = algebraPolynomialFreeModule(ring, 1);
    const one = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const multiplicationX = algebraPolynomialPresentationMorphism({
        source: one,
        target: one,
        map: algebraPolynomialModuleMap(free, free, [
            algebraPolynomialModuleVector(free, [x])
        ])
    });
    const quotient = algebraPolynomialFreydCokernel(multiplicationX);
    const pair = algebraPolynomialFreydChainPair(
        multiplicationX,
        quotient.projection
    );
    return { ring, multiplicationX, quotient, pair };
};

describe('v3.2 polynomial Freyd homology category', () => {
    it('plans homology through inherited universal-operation capabilities',
        async () => {
            const value = fixture();
            const model = algebraPolynomialFreydHomologyCategoryModel(value.ring);
            const plan = planCategoryOperation(
                model.category.operations,
                model.operations.homologyAt
            );
            assert.equal(plan.method.kind, 'derived');
            assert.deepEqual(
                plan.prerequisites.map(entry => entry.operation.id),
                [
                    model.base.base.operations.kernel.id,
                    model.base.base.operations.kernelLift.id,
                    model.base.base.operations.cokernel.id
                ]
            );
            const homology = await executeCategoryOperation(
                model.category,
                model.operations.homologyAt,
                value.pair
            );
            const exactness = await executeCategoryOperation(
                model.category,
                model.operations.exactnessAt,
                homology.value
            );
            assert.equal(homology.value.boundary.reconstructs, true);
            assert.equal(exactness.value.exact, true);
            assert.equal(homology.plan.method.kind, 'derived');
            assert.equal(exactness.plan.method.kind, 'derived');
        });

    it('lowers a retained homology-then-exactness program byte-for-byte',
        async () => {
            const value = fixture();
            const model = algebraPolynomialFreydHomologyCategoryModel(value.ring);
            const directHomology = (await executeCategoryOperation(
                model.category,
                model.operations.homologyAt,
                value.pair
            )).value;
            const directExactness = (await executeCategoryOperation(
                model.category,
                model.operations.exactnessAt,
                directHomology
            )).value;
            const builder = createCategoricalProgramBuilder(
                'polynomial-freyd-homology.at-degree',
                'v1'
            );
            const pair = builder.input(
                'pair',
                model.operations.homologyAt.input
            );
            const homology = builder.operation(
                'homology',
                model.operations.homologyAt,
                pair
            );
            const exactness = builder.operation(
                'exactness',
                model.operations.exactnessAt,
                homology
            );
            const compilation = compileAlgebraPolynomialFreydHomologyProgram(
                model,
                builder.build([
                    { id: 'homology', value: homology },
                    { id: 'exactness', value: exactness }
                ])
            );
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph,
                engine: createAlgebraPolynomialFreydHomologyEngine(model),
                inputs: [{ id: 'pair', value: value.pair }]
            });
            assert.equal(
                serializeAlgebraPolynomialFreydHomologyAt(
                    execution.outputs[0].value as typeof directHomology
                ),
                serializeAlgebraPolynomialFreydHomologyAt(directHomology)
            );
            assert.equal(
                serializeAlgebraPolynomialFreydExactnessAt(
                    execution.outputs[1].value as typeof directExactness
                ),
                serializeAlgebraPolynomialFreydExactnessAt(directExactness)
            );
            assert.deepEqual(
                compilation.nodes.map(node => node.selectedMethodKind),
                ['derived', 'derived']
            );
            assert.equal(compilation.graph.nodes.length, 2);
        });

    it('retains the unchanged Abelian category and whole chain-pair operation',
        async () => {
            const value = fixture();
            const model = algebraPolynomialFreydHomologyCategoryModel(value.ring);
            assert.equal(model.tower.outputDoctrineId, 'abelian-category');
            assert.ok(model.category.operations.methods.some(method =>
                method.operation.id === model.base.operations.image.id
            ));
            const pair = await executeCategoryOperation(
                model.category,
                model.operations.chainPair,
                {
                    dNext: value.multiplicationX,
                    d: value.quotient.projection
                }
            );
            assert.equal(pair.value.isChainPair, true);
            assert.equal(pair.plan.method.kind, 'primitive');
        });

    it('lowers a whole chain-map and induced-homology program', async () => {
        const value = fixture();
        const model = algebraPolynomialFreydHomologyCategoryModel(value.ring);
        const homology = (await executeCategoryOperation(
            model.category,
            model.operations.homologyAt,
            value.pair
        )).value;
        const chainMapInput = {
            source: homology,
            target: homology,
            fNext: algebraPolynomialPresentationMorphismIdentity(
                homology.pair.dNext.source
            ),
            f: algebraPolynomialPresentationMorphismIdentity(
                homology.pair.dNext.target
            ),
            fPrev: algebraPolynomialPresentationMorphismIdentity(
                homology.pair.d.target
            )
        };
        const directChainMap = (await executeCategoryOperation(
            model.category,
            model.operations.chainMap,
            chainMapInput
        )).value;
        const directInduced = (await executeCategoryOperation(
            model.category,
            model.operations.inducedHomologyMap,
            directChainMap
        )).value;
        const builder = createCategoricalProgramBuilder(
            'polynomial-freyd-homology.functorial',
            'v1'
        );
        const input = builder.input('chain-map-input',
            model.operations.chainMap.input);
        const chainMap = builder.operation(
            'chain-map',
            model.operations.chainMap,
            input
        );
        const induced = builder.operation(
            'induced',
            model.operations.inducedHomologyMap,
            chainMap
        );
        const compilation = compileAlgebraPolynomialFreydHomologyProgram(
            model,
            builder.build([
                { id: 'chain-map', value: chainMap },
                { id: 'induced', value: induced }
            ])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraPolynomialFreydHomologyEngine(model),
            inputs: [{ id: 'chain-map-input', value: chainMapInput }]
        });
        assert.equal(
            serializeAlgebraPolynomialFreydHomologyChainMap(
                execution.outputs[0].value as typeof directChainMap
            ),
            serializeAlgebraPolynomialFreydHomologyChainMap(directChainMap)
        );
        assert.equal(
            serializeAlgebraPolynomialFreydInducedHomologyMap(
                execution.outputs[1].value as typeof directInduced
            ),
            serializeAlgebraPolynomialFreydInducedHomologyMap(directInduced)
        );
        assert.deepEqual(
            compilation.nodes.map(node => node.selectedMethodKind),
            ['primitive', 'derived']
        );
        const inducedPlan = planCategoryOperation(
            model.category.operations,
            model.operations.inducedHomologyMap
        );
        assert.deepEqual(
            inducedPlan.prerequisites.map(entry => entry.operation.id),
            [
                model.base.base.operations.kernelLift.id,
                model.base.base.operations.cokernelColift.id
            ]
        );
    });
});
