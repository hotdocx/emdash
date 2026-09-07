/** Focused category, compiler, and graph tests for the Freyd snake map. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydShortExactError,
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydSnakeCategoryModel,
    algebraPolynomialFreydShortExactTriple,
    algebraPolynomialFreydZeroPresentation,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule,
    compileAlgebraPolynomialFreydSnakeProgram,
    createAlgebraPolynomialFreydSnakeEngine,
    createCategoricalProgramBuilder,
    executeAlgebraComputationGraph,
    executeCategoryOperation,
    planCategoryOperation,
    serializeAlgebraPolynomialFreydSnakeConnecting,
    serializeAlgebraPolynomialFreydSnakeTriple,
    serializeAlgebraPolynomialFreydShortExactTriple
} from '../src/v3_2';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const ambient = algebraPolynomialFreeModule(ring, 1);
    const object = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(ambient, [])
    );
    const delta = algebraPolynomialPresentationMorphism({
        source: object,
        target: object,
        map: algebraPolynomialModuleMap(ambient, ambient, [
            algebraPolynomialModuleVector(ambient, [x])
        ])
    });
    const beta = algebraPolynomialPresentationMorphismIdentity(object);
    const lambda = algebraPolynomialPresentationMorphism({
        source: object,
        target: object,
        map: algebraPolynomialModuleMapZero(ambient, ambient)
    });
    return { ring, object, delta, beta, lambda };
};

describe('v3.2 polynomial Freyd snake categorical program', () => {
    it('checks omitted short-exact aliases against their retained owners when serializing', () => {
        const value = fixture();
        const zero = algebraPolynomialFreydZeroPresentation(value.ring);
        const incoming = algebraPolynomialPresentationMorphismIdentity(value.object);
        const outgoing = algebraPolynomialPresentationMorphismZero(value.object, zero);
        const row = algebraPolynomialFreydShortExactTriple(incoming, outgoing);
        assert.equal(serializeAlgebraPolynomialFreydShortExactTriple(row), serializeAlgebraPolynomialFreydShortExactTriple(row));
        for (const changed of [
            { ...row, incoming: algebraPolynomialPresentationMorphismIdentity(value.object) },
            { ...row, outgoing: algebraPolynomialPresentationMorphismZero(value.object, zero) },
            { ...row, pair: { ...row.pair } },
            { ...row, exactness: { ...row.exactness, homology: { ...row.homology } } }
        ]) assert.throws(() => serializeAlgebraPolynomialFreydShortExactTriple(changed), /actual retained pair and homology/u);
    });

    it('plans the complete CAP dependency chain', () => {
        const value = fixture();
        const model = algebraPolynomialFreydSnakeCategoryModel(value.ring);
        const plan = planCategoryOperation(
            model.category.operations,
            model.operations.snakeConnecting
        );
        assert.equal(plan.method.kind, 'derived');
        assert.deepEqual(
            plan.prerequisites.map(entry => entry.operation.id),
            [
                model.base.base.operations.cokernelColift.id,
                model.base.base.operations.kernel.id,
                model.base.base.operations.cokernel.id,
                model.base.base.operations.kernelLift.id,
                model.operations.fiberProduct.id,
                model.operations.pushout.id,
                model.base.operations.coliftAlongEpimorphism.id,
                model.base.operations.liftAlongMonomorphism.id
            ]
        );
        assert.equal(model.tower.outputDoctrineId, 'abelian-category');
    });

    it('lowers a retained triple-then-connecting program byte-for-byte',
        async () => {
            const value = fixture();
            const model = algebraPolynomialFreydSnakeCategoryModel(value.ring);
            const directTriple = (await executeCategoryOperation(
                model.category,
                model.operations.snakeTriple,
                {
                    delta: value.delta,
                    beta: value.beta,
                    lambda: value.lambda
                }
            )).value;
            const directConnecting = (await executeCategoryOperation(
                model.category,
                model.operations.snakeConnecting,
                directTriple
            )).value;
            const builder = createCategoricalProgramBuilder(
                'polynomial-freyd-snake.connecting',
                'v1'
            );
            const input = builder.input(
                'triple-input',
                model.operations.snakeTriple.input
            );
            const triple = builder.operation(
                'triple',
                model.operations.snakeTriple,
                input
            );
            const connecting = builder.operation(
                'connecting',
                model.operations.snakeConnecting,
                triple
            );
            const compilation = compileAlgebraPolynomialFreydSnakeProgram(
                model,
                builder.build([
                    { id: 'triple', value: triple },
                    { id: 'connecting', value: connecting }
                ])
            );
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph,
                engine: createAlgebraPolynomialFreydSnakeEngine(model),
                inputs: [{
                    id: 'triple-input',
                    value: {
                        delta: value.delta,
                        beta: value.beta,
                        lambda: value.lambda
                    }
                }]
            });
            assert.equal(
                serializeAlgebraPolynomialFreydSnakeTriple(
                    execution.outputs[0].value as typeof directTriple
                ),
                serializeAlgebraPolynomialFreydSnakeTriple(directTriple)
            );
            assert.equal(
                serializeAlgebraPolynomialFreydSnakeConnecting(
                    execution.outputs[1].value as typeof directConnecting
                ),
                serializeAlgebraPolynomialFreydSnakeConnecting(directConnecting)
            );
            assert.deepEqual(
                compilation.nodes.map(node => node.selectedMethodKind),
                ['primitive', 'derived']
            );
        });

    it('executes the universal roles and a witness-rich short exact boundary',
        async () => {
            const value = fixture();
            const model = algebraPolynomialFreydSnakeCategoryModel(value.ring);
            const triple = (await executeCategoryOperation(
                model.category,
                model.operations.snakeTriple,
                {
                    delta: value.delta,
                    beta: value.beta,
                    lambda: value.lambda
                }
            )).value;
            const snake = (await executeCategoryOperation(
                model.category,
                model.operations.snakeConnecting,
                triple
            )).value;
            const fiberProduct = (await executeCategoryOperation(
                model.category,
                model.operations.fiberProduct,
                { left: snake.iota, right: snake.epsilon }
            )).value;
            const fiberFactor = (await executeCategoryOperation(
                model.category,
                model.operations.fiberProductLift,
                {
                    fiberProduct,
                    testLeft: fiberProduct.projectionLeft,
                    testRight: fiberProduct.projectionRight
                }
            )).value;
            assert.equal(fiberFactor.reconstructs, true);
            const projectionLeft = (await executeCategoryOperation(
                model.category,
                model.operations.fiberProductProjectionLeft,
                fiberProduct
            )).value;
            const projectionRight = (await executeCategoryOperation(
                model.category,
                model.operations.fiberProductProjectionRight,
                fiberProduct
            )).value;
            assert.equal(
                model.category.equalMorphisms(
                    projectionLeft,
                    fiberProduct.projectionLeft
                ),
                true
            );
            assert.equal(
                model.category.equalMorphisms(
                    projectionRight,
                    fiberProduct.projectionRight
                ),
                true
            );
            const pushout = (await executeCategoryOperation(
                model.category,
                model.operations.pushout,
                { left: snake.mu, right: snake.pi }
            )).value;
            const pushoutCofactor = (await executeCategoryOperation(
                model.category,
                model.operations.pushoutColift,
                {
                    pushout,
                    testLeft: pushout.injectionLeft,
                    testRight: pushout.injectionRight
                }
            )).value;
            assert.equal(pushoutCofactor.reconstructs, true);
            const injectionLeft = (await executeCategoryOperation(
                model.category,
                model.operations.pushoutInjectionLeft,
                pushout
            )).value;
            const injectionRight = (await executeCategoryOperation(
                model.category,
                model.operations.pushoutInjectionRight,
                pushout
            )).value;
            assert.equal(
                model.category.equalMorphisms(
                    injectionLeft,
                    pushout.injectionLeft
                ),
                true
            );
            assert.equal(
                model.category.equalMorphisms(
                    injectionRight,
                    pushout.injectionRight
                ),
                true
            );
            const zeroObject = algebraPolynomialFreydZeroPresentation(value.ring);
            const shortExact = (await executeCategoryOperation(
                model.category,
                model.operations.shortExactTriple,
                {
                    incoming: algebraPolynomialPresentationMorphismZero(
                        zeroObject,
                        value.object
                    ),
                    outgoing:
                        algebraPolynomialPresentationMorphismIdentity(value.object)
                }
            )).value;
            assert.equal(shortExact.shortExact, true);
            assert.equal(shortExact.exactness.exact, true);
            assert.equal(shortExact.incomingMonomorphism.monic, true);
            assert.equal(shortExact.outgoingEpimorphism.epic, true);
            assert.equal(
                serializeAlgebraPolynomialFreydShortExactTriple(shortExact),
                serializeAlgebraPolynomialFreydShortExactTriple(
                    algebraPolynomialFreydShortExactTriple(
                        algebraPolynomialPresentationMorphismZero(
                            zeroObject,
                            value.object
                        ),
                        algebraPolynomialPresentationMorphismIdentity(value.object)
                    )
                )
            );
            assert.throws(
                () => algebraPolynomialFreydShortExactTriple(
                    algebraPolynomialPresentationMorphismIdentity(value.object),
                    algebraPolynomialPresentationMorphismIdentity(value.object)
                ),
                (error: unknown) => {
                    assert.ok(error instanceof AlgebraPolynomialFreydShortExactError);
                    assert.equal(error.code, 'ZERO_COMPOSITE_FAILED');
                    return true;
                }
            );
        });
});
