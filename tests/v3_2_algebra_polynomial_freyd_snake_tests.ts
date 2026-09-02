/** Focused CAP-style snake connecting morphism in polynomial Freyd. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydSnakeError,
    RATIONAL_DOMAIN,
    algebraPolynomialConstant,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialText,
    algebraPolynomialVariable,
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydAbelianCategoryModel,
    algebraPolynomialFreydSnakeReferenceOperations,
    algebraPolynomialFreydSnakeTriple,
    createAlgebraComputationGraphBuilder,
    createAlgebraTypeScriptReferenceEngine,
    executeAlgebraComputationGraph,
    serializeAlgebraPolynomialFreydSnakeConnecting,
    serializeAlgebraPolynomialFreydSnakeTriple,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const snakeError = (code: AlgebraPolynomialFreydSnakeError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydSnakeError);
        assert.equal(error.code, code);
        return true;
    };

describe('v3.2 CAP-style polynomial Freyd snake morphism', () => {
    it('reproduces the CAP rational vector-space example without a section', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const module = (rank: number) => algebraPolynomialFreeModule(ring, rank);
        const presentation = (rank: number) => {
            const ambient = module(rank);
            return algebraPresentedPolynomialModule(
                algebraPolynomialSubmodule(ambient, [])
            );
        };
        const A = presentation(2);
        const B = presentation(2);
        const C = presentation(3);
        const D = presentation(1);
        const polynomial = (value: string) =>
            algebraPolynomialConstant(ring, value);
        const morphism = (
            source: typeof A,
            target: typeof A,
            columns: readonly (readonly string[])[]
        ) => algebraPolynomialPresentationMorphism({
            source,
            target,
            map: algebraPolynomialModuleMap(
                source.ambient,
                target.ambient,
                columns.map(column => algebraPolynomialModuleVector(
                    target.ambient,
                    column.map(polynomial)
                ))
            )
        });
        const delta = morphism(A, B, [['1', '0'], ['0', '0']]);
        const beta = morphism(B, C, [['2', '4', '0'], ['3', '5', '0']]);
        const lambda = morphism(C, D, [['0'], ['0'], ['1']]);
        const triple = algebraPolynomialFreydSnakeTriple(delta, beta, lambda);
        const result = algebraPolynomialFreydSnakeConnecting(triple);
        assert.equal(triple.tripleZeroAgreement.agrees, true);
        assert.equal(result.gammaColift.reconstructionAgreement.agrees, true);
        assert.equal(result.alphaLift.reconstructionAgreement.agrees, true);
        assert.equal(result.fiberProduct.compatibilityAgreement.agrees, true);
        assert.equal(result.p1Epimorphism.epic, true);
        assert.equal(result.pushout.compatibilityAgreement.agrees, true);
        assert.equal(result.q2Monomorphism.monic, true);
        assert.equal(result.uColift.reconstructionAgreement.agrees, true);
        assert.equal(result.connectingLift.reconstructionAgreement.agrees, true);
        assert.equal(result.assumesSplitEpimorphisms, false);
        assert.equal(result.source.ambient.rank, 2);
        assert.equal(result.target.ambient.rank, 2);
        assert.deepEqual(
            result.connecting.map.columns.map(column =>
                column.components.map(algebraPolynomialText)),
            [['0', '0'], ['0', '-1']]
        );
        assert.ok(Object.isFrozen(result));
    });

    it('computes across the nonsplit quotient R → R/(x)', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const object = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
        const multiplicationX = algebraPolynomialPresentationMorphism({
            source: object,
            target: object,
            map: algebraPolynomialModuleMap(ambient, ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        });
        const identity = algebraPolynomialPresentationMorphismIdentity(object);
        const zero = algebraPolynomialPresentationMorphism({
            source: object,
            target: object,
            map: algebraPolynomialModuleMapZero(ambient, ambient)
        });
        const result = algebraPolynomialFreydSnakeConnecting(
            algebraPolynomialFreydSnakeTriple(
                multiplicationX,
                identity,
                zero
            )
        );
        assert.equal(result.deltaCokernel.object.relations.generators.length, 1);
        assert.deepEqual(
            result.deltaCokernel.object.relations.generators[0].components
                .map(algebraPolynomialText),
            [algebraPolynomialText(x)]
        );
        assert.equal(result.epsilonEpimorphism.epic, true);
        assert.equal(result.p1Epimorphism.epic, true);
        assert.equal(result.q2Monomorphism.monic, true);
        assert.equal(result.uColift.reconstructs, true);
        assert.equal(result.connectingLift.reconstructs, true);
        assert.equal(result.assumesSplitEpimorphisms, false);
        assert.equal('projectionSection' in result, false);
        assert.ok(Object.isFrozen(result));
    });

    it('retains and rejects a nonzero triple composite', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const object = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
        const identity = algebraPolynomialPresentationMorphismIdentity(object);
        const triple = algebraPolynomialFreydSnakeTriple(
            identity,
            identity,
            identity
        );
        assert.equal(triple.tripleZeroAgreement.agrees, false);
        assert.equal(triple.isSnakeTriple, false);
        assert.throws(
            () => algebraPolynomialFreydSnakeConnecting(triple),
            snakeError('TRIPLE_ZERO_FAILED')
        );
    });

    it('executes retained native operations with canonical whole serialization',
        async () => {
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
            const directTriple = algebraPolynomialFreydSnakeTriple(
                delta,
                beta,
                lambda
            );
            const direct = algebraPolynomialFreydSnakeConnecting(directTriple);
            const operations = algebraPolynomialFreydSnakeReferenceOperations(
                algebraPolynomialFreydAbelianCategoryModel(ring),
                ring
            );
            const builder = createAlgebraComputationGraphBuilder(
                'polynomial-freyd-snake.native',
                'v1'
            );
            const input = builder.input('triple-input',
                operations.tripleInputSchema);
            const triple = builder.operation('triple', operations.triple, input);
            const connecting = builder.operation(
                'connecting',
                operations.connecting,
                triple
            );
            const execution = await executeAlgebraComputationGraph({
                graph: builder.build([
                    { id: 'triple', value: triple },
                    { id: 'connecting', value: connecting }
                ]),
                engine: createAlgebraTypeScriptReferenceEngine({
                    implementations: operations.implementations
                }),
                inputs: [{
                    id: 'triple-input',
                    value: { delta, beta, lambda }
                }]
            });
            assert.equal(
                serializeAlgebraPolynomialFreydSnakeTriple(
                    execution.outputs[0].value as typeof directTriple
                ),
                serializeAlgebraPolynomialFreydSnakeTriple(directTriple)
            );
            const compiled = execution.outputs[1].value as typeof direct;
            assert.equal(
                serializeAlgebraPolynomialFreydSnakeConnecting(compiled),
                serializeAlgebraPolynomialFreydSnakeConnecting(direct)
            );
            assert.equal(
                serializeAlgebraPolynomialFreydSnakeConnecting(
                    algebraPolynomialFreydSnakeConnecting(
                        algebraPolynomialFreydSnakeTriple(delta, beta, lambda)
                    )
                ),
                serializeAlgebraPolynomialFreydSnakeConnecting(direct)
            );
        });
});
