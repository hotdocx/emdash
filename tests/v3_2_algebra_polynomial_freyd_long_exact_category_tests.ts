/** Direct categorical execution, dependency plans, and whole-result graph lowering. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraCategoryError, CategoryOperationPlan, createCategoryOperationRegistry,
    executeCategoryOperation, planCategoryOperation
} from '../src/v3_2/algebra_category';
import {
    AlgebraCategoricalProgramError, createCategoricalProgramBuilder
} from '../src/v3_2/algebra_categorical_program';
import { executeAlgebraComputationGraph } from '../src/v3_2/algebra_graph';
import {
    ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_CATEGORY_PROFILE,
    algebraPolynomialFreydLongExactCategoryModel,
    compileAlgebraPolynomialFreydLongExactProgram,
    createAlgebraPolynomialFreydLongExactEngine
} from '../src/v3_2/algebra_polynomial_freyd_long_exact_category';
import {
    serializeAlgebraPolynomialFreydLongExactSnakeReferences
} from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import {
    algebraPolynomialFreydBoundedLongExactHomology
} from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import { serializeAlgebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact_serialization';
import { serializeAlgebraPolynomialFreydBoundedShortExactSequence } from '../src/v3_2/algebra_polynomial_freyd_bounded_short_exact_serialization';
import { serializeAlgebraPolynomialFreydHomologyConnecting } from '../src/v3_2/algebra_polynomial_freyd_homology_connecting_serialization';
import { serializeAlgebraPolynomialFreydHomologyWindow } from '../src/v3_2/algebra_polynomial_freyd_homology_window_serialization';
import { serializeAlgebraPolynomialFreydSnakeExactSequence } from '../src/v3_2/algebra_polynomial_freyd_snake_exact_serialization';
import { polynomialFreydHomologyFixture as fixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';

const sequenceInput = (sequence: ReturnType<typeof fixture>) => ({
    subcomplex: sequence.subcomplex, middleComplex: sequence.middleComplex,
    quotientComplex: sequence.quotientComplex, inclusion: sequence.inclusion, projection: sequence.projection
});
const prerequisiteIds = (plan: CategoryOperationPlan): string[] =>
    [plan.operation.id, ...plan.prerequisites.flatMap(prerequisiteIds)];

describe('v3.2 long exact homology categorical operations', () => {
    it('retains both capability families without duplicate inherited identities', () => {
        const model = algebraPolynomialFreydLongExactCategoryModel(fixture().ring);
        const methods = model.category.operations.methods;
        const methodKeys = methods.map(m => m.operation.id + '/' + m.operation.revision + '/' + m.id);
        assert.equal(new Set(methodKeys).size, methodKeys.length);
        const loweringKeys = model.lowerings.map(value => value.categoryOperation.id + '/' + value.categoryOperation.revision);
        assert.equal(new Set(loweringKeys).size, loweringKeys.length);
        for (const inherited of [...model.homology.category.operations.methods,
            ...model.snake.category.operations.methods.filter(m => Object.values(model.snake.operations).some(op => op.id === m.operation.id))]) {
            assert.ok(methods.includes(inherited));
        }
        assert.equal(model.tower.outputDoctrineId, 'abelian-category');
        assert.ok(model.tower.introducedRoles.includes('bounded-long-exact-homology'));
        assert.ok(model.tower.introducedRoles.includes('snake-exact-sequence'));
        assert.equal(ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_CATEGORY_PROFILE.claimsFormalCategory, false);
        assert.equal(ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_CATEGORY_PROFILE.dualImplementation, false);
        assert.ok(createAlgebraPolynomialFreydLongExactEngine(model));
    });

    it('plans the whole result through its actual universal-operation capabilities', () => {
        const model = algebraPolynomialFreydLongExactCategoryModel(fixture().ring);
        const plan = planCategoryOperation(model.category.operations, model.operations.boundedLongExact);
        const ids = prerequisiteIds(plan);
        assert.equal(plan.method.kind, 'derived');
        for (const operation of [model.operations.homologyWindow, model.operations.homologyConnecting,
            model.snake.operations.snakeConnecting, model.homology.operations.homologyAt,
            model.homology.operations.inducedHomologyMap, model.homology.operations.exactnessAt,
            model.homology.base.base.operations.kernelLift, model.homology.base.base.operations.cokernelColift]) {
            assert.ok(ids.includes(operation.id), operation.id);
        }
        const unavailable = createCategoryOperationRegistry(model.category.operations.methods.filter(method =>
            method.operation.id !== model.homology.base.base.operations.kernel.id));
        assert.throws(() => planCategoryOperation(unavailable, model.operations.boundedLongExact),
            (error: unknown) => error instanceof AlgebraCategoryError && error.code === 'UNAVAILABLE_OPERATION');
    });

    it('executes and lowers sequence → long exact → all reference snakes byte-for-byte', async () => {
        const source = fixture('boundary');
        const model = algebraPolynomialFreydLongExactCategoryModel(source.ring);
        const input = sequenceInput(source);
        const directSequence = (await executeCategoryOperation(model.category, model.operations.boundedShortExact, input)).value;
        const direct = (await executeCategoryOperation(model.category, model.operations.boundedLongExact, directSequence)).value;
        const references = (await executeCategoryOperation(model.category, model.operations.snakeReferences, direct)).value;
        const builder = createCategoricalProgramBuilder('long-exact.complete', 'v1');
        const initial = builder.input('sequence-input', model.operations.boundedShortExact.input);
        const sequence = builder.operation('sequence', model.operations.boundedShortExact, initial);
        const whole = builder.operation('long-exact', model.operations.boundedLongExact, sequence);
        const snakes = builder.operation('snake-references', model.operations.snakeReferences, whole);
        const compilation = compileAlgebraPolynomialFreydLongExactProgram(model, builder.build([
            { id: 'sequence', value: sequence }, { id: 'long-exact', value: whole }, { id: 'snake-references', value: snakes }
        ]));
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph, engine: createAlgebraPolynomialFreydLongExactEngine(model),
            inputs: [{ id: 'sequence-input', value: input }]
        });
        const actualSequence = execution.outputs[0].value as typeof directSequence;
        const actual = execution.outputs[1].value as typeof direct;
        const actualReferences = execution.outputs[2].value as typeof references;
        assert.equal(serializeAlgebraPolynomialFreydBoundedShortExactSequence(actualSequence),
            serializeAlgebraPolynomialFreydBoundedShortExactSequence(directSequence));
        assert.equal(serializeAlgebraPolynomialFreydBoundedLongExactHomology(actual),
            serializeAlgebraPolynomialFreydBoundedLongExactHomology(direct));
        assert.equal(serializeAlgebraPolynomialFreydLongExactSnakeReferences(actualReferences),
            serializeAlgebraPolynomialFreydLongExactSnakeReferences(references));
        assert.equal(actual.sequence, actualSequence);
        assert.equal(actualReferences.result, actual);
        actualReferences.sequences.forEach((value, degree) => {
            assert.equal(value.connecting, actual.windows[degree].connecting.trace.snake);
            assert.equal(value.arrows.length, 5);
            assert.equal(value.pairs.length, 4);
        });
        assert.equal(compilation.graph.nodes.length, 3);
        assert.deepEqual(compilation.nodes.map(node => node.selectedMethodKind), ['derived', 'derived', 'derived']);
    });

    it('lowers retained window/connecting observations without rebuilding their owners', async () => {
        const source = fixture();
        const model = algebraPolynomialFreydLongExactCategoryModel(source.ring);
        const result = algebraPolynomialFreydBoundedLongExactHomology(source);
        const input = { result, degree: 1 };
        const directWindow = (await executeCategoryOperation(model.category, model.operations.windowAt, input)).value;
        const directConnecting = (await executeCategoryOperation(model.category, model.operations.windowConnecting, directWindow)).value;
        const directSnake = (await executeCategoryOperation(model.category, model.operations.connectingSnake, directConnecting)).value;
        const directExact = (await executeCategoryOperation(model.category, model.operations.snakeExactSequence, directSnake)).value;
        const builder = createCategoricalProgramBuilder('long-exact.retained-window', 'v1');
        const initial = builder.input('window-input', model.operations.windowAt.input);
        const window = builder.operation('window', model.operations.windowAt, initial);
        const connecting = builder.operation('connecting', model.operations.windowConnecting, window);
        const snake = builder.operation('snake', model.operations.connectingSnake, connecting);
        const exact = builder.operation('exact-snake', model.operations.snakeExactSequence, snake);
        const compilation = compileAlgebraPolynomialFreydLongExactProgram(model, builder.build([
            { id: 'window', value: window }, { id: 'connecting', value: connecting }, { id: 'exact-snake', value: exact }
        ]));
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph, engine: createAlgebraPolynomialFreydLongExactEngine(model),
            inputs: [{ id: 'window-input', value: input }]
        });
        assert.equal(execution.outputs[0].value, result.windows[1]);
        assert.equal(execution.outputs[1].value, result.windows[1].connecting);
        assert.equal(serializeAlgebraPolynomialFreydHomologyWindow(execution.outputs[0].value as typeof directWindow),
            serializeAlgebraPolynomialFreydHomologyWindow(directWindow));
        assert.equal(serializeAlgebraPolynomialFreydHomologyConnecting(execution.outputs[1].value as typeof directConnecting),
            serializeAlgebraPolynomialFreydHomologyConnecting(directConnecting));
        assert.equal(serializeAlgebraPolynomialFreydSnakeExactSequence(execution.outputs[2].value as typeof directExact),
            serializeAlgebraPolynomialFreydSnakeExactSequence(directExact));
        assert.deepEqual(compilation.nodes.map(node => node.selectedMethodKind), ['primitive', 'primitive', 'primitive', 'derived']);
    });

    it('exposes independent connecting and window construction as categorical operations', async () => {
        const sequence = fixture();
        const model = algebraPolynomialFreydLongExactCategoryModel(sequence.ring);
        const input = { sequence, degree: 1 };
        const connecting = (await executeCategoryOperation(model.category, model.operations.homologyConnecting, input)).value;
        const window = (await executeCategoryOperation(model.category, model.operations.homologyWindow, input)).value;
        assert.equal(serializeAlgebraPolynomialFreydHomologyConnecting(connecting),
            serializeAlgebraPolynomialFreydHomologyConnecting(window.connecting));
        assert.equal(window.isExact, true);
        const builder = createCategoricalProgramBuilder('long-exact.independent-operations', 'v1');
        const initial = builder.input('degree-input', model.operations.homologyConnecting.input);
        const connectingNode = builder.operation('connecting', model.operations.homologyConnecting, initial);
        const windowNode = builder.operation('window', model.operations.homologyWindow, initial);
        const compilation = compileAlgebraPolynomialFreydLongExactProgram(model, builder.build([
            { id: 'connecting', value: connectingNode }, { id: 'window', value: windowNode }
        ]));
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph, engine: createAlgebraPolynomialFreydLongExactEngine(model),
            inputs: [{ id: 'degree-input', value: input }]
        });
        assert.equal(serializeAlgebraPolynomialFreydHomologyConnecting(execution.outputs[0].value as typeof connecting),
            serializeAlgebraPolynomialFreydHomologyConnecting(connecting));
        assert.equal(serializeAlgebraPolynomialFreydHomologyWindow(execution.outputs[1].value as typeof window),
            serializeAlgebraPolynomialFreydHomologyWindow(window));
    });

    it('does not treat an unsupported connecting-method trace as the snake reference view', async () => {
        const sequence = fixture();
        const model = algebraPolynomialFreydLongExactCategoryModel(sequence.ring);
        const value = (await executeCategoryOperation(model.category, model.operations.homologyConnecting, { sequence, degree: 1 })).value;
        const unsupported = { ...value, trace: { ...value.trace, kind: 'another-method' } };
        await assert.rejects(() => executeCategoryOperation(model.category, model.operations.connectingSnake, unsupported));
    });

    it('rejects foreign rings, malformed degree data, and incompatible graph schemas', () => {
        const sequence = fixture();
        const model = algebraPolynomialFreydLongExactCategoryModel(sequence.ring);
        const foreign = fixture('two', 'y');
        assert.throws(() => model.operations.boundedShortExact.input.normalize(sequenceInput(foreign), 'foreign'));
        assert.throws(() => model.operations.boundedLongExact.input.normalize(foreign, 'foreign'));
        assert.throws(() => model.operations.homologyConnecting.input.normalize({ sequence, degree: 0.5 }, 'degree'));
        assert.throws(() => model.operations.boundedLongExact.input.normalize({ ...sequence, kind: 'wrong' }, 'kind'));
        const builder = createCategoricalProgramBuilder('long-exact.bad-schema', 'v1');
        const input = builder.input('sequence', model.operations.boundedLongExact.input);
        assert.throws(() => builder.operation('bad', model.operations.homologyConnecting, input as never),
            (error: unknown) => error instanceof AlgebraCategoricalProgramError && error.code === 'SCHEMA_MISMATCH');
    });

    it('rejects a reference family whose connecting-owner order has been changed', async () => {
        const sequence = fixture();
        const model = algebraPolynomialFreydLongExactCategoryModel(sequence.ring);
        const whole = algebraPolynomialFreydBoundedLongExactHomology(sequence);
        const result = (await executeCategoryOperation(model.category, model.operations.snakeReferences, whole)).value;
        assert.throws(() => serializeAlgebraPolynomialFreydLongExactSnakeReferences({
            ...result, sequences: [...result.sequences].reverse()
        }));
    });
});
