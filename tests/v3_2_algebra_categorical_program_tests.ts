/** Focused CAS-COMPILER-6A staged categorical-program tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_INTEGER_SCHEMA,
    algebraIntegerText
} from '../src/v3_2/algebra_exact';
import {
    ALGEBRA_INTEGER_NEGATE_OPERATION,
    ALGEBRA_EXACT_REFERENCE_IMPLEMENTATIONS
} from '../src/v3_2/algebra_reference_operations';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';
import { executeAlgebraComputationGraph } from '../src/v3_2/algebra_graph';
import {
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory
} from '../src/v3_2/algebra_category';
import {
    AlgebraCategoricalProgramError,
    compileCategoricalProgram,
    createCategoricalProgramBuilder
} from '../src/v3_2/algebra_categorical_program';
import { ALGEBRA_BASE_DOCTRINES } from '../src/v3_2/algebra_doctrine';
import {
    additiveClosureConstructor,
    buildCategoricalTower,
    freydConstructor
} from '../src/v3_2/algebra_tower';

const categoryNegate = defineCategoryOperation({
    id: 'fixture.compiler.integer-negate',
    revision: 'v1',
    input: ALGEBRA_INTEGER_SCHEMA,
    output: ALGEBRA_INTEGER_SCHEMA
});

const category = defineComputableCategory({
    id: 'fixture.compiler.category',
    revision: 'v1',
    objectSchema: ALGEBRA_INTEGER_SCHEMA,
    morphismSchema: ALGEBRA_INTEGER_SCHEMA,
    operations: createCategoryOperationRegistry([
        defineCategoryMethod({
            id: 'fixture.compiler.negate-method',
            operation: categoryNegate,
            kind: 'primitive',
            execute: value => ({ ...value, value: -value.value })
        })
    ]),
    source: value => value,
    target: value => value,
    identityMorphism: value => value,
    compose: (after, before) => ({ ...after, value: after.value + before.value }),
    equalObjects: (left, right) => left.value === right.value,
    equalMorphisms: (left, right) => left.value === right.value
});

const emptyTower = buildCategoricalTower(
    'fixture.compiler.empty-tower',
    ALGEBRA_BASE_DOCTRINES,
    'category',
    []
);

const compilerError = (code: AlgebraCategoricalProgramError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraCategoricalProgramError);
        assert.equal(error.code, code);
        return true;
    };

describe('v3.2 retained categorical-program lowering', () => {
    it('lowers and executes a retained double-negation categorical program', async () => {
        const builder = createCategoricalProgramBuilder(
            'fixture.compiler.double-negate',
            'v1'
        );
        const input = builder.input('value', ALGEBRA_INTEGER_SCHEMA);
        const negative = builder.operation('negative', categoryNegate, input);
        const restored = builder.operation('restored', categoryNegate, negative);
        const program = builder.build([{ id: 'result', value: restored }]);
        const compilation = compileCategoricalProgram({
            program,
            category: category as never,
            tower: emptyTower,
            lowerings: [{
                categoryOperation: categoryNegate as never,
                algebraOperation: ALGEBRA_INTEGER_NEGATE_OPERATION as never
            }]
        });
        assert.equal(compilation.nodes.length, 2);
        assert.equal(
            compilation.nodes[0].selectedMethodId,
            'fixture.compiler.negate-method'
        );
        assert.equal(compilation.nodes[0].selectedMethodKind, 'primitive');
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraTypeScriptReferenceEngine({
                implementations: ALGEBRA_EXACT_REFERENCE_IMPLEMENTATIONS
            }),
            inputs: [{ id: 'value', value: '7' }]
        });
        assert.equal(algebraIntegerText(execution.outputs[0].value as never), '7');
        assert.ok(Object.isFrozen(program));
        assert.ok(Object.isFrozen(compilation));
    });

    it('retains tower lowering rules even for an input-only program', () => {
        const tower = buildCategoricalTower(
            'fixture.compiler.module-tower',
            ALGEBRA_BASE_DOCTRINES,
            'preadditive-category',
            [additiveClosureConstructor(), freydConstructor()]
        );
        const builder = createCategoricalProgramBuilder(
            'fixture.compiler.input-only',
            'v1'
        );
        const value = builder.input('value', ALGEBRA_INTEGER_SCHEMA);
        const compilation = compileCategoricalProgram({
            program: builder.build([{ id: 'result', value }]),
            category: category as never,
            tower,
            lowerings: []
        });
        assert.equal(compilation.nodes.length, 0);
        assert.deepEqual(compilation.towerRules.map(rule => rule.id), [
            'additive-closure.matrix-lowering',
            'freyd.presentation-lowering'
        ]);
    });

    it('rejects missing, duplicate, schema-mismatched, and foreign lowerings', () => {
        const builder = createCategoricalProgramBuilder('fixture.compiler.bad', 'v1');
        const input = builder.input('value', ALGEBRA_INTEGER_SCHEMA);
        const output = builder.operation('negative', categoryNegate, input);
        const program = builder.build([{ id: 'result', value: output }]);
        assert.throws(
            () => compileCategoricalProgram({
                program,
                category: category as never,
                tower: emptyTower,
                lowerings: []
            }),
            compilerError('MISSING_LOWERING')
        );
        const lowering = {
            categoryOperation: categoryNegate as never,
            algebraOperation: ALGEBRA_INTEGER_NEGATE_OPERATION as never
        };
        assert.throws(
            () => compileCategoricalProgram({
                program,
                category: category as never,
                tower: emptyTower,
                lowerings: [lowering, lowering]
            }),
            compilerError('DUPLICATE_LOWERING')
        );
        const otherBuilder = createCategoricalProgramBuilder(
            'fixture.compiler.foreign',
            'v1'
        );
        assert.throws(
            () => otherBuilder.operation('foreign-node', categoryNegate, input),
            compilerError('FOREIGN_VALUE')
        );
    });
});
