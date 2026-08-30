/** Focused CAS-CATEGORY-5A core registry tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { defineAlgebraRuntimeSchema } from '../src/v3_2/algebra_engine';
import {
    AlgebraCategoryError,
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory,
    executeCategoryOperation,
    planCategoryOperation
} from '../src/v3_2/algebra_category';

const numberSchema = defineAlgebraRuntimeSchema<number>({
    id: 'fixture.category.number',
    revision: 'v1',
    normalize(value: unknown) {
        if (!Number.isSafeInteger(value)) throw new Error('safe integer expected');
        return value as number;
    }
});

const double = defineCategoryOperation({
    id: 'fixture.category.double',
    revision: 'v1',
    input: numberSchema,
    output: numberSchema
});
const quadruple = defineCategoryOperation({
    id: 'fixture.category.quadruple',
    revision: 'v1',
    input: numberSchema,
    output: numberSchema
});

const categoryError = (code: AlgebraCategoryError['code']) => (error: unknown) => {
    assert.ok(error instanceof AlgebraCategoryError);
    assert.equal(error.code, code);
    return true;
};

describe('v3.2 computable-category operation registry', () => {
    it('selects the least-weight deterministic primitive or derived method', async () => {
        const registry = createCategoryOperationRegistry([
            defineCategoryMethod({
                id: 'fixture.double.primitive',
                operation: double,
                kind: 'primitive',
                weight: 2,
                execute: value => value * 2
            }),
            defineCategoryMethod({
                id: 'fixture.quadruple.expensive',
                operation: quadruple,
                kind: 'primitive',
                weight: 10,
                execute: value => value * 4
            }),
            defineCategoryMethod({
                id: 'fixture.quadruple.derived',
                operation: quadruple,
                kind: 'derived',
                weight: 1,
                prerequisites: [double],
                execute: async (value, context) => context.call(
                    double,
                    await context.call(double, value)
                )
            })
        ]);
        const plan = planCategoryOperation(registry, quadruple);
        assert.equal(plan.method.id, 'fixture.quadruple.derived');
        assert.equal(plan.totalWeight, 3);
        assert.equal(plan.prerequisites[0].method.id, 'fixture.double.primitive');
        const category = defineComputableCategory({
            id: 'fixture.number-category',
            revision: 'v1',
            objectSchema: numberSchema,
            morphismSchema: numberSchema,
            operations: registry,
            source: () => 0,
            target: () => 0,
            identityMorphism: () => 1,
            compose: (after, before) => after * before,
            equalObjects: (left, right) => left === right,
            equalMorphisms: (left, right) => left === right
        });
        const result = await executeCategoryOperation(category, quadruple, 3);
        assert.equal(result.value, 12);
        assert.ok(Object.isFrozen(category));
        assert.ok(Object.isFrozen(plan));
    });

    it('rejects unavailable operations, duplicate methods, and cycles', () => {
        const empty = createCategoryOperationRegistry([]);
        assert.throws(
            () => planCategoryOperation(empty, double),
            categoryError('UNAVAILABLE_OPERATION')
        );
        const method = defineCategoryMethod({
            id: 'fixture.duplicate',
            operation: double,
            kind: 'primitive',
            execute: value => value * 2
        });
        assert.throws(
            () => createCategoryOperationRegistry([method, method]),
            categoryError('DUPLICATE_METHOD')
        );
        const cycle = createCategoryOperationRegistry([
            defineCategoryMethod({
                id: 'fixture.double.cycle',
                operation: double,
                kind: 'derived',
                prerequisites: [quadruple],
                execute: value => value
            }),
            defineCategoryMethod({
                id: 'fixture.quadruple.cycle',
                operation: quadruple,
                kind: 'derived',
                prerequisites: [double],
                execute: value => value
            })
        ]);
        assert.throws(
            () => planCategoryOperation(cycle, double),
            categoryError('DERIVATION_CYCLE')
        );
    });
});
