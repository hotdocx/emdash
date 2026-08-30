/** Focused CAS-CATEGORY-5A core registry tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { defineAlgebraRuntimeSchema } from '../src/v3_2/algebra_engine';
import { RATIONAL_DOMAIN, algebraRationalText } from '../src/v3_2/algebra_exact';
import {
    algebraMatrix,
    algebraMatrixSpace,
    algebraZeroMatrix
} from '../src/v3_2/algebra_matrix';
import {
    algebraFreeModule,
    algebraModuleMorphism
} from '../src/v3_2/algebra_module';
import {
    AlgebraCategoryError,
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory,
    executeCategoryOperation,
    planCategoryOperation
} from '../src/v3_2/algebra_category';
import {
    algebraModuleComputableCategory,
    algebraRingComputableCategory
} from '../src/v3_2/algebra_category_instances';

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

    it('instantiates a ring as a strict one-object computable category', () => {
        const category = algebraRingComputableCategory(RATIONAL_DOMAIN);
        const object = category.source(RATIONAL_DOMAIN.one);
        assert.ok(category.equalObjects(object, category.target(RATIONAL_DOMAIN.zero)));
        assert.equal(
            algebraRationalText(category.identityMorphism(object)),
            '1'
        );
        assert.equal(
            algebraRationalText(category.compose(
                RATIONAL_DOMAIN.normalize('2/3'),
                RATIONAL_DOMAIN.normalize('9/4')
            )),
            '3/2'
        );
        assert.equal(category.operations.methods.length, 0);
    });

    it('instantiates presented modules with whole and derived kernel/cokernel operations', async () => {
        const source = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const morphism = algebraModuleMorphism(
            source,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '0'], ['0', '0']]
            ),
            algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 0, 0))
        );
        const runtime = algebraModuleComputableCategory(RATIONAL_DOMAIN);
        const category = runtime.category;
        assert.ok(category.equalObjects(category.source(morphism), source));
        assert.ok(category.equalMorphisms(
            category.compose(category.identityMorphism(target), morphism),
            morphism
        ));
        const kernel = await executeCategoryOperation(
            category as never,
            runtime.operations.kernel,
            morphism
        );
        const kernelObject = await executeCategoryOperation(
            category as never,
            runtime.operations.kernelObject,
            morphism
        );
        assert.equal(kernel.value.object.generators, 1);
        assert.equal(kernelObject.value.generators, 1);
        assert.equal(kernelObject.plan.method.kind, 'derived');
        assert.equal(kernelObject.plan.prerequisites[0].operation.id,
            runtime.operations.kernel.id);

        const cokernel = await executeCategoryOperation(
            category as never,
            runtime.operations.cokernel,
            morphism
        );
        const cokernelObject = await executeCategoryOperation(
            category as never,
            runtime.operations.cokernelObject,
            morphism
        );
        assert.equal(cokernel.value.object.relations.parent.columns, 2);
        assert.equal(cokernelObject.value.relations.parent.columns, 2);
        assert.equal(cokernelObject.plan.method.kind, 'derived');
    });
});
