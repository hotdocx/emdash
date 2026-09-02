/** Focused CAS-DOCTRINE-5B hierarchy and qualification tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { defineAlgebraRuntimeSchema } from '../src/v3_2/algebra_engine';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory
} from '../src/v3_2/algebra_category';
import { algebraModuleComputableCategory } from '../src/v3_2/algebra_category_instances';
import {
    ABELIAN_DOCTRINE,
    ALGEBRA_BASE_DOCTRINES,
    AlgebraDoctrineError,
    COMPUTATIONAL_WEAK_COKERNEL_DOCTRINE,
    COMPUTATIONAL_WEAK_KERNEL_DOCTRINE,
    PREABELIAN_DOCTRINE,
    createDoctrineRegistry,
    defineDoctrine,
    qualifyCategoryDoctrine
} from '../src/v3_2/algebra_doctrine';

const numberSchema = defineAlgebraRuntimeSchema<number>({
    id: 'fixture.doctrine.number',
    revision: 'v1',
    normalize(value: unknown) {
        if (!Number.isSafeInteger(value)) throw new Error('integer expected');
        return value as number;
    }
});

describe('v3.2 operational categorical doctrines', () => {
    it('builds the inherited self-dual pre-Abelian and Abelian hierarchy', () => {
        assert.deepEqual(PREABELIAN_DOCTRINE.parents, ['additive-category']);
        assert.equal(PREABELIAN_DOCTRINE.dual.roles.kernel, 'cokernel');
        assert.equal(PREABELIAN_DOCTRINE.dual.roles.cokernel, 'kernel');
        assert.equal(
            PREABELIAN_DOCTRINE.dual.roles['kernel-embedding'],
            'cokernel-projection'
        );
        assert.equal(
            PREABELIAN_DOCTRINE.dual.roles['kernel-lift'],
            'cokernel-colift'
        );
        assert.equal(ABELIAN_DOCTRINE.dual.roles.image, 'coimage');
        assert.equal(
            ALGEBRA_BASE_DOCTRINES.byId.get('category')?.dual.doctrineId,
            'category'
        );
        assert.equal(
            COMPUTATIONAL_WEAK_KERNEL_DOCTRINE.dual.doctrineId,
            COMPUTATIONAL_WEAK_COKERNEL_DOCTRINE.id
        );
        assert.equal(
            COMPUTATIONAL_WEAK_COKERNEL_DOCTRINE.dual.roles[
                'weak-cokernel-colift'
            ],
            'weak-kernel-lift'
        );
        assert.deepEqual(COMPUTATIONAL_WEAK_KERNEL_DOCTRINE.parents, [
            'additive-category'
        ]);
    });

    it('reports inherited missing roles for the current module category', () => {
        const runtime = algebraModuleComputableCategory(RATIONAL_DOMAIN);
        const qualification = qualifyCategoryDoctrine(
            runtime.category as never,
            ALGEBRA_BASE_DOCTRINES,
            PREABELIAN_DOCTRINE.id,
            [
                { role: 'kernel', operation: runtime.operations.kernel as never },
                { role: 'cokernel', operation: runtime.operations.cokernel as never }
            ]
        );
        assert.equal(qualification.status, 'missing');
        assert.deepEqual(qualification.availableRoles, ['cokernel', 'kernel']);
        assert.deepEqual(qualification.missingRoles, [
            'add-morphisms',
            'biproduct',
            'cokernel-colift',
            'cokernel-object',
            'cokernel-projection',
            'kernel-embedding',
            'kernel-lift',
            'kernel-object',
            'negate-morphism',
            'zero-morphism',
            'zero-object'
        ]);
    });

    it('qualifies a category only when every inherited role is plannable', () => {
        const roles = [
            'zero-morphism', 'add-morphisms', 'negate-morphism',
            'zero-object', 'biproduct',
            'kernel', 'kernel-object', 'kernel-embedding', 'kernel-lift',
            'cokernel', 'cokernel-object', 'cokernel-projection',
            'cokernel-colift',
            'monomorphism-witness', 'epimorphism-witness',
            'lift-along-monomorphism', 'colift-along-epimorphism',
            'image', 'image-object', 'image-embedding',
            'coastriction-to-image',
            'coimage', 'coimage-object', 'coimage-projection',
            'astriction-from-coimage',
            'coimage-image-comparison', 'coimage-image-isomorphism'
        ];
        const operations = roles.map(role => defineCategoryOperation({
            id: `fixture.doctrine.${role}`,
            revision: 'v1',
            input: numberSchema,
            output: numberSchema
        }));
        const methods = operations.map((operation, index) =>
            defineCategoryMethod({
                id: `fixture.doctrine.method-${index}`,
                operation,
                kind: 'primitive',
                execute: value => value
            })
        );
        const category = defineComputableCategory({
            id: 'fixture.doctrine.category',
            revision: 'v1',
            objectSchema: numberSchema,
            morphismSchema: numberSchema,
            operations: createCategoryOperationRegistry(methods),
            source: () => 0,
            target: () => 0,
            identityMorphism: () => 0,
            compose: (after, before) => after + before,
            equalObjects: (left, right) => left === right,
            equalMorphisms: (left, right) => left === right
        });
        const qualification = qualifyCategoryDoctrine(
            category as never,
            ALGEBRA_BASE_DOCTRINES,
            ABELIAN_DOCTRINE.id,
            roles.map((role, index) => ({ role, operation: operations[index] as never }))
        );
        assert.equal(qualification.status, 'qualified');
        assert.equal(qualification.missingRoles.length, 0);
        assert.deepEqual(qualification.requiredRoles, [...roles].sort());
        assert.ok(Object.isFrozen(qualification));
    });

    it('rejects doctrine cycles, non-involutive duals, and duplicate bindings', () => {
        assert.throws(
            () => createDoctrineRegistry([
                defineDoctrine({ id: 'fixture.a', parents: ['fixture.b'] }),
                defineDoctrine({ id: 'fixture.b', parents: ['fixture.a'] })
            ]),
            error => {
                assert.ok(error instanceof AlgebraDoctrineError);
                assert.equal(error.code, 'HIERARCHY_CYCLE');
                return true;
            }
        );
        assert.throws(
            () => createDoctrineRegistry([
                defineDoctrine({
                    id: 'fixture.dual-a',
                    dual: { doctrineId: 'fixture.dual-b' }
                }),
                defineDoctrine({ id: 'fixture.dual-b' })
            ]),
            error => {
                assert.ok(error instanceof AlgebraDoctrineError);
                assert.equal(error.code, 'INVALID_DUAL');
                return true;
            }
        );
    });
});
