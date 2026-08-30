/** Focused CAS-TOWER-5C constructor/tower/reinterpretation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraMatrix, algebraMatrixEquals, algebraMatrixSpace, algebraZeroMatrix } from '../src/v3_2/algebra_matrix';
import { algebraFreeModule, algebraModuleMorphism } from '../src/v3_2/algebra_module';
import { algebraModuleComputableCategory } from '../src/v3_2/algebra_category_instances';
import { ALGEBRA_BASE_DOCTRINES } from '../src/v3_2/algebra_doctrine';
import {
    AlgebraTowerError,
    additiveClosureConstructor,
    buildCategoricalTower,
    cofreydConstructor,
    defineCategoryConstructorDescriptor,
    defineComputationalReinterpretation,
    freydConstructor,
    oppositeComputableCategory,
    oppositeConstructorDescriptor
} from '../src/v3_2/algebra_tower';

const towerError = (code: AlgebraTowerError['code']) => (error: unknown) => {
    assert.ok(error instanceof AlgebraTowerError);
    assert.equal(error.code, code);
    return true;
};

describe('v3.2 categorical constructor towers', () => {
    it('retains AdditiveClosure and Freyd layers without overstating doctrine', () => {
        const tower = buildCategoricalTower(
            'fixture.module-tower',
            ALGEBRA_BASE_DOCTRINES,
            'preadditive-category',
            [additiveClosureConstructor(), freydConstructor()]
        );
        assert.equal(tower.outputDoctrineId, 'additive-category');
        assert.deepEqual(tower.introducedRoles, [
            'biproduct',
            'cokernel',
            'zero-object'
        ]);
        assert.deepEqual(tower.constructors.map(value => value.id), [
            'category-constructor.additive-closure',
            'category-constructor.freyd'
        ]);
        assert.equal(tower.loweringRules.length, 2);
        assert.ok(Object.isFrozen(tower));
    });

    it('records Freyd/CoFreyd and doctrine-opposite dual metadata', () => {
        assert.equal(
            freydConstructor().dualConstructorId,
            cofreydConstructor().id
        );
        assert.equal(
            cofreydConstructor().dualConstructorId,
            freydConstructor().id
        );
        const opposite = oppositeConstructorDescriptor(
            ALGEBRA_BASE_DOCTRINES,
            'preabelian-category'
        );
        assert.equal(opposite.outputDoctrineId, 'preabelian-category');
        assert.equal(opposite.loweringRules[0].kind, 'dual-operation');
    });

    it('rejects doctrine-incompatible towers and duplicate lowering rules', () => {
        assert.throws(
            () => buildCategoricalTower(
                'fixture.invalid-tower',
                ALGEBRA_BASE_DOCTRINES,
                'preadditive-category',
                [freydConstructor()]
            ),
            towerError('DOCTRINE_MISMATCH')
        );
        const rule = {
            id: 'fixture.duplicate-rule',
            kind: 'operation-lowering' as const,
            source: 'a',
            target: 'b'
        };
        assert.throws(
            () => defineCategoryConstructorDescriptor({
                id: 'fixture.constructor',
                inputDoctrineId: 'category',
                outputDoctrineId: 'category',
                introducedRoles: [],
                objectLayer: 'object',
                morphismLayer: 'morphism',
                dualConstructorId: 'fixture.constructor',
                loweringRules: [rule, rule]
            }),
            towerError('DUPLICATE_LOWERING_RULE')
        );
    });

    it('executes opposite composition by reversing underlying composition', () => {
        const module = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const witness = algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 0, 0));
        const f = algebraModuleMorphism(
            module,
            module,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '1'], ['0', '1']]
            ),
            witness
        );
        const g = algebraModuleMorphism(
            module,
            module,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '0'], ['1', '1']]
            ),
            witness
        );
        const original = algebraModuleComputableCategory(RATIONAL_DOMAIN).category;
        const opposite = oppositeComputableCategory(original);
        const composite = opposite.compose(
            { kind: 'opposite-morphism', underlying: f },
            { kind: 'opposite-morphism', underlying: g }
        );
        const expected = original.compose(g, f);
        assert.ok(algebraMatrixEquals(
            composite.underlying.matrix,
            expected.matrix
        ));
        assert.ok(opposite.equalObjects(
            opposite.source({ kind: 'opposite-morphism', underlying: f }),
            original.target(f)
        ));
    });

    it('retains explicit public/model reinterpretation and lowering data', () => {
        const runtime = algebraModuleComputableCategory(RATIONAL_DOMAIN).category;
        const reinterpretation = defineComputationalReinterpretation({
            id: 'fixture.presented-module-reinterpretation',
            publicCategoryId: runtime.identity.id,
            modelingCategoryId: 'fixture.freyd-additive-closure-model',
            toModel: value => value,
            fromModel: value => value,
            loweringRules: [{
                id: 'fixture.cancel-model-roundtrip',
                kind: 'reinterpretation',
                source: 'freyd-additive-closure-model',
                target: 'algebra-presented-module'
            }]
        });
        const module = algebraFreeModule(RATIONAL_DOMAIN, 3);
        assert.equal(
            reinterpretation.fromModel(reinterpretation.toModel(module)),
            module
        );
        assert.equal(reinterpretation.loweringRules[0].kind, 'reinterpretation');
        assert.ok(Object.isFrozen(reinterpretation));
    });
});
