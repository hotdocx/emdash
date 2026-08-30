/** Focused CAS-MODULE-4B1 field-linear presentation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { INTEGER_DOMAIN, RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraIdentityMatrix,
    algebraMatrix,
    algebraMatrixEquals,
    algebraMatrixMultiply,
    algebraMatrixSpace,
    algebraZeroMatrix
} from '../src/v3_2/algebra_matrix';
import {
    ALGEBRA_MODULE_PROFILE,
    AlgebraModuleError,
    algebraFreeModule,
    algebraMatrixSyzygies,
    algebraModuleCokernel,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleKernel,
    algebraModuleMorphism,
    algebraModuleRealization,
    algebraPresentedModule,
    algebraPresentedModuleText
} from '../src/v3_2/algebra_module';

const moduleError = (
    expected: AlgebraModuleError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraModuleError);
    assert.equal(error.code, expected);
    return true;
};

const zeroWitness = (targetRelations: number, sourceRelations: number) =>
    algebraZeroMatrix(algebraMatrixSpace(
        RATIONAL_DOMAIN,
        targetRelations,
        sourceRelations
    ));

describe('v3.2 field-linear presented modules', () => {
    it('models a presentation as the cokernel of a column-relation matrix', () => {
        const relations = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
            [['1'], ['0']]
        );
        const module = algebraPresentedModule(RATIONAL_DOMAIN, 2, relations);
        assert.equal(module.generators, 2);
        assert.equal(module.relations.parent.columns, 1);
        assert.equal(algebraPresentedModuleText(module), 'coker([1]\n[0])');
        assert.equal(
            ALGEBRA_MODULE_PROFILE.presentation,
            'cokernel-of-column-relation-matrix'
        );
        assert.ok(Object.isFrozen(module));
    });

    it('constructs free modules, identities, and composable morphisms', () => {
        const source = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const middle = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const f = algebraModuleMorphism(
            source,
            middle,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '2'], ['0', '1']]
            ),
            zeroWitness(0, 0)
        );
        const g = algebraModuleMorphism(
            middle,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
                [['3', '4']]
            ),
            zeroWitness(0, 0)
        );
        const composite = algebraModuleCompose(g, f);
        assert.ok(algebraMatrixEquals(
            composite.matrix,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
                [['3', '10']]
            )
        ));
        assert.ok(algebraMatrixEquals(
            algebraModuleIdentity(source).matrix,
            algebraIdentityMatrix(RATIONAL_DOMAIN, 2)
        ));
    });

    it('checks the retained relation witness equation', () => {
        const relations = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
            [['1'], ['0']]
        );
        const module = algebraPresentedModule(RATIONAL_DOMAIN, 2, relations);
        const identity = algebraModuleIdentity(module);
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(identity.matrix, module.relations),
            algebraMatrixMultiply(
                module.relations,
                identity.relationWitness
            )
        ));
        assert.throws(
            () => algebraModuleMorphism(
                module,
                module,
                algebraIdentityMatrix(RATIONAL_DOMAIN, 2),
                algebraMatrix(
                    algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1),
                    [['0']]
                )
            ),
            moduleError('MORPHISM_LAW_FAILED')
        );
    });

    it('realizes the quotient with an explicit projection and section', () => {
        const relations = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
            [['1'], ['0']]
        );
        const module = algebraPresentedModule(RATIONAL_DOMAIN, 2, relations);
        const realization = algebraModuleRealization(module);
        assert.equal(realization.dimension, 1);
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(realization.projection, module.relations),
            algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1))
        ));
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(realization.projection, realization.section),
            algebraIdentityMatrix(RATIONAL_DOMAIN, 1)
        ));
    });

    it('computes a free kernel object and inclusion', () => {
        const source = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const morphism = algebraModuleMorphism(
            source,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '0'], ['0', '0']]
            ),
            zeroWitness(0, 0)
        );
        const kernel = algebraModuleKernel(morphism);
        assert.equal(kernel.object.generators, 1);
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(morphism.matrix, kernel.inclusion.matrix),
            algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1))
        ));
    });

    it('constructs the cokernel by adjoining morphism columns as relations', () => {
        const source = algebraFreeModule(RATIONAL_DOMAIN, 1);
        const target = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const morphism = algebraModuleMorphism(
            source,
            target,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
                [['1'], ['0']]
            ),
            zeroWitness(0, 0)
        );
        const cokernel = algebraModuleCokernel(morphism);
        assert.equal(cokernel.object.generators, 2);
        assert.equal(cokernel.object.relations.parent.columns, 1);
        assert.equal(algebraModuleRealization(cokernel.object).dimension, 1);
        assert.ok(algebraMatrixEquals(
            cokernel.projection.matrix,
            algebraIdentityMatrix(RATIONAL_DOMAIN, 2)
        ));
    });

    it('exposes matrix syzygies and rejects non-field presentations', () => {
        const matrix = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
            [['1', '1']]
        );
        const syzygies = algebraMatrixSyzygies(matrix);
        assert.equal(syzygies.nullity, 1);
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(matrix, syzygies.generators),
            algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 1, 1))
        ));
        assert.throws(
            () => algebraPresentedModule(
                INTEGER_DOMAIN as never,
                1
            ),
            moduleError('NON_FIELD_COEFFICIENTS')
        );
        assert.equal(ALGEBRA_MODULE_PROFILE.polynomialModuleGroebner, false);
    });
});
