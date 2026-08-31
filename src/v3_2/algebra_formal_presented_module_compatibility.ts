/** Shared presentation data across formal matrices and the categorical model. */

import {
    algebraFormalMatrixTerm
} from './algebra_formal_finite_module';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPresentedAlgebraModule
} from './algebra_presented_module';
import {
    AlgebraPresentedModuleTowerModel,
    algebraPresentedModuleTowerModel
} from './algebra_presented_module_tower';
import {
    algebraPresentedAlgebraEquals
} from './algebra_presented_algebra';
import {
    KernelExpression
} from './kernel';

export const ALGEBRA_FORMAL_PRESENTED_MODULE_COMPATIBILITY_PROFILE =
    Object.freeze({
        revision: 'emdash-formal-presented-module-compatibility-v1' as const,
        formalRepresentation: 'column-relation-matrix' as const,
        categoricalRepresentation: 'direct-presented-algebra-module-data' as const,
        interpretation: 'representation-only-not-formal-category' as const,
        addsCoreOwner: false as const,
        performsIo: false as const
    });

export interface AlgebraFormalPresentedModuleCompatibility<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_PRESENTED_MODULE_COMPATIBILITY_PROFILE.revision;
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly relationRows: number;
    readonly relationColumns: number;
    readonly formalRelationMatrix: KernelExpression;
    readonly tower: AlgebraPresentedModuleTowerModel<P, C, I>;
    readonly modeledModule: AlgebraPresentedAlgebraModule<P, C, I>;
    readonly restoredModule: AlgebraPresentedAlgebraModule<P, C, I>;
}

export function defineAlgebraFormalPresentedModuleCompatibility<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly module: AlgebraPresentedAlgebraModule<P, C, I>;
}): AlgebraFormalPresentedModuleCompatibility<P, C, I> {
    if (!algebraPresentedAlgebraEquals(
        input.reifier.algebra,
        input.module.freeModule.algebra
    )) {
        throw new Error(
            'Formal reifier and categorical module use different algebras'
        );
    }
    const relationRows = input.module.freeModule.rank;
    const relationColumns = input.module.combinedRelations.generators.length;
    const formalRelationMatrix = algebraFormalMatrixTerm(
        input.reifier,
        input.module.combinedRelations.generators,
        relationRows
    );
    const tower = algebraPresentedModuleTowerModel<P, C, I>();
    const modeledModule = tower.reinterpretation.toModel(input.module);
    const restoredModule = tower.reinterpretation.fromModel(modeledModule);
    if (!sameAlgebraParent(restoredModule, input.module)) {
        throw new Error(
            'Presented-module categorical reinterpretation changed the module'
        );
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_PRESENTED_MODULE_COMPATIBILITY_PROFILE.revision,
        module: input.module,
        relationRows,
        relationColumns,
        formalRelationMatrix,
        tower,
        modeledModule,
        restoredModule
    });
}
