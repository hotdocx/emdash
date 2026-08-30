/**
 * Concrete Freyd(AdditiveClosure(RingCategory(F))) model for field modules.
 *
 * The constructor tower is retained for generic categorical programming, while
 * the executable representation is the direct presentation-matrix model.
 */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraEngine
} from './algebra_engine';
import {
    AlgebraPresentedModule
} from './algebra_module';
import {
    AlgebraModuleComputableCategory,
    algebraModuleComputableCategory
} from './algebra_category_instances';
import {
    AlgebraModuleReferenceOperations,
    algebraModuleReferenceOperations
} from './algebra_module_reference_operations';
import {
    ComputableCategory
} from './algebra_category';
import {
    CategoricalCompilation,
    CategoricalProgram,
    CategoryOperationLowering,
    compileCategoricalProgram
} from './algebra_categorical_program';
import {
    ALGEBRA_BASE_DOCTRINES
} from './algebra_doctrine';
import {
    CategoricalTower,
    ComputationalReinterpretation,
    additiveClosureConstructor,
    buildCategoricalTower,
    defineComputationalReinterpretation,
    freydConstructor
} from './algebra_tower';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';

export const ALGEBRA_FREYD_PROFILE = Object.freeze({
    revision: 'emdash-field-module-freyd-model-v1' as const,
    model: 'Freyd-AdditiveClosure-RingCategory' as const,
    publicRepresentation: 'direct-presentation-matrices' as const,
    runtimeBoxing: false as const,
    proofObligation: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraFieldModuleFreydModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FREYD_PROFILE.revision;
    readonly field: AlgebraFieldDomain<P, C, I>;
    readonly runtime: AlgebraModuleComputableCategory<P, C, I>;
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraPresentedModule<P, C, I>,
        AlgebraPresentedModule<P, C, I>
    >;
    readonly operations: AlgebraModuleReferenceOperations<P, C, I>;
    readonly lowerings: readonly CategoryOperationLowering[];
}

const eraseCategory = <O, M>(
    category: ComputableCategory<O, M>
): ComputableCategory<unknown, unknown> => category as unknown as
    ComputableCategory<unknown, unknown>;

export function algebraFieldModuleFreydModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(field: AlgebraFieldDomain<P, C, I>): AlgebraFieldModuleFreydModel<P, C, I> {
    const suffix = field.parent.identity.id;
    const runtime = algebraModuleComputableCategory(field);
    const tower = buildCategoricalTower(
        `algebra.tower.freyd-modules/${suffix}`,
        ALGEBRA_BASE_DOCTRINES,
        'preadditive-category',
        [additiveClosureConstructor(), freydConstructor()]
    );
    const modelingCategoryId =
        `algebra.category.freyd-additive-closure/${suffix}`;
    const reinterpretation = defineComputationalReinterpretation({
        id: `algebra.reinterpretation.freyd-modules/${suffix}`,
        publicCategoryId: runtime.category.identity.id,
        modelingCategoryId,
        toModel: (value: AlgebraPresentedModule<P, C, I>) => value,
        fromModel: (value: AlgebraPresentedModule<P, C, I>) => value,
        loweringRules: [{
            id: `freyd.direct-presentation/${suffix}`,
            kind: 'reinterpretation',
            source: modelingCategoryId,
            target: runtime.category.identity.id
        }]
    });
    const operations = algebraModuleReferenceOperations(runtime);
    const lowerings = Object.freeze<CategoryOperationLowering[]>([
        Object.freeze({
            categoryOperation: runtime.operations.kernel,
            algebraOperation: operations.kernel
        }) as CategoryOperationLowering,
        Object.freeze({
            categoryOperation: runtime.operations.cokernel,
            algebraOperation: operations.cokernel
        }) as CategoryOperationLowering
    ]);
    return Object.freeze({
        profileRevision: ALGEBRA_FREYD_PROFILE.revision,
        field,
        runtime,
        tower,
        reinterpretation,
        operations,
        lowerings
    });
}

export const compileAlgebraFieldModuleFreydProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraFieldModuleFreydModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: eraseCategory(model.runtime.category),
    tower: model.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.reinterpretation]
});

export const createAlgebraFieldModuleFreydEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraFieldModuleFreydModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.freyd-modules/` +
            model.field.parent.identity.id,
        revision: ALGEBRA_FREYD_PROFILE.revision,
        implementations: model.operations.implementations
    });
