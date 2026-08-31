/** Strict semilinear module category, constructor tower, and graph lowering. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraEngine,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    CategoryOperation,
    ComputableCategory,
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory
} from './algebra_category';
import {
    CategoricalCompilation,
    CategoricalProgram,
    CategoryOperationLowering,
    compileCategoricalProgram
} from './algebra_categorical_program';
import { ALGEBRA_BASE_DOCTRINES } from './algebra_doctrine';
import {
    CategoricalTower,
    ComputationalReinterpretation,
    buildCategoricalTower,
    defineCategoryConstructorDescriptor,
    defineComputationalReinterpretation
} from './algebra_tower';
import {
    AlgebraPresentedAlgebraModule
} from './algebra_presented_module';
import {
    AlgebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapApply,
    algebraPresentedAlgebraModuleSemilinearMapCompose,
    algebraPresentedAlgebraModuleSemilinearMapEquals,
    algebraPresentedAlgebraModuleSemilinearMapIdentity
} from './algebra_presented_module_map';
import {
    AlgebraPresentedModuleBaseChange,
    algebraPresentedModuleBaseChange
} from './algebra_presented_module_base_change';
import {
    AlgebraPresentedModuleLocalization,
    algebraPresentedModuleLocalization
} from './algebra_presented_module_localization';
import {
    AlgebraAffineQuasiCoherentCechDiagram,
    algebraAffineQuasiCoherentCechDiagram
} from './algebra_quasicoherent_cech';
import {
    AlgebraPresentedModuleBaseChangeInput,
    AlgebraPresentedModuleLocalizationInput,
    AlgebraPresentedModuleMapApplyInput,
    AlgebraPresentedModuleReferenceOperations,
    AlgebraQuasiCoherentCechInput,
    algebraPresentedModuleReferenceOperations
} from './algebra_presented_module_reference_operations';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';

export const ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE = Object.freeze({
    revision: 'emdash-presented-module-category-tower-v1' as const,
    category: 'strict-semilinear-total-category' as const,
    doctrine: 'category' as const,
    additiveAcrossVaryingRings: false as const,
    runtimeRepresentation: 'direct-presented-module-data' as const,
    runtimeBoxing: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

const constructor = (
    id: string,
    objectLayer: string,
    morphismLayer: string,
    role: string,
    ruleId: string,
    target: string
) => defineCategoryConstructorDescriptor({
    id,
    inputDoctrineId: 'category',
    outputDoctrineId: 'category',
    introducedRoles: [role],
    objectLayer,
    morphismLayer,
    dualConstructorId: id,
    loweringRules: [{
        id: ruleId,
        kind: 'operation-lowering',
        source: objectLayer,
        target
    }]
});

export const presentedAlgebraModulesConstructor = () => constructor(
    'category-constructor.presented-algebra-modules',
    'quotient-algebra-module-presentation',
    'relation-checked-semilinear-map',
    'presented-algebra-module',
    'presented-module.presentation-to-reduced-module-basis',
    'reduced-polynomial-module-presentation'
);

export const presentedModuleBaseChangeConstructor = () => constructor(
    'category-constructor.presented-module-base-change',
    'module-over-source-algebra',
    'canonical-semilinear-unit',
    'module-base-change',
    'presented-module.base-change-to-transported-relations',
    'transported-module-presentation'
);

export const affineQuasiCoherentModuleConstructor = () => constructor(
    'category-constructor.affine-quasicoherent-module',
    'affine-scheme-with-coordinate-module',
    'basic-open-semilinear-restriction',
    'affine-quasicoherent-module',
    'presented-module.quasicoherent-to-localized-values',
    'localized-module-values'
);

export const quasiCoherentCechConstructor = () => constructor(
    'category-constructor.quasicoherent-cech',
    'ordered-module-valued-cech-simplex',
    'signed-semilinear-face',
    'module-cech-diagram',
    'presented-module.cech-to-product-localizations',
    'varying-ring-module-cech-diagram'
);

export interface AlgebraPresentedModuleTowerModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraPresentedAlgebraModule<P, C, I>,
        AlgebraPresentedAlgebraModule<P, C, I>
    >;
}

export function algebraPresentedModuleTowerModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraPresentedModuleTowerModel<P, C, I> {
    const tower = buildCategoricalTower(
        'algebra.tower.presented-modules-affine-descent',
        ALGEBRA_BASE_DOCTRINES,
        'category',
        [
            presentedAlgebraModulesConstructor(),
            presentedModuleBaseChangeConstructor(),
            affineQuasiCoherentModuleConstructor(),
            quasiCoherentCechConstructor()
        ]
    );
    return Object.freeze({
        tower,
        reinterpretation: defineComputationalReinterpretation({
            id: 'algebra.reinterpretation.presented-algebra-modules',
            publicCategoryId: 'algebra.category.presented-module-total',
            modelingCategoryId: 'algebra.category.presented-module-model',
            toModel: (value: AlgebraPresentedAlgebraModule<P, C, I>) => value,
            fromModel: (value: AlgebraPresentedAlgebraModule<P, C, I>) => value,
            loweringRules: [{
                id: 'presented-module.direct-representation',
                kind: 'reinterpretation',
                source: 'algebra.category.presented-module-model',
                target: 'algebra.category.presented-module-total'
            }]
        })
    });
}

export interface AlgebraPresentedModuleCategoryOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly mapApply: CategoryOperation<
        AlgebraPresentedModuleMapApplyInput<P, C, I>,
        ReturnType<typeof algebraPresentedAlgebraModuleSemilinearMapApply<P, C, I>>
    >;
    readonly baseChange: CategoryOperation<
        AlgebraPresentedModuleBaseChangeInput<P, C, I>,
        AlgebraPresentedModuleBaseChange<P, C, I>
    >;
    readonly localization: CategoryOperation<
        AlgebraPresentedModuleLocalizationInput<P, C, I>,
        AlgebraPresentedModuleLocalization<P, C, I>
    >;
    readonly cech: CategoryOperation<
        AlgebraQuasiCoherentCechInput<P, C, I>,
        AlgebraAffineQuasiCoherentCechDiagram<P, C, I>
    >;
}

export interface AlgebraPresentedModuleCategoricalModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraPresentedAlgebraModule<P, C, I>,
        AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>
    >;
    readonly operations: AlgebraPresentedModuleCategoryOperations<P, C, I>;
    readonly native: AlgebraPresentedModuleReferenceOperations<P, C, I>;
    readonly towerModel: AlgebraPresentedModuleTowerModel<P, C, I>;
    readonly lowerings: readonly CategoryOperationLowering[];
}

export function algebraPresentedModuleCategoricalModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraPresentedModuleCategoricalModel<P, C, I> {
    const native = algebraPresentedModuleReferenceOperations<P, C, I>();
    const mapApply = defineCategoryOperation({
        id: 'algebra.category.presented-module.map-apply',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        input: native.mapApplyInputSchema,
        output: native.mapApply.output
    });
    const baseChange = defineCategoryOperation({
        id: 'algebra.category.presented-module.base-change',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        input: native.baseChangeInputSchema,
        output: native.baseChange.output
    });
    const localization = defineCategoryOperation({
        id: 'algebra.category.presented-module.localization',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        input: native.localizationInputSchema,
        output: native.localization.output
    });
    const cech = defineCategoryOperation({
        id: 'algebra.category.presented-module.quasicoherent-cech',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        input: native.cechInputSchema,
        output: native.cech.output
    });
    const objectSchema = defineAlgebraRuntimeSchema<
        AlgebraPresentedAlgebraModule<P, C, I>
    >({
        id: 'algebra.category.presented-module-object',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' ||
                value === null ||
                (value as { kind?: unknown }).kind !== 'presented-algebra-module'
            ) throw new Error(`presented module expected at ${path}`);
            return value as AlgebraPresentedAlgebraModule<P, C, I>;
        }
    });
    const morphismSchema = defineAlgebraRuntimeSchema<
        AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>
    >({
        id: 'algebra.category.presented-module-semilinear-map',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' ||
                value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-presented-module-semilinear-map'
            ) throw new Error(`presented semilinear map expected at ${path}`);
            return value as AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
        }
    });
    const operations = Object.freeze({ mapApply, baseChange, localization, cech });
    const category = defineComputableCategory({
        id: 'algebra.category.presented-module-total',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        objectSchema,
        morphismSchema,
        operations: createCategoryOperationRegistry([
            defineCategoryMethod({
                id: 'algebra.presented-module.map-apply.primitive',
                operation: mapApply,
                kind: 'primitive',
                execute: input => algebraPresentedAlgebraModuleSemilinearMapApply(
                    input.map,
                    input.element
                )
            }),
            defineCategoryMethod({
                id: 'algebra.presented-module.base-change.primitive',
                operation: baseChange,
                kind: 'primitive',
                execute: input => algebraPresentedModuleBaseChange(
                    input.scalarMap,
                    input.module
                )
            }),
            defineCategoryMethod({
                id: 'algebra.presented-module.localization.primitive',
                operation: localization,
                kind: 'primitive',
                execute: input => algebraPresentedModuleLocalization(
                    input.module,
                    input.element
                )
            }),
            defineCategoryMethod({
                id: 'algebra.presented-module.cech.primitive',
                operation: cech,
                kind: 'primitive',
                execute: input => algebraAffineQuasiCoherentCechDiagram(
                    input.presentation,
                    input.cover
                )
            })
        ]),
        source: morphism => morphism.source,
        target: morphism => morphism.target,
        identityMorphism: algebraPresentedAlgebraModuleSemilinearMapIdentity,
        compose: algebraPresentedAlgebraModuleSemilinearMapCompose,
        equalObjects: (left, right) => sameAlgebraParent(left, right),
        equalMorphisms: algebraPresentedAlgebraModuleSemilinearMapEquals
    });
    const towerModel = algebraPresentedModuleTowerModel<P, C, I>();
    return Object.freeze({
        category,
        operations,
        native,
        towerModel,
        lowerings: Object.freeze([
            { categoryOperation: mapApply, algebraOperation: native.mapApply },
            { categoryOperation: baseChange, algebraOperation: native.baseChange },
            {
                categoryOperation: localization,
                algebraOperation: native.localization
            },
            { categoryOperation: cech, algebraOperation: native.cech }
        ] as CategoryOperationLowering[])
    });
}

export const compileAlgebraPresentedModuleProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPresentedModuleCategoricalModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: model.category as unknown as ComputableCategory<unknown, unknown>,
    tower: model.towerModel.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.towerModel.reinterpretation]
});

export const createAlgebraPresentedModuleEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPresentedModuleCategoricalModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: 'algebra.typescript-reference.presented-modules',
        revision: ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.revision,
        implementations: model.native.implementations
    });
