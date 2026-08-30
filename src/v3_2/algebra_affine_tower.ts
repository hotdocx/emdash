/** Affine constructor tower, direct reinterpretation, and staged bindings. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraEngine } from './algebra_engine';
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
    defineComputationalReinterpretation,
    oppositeConstructorDescriptor
} from './algebra_tower';
import {
    AlgebraAffineMorphism,
    AlgebraAffineScheme,
    algebraAffineSchemeComputableCategory
} from './algebra_affine_scheme';
import {
    AlgebraAffineCoverOperationInput,
    AlgebraAffineReferenceOperations,
    AlgebraFiberProductOperationInput,
    algebraAffineReferenceOperations
} from './algebra_affine_reference_operations';
import { AlgebraAffineFiberProduct, algebraAffineFiberProduct } from './algebra_tensor';
import { AlgebraAffineCover, algebraAffineCover } from './algebra_cech';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';

export const ALGEBRA_AFFINE_TOWER_PROFILE = Object.freeze({
    revision: 'emdash-affine-category-tower-v1' as const,
    runtimeRepresentation: 'direct-presented-affine-data' as const,
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

export const affinePresentedAlgebrasConstructor = () => constructor(
    'category-constructor.presented-algebras',
    'finite-generator-relation-presentation',
    'generator-image-map',
    'presented-algebra',
    'affine.presentation-to-quotient',
    'canonical-quotient-ring'
);

export const affineSpecConstructor = () => constructor(
    'category-constructor.affine-spec',
    'formal-affine-spectrum',
    'opposite-algebra-map',
    'affine-spectrum',
    'affine.spec-to-direct-scheme',
    'direct-affine-scheme'
);

export const affinePrincipalOpensConstructor = () => constructor(
    'category-constructor.principal-opens',
    'principal-open-chart',
    'localization-restriction',
    'principal-open',
    'affine.open-to-localization',
    'adjoined-inverse-localization'
);

export const affineFiniteCoversConstructor = () => constructor(
    'category-constructor.finite-affine-covers',
    'finite-open-cover',
    'cover-refinement',
    'finite-affine-cover',
    'affine.cover-to-localized-charts',
    'affine-basic-open-charts'
);

export const affineCechConstructor = () => constructor(
    'category-constructor.affine-cech-nerve',
    'ordered-cech-simplex',
    'signed-face-restriction',
    'cech-nerve',
    'affine.cech-to-product-localizations',
    'product-localization-nerve'
);

export interface AlgebraAffineTowerModel<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraAffineScheme<P, C, I>,
        AlgebraAffineScheme<P, C, I>
    >;
}

export function algebraAffineTowerModel<P extends AlgebraParent, C extends AlgebraElement<P>, I>():
    AlgebraAffineTowerModel<P, C, I> {
    const tower = buildCategoricalTower(
        'algebra.tower.affine-geometry',
        ALGEBRA_BASE_DOCTRINES,
        'category',
        [
            affinePresentedAlgebrasConstructor(),
            oppositeConstructorDescriptor(ALGEBRA_BASE_DOCTRINES, 'category'),
            affineSpecConstructor(),
            affinePrincipalOpensConstructor(),
            affineFiniteCoversConstructor(),
            affineCechConstructor()
        ]
    );
    return Object.freeze({
        tower,
        reinterpretation: defineComputationalReinterpretation({
            id: 'algebra.reinterpretation.affine-schemes',
            publicCategoryId: 'algebra.category.affine-schemes',
            modelingCategoryId: 'algebra.category.affine-model',
            toModel: (value: AlgebraAffineScheme<P, C, I>) => value,
            fromModel: (value: AlgebraAffineScheme<P, C, I>) => value,
            loweringRules: [{
                id: 'affine.direct-scheme-representation',
                kind: 'reinterpretation',
                source: 'algebra.category.affine-model',
                target: 'algebra.category.affine-schemes'
            }]
        })
    });
}

export interface AlgebraAffineCategoryOperations<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly fiberProduct: CategoryOperation<
        AlgebraFiberProductOperationInput<P, C, I>,
        AlgebraAffineFiberProduct<P, C, I>
    >;
    readonly cover: CategoryOperation<
        AlgebraAffineCoverOperationInput<P, C, I>,
        AlgebraAffineCover<P, C, I>
    >;
}

export interface AlgebraAffineCategoricalModel<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly category: ComputableCategory<
        AlgebraAffineScheme<P, C, I>,
        AlgebraAffineMorphism<P, C, I>
    >;
    readonly operations: AlgebraAffineCategoryOperations<P, C, I>;
    readonly native: AlgebraAffineReferenceOperations<P, C, I>;
    readonly towerModel: AlgebraAffineTowerModel<P, C, I>;
    readonly lowerings: readonly CategoryOperationLowering[];
}

export function algebraAffineCategoricalModel<P extends AlgebraParent, C extends AlgebraElement<P>, I>():
    AlgebraAffineCategoricalModel<P, C, I> {
    const base = algebraAffineSchemeComputableCategory<P, C, I>().category;
    const native = algebraAffineReferenceOperations<P, C, I>();
    const fiberProduct = defineCategoryOperation({
        id: 'algebra.category.affine.fiber-product',
        revision: ALGEBRA_AFFINE_TOWER_PROFILE.revision,
        input: native.fiberInputSchema,
        output: native.fiberProduct.output
    });
    const cover = defineCategoryOperation({
        id: 'algebra.category.affine.cover',
        revision: ALGEBRA_AFFINE_TOWER_PROFILE.revision,
        input: native.coverInputSchema,
        output: native.cover.output
    });
    const category = defineComputableCategory({
        id: base.identity.id,
        revision: base.identity.revision,
        objectSchema: base.objectSchema,
        morphismSchema: base.morphismSchema,
        operations: createCategoryOperationRegistry([
            defineCategoryMethod({
                id: 'algebra.affine.fiber-product.primitive',
                operation: fiberProduct,
                kind: 'primitive',
                execute: input => algebraAffineFiberProduct(input.left, input.right)
            }),
            defineCategoryMethod({
                id: 'algebra.affine.cover.primitive',
                operation: cover,
                kind: 'primitive',
                execute: input => algebraAffineCover(
                    input.ambient,
                    input.elements,
                    input.maximumDegree
                )
            })
        ]),
        source: base.source,
        target: base.target,
        identityMorphism: base.identityMorphism,
        compose: base.compose,
        equalObjects: base.equalObjects,
        equalMorphisms: base.equalMorphisms
    });
    const towerModel = algebraAffineTowerModel<P, C, I>();
    return Object.freeze({
        category,
        operations: Object.freeze({ fiberProduct, cover }),
        native,
        towerModel,
        lowerings: Object.freeze([
            { categoryOperation: fiberProduct, algebraOperation: native.fiberProduct },
            { categoryOperation: cover, algebraOperation: native.cover }
        ] as CategoryOperationLowering[])
    });
}

export const compileAlgebraAffineProgram = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    model: AlgebraAffineCategoricalModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: model.category as unknown as ComputableCategory<unknown, unknown>,
    tower: model.towerModel.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.towerModel.reinterpretation]
});

export const createAlgebraAffineEngine = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    model: AlgebraAffineCategoricalModel<P, C, I>
): AlgebraEngine => createAlgebraTypeScriptReferenceEngine({
    id: 'algebra.typescript-reference.affine',
    revision: ALGEBRA_AFFINE_TOWER_PROFILE.revision,
    implementations: model.native.implementations
});
