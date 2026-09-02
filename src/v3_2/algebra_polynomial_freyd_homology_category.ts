/** Category operations and graph lowering for polynomial Freyd homology. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraEngine
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
import {
    ALGEBRA_BASE_DOCTRINES
} from './algebra_doctrine';
import {
    CategoricalTower,
    buildCategoricalTower,
    defineCategoryConstructorDescriptor
} from './algebra_tower';
import {
    AlgebraPolynomialRing
} from './algebra_polynomial';
import {
    AlgebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialFreydAbelianCategoryModel,
    algebraPolynomialFreydAbelianCategoryModel
} from './algebra_polynomial_freyd_abelian_category';
import {
    AlgebraPolynomialFreydChainPair,
    AlgebraPolynomialFreydExactnessAt,
    AlgebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialFreydHomologyChainMap,
    AlgebraPolynomialFreydInducedHomologyMap,
    algebraPolynomialFreydHomologyChainMap,
    algebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_functorial_homology';
import {
    AlgebraPolynomialFreydChainPairInput,
    AlgebraPolynomialFreydHomologyChainMapInput,
    AlgebraPolynomialFreydHomologyReferenceOperations,
    algebraPolynomialFreydHomologyReferenceOperations
} from './algebra_polynomial_freyd_homology_reference_operations';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_CATEGORY_PROFILE =
    Object.freeze({
        revision: 'emdash-polynomial-freyd-homology-category-v1' as const,
        doctrine: 'abelian-category' as const,
        programBoundary: 'whole-homology-then-exactness' as const,
        derivedCallbackInlining: false as const,
        claimsFormalCategory: false as const,
        performsIo: false as const
    });

export interface AlgebraPolynomialFreydHomologyOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly chainPair: CategoryOperation<
        AlgebraPolynomialFreydChainPairInput<P, C, I>,
        AlgebraPolynomialFreydChainPair<P, C, I>
    >;
    readonly homologyAt: CategoryOperation<
        AlgebraPolynomialFreydChainPair<P, C, I>,
        AlgebraPolynomialFreydHomologyAt<P, C, I>
    >;
    readonly exactnessAt: CategoryOperation<
        AlgebraPolynomialFreydHomologyAt<P, C, I>,
        AlgebraPolynomialFreydExactnessAt<P, C, I>
    >;
    readonly chainMap: CategoryOperation<
        AlgebraPolynomialFreydHomologyChainMapInput<P, C, I>,
        AlgebraPolynomialFreydHomologyChainMap<P, C, I>
    >;
    readonly inducedHomologyMap: CategoryOperation<
        AlgebraPolynomialFreydHomologyChainMap<P, C, I>,
        AlgebraPolynomialFreydInducedHomologyMap<P, C, I>
    >;
}

export interface AlgebraPolynomialFreydHomologyCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly base: AlgebraPolynomialFreydAbelianCategoryModel<P, C, I>;
    readonly category: ComputableCategory<
        AlgebraPresentedPolynomialModule<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly operations: AlgebraPolynomialFreydHomologyOperations<P, C, I>;
    readonly native:
        AlgebraPolynomialFreydHomologyReferenceOperations<P, C, I>;
    readonly tower: CategoricalTower;
    readonly lowerings: readonly CategoryOperationLowering[];
}

const eraseCategory = <O, M>(category: ComputableCategory<O, M>):
    ComputableCategory<unknown, unknown> =>
    category as unknown as ComputableCategory<unknown, unknown>;

export function algebraPolynomialFreydHomologyCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialFreydHomologyCategoryModel<P, C, I> {
    const base = algebraPolynomialFreydAbelianCategoryModel(ring);
    const native = algebraPolynomialFreydHomologyReferenceOperations(base, ring);
    const revision = ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_CATEGORY_PROFILE.revision;
    const prefix = `algebra.category.polynomial-freyd-homology/` +
        ring.identity.id;
    const chainPair = defineCategoryOperation({
        id: `${prefix}/chain-pair`,
        revision,
        input: native.chainPair.input,
        output: native.chainPair.output
    });
    const homologyAt = defineCategoryOperation({
        id: `${prefix}/homology-at`,
        revision,
        input: native.homologyAt.input,
        output: native.homologyAt.output
    });
    const exactnessAt = defineCategoryOperation({
        id: `${prefix}/exactness-at`,
        revision,
        input: native.exactnessAt.input,
        output: native.exactnessAt.output
    });
    const chainMap = defineCategoryOperation({
        id: `${prefix}/chain-map`,
        revision,
        input: native.chainMap.input,
        output: native.chainMap.output
    });
    const inducedHomologyMap = defineCategoryOperation({
        id: `${prefix}/induced-map`,
        revision,
        input: native.inducedHomologyMap.input,
        output: native.inducedHomologyMap.output
    });
    const operations = Object.freeze({
        chainPair,
        homologyAt,
        exactnessAt,
        chainMap,
        inducedHomologyMap
    });
    const methods = [
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-homology.chain-pair.primitive',
            operation: chainPair,
            kind: 'primitive',
            execute: input => algebraPolynomialFreydChainPair(
                input.dNext,
                input.d
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-homology.homology-at.derived',
            operation: homologyAt,
            kind: 'derived',
            prerequisites: [
                base.base.operations.kernel,
                base.base.operations.kernelLift,
                base.base.operations.cokernel
            ],
            execute: pair => algebraPolynomialFreydHomologyAt(pair)
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-homology.exactness-at.derived',
            operation: exactnessAt,
            kind: 'derived',
            prerequisites: [base.operations.epimorphismWitness],
            execute: algebraPolynomialFreydExactnessAt
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-homology.chain-map.primitive',
            operation: chainMap,
            kind: 'primitive',
            execute: algebraPolynomialFreydHomologyChainMap
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-homology.induced-map.derived',
            operation: inducedHomologyMap,
            kind: 'derived',
            prerequisites: [
                base.base.operations.kernelLift,
                base.base.operations.cokernelColift
            ],
            execute: chainMapValue =>
                algebraPolynomialFreydInducedHomologyMap(chainMapValue)
        })
    ];
    const category = defineComputableCategory({
        id: prefix,
        revision,
        objectSchema: base.category.objectSchema,
        morphismSchema: base.category.morphismSchema,
        operations: createCategoryOperationRegistry([
            ...base.category.operations.methods,
            ...methods
        ]),
        source: morphism => base.category.source(morphism),
        target: morphism => base.category.target(morphism),
        identityMorphism: object => base.category.identityMorphism(object),
        compose: (after, before) => base.category.compose(after, before),
        equalObjects: (left, right) => base.category.equalObjects(left, right),
        equalMorphisms: (left, right) => base.category.equalMorphisms(left, right)
    });
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-freyd-homology',
        inputDoctrineId: 'abelian-category',
        outputDoctrineId: 'abelian-category',
        introducedRoles: [
            'chain-pair',
            'homology-at',
            'exactness-at',
            'homology-chain-map',
            'induced-homology-map'
        ],
        objectLayer: 'unchanged-polynomial-presentation',
        morphismLayer: 'unchanged-target-factorization-quotient',
        dualConstructorId: 'category-constructor.polynomial-freyd-homology',
        loweringRules: [{
            id: 'polynomial-freyd-homology.whole-operation',
            kind: 'operation-lowering',
            source: 'kernel-lift-cokernel-homology',
            target: native.homologyAt.identity.id
        }]
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-freyd-homology/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        base.tower.baseDoctrineId,
        [...base.tower.constructors, constructor]
    );
    const lowerings = Object.freeze([
        ...base.lowerings,
        {
            categoryOperation: chainPair,
            algebraOperation: native.chainPair
        },
        {
            categoryOperation: homologyAt,
            algebraOperation: native.homologyAt
        },
        {
            categoryOperation: exactnessAt,
            algebraOperation: native.exactnessAt
        },
        {
            categoryOperation: chainMap,
            algebraOperation: native.chainMap
        },
        {
            categoryOperation: inducedHomologyMap,
            algebraOperation: native.inducedHomologyMap
        }
    ] as CategoryOperationLowering[]);
    return Object.freeze({ base, category, operations, native, tower, lowerings });
}

export const compileAlgebraPolynomialFreydHomologyProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialFreydHomologyCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: eraseCategory(model.category),
    tower: model.tower,
    lowerings: model.lowerings
});

export const createAlgebraPolynomialFreydHomologyEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialFreydHomologyCategoryModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.polynomial-freyd-homology/` +
            model.base.base.base.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_CATEGORY_PROFILE.revision,
        implementations: [
            ...model.base.base.base.native.implementations,
            ...model.base.base.base.nativeAdditiveOperations.implementations,
            ...model.base.base.native.implementations,
            ...model.base.native.implementations,
            ...model.native.implementations
        ]
    });
