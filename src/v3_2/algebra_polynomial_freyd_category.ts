/** Direct computational Freyd category of polynomial module presentations. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    algebraAlgorithmIdentity,
    AlgebraOperation,
    AlgebraEngine,
    defineAlgebraOperation,
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
import {
    ALGEBRA_BASE_DOCTRINES,
    DoctrineQualification,
    qualifyCategoryDoctrine
} from './algebra_doctrine';
import {
    CategoricalTower,
    ComputationalReinterpretation,
    buildCategoricalTower,
    defineCategoryConstructorDescriptor,
    defineComputationalReinterpretation
} from './algebra_tower';
import {
    AlgebraPolynomialFreeModule,
    AlgebraPolynomialModuleVector,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPresentedPolynomialModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapAdd,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapNegate,
    algebraPolynomialModuleMapZero,
    algebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialPresentationMorphismInput,
    AlgebraPolynomialPresentationMorphismReferenceOperations,
    algebraPolynomialPresentationMorphismReferenceOperations
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialOne,
    algebraPolynomialZero
} from './algebra_polynomial';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';
import {
    AlgebraPolynomialWeakKernelCategoryModel,
    algebraPolynomialWeakKernelCategoryModel
} from './algebra_polynomial_weak_kernel_category';

export const ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-category-v4' as const,
    objectRepresentation: 'ordered-relation-presentation' as const,
    morphismRepresentation:
        'generator-map-with-computed-relation-witness' as const,
    equality: 'target-relation-congruence' as const,
    doctrine: 'additive-category' as const,
    additiveHomOperations: true as const,
    formalStructure: 'additive-category' as const,
    formalLawBoundary: 'arbitrary-quotient-points' as const,
    abelianClaim: false as const,
    performsIo: false as const
});

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export const algebraPresentedPolynomialModuleEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedPolynomialModule<P, C, I>,
    right: AlgebraPresentedPolynomialModule<P, C, I>
): boolean => sameAlgebraParent(left.ambient, right.ambient) &&
    left.relations.generators.length === right.relations.generators.length &&
    left.relations.generators.every((relation, index) =>
        algebraPolynomialModuleEquals(relation, right.relations.generators[index])
    );

export function algebraPolynomialPresentationMorphismIdentity<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(presentation: AlgebraPresentedPolynomialModule<P, C, I>):
    AlgebraPolynomialPresentationMorphism<P, C, I> {
    const result = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: algebraPolynomialModuleMapIdentity(presentation.ambient)
    });
    if (!result.preservesRelations) {
        throw new Error('Presentation identity failed relation preservation');
    }
    return result;
}

export function algebraPolynomialPresentationMorphismCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraPolynomialPresentationMorphism<P, C, I>,
    before: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialPresentationMorphism<P, C, I> {
    if (!algebraPresentedPolynomialModuleEquals(before.target, after.source)) {
        throw new Error('Presentation morphisms are not composable');
    }
    const result = algebraPolynomialPresentationMorphism({
        source: before.source,
        target: after.target,
        map: algebraPolynomialModuleMapCompose(after.map, before.map)
    });
    if (!result.preservesRelations) {
        throw new Error('Composite presentation map failed relation preservation');
    }
    return result;
}

export function algebraPolynomialPresentationMorphismZero<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedPolynomialModule<P, C, I>,
    target: AlgebraPresentedPolynomialModule<P, C, I>
): AlgebraPolynomialPresentationMorphism<P, C, I> {
    if (!sameAlgebraParent(source.ambient.ring, target.ambient.ring)) {
        throw new Error('Presentation zero requires one polynomial ring');
    }
    const result = algebraPolynomialPresentationMorphism({
        source,
        target,
        map: algebraPolynomialModuleMapZero(source.ambient, target.ambient)
    });
    if (!result.preservesRelations) {
        throw new Error('Presentation zero failed relation preservation');
    }
    return result;
}

export function algebraPolynomialPresentationMorphismAdd<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialPresentationMorphism<P, C, I>,
    right: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialPresentationMorphism<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(left.source, right.source) ||
        !algebraPresentedPolynomialModuleEquals(left.target, right.target)
    ) throw new Error('Presentation addition requires identical endpoints');
    const result = algebraPolynomialPresentationMorphism({
        source: left.source,
        target: left.target,
        map: algebraPolynomialModuleMapAdd(left.map, right.map)
    });
    if (!result.preservesRelations) {
        throw new Error('Presentation sum failed relation preservation');
    }
    return result;
}

export function algebraPolynomialPresentationMorphismNegate<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraPolynomialPresentationMorphism<P, C, I>):
    AlgebraPolynomialPresentationMorphism<P, C, I> {
    const result = algebraPolynomialPresentationMorphism({
        source: morphism.source,
        target: morphism.target,
        map: algebraPolynomialModuleMapNegate(morphism.map)
    });
    if (!result.preservesRelations) {
        throw new Error('Presentation negation failed relation preservation');
    }
    return result;
}

export const algebraPolynomialPresentationMorphismCongruence = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialPresentationMorphism<P, C, I>,
    right: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialPresentationMorphismAgreement<P, C, I> => {
    if (
        !algebraPresentedPolynomialModuleEquals(left.source, right.source) ||
        !algebraPresentedPolynomialModuleEquals(left.target, right.target)
    ) throw new Error('Presentation morphisms have different endpoints');
    return algebraPolynomialPresentationMorphismAgreement({
        source: left.source,
        target: left.target,
        left: left.map,
        right: right.map
    });
};

export interface AlgebraPolynomialFreydElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-element';
    readonly presentation: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export const algebraPolynomialFreeOnePresentation = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPresentedPolynomialModule<P, C, I> => {
    const freeOne = algebraPolynomialFreeModule(ring, 1);
    return algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(freeOne, [])
    );
};

export function algebraPolynomialFreydElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    presentation: AlgebraPresentedPolynomialModule<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): AlgebraPolynomialFreydElement<P, C, I> {
    if (!sameAlgebraParent(vector.parent, presentation.ambient)) {
        throw new Error('Freyd element vector belongs to a foreign free module');
    }
    const source = algebraPolynomialFreeOnePresentation(
        presentation.ambient.ring
    );
    const morphism = algebraPolynomialPresentationMorphism({
        source,
        target: presentation,
        map: algebraPolynomialModuleMap(
            source.ambient,
            presentation.ambient,
            [vector]
        )
    });
    if (!morphism.preservesRelations) {
        throw new Error('Rank-one source map unexpectedly failed preservation');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-element',
        presentation,
        source,
        vector,
        morphism
    });
}

export const algebraPolynomialFreydElementAgreement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialFreydElement<P, C, I>,
    right: AlgebraPolynomialFreydElement<P, C, I>
): AlgebraPolynomialPresentationMorphismAgreement<P, C, I> =>
    algebraPolynomialPresentationMorphismCongruence(
        left.morphism,
        right.morphism
    );

export interface AlgebraPolynomialFreydZeroObjectInput {
    readonly kind: 'algebra-polynomial-freyd-zero-object-input';
}

export const ALGEBRA_POLYNOMIAL_FREYD_ZERO_OBJECT_INPUT = Object.freeze({
    kind: 'algebra-polynomial-freyd-zero-object-input' as const
});

export interface AlgebraPolynomialFreydObjectPair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly right: AlgebraPresentedPolynomialModule<P, C, I>;
}

export interface AlgebraPolynomialFreydMorphismEndpoints<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly target: AlgebraPresentedPolynomialModule<P, C, I>;
}

export interface AlgebraPolynomialFreydMorphismPair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly right: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydBiproduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-biproduct';
    readonly left: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly right: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly object: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly injectionLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly injectionRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly projectionLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly projectionRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export const algebraPolynomialFreydZeroPresentation = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPresentedPolynomialModule<P, C, I> => {
    const ambient = algebraPolynomialFreeModule(ring, 0);
    return algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(ambient, [])
    );
};

const assertPresentationPairRing = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedPolynomialModule<P, C, I>,
    right: AlgebraPresentedPolynomialModule<P, C, I>
): void => {
    if (!sameAlgebraParent(left.ambient.ring, right.ambient.ring)) {
        throw new Error('Presentation direct sum requires one polynomial ring');
    }
};

const algebraPolynomialFreydEmbedVector = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    vector: AlgebraPolynomialModuleVector<P, C, I>,
    target: AlgebraPolynomialFreeModule<P, C, I>,
    leftRank: number,
    side: 'left' | 'right'
): AlgebraPolynomialModuleVector<P, C, I> => {
    const missing = target.rank - vector.parent.rank;
    const zeros = Array.from({ length: missing }, () =>
        algebraPolynomialZero(target.ring)
    );
    return algebraPolynomialModuleVector(
        target,
        side === 'left'
            ? [...vector.components, ...zeros]
            : [...zeros.slice(0, leftRank), ...vector.components]
    );
};

export function algebraPolynomialFreydDirectSumPresentation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedPolynomialModule<P, C, I>,
    right: AlgebraPresentedPolynomialModule<P, C, I>
): AlgebraPresentedPolynomialModule<P, C, I> {
    assertPresentationPairRing(left, right);
    const ambient = algebraPolynomialFreeModule(
        left.ambient.ring,
        left.ambient.rank + right.ambient.rank
    );
    return algebraPresentedPolynomialModule(algebraPolynomialSubmodule(
        ambient,
        [
            ...left.relations.generators.map(vector =>
                algebraPolynomialFreydEmbedVector(
                    vector,
                    ambient,
                    left.ambient.rank,
                    'left'
                )
            ),
            ...right.relations.generators.map(vector =>
                algebraPolynomialFreydEmbedVector(
                    vector,
                    ambient,
                    left.ambient.rank,
                    'right'
                )
            )
        ]
    ));
}

const algebraPolynomialFreydBasisVector = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    index: number
): AlgebraPolynomialModuleVector<P, C, I> =>
    algebraPolynomialModuleVector(
        module,
        Array.from({ length: module.rank }, (_, position) =>
            position === index
                ? algebraPolynomialOne(module.ring)
                : algebraPolynomialZero(module.ring)
        )
    );

export function algebraPolynomialFreydBiproduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedPolynomialModule<P, C, I>,
    right: AlgebraPresentedPolynomialModule<P, C, I>
): AlgebraPolynomialFreydBiproduct<P, C, I> {
    const object = algebraPolynomialFreydDirectSumPresentation(left, right);
    const leftRank = left.ambient.rank;
    const rightRank = right.ambient.rank;
    const injectionLeft = algebraPolynomialPresentationMorphism({
        source: left,
        target: object,
        map: algebraPolynomialModuleMap(
            left.ambient,
            object.ambient,
            Array.from({ length: leftRank }, (_, index) =>
                algebraPolynomialFreydBasisVector(object.ambient, index)
            )
        )
    });
    const injectionRight = algebraPolynomialPresentationMorphism({
        source: right,
        target: object,
        map: algebraPolynomialModuleMap(
            right.ambient,
            object.ambient,
            Array.from({ length: rightRank }, (_, index) =>
                algebraPolynomialFreydBasisVector(
                    object.ambient,
                    leftRank + index
                )
            )
        )
    });
    const projectionLeft = algebraPolynomialPresentationMorphism({
        source: object,
        target: left,
        map: algebraPolynomialModuleMap(
            object.ambient,
            left.ambient,
            Array.from({ length: leftRank + rightRank }, (_, index) =>
                index < leftRank
                    ? algebraPolynomialFreydBasisVector(left.ambient, index)
                    : algebraPolynomialModuleVector(
                        left.ambient,
                        Array.from({ length: leftRank }, () =>
                            algebraPolynomialZero(left.ambient.ring)
                        )
                    )
            )
        )
    });
    const projectionRight = algebraPolynomialPresentationMorphism({
        source: object,
        target: right,
        map: algebraPolynomialModuleMap(
            object.ambient,
            right.ambient,
            Array.from({ length: leftRank + rightRank }, (_, index) =>
                index < leftRank
                    ? algebraPolynomialModuleVector(
                        right.ambient,
                        Array.from({ length: rightRank }, () =>
                            algebraPolynomialZero(right.ambient.ring)
                        )
                    )
                    : algebraPolynomialFreydBasisVector(
                        right.ambient,
                        index - leftRank
                    )
            )
        )
    });
    if (
        !injectionLeft.preservesRelations ||
        !injectionRight.preservesRelations ||
        !projectionLeft.preservesRelations ||
        !projectionRight.preservesRelations
    ) throw new Error('Constructed Freyd biproduct map failed preservation');
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-biproduct',
        left,
        right,
        object,
        injectionLeft,
        injectionRight,
        projectionLeft,
        projectionRight
    });
}

export function algebraPolynomialPresentationMorphismDirectSum<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialPresentationMorphism<P, C, I>,
    right: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialPresentationMorphism<P, C, I> {
    assertPresentationPairRing(left.source, right.source);
    assertPresentationPairRing(left.target, right.target);
    const source = algebraPolynomialFreydDirectSumPresentation(
        left.source,
        right.source
    );
    const target = algebraPolynomialFreydDirectSumPresentation(
        left.target,
        right.target
    );
    const result = algebraPolynomialPresentationMorphism({
        source,
        target,
        map: algebraPolynomialModuleMap(
            source.ambient,
            target.ambient,
            [
                ...left.map.columns.map(vector =>
                    algebraPolynomialFreydEmbedVector(
                        vector,
                        target.ambient,
                        left.target.ambient.rank,
                        'left'
                    )
                ),
                ...right.map.columns.map(vector =>
                    algebraPolynomialFreydEmbedVector(
                        vector,
                        target.ambient,
                        left.target.ambient.rank,
                        'right'
                    )
                )
            ]
        )
    });
    if (!result.preservesRelations) {
        throw new Error('Direct-sum presentation map failed preservation');
    }
    return result;
}

export interface AlgebraPolynomialFreydCategoryOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly zeroMorphism: CategoryOperation<
        AlgebraPolynomialFreydMorphismEndpoints<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly addMorphisms: CategoryOperation<
        AlgebraPolynomialFreydMorphismPair<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly negateMorphism: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly zeroObject: CategoryOperation<
        AlgebraPolynomialFreydZeroObjectInput,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly biproduct: CategoryOperation<
        AlgebraPolynomialFreydObjectPair<P, C, I>,
        AlgebraPolynomialFreydBiproduct<P, C, I>
    >;
    readonly directSumMorphism: CategoryOperation<
        AlgebraPolynomialFreydMorphismPair<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
}

export interface AlgebraPolynomialFreydNativeAdditiveOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly zeroMorphism: AlgebraOperation<
        AlgebraPolynomialFreydMorphismEndpoints<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly addMorphisms: AlgebraOperation<
        AlgebraPolynomialFreydMorphismPair<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly negateMorphism: AlgebraOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly zeroObject: AlgebraOperation<
        AlgebraPolynomialFreydZeroObjectInput,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly biproduct: AlgebraOperation<
        AlgebraPolynomialFreydObjectPair<P, C, I>,
        AlgebraPolynomialFreydBiproduct<P, C, I>
    >;
    readonly directSumMorphism: AlgebraOperation<
        AlgebraPolynomialFreydMorphismPair<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export interface AlgebraPolynomialFreydCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraPresentedPolynomialModule<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly morphismOperation: CategoryOperation<
        AlgebraPolynomialPresentationMorphismInput<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly native:
        AlgebraPolynomialPresentationMorphismReferenceOperations<P, C, I>;
    readonly operations: AlgebraPolynomialFreydCategoryOperations<P, C, I>;
    readonly nativeAdditiveOperations:
        AlgebraPolynomialFreydNativeAdditiveOperations<P, C, I>;
    readonly additiveHomOperations: {
        readonly zero: (
            source: AlgebraPresentedPolynomialModule<P, C, I>,
            target: AlgebraPresentedPolynomialModule<P, C, I>
        ) => AlgebraPolynomialPresentationMorphism<P, C, I>;
        readonly add: (
            left: AlgebraPolynomialPresentationMorphism<P, C, I>,
            right: AlgebraPolynomialPresentationMorphism<P, C, I>
        ) => AlgebraPolynomialPresentationMorphism<P, C, I>;
        readonly negate: (
            morphism: AlgebraPolynomialPresentationMorphism<P, C, I>
        ) => AlgebraPolynomialPresentationMorphism<P, C, I>;
        readonly directSumObjects: (
            left: AlgebraPresentedPolynomialModule<P, C, I>,
            right: AlgebraPresentedPolynomialModule<P, C, I>
        ) => AlgebraPresentedPolynomialModule<P, C, I>;
        readonly directSumMorphisms: (
            left: AlgebraPolynomialPresentationMorphism<P, C, I>,
            right: AlgebraPolynomialPresentationMorphism<P, C, I>
        ) => AlgebraPolynomialPresentationMorphism<P, C, I>;
        readonly zeroObject: () => AlgebraPresentedPolynomialModule<P, C, I>;
        readonly biproduct: (
            left: AlgebraPresentedPolynomialModule<P, C, I>,
            right: AlgebraPresentedPolynomialModule<P, C, I>
        ) => AlgebraPolynomialFreydBiproduct<P, C, I>;
        readonly formalStructure: 'additive-category';
        readonly formalLawBoundary: 'arbitrary-quotient-points';
    };
    readonly doctrineQualification: DoctrineQualification;
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraPresentedPolynomialModule<P, C, I>,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly lowerings: readonly CategoryOperationLowering[];
}

export function algebraPolynomialFreydCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialFreydCategoryModel<P, C, I> {
    const native =
        algebraPolynomialPresentationMorphismReferenceOperations<P, C, I>();
    const objectSchema = defineAlgebraRuntimeSchema<
        AlgebraPresentedPolynomialModule<P, C, I>
    >({
        id: `algebra.category.polynomial-freyd-object/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-presented-polynomial-module'
            ) throw new Error(`polynomial presentation expected at ${path}`);
            const presentation = value as AlgebraPresentedPolynomialModule<P, C, I>;
            if (!sameAlgebraParent(presentation.ambient.ring, ring)) {
                throw new Error(`foreign presentation ring at ${path}`);
            }
            return presentation;
        }
    });
    const morphismSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >({
        id: `algebra.category.polynomial-freyd-morphism/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-polynomial-presentation-morphism'
            ) throw new Error(`presentation morphism expected at ${path}`);
            const morphism = value as AlgebraPolynomialPresentationMorphism<P, C, I>;
            if (!morphism.preservesRelations ||
                !sameAlgebraParent(morphism.source.ambient.ring, ring)) {
                throw new Error(`invalid or foreign presentation map at ${path}`);
            }
            return morphism;
        }
    });
    const zeroObjectInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydZeroObjectInput
    >({
        id: `algebra.category.polynomial-freyd-zero-input/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-freyd-zero-object-input') {
                throw new Error(`zero-object input expected at ${path}`);
            }
            return ALGEBRA_POLYNOMIAL_FREYD_ZERO_OBJECT_INPUT;
        }
    });
    const objectPairSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydObjectPair<P, C, I>
    >({
        id: `algebra.category.polynomial-freyd-object-pair/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`object pair expected at ${path}`);
            return Object.freeze({
                left: objectSchema.normalize(value.left, `${path}.left`),
                right: objectSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const morphismEndpointsSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydMorphismEndpoints<P, C, I>
    >({
        id: `algebra.category.polynomial-freyd-endpoints/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`morphism endpoints expected at ${path}`);
            return Object.freeze({
                source: objectSchema.normalize(value.source, `${path}.source`),
                target: objectSchema.normalize(value.target, `${path}.target`)
            });
        }
    });
    const morphismPairSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydMorphismPair<P, C, I>
    >({
        id: `algebra.category.polynomial-freyd-morphism-pair/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`morphism pair expected at ${path}`);
            return Object.freeze({
                left: morphismSchema.normalize(value.left, `${path}.left`),
                right: morphismSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const biproductSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydBiproduct<P, C, I>
    >({
        id: `algebra.category.polynomial-freyd-biproduct/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-freyd-biproduct') {
                throw new Error(`Freyd biproduct expected at ${path}`);
            }
            return algebraPolynomialFreydBiproduct(
                objectSchema.normalize(value.left, `${path}.left`),
                objectSchema.normalize(value.right, `${path}.right`)
            );
        }
    });
    const morphismOperation = defineCategoryOperation({
        id: `algebra.category.polynomial-freyd.morphism/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: native.morphismInputSchema,
        output: native.morphism.output
    });
    const operationPrefix =
        `algebra.category.polynomial-freyd/${ring.identity.id}`;
    const zeroMorphism = defineCategoryOperation({
        id: `${operationPrefix}/zero-morphism`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: morphismEndpointsSchema,
        output: morphismSchema
    });
    const addMorphisms = defineCategoryOperation({
        id: `${operationPrefix}/add-morphisms`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: morphismPairSchema,
        output: morphismSchema
    });
    const negateMorphism = defineCategoryOperation({
        id: `${operationPrefix}/negate-morphism`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: morphismSchema,
        output: morphismSchema
    });
    const zeroObject = defineCategoryOperation({
        id: `${operationPrefix}/zero-object`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: zeroObjectInputSchema,
        output: objectSchema
    });
    const biproduct = defineCategoryOperation({
        id: `${operationPrefix}/biproduct`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: objectPairSchema,
        output: biproductSchema
    });
    const directSumMorphism = defineCategoryOperation({
        id: `${operationPrefix}/direct-sum-morphism`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: morphismPairSchema,
        output: morphismSchema
    });
    const operations = Object.freeze({
        zeroMorphism,
        addMorphisms,
        negateMorphism,
        zeroObject,
        biproduct,
        directSumMorphism
    });
    const operationRegistry = createCategoryOperationRegistry([
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.morphism.primitive',
            operation: morphismOperation,
            kind: 'primitive',
            execute: algebraPolynomialPresentationMorphism
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.zero-morphism.primitive',
            operation: zeroMorphism,
            kind: 'primitive',
            execute: input => algebraPolynomialPresentationMorphismZero(
                input.source,
                input.target
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.add-morphisms.primitive',
            operation: addMorphisms,
            kind: 'primitive',
            execute: input => algebraPolynomialPresentationMorphismAdd(
                input.left,
                input.right
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.negate-morphism.primitive',
            operation: negateMorphism,
            kind: 'primitive',
            execute: algebraPolynomialPresentationMorphismNegate
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.zero-object.primitive',
            operation: zeroObject,
            kind: 'primitive',
            execute: () => algebraPolynomialFreydZeroPresentation(ring)
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.biproduct.primitive',
            operation: biproduct,
            kind: 'primitive',
            execute: input => algebraPolynomialFreydBiproduct(
                input.left,
                input.right
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd.direct-sum-morphism.primitive',
            operation: directSumMorphism,
            kind: 'primitive',
            execute: input => algebraPolynomialPresentationMorphismDirectSum(
                input.left,
                input.right
            )
        })
    ]);
    const category = defineComputableCategory({
        id: `algebra.category.polynomial-freyd/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        objectSchema,
        morphismSchema,
        operations: operationRegistry,
        source: morphism => morphism.source,
        target: morphism => morphism.target,
        identityMorphism: algebraPolynomialPresentationMorphismIdentity,
        compose: algebraPolynomialPresentationMorphismCompose,
        equalObjects: algebraPresentedPolynomialModuleEquals,
        equalMorphisms: (left, right) =>
            algebraPolynomialPresentationMorphismCongruence(left, right).agrees
    });
    const doctrineQualification = qualifyCategoryDoctrine(
        category as unknown as ComputableCategory<unknown, unknown>,
        ALGEBRA_BASE_DOCTRINES,
        'additive-category',
        [
            { role: 'zero-morphism', operation: zeroMorphism },
            { role: 'add-morphisms', operation: addMorphisms },
            { role: 'negate-morphism', operation: negateMorphism },
            { role: 'zero-object', operation: zeroObject },
            { role: 'biproduct', operation: biproduct }
        ]
    );
    if (doctrineQualification.status !== 'qualified') {
        throw new Error(
            `Polynomial Freyd additive qualification missing: ` +
            doctrineQualification.missingRoles.join(', ')
        );
    }
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-freyd-presentations',
        inputDoctrineId: 'category',
        outputDoctrineId: 'additive-category',
        introducedRoles: [
            'freyd-presentation',
            'zero-morphism',
            'add-morphisms',
            'negate-morphism',
            'zero-object',
            'biproduct'
        ],
        objectLayer: 'ordered-polynomial-relation-matrix',
        morphismLayer: 'relation-preserving-map-modulo-target-factorization',
        dualConstructorId: 'category-constructor.polynomial-freyd-presentations',
        loweringRules: [{
            id: 'polynomial-freyd.morphism-to-membership-witness',
            kind: 'operation-lowering',
            source: 'relation-preserving-map-modulo-target-factorization',
            target: native.morphism.identity.id
        }]
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-freyd/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        'category',
        [constructor]
    );
    const modelCategoryId =
        `algebra.category.polynomial-freyd-model/${ring.identity.id}`;
    const reinterpretation = defineComputationalReinterpretation({
        id: `algebra.reinterpretation.polynomial-freyd/${ring.identity.id}`,
        publicCategoryId: category.identity.id,
        modelingCategoryId: modelCategoryId,
        toModel: (value: AlgebraPresentedPolynomialModule<P, C, I>) => value,
        fromModel: (value: AlgebraPresentedPolynomialModule<P, C, I>) => value,
        loweringRules: [{
            id: 'polynomial-freyd.direct-presentation',
            kind: 'reinterpretation',
            source: modelCategoryId,
            target: category.identity.id
        }]
    });
    const nativeZeroMorphism = defineAlgebraOperation({
        id: zeroMorphism.id.replace('algebra.category.', 'algebra.'),
        revision: zeroMorphism.revision,
        input: zeroMorphism.input,
        output: zeroMorphism.output
    });
    const nativeAddMorphisms = defineAlgebraOperation({
        id: addMorphisms.id.replace('algebra.category.', 'algebra.'),
        revision: addMorphisms.revision,
        input: addMorphisms.input,
        output: addMorphisms.output
    });
    const nativeNegateMorphism = defineAlgebraOperation({
        id: negateMorphism.id.replace('algebra.category.', 'algebra.'),
        revision: negateMorphism.revision,
        input: negateMorphism.input,
        output: negateMorphism.output
    });
    const nativeZeroObject = defineAlgebraOperation({
        id: zeroObject.id.replace('algebra.category.', 'algebra.'),
        revision: zeroObject.revision,
        input: zeroObject.input,
        output: zeroObject.output
    });
    const nativeBiproduct = defineAlgebraOperation({
        id: biproduct.id.replace('algebra.category.', 'algebra.'),
        revision: biproduct.revision,
        input: biproduct.input,
        output: biproduct.output
    });
    const nativeDirectSumMorphism = defineAlgebraOperation({
        id: directSumMorphism.id.replace('algebra.category.', 'algebra.'),
        revision: directSumMorphism.revision,
        input: directSumMorphism.input,
        output: directSumMorphism.output
    });
    const nativeAdditiveImplementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: nativeZeroMorphism,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/freyd-zero-morphism',
                'v1'
            ),
            execute: input => algebraPolynomialPresentationMorphismZero(
                input.source,
                input.target
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: nativeAddMorphisms,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/freyd-add-morphisms',
                'v1'
            ),
            execute: input => algebraPolynomialPresentationMorphismAdd(
                input.left,
                input.right
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: nativeNegateMorphism,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/freyd-negate-morphism',
                'v1'
            ),
            execute: algebraPolynomialPresentationMorphismNegate
        }),
        defineAlgebraReferenceImplementation({
            operation: nativeZeroObject,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/freyd-zero-object',
                'v1'
            ),
            execute: () => algebraPolynomialFreydZeroPresentation(ring)
        }),
        defineAlgebraReferenceImplementation({
            operation: nativeBiproduct,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/freyd-biproduct',
                'v1'
            ),
            execute: input => algebraPolynomialFreydBiproduct(
                input.left,
                input.right
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: nativeDirectSumMorphism,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/freyd-direct-sum-morphism',
                'v1'
            ),
            execute: input => algebraPolynomialPresentationMorphismDirectSum(
                input.left,
                input.right
            )
        })
    ]);
    const nativeAdditiveOperations = Object.freeze({
        zeroMorphism: nativeZeroMorphism,
        addMorphisms: nativeAddMorphisms,
        negateMorphism: nativeNegateMorphism,
        zeroObject: nativeZeroObject,
        biproduct: nativeBiproduct,
        directSumMorphism: nativeDirectSumMorphism,
        implementations: nativeAdditiveImplementations
    });
    return Object.freeze({
        category,
        morphismOperation,
        native,
        operations,
        nativeAdditiveOperations,
        additiveHomOperations: Object.freeze({
            zero: algebraPolynomialPresentationMorphismZero,
            add: algebraPolynomialPresentationMorphismAdd,
            negate: algebraPolynomialPresentationMorphismNegate,
            directSumObjects: algebraPolynomialFreydDirectSumPresentation,
            directSumMorphisms: algebraPolynomialPresentationMorphismDirectSum,
            zeroObject: () => algebraPolynomialFreydZeroPresentation(ring),
            biproduct: algebraPolynomialFreydBiproduct,
            formalStructure: 'additive-category' as const,
            formalLawBoundary: 'arbitrary-quotient-points' as const
        }),
        doctrineQualification,
        tower,
        reinterpretation,
        lowerings: Object.freeze([
            {
                categoryOperation: morphismOperation,
                algebraOperation: native.morphism
            },
            { categoryOperation: zeroMorphism, algebraOperation: nativeZeroMorphism },
            { categoryOperation: addMorphisms, algebraOperation: nativeAddMorphisms },
            { categoryOperation: negateMorphism, algebraOperation: nativeNegateMorphism },
            { categoryOperation: zeroObject, algebraOperation: nativeZeroObject },
            { categoryOperation: biproduct, algebraOperation: nativeBiproduct },
            {
                categoryOperation: directSumMorphism,
                algebraOperation: nativeDirectSumMorphism
            }
        ] as CategoryOperationLowering[])
    });
}

export const compileAlgebraPolynomialFreydProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialFreydCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: model.category as unknown as ComputableCategory<unknown, unknown>,
    tower: model.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.reinterpretation]
});

export const createAlgebraPolynomialFreydEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialFreydCategoryModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.polynomial-freyd/` +
            model.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        implementations: [
            ...model.native.implementations,
            ...model.nativeAdditiveOperations.implementations
        ]
    });

/** Explicit capability boundary for the next Abelian tranche. */
export interface AlgebraPolynomialWeakKernelCapability<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-weak-kernel-capability';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly basis: 'groebner-syzygy';
    readonly operationalFieldCoefficients: true;
    readonly provider:
        AlgebraPolynomialWeakKernelCategoryModel<P, C, I>;
    readonly qualification: 'qualified';
    readonly claimsAbelianStructure: false;
}

/** Compatibility facade backed by the executable finite-free provider. */
export function algebraPolynomialWeakKernelCapability<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialWeakKernelCapability<P, C, I> {
    if ((ring.coefficientDomain as { field?: unknown }).field !== true) {
        throw new Error('Weak-kernel capability requires operational field coefficients');
    }
    const provider = algebraPolynomialWeakKernelCategoryModel(ring);
    if (provider.qualification.status !== 'qualified') {
        throw new Error('Weak-kernel provider did not qualify its doctrine');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-weak-kernel-capability',
        ring,
        basis: 'groebner-syzygy',
        operationalFieldCoefficients: true,
        provider,
        qualification: 'qualified',
        claimsAbelianStructure: false
    });
}
