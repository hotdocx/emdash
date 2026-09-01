/** Direct computational Freyd category of polynomial module presentations. */

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
import {
    ALGEBRA_BASE_DOCTRINES
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
    algebraPolynomialZero
} from './algebra_polynomial';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-category-v3' as const,
    objectRepresentation: 'ordered-relation-presentation' as const,
    morphismRepresentation:
        'generator-map-with-computed-relation-witness' as const,
    equality: 'target-relation-congruence' as const,
    doctrine: 'category' as const,
    additiveHomOperations: true as const,
    formalStructure: 'preadditive-category' as const,
    formalLawBoundary: 'arbitrary-quotient-points' as const,
    abelianClaim: false as const,
    performsIo: false as const
});

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
        readonly formalStructure: 'preadditive-category';
        readonly formalLawBoundary: 'arbitrary-quotient-points';
    };
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
    const morphismOperation = defineCategoryOperation({
        id: `algebra.category.polynomial-freyd.morphism/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        input: native.morphismInputSchema,
        output: native.morphism.output
    });
    const category = defineComputableCategory({
        id: `algebra.category.polynomial-freyd/${ring.identity.id}`,
        revision: ALGEBRA_POLYNOMIAL_FREYD_CATEGORY_PROFILE.revision,
        objectSchema,
        morphismSchema,
        operations: createCategoryOperationRegistry([
            defineCategoryMethod({
                id: 'algebra.polynomial-freyd.morphism.primitive',
                operation: morphismOperation,
                kind: 'primitive',
                execute: algebraPolynomialPresentationMorphism
            })
        ]),
        source: morphism => morphism.source,
        target: morphism => morphism.target,
        identityMorphism: algebraPolynomialPresentationMorphismIdentity,
        compose: algebraPolynomialPresentationMorphismCompose,
        equalObjects: algebraPresentedPolynomialModuleEquals,
        equalMorphisms: (left, right) =>
            algebraPolynomialPresentationMorphismCongruence(left, right).agrees
    });
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-freyd-presentations',
        inputDoctrineId: 'category',
        outputDoctrineId: 'category',
        introducedRoles: ['freyd-presentation'],
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
    return Object.freeze({
        category,
        morphismOperation,
        native,
        additiveHomOperations: Object.freeze({
            zero: algebraPolynomialPresentationMorphismZero,
            add: algebraPolynomialPresentationMorphismAdd,
            negate: algebraPolynomialPresentationMorphismNegate,
            formalStructure: 'preadditive-category' as const,
            formalLawBoundary: 'arbitrary-quotient-points' as const
        }),
        tower,
        reinterpretation,
        lowerings: Object.freeze([{
            categoryOperation: morphismOperation,
            algebraOperation: native.morphism
        }] as CategoryOperationLowering[])
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
        implementations: model.native.implementations
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
    readonly claimsAbelianStructure: false;
}

export function algebraPolynomialWeakKernelCapability<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialWeakKernelCapability<P, C, I> {
    if ((ring.coefficientDomain as { field?: unknown }).field !== true) {
        throw new Error('Weak-kernel capability requires operational field coefficients');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-weak-kernel-capability',
        ring,
        basis: 'groebner-syzygy',
        operationalFieldCoefficients: true,
        claimsAbelianStructure: false
    });
}
