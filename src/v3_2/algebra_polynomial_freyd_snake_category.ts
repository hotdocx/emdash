/** Categorical operations and graph lowering for the polynomial Freyd snake. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraEngine,
    AlgebraRuntimeSchema
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
    AlgebraPolynomialFreydFiberProduct,
    AlgebraPolynomialFreydFiberProductFactor,
    algebraPolynomialFreydFiberProduct,
    algebraPolynomialFreydFiberProductFactor
} from './algebra_polynomial_freyd_fiber_product';
import {
    AlgebraPolynomialFreydPushout,
    AlgebraPolynomialFreydPushoutCofactor,
    algebraPolynomialFreydPushout,
    algebraPolynomialFreydPushoutCofactor
} from './algebra_polynomial_freyd_pushout';
import {
    AlgebraPolynomialFreydShortExactTriple,
    algebraPolynomialFreydShortExactTriple
} from './algebra_polynomial_freyd_short_exact';
import {
    AlgebraPolynomialFreydSnakeConnecting,
    AlgebraPolynomialFreydSnakeTriple,
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydSnakeTriple
} from './algebra_polynomial_freyd_snake';
import {
    AlgebraPolynomialFreydFiberProductLiftInput,
    AlgebraPolynomialFreydMorphismPairInput,
    AlgebraPolynomialFreydPushoutColiftInput,
    AlgebraPolynomialFreydShortExactTripleInput,
    AlgebraPolynomialFreydSnakeReferenceOperations,
    AlgebraPolynomialFreydSnakeTripleInput,
    algebraPolynomialFreydSnakeReferenceOperations
} from './algebra_polynomial_freyd_snake_reference_operations';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_FREYD_SNAKE_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-snake-category-v1' as const,
    doctrine: 'abelian-category' as const,
    programBoundary: 'whole-triple-then-connecting' as const,
    derivedCallbackInlining: false as const,
    claimsFormalCategory: false as const,
    performsIo: false as const
});

export interface AlgebraPolynomialFreydSnakeOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly fiberProduct: CategoryOperation<
        AlgebraPolynomialFreydMorphismPairInput<P, C, I>,
        AlgebraPolynomialFreydFiberProduct<P, C, I>
    >;
    readonly fiberProductProjectionLeft: CategoryOperation<
        AlgebraPolynomialFreydFiberProduct<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly fiberProductProjectionRight: CategoryOperation<
        AlgebraPolynomialFreydFiberProduct<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly fiberProductLift: CategoryOperation<
        AlgebraPolynomialFreydFiberProductLiftInput<P, C, I>,
        AlgebraPolynomialFreydFiberProductFactor<P, C, I>
    >;
    readonly pushout: CategoryOperation<
        AlgebraPolynomialFreydMorphismPairInput<P, C, I>,
        AlgebraPolynomialFreydPushout<P, C, I>
    >;
    readonly pushoutInjectionLeft: CategoryOperation<
        AlgebraPolynomialFreydPushout<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly pushoutInjectionRight: CategoryOperation<
        AlgebraPolynomialFreydPushout<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly pushoutColift: CategoryOperation<
        AlgebraPolynomialFreydPushoutColiftInput<P, C, I>,
        AlgebraPolynomialFreydPushoutCofactor<P, C, I>
    >;
    readonly shortExactTriple: CategoryOperation<
        AlgebraPolynomialFreydShortExactTripleInput<P, C, I>,
        AlgebraPolynomialFreydShortExactTriple<P, C, I>
    >;
    readonly snakeTriple: CategoryOperation<
        AlgebraPolynomialFreydSnakeTripleInput<P, C, I>,
        AlgebraPolynomialFreydSnakeTriple<P, C, I>
    >;
    readonly snakeConnecting: CategoryOperation<
        AlgebraPolynomialFreydSnakeTriple<P, C, I>,
        AlgebraPolynomialFreydSnakeConnecting<P, C, I>
    >;
}

export interface AlgebraPolynomialFreydSnakeCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly base: AlgebraPolynomialFreydAbelianCategoryModel<P, C, I>;
    readonly category: ComputableCategory<
        AlgebraPresentedPolynomialModule<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly operations: AlgebraPolynomialFreydSnakeOperations<P, C, I>;
    readonly native: AlgebraPolynomialFreydSnakeReferenceOperations<P, C, I>;
    readonly tower: CategoricalTower;
    readonly lowerings: readonly CategoryOperationLowering[];
}

const eraseCategory = <O, M>(category: ComputableCategory<O, M>):
    ComputableCategory<unknown, unknown> =>
    category as unknown as ComputableCategory<unknown, unknown>;

export function algebraPolynomialFreydSnakeCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialFreydSnakeCategoryModel<P, C, I> {
    const base = algebraPolynomialFreydAbelianCategoryModel(ring);
    const native = algebraPolynomialFreydSnakeReferenceOperations(base, ring);
    const revision = ALGEBRA_POLYNOMIAL_FREYD_SNAKE_CATEGORY_PROFILE.revision;
    const prefix = `algebra.category.polynomial-freyd-snake/` +
        ring.identity.id;
    const categoryOperation = <Input, Output>(
        id: string,
        nativeOperation: {
            readonly input: AlgebraRuntimeSchema<Input>;
            readonly output: AlgebraRuntimeSchema<Output>;
        }
    ) => defineCategoryOperation({
        id: `${prefix}/${id}`,
        revision,
        input: nativeOperation.input,
        output: nativeOperation.output
    });
    const fiberProduct = categoryOperation('fiber-product', native.fiberProduct);
    const fiberProductProjectionLeft = categoryOperation(
        'fiber-product-projection-left',
        native.fiberProductProjectionLeft
    );
    const fiberProductProjectionRight = categoryOperation(
        'fiber-product-projection-right',
        native.fiberProductProjectionRight
    );
    const fiberProductLift = categoryOperation(
        'fiber-product-lift',
        native.fiberProductLift
    );
    const pushout = categoryOperation('pushout', native.pushout);
    const pushoutInjectionLeft = categoryOperation(
        'pushout-injection-left',
        native.pushoutInjectionLeft
    );
    const pushoutInjectionRight = categoryOperation(
        'pushout-injection-right',
        native.pushoutInjectionRight
    );
    const pushoutColift = categoryOperation(
        'pushout-colift',
        native.pushoutColift
    );
    const shortExactTriple = categoryOperation(
        'short-exact-triple',
        native.shortExactTriple
    );
    const snakeTriple = categoryOperation('snake-triple', native.triple);
    const snakeConnecting = categoryOperation(
        'snake-connecting-morphism',
        native.connecting
    );
    const operations = Object.freeze({
        fiberProduct,
        fiberProductProjectionLeft,
        fiberProductProjectionRight,
        fiberProductLift,
        pushout,
        pushoutInjectionLeft,
        pushoutInjectionRight,
        pushoutColift,
        shortExactTriple,
        snakeTriple,
        snakeConnecting
    });
    const methods = [
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.fiber-product.derived',
            operation: fiberProduct,
            kind: 'derived',
            prerequisites: [
                base.base.base.operations.biproduct,
                base.base.operations.kernel
            ],
            execute: input => algebraPolynomialFreydFiberProduct(
                input.left,
                input.right
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.fiber-product-left.derived',
            operation: fiberProductProjectionLeft,
            kind: 'derived',
            prerequisites: [fiberProduct],
            execute: value => value.projectionLeft
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.fiber-product-right.derived',
            operation: fiberProductProjectionRight,
            kind: 'derived',
            prerequisites: [fiberProduct],
            execute: value => value.projectionRight
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.fiber-product-lift.derived',
            operation: fiberProductLift,
            kind: 'derived',
            prerequisites: [fiberProduct, base.base.operations.kernelLift],
            execute: input => algebraPolynomialFreydFiberProductFactor(
                input.fiberProduct,
                input.testLeft,
                input.testRight,
                input.maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: input.maximumReductionSteps }
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.pushout.derived',
            operation: pushout,
            kind: 'derived',
            prerequisites: [
                base.base.base.operations.biproduct,
                base.base.operations.cokernel
            ],
            execute: input => algebraPolynomialFreydPushout(
                input.left,
                input.right
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.pushout-left.derived',
            operation: pushoutInjectionLeft,
            kind: 'derived',
            prerequisites: [pushout],
            execute: value => value.injectionLeft
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.pushout-right.derived',
            operation: pushoutInjectionRight,
            kind: 'derived',
            prerequisites: [pushout],
            execute: value => value.injectionRight
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.pushout-colift.derived',
            operation: pushoutColift,
            kind: 'derived',
            prerequisites: [pushout, base.base.operations.cokernelColift],
            execute: input => algebraPolynomialFreydPushoutCofactor(
                input.pushout,
                input.testLeft,
                input.testRight
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.short-exact.derived',
            operation: shortExactTriple,
            kind: 'derived',
            prerequisites: [
                base.base.operations.kernel,
                base.base.operations.kernelLift,
                base.base.operations.cokernel,
                base.operations.monomorphismWitness,
                base.operations.epimorphismWitness
            ],
            execute: input => algebraPolynomialFreydShortExactTriple(
                input.incoming,
                input.outgoing,
                input.maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: input.maximumReductionSteps }
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.triple.primitive',
            operation: snakeTriple,
            kind: 'primitive',
            execute: input => algebraPolynomialFreydSnakeTriple(
                input.delta,
                input.beta,
                input.lambda
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-snake.connecting.derived',
            operation: snakeConnecting,
            kind: 'derived',
            prerequisites: [
                base.base.operations.cokernelColift,
                base.base.operations.kernel,
                base.base.operations.cokernel,
                base.base.operations.kernelLift,
                fiberProduct,
                pushout,
                base.operations.coliftAlongEpimorphism,
                base.operations.liftAlongMonomorphism
            ],
            execute: triple => algebraPolynomialFreydSnakeConnecting(triple)
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
        id: 'category-constructor.polynomial-freyd-snake',
        inputDoctrineId: 'abelian-category',
        outputDoctrineId: 'abelian-category',
        introducedRoles: [
            'fiber-product',
            'fiber-product-projection-1',
            'fiber-product-projection-2',
            'fiber-product-lift',
            'pushout',
            'pushout-injection-1',
            'pushout-injection-2',
            'pushout-colift',
            'short-exact-triple',
            'snake-triple',
            'snake-connecting-morphism'
        ],
        objectLayer: 'unchanged-polynomial-presentation',
        morphismLayer: 'unchanged-target-factorization-quotient',
        dualConstructorId: 'category-constructor.polynomial-freyd-snake',
        loweringRules: [
            {
                id: 'polynomial-freyd-snake.fiber-product',
                kind: 'operation-lowering',
                source: 'biproduct-kernel-fiber-product',
                target: native.fiberProduct.identity.id
            },
            {
                id: 'polynomial-freyd-snake.pushout',
                kind: 'operation-lowering',
                source: 'biproduct-cokernel-pushout',
                target: native.pushout.identity.id
            },
            {
                id: 'polynomial-freyd-snake.short-exact',
                kind: 'operation-lowering',
                source: 'kernel-lift-exactness-monic-epic',
                target: native.shortExactTriple.identity.id
            },
            {
                id: 'polynomial-freyd-snake.connecting',
                kind: 'operation-lowering',
                source: 'cap-fiber-pushout-normal-factors',
                target: native.connecting.identity.id
            }
        ]
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-freyd-snake/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        base.tower.baseDoctrineId,
        [...base.tower.constructors, constructor]
    );
    const lowerings = Object.freeze([
        ...base.lowerings,
        { categoryOperation: fiberProduct, algebraOperation: native.fiberProduct },
        {
            categoryOperation: fiberProductProjectionLeft,
            algebraOperation: native.fiberProductProjectionLeft
        },
        {
            categoryOperation: fiberProductProjectionRight,
            algebraOperation: native.fiberProductProjectionRight
        },
        {
            categoryOperation: fiberProductLift,
            algebraOperation: native.fiberProductLift
        },
        { categoryOperation: pushout, algebraOperation: native.pushout },
        {
            categoryOperation: pushoutInjectionLeft,
            algebraOperation: native.pushoutInjectionLeft
        },
        {
            categoryOperation: pushoutInjectionRight,
            algebraOperation: native.pushoutInjectionRight
        },
        { categoryOperation: pushoutColift, algebraOperation: native.pushoutColift },
        {
            categoryOperation: shortExactTriple,
            algebraOperation: native.shortExactTriple
        },
        { categoryOperation: snakeTriple, algebraOperation: native.triple },
        { categoryOperation: snakeConnecting, algebraOperation: native.connecting }
    ] as CategoryOperationLowering[]);
    return Object.freeze({ base, category, operations, native, tower, lowerings });
}

export const compileAlgebraPolynomialFreydSnakeProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialFreydSnakeCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: eraseCategory(model.category),
    tower: model.tower,
    lowerings: model.lowerings
});

export const createAlgebraPolynomialFreydSnakeEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialFreydSnakeCategoryModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.polynomial-freyd-snake/` +
            model.base.base.base.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_FREYD_SNAKE_CATEGORY_PROFILE.revision,
        implementations: [
            ...model.base.base.base.native.implementations,
            ...model.base.base.base.nativeAdditiveOperations.implementations,
            ...model.base.base.native.implementations,
            ...model.base.native.implementations,
            ...model.native.implementations
        ]
    });
