/** Categorical capabilities and explicit whole-operation lowering for long exact homology. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraOperation } from './algebra_engine';
import { AlgebraPolynomialRing } from './algebra_polynomial';
import {
    CategoryOperation, ComputableCategory, createCategoryOperationRegistry,
    defineCategoryMethod, defineCategoryOperation, defineComputableCategory
} from './algebra_category';
import {
    CategoricalProgram, CategoryOperationLowering, compileCategoricalProgram
} from './algebra_categorical_program';
import { ALGEBRA_BASE_DOCTRINES } from './algebra_doctrine';
import { buildCategoricalTower, defineCategoryConstructorDescriptor } from './algebra_tower';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import { algebraPolynomialFreydHomologyCategoryModel } from './algebra_polynomial_freyd_homology_category';
import { algebraPolynomialFreydSnakeCategoryModel } from './algebra_polynomial_freyd_snake_category';
import { algebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact';
import { algebraPolynomialFreydHomologyConnecting } from './algebra_polynomial_freyd_homology_connecting';
import { algebraPolynomialFreydHomologyWindow } from './algebra_polynomial_freyd_homology_window';
import {
    algebraPolynomialFreydBoundedLongExactHomology, algebraPolynomialFreydLongExactWindowAt
} from './algebra_polynomial_freyd_long_exact';
import { algebraPolynomialFreydSnakeExactSequenceFromConnecting } from './algebra_polynomial_freyd_snake_exact';
import {
    algebraPolynomialFreydLongExactReferenceOperations,
    algebraPolynomialFreydHomologyConnectingSnakeReference,
    algebraPolynomialFreydLongExactSnakeReferences
} from './algebra_polynomial_freyd_long_exact_reference_operations';

export const ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-long-exact-category-v1' as const,
    programBoundary: 'whole-bounded-result-and-retained-reference-family' as const,
    derivedCallbackInlining: false as const,
    claimsFormalCategory: false as const,
    dualImplementation: false as const,
    performsIo: false as const
});

export function algebraPolynomialFreydLongExactCategoryModel<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(ring: AlgebraPolynomialRing<P, C, I>) {
    const homology = algebraPolynomialFreydHomologyCategoryModel(ring);
    const snake = algebraPolynomialFreydSnakeCategoryModel(ring);
    const native = algebraPolynomialFreydLongExactReferenceOperations(ring, snake.native.connecting.output);
    const revision = ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_CATEGORY_PROFILE.revision;
    const prefix = 'algebra.category.polynomial-freyd-long-exact/' + ring.identity.id;
    const operation = <Input, Output>(name: string, op: AlgebraOperation<Input, Output>) =>
        defineCategoryOperation({ id: prefix + '/' + name, revision, input: op.input, output: op.output });
    const boundedShortExact = operation('bounded-short-exact', native.boundedShortExact);
    const homologyConnecting = operation('homology-connecting', native.homologyConnecting);
    const homologyWindow = operation('homology-window', native.homologyWindow);
    const boundedLongExact = operation('bounded-long-exact', native.boundedLongExact);
    const windowAt = operation('window-at', native.windowAt);
    const windowConnecting = operation('window-connecting', native.windowConnecting);
    const connectingSnake = operation('connecting-reference-snake', native.connectingSnake);
    const snakeExactSequence = operation('snake-exact-sequence', native.snakeExactSequence);
    const snakeReferences = operation('snake-reference-family', native.snakeReferences);
    const operations = Object.freeze({
        boundedShortExact, homologyConnecting, homologyWindow, boundedLongExact,
        windowAt, windowConnecting, connectingSnake, snakeExactSequence, snakeReferences
    });
    const preabelian = homology.base.base.operations;
    const abelian = homology.base.operations;
    const method = <Input, Output>(
        name: string, op: CategoryOperation<Input, Output>, kind: 'primitive' | 'derived',
        prerequisites: readonly CategoryOperation<unknown, unknown>[], execute: (input: Input) => Output
    ) => defineCategoryMethod({ id: prefix + '/method/' + name, operation: op, kind, prerequisites, execute });
    const methods = [
        method('bounded-short-exact', boundedShortExact, 'derived', [snake.operations.shortExactTriple],
            algebraPolynomialFreydBoundedShortExactSequence),
        method('homology-connecting', homologyConnecting, 'derived', [
            homology.operations.homologyAt, snake.operations.snakeConnecting,
            preabelian.kernelLift, preabelian.cokernel, preabelian.cokernelColift,
            abelian.monomorphismWitness, abelian.liftAlongMonomorphism, abelian.coliftAlongEpimorphism
        ], input => algebraPolynomialFreydHomologyConnecting(input.sequence, input.degree)),
        method('homology-window', homologyWindow, 'derived', [
            homologyConnecting, homology.operations.homologyAt,
            homology.operations.inducedHomologyMap, homology.operations.exactnessAt
        ], input => algebraPolynomialFreydHomologyWindow(input.sequence, input.degree)),
        method('bounded-long-exact', boundedLongExact, 'derived', [homologyWindow],
            algebraPolynomialFreydBoundedLongExactHomology),
        method('window-at', windowAt, 'primitive', [], input => algebraPolynomialFreydLongExactWindowAt(input.result, input.degree)),
        method('window-connecting', windowConnecting, 'primitive', [], input => input.connecting),
        method('connecting-reference-snake', connectingSnake, 'primitive', [], algebraPolynomialFreydHomologyConnectingSnakeReference),
        method('snake-exact-sequence', snakeExactSequence, 'derived', [
            preabelian.kernel, preabelian.kernelLift, preabelian.cokernel,
            preabelian.cokernelColift, homology.operations.exactnessAt
        ], algebraPolynomialFreydSnakeExactSequenceFromConnecting),
        method('snake-reference-family', snakeReferences, 'derived', [snakeExactSequence],
            algebraPolynomialFreydLongExactSnakeReferences)
    ];
    // The homology category already contains the common Abelian base. Add
    // only snake-owned methods, never a second copy of that inherited base.
    const snakeIds = new Set(Object.values(snake.operations).map(op => op.id));
    const snakeMethods = snake.category.operations.methods.filter(m => snakeIds.has(m.operation.id));
    const category = defineComputableCategory({
        id: prefix, revision,
        objectSchema: homology.category.objectSchema,
        morphismSchema: homology.category.morphismSchema,
        operations: createCategoryOperationRegistry([...homology.category.operations.methods, ...snakeMethods, ...methods]),
        source: value => homology.category.source(value),
        target: value => homology.category.target(value),
        identityMorphism: value => homology.category.identityMorphism(value),
        compose: (after, before) => homology.category.compose(after, before),
        equalObjects: (left, right) => homology.category.equalObjects(left, right),
        equalMorphisms: (left, right) => homology.category.equalMorphisms(left, right)
    });
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-freyd-long-exact',
        inputDoctrineId: 'abelian-category', outputDoctrineId: 'abelian-category',
        introducedRoles: [
            'short-exact-bounded-complex', 'homology-connecting', 'homology-window',
            'bounded-long-exact-homology', 'long-exact-window',
            'homology-connecting-observation', 'homology-snake-reference',
            'snake-exact-sequence', 'long-exact-snake-references'
        ],
        objectLayer: 'unchanged-polynomial-presentation',
        morphismLayer: 'unchanged-target-factorization-quotient',
        // A prospective metadata route, not an installed dual implementation.
        dualConstructorId: 'category-constructor.polynomial-freyd-long-coexact',
        loweringRules: [{
            id: 'polynomial-freyd-long-exact.whole-operation', kind: 'operation-lowering',
            source: 'retained-homology-windows', target: native.boundedLongExact.identity.id
        }]
    });
    const tower = buildCategoricalTower(
        'algebra.tower.polynomial-freyd-long-exact/' + ring.identity.id,
        ALGEBRA_BASE_DOCTRINES, homology.tower.baseDoctrineId,
        [...homology.tower.constructors, ...snake.tower.constructors.slice(-1), constructor]
    );
    const lowerings = Object.freeze([
        ...homology.lowerings,
        ...snake.lowerings.filter(lowering => snakeIds.has(lowering.categoryOperation.id)),
        { categoryOperation: boundedShortExact, algebraOperation: native.boundedShortExact },
        { categoryOperation: homologyConnecting, algebraOperation: native.homologyConnecting },
        { categoryOperation: homologyWindow, algebraOperation: native.homologyWindow },
        { categoryOperation: boundedLongExact, algebraOperation: native.boundedLongExact },
        { categoryOperation: windowAt, algebraOperation: native.windowAt },
        { categoryOperation: windowConnecting, algebraOperation: native.windowConnecting },
        { categoryOperation: connectingSnake, algebraOperation: native.connectingSnake },
        { categoryOperation: snakeExactSequence, algebraOperation: native.snakeExactSequence },
        { categoryOperation: snakeReferences, algebraOperation: native.snakeReferences }
    ] as CategoryOperationLowering[]);
    return Object.freeze({ homology, snake, category, operations, native, tower, lowerings });
}

export type AlgebraPolynomialFreydLongExactCategoryModel<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydLongExactCategoryModel<P, C, I>>;

export function compileAlgebraPolynomialFreydLongExactProgram<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(model: AlgebraPolynomialFreydLongExactCategoryModel<P, C, I>, program: CategoricalProgram) {
    return compileCategoricalProgram({
        program, category: model.category as unknown as ComputableCategory<unknown, unknown>,
        tower: model.tower, lowerings: model.lowerings
    });
}

export function createAlgebraPolynomialFreydLongExactEngine<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(model: AlgebraPolynomialFreydLongExactCategoryModel<P, C, I>) {
    const h = model.homology;
    return createAlgebraTypeScriptReferenceEngine({
        id: 'algebra.typescript-reference.polynomial-freyd-long-exact/' + model.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_CATEGORY_PROFILE.revision,
        implementations: [
            ...h.base.base.base.native.implementations,
            ...h.base.base.base.nativeAdditiveOperations.implementations,
            ...h.base.base.native.implementations, ...h.base.native.implementations,
            ...h.native.implementations, ...model.snake.native.implementations,
            ...model.native.implementations
        ]
    });
}
