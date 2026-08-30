/** Computable constructible inclusion category and staged/native bindings. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraEngine,
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import { AlgebraPolynomialRing, algebraPolynomialSchema } from './algebra_polynomial';
import { algebraPolynomialIdealSchema } from './algebra_ideal';
import {
    AlgebraConstructibleEquivalence,
    AlgebraConstructibleSet,
    algebraConstructibleDifference,
    algebraConstructibleEquivalence,
    algebraConstructibleIntersection,
    algebraConstructibleSet,
    algebraConstructibleUnion,
    algebraLocallyClosedPiece
} from './algebra_constructible';
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
    AlgebraConstructibleTowerModel,
    algebraConstructibleTowerModel
} from './algebra_constructible_tower';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_CONSTRUCTIBLE_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-constructible-category-v1' as const,
    morphism: 'computed-inclusion-with-retained-difference' as const,
    wholeOperations: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraConstructibleCategoryErrorCode =
    | 'NOT_INCLUDED'
    | 'NON_COMPOSABLE_INCLUSIONS';

export class AlgebraConstructibleCategoryError extends Error {
    constructor(
        public readonly code: AlgebraConstructibleCategoryErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraConstructibleCategoryError';
    }
}

const fail = (
    code: AlgebraConstructibleCategoryErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraConstructibleCategoryError(code, path, message);
};

export interface AlgebraConstructibleBinaryInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraConstructibleSet<P, C, I>;
    readonly right: AlgebraConstructibleSet<P, C, I>;
}

export interface AlgebraConstructibleInclusion<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-constructible-inclusion';
    readonly source: AlgebraConstructibleSet<P, C, I>;
    readonly target: AlgebraConstructibleSet<P, C, I>;
    readonly difference: AlgebraConstructibleSet<P, C, I>;
}

export function algebraConstructibleInclusion<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraConstructibleSet<P, C, I>,
    target: AlgebraConstructibleSet<P, C, I>
): AlgebraConstructibleInclusion<P, C, I> {
    const difference = algebraConstructibleDifference(source, target);
    if (!difference.empty) {
        return fail('NOT_INCLUDED', 'constructibleInclusion', 'Source is not included in target');
    }
    return Object.freeze({
        kind: 'algebra-constructible-inclusion',
        source,
        target,
        difference
    });
}

export interface AlgebraConstructibleCategoryOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly union: CategoryOperation<
        AlgebraConstructibleBinaryInput<P, C, I>,
        AlgebraConstructibleSet<P, C, I>
    >;
    readonly intersection: CategoryOperation<
        AlgebraConstructibleBinaryInput<P, C, I>,
        AlgebraConstructibleSet<P, C, I>
    >;
    readonly difference: CategoryOperation<
        AlgebraConstructibleBinaryInput<P, C, I>,
        AlgebraConstructibleSet<P, C, I>
    >;
    readonly equivalence: CategoryOperation<
        AlgebraConstructibleBinaryInput<P, C, I>,
        AlgebraConstructibleEquivalence<P, C, I>
    >;
}

export interface AlgebraConstructibleComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraConstructibleSet<P, C, I>,
        AlgebraConstructibleInclusion<P, C, I>
    >;
    readonly setSchema: AlgebraRuntimeSchema<AlgebraConstructibleSet<P, C, I>>;
    readonly binarySchema: AlgebraRuntimeSchema<AlgebraConstructibleBinaryInput<P, C, I>>;
    readonly operations: AlgebraConstructibleCategoryOperations<P, C, I>;
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export function algebraConstructibleComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>): AlgebraConstructibleComputableCategory<P, C, I> {
    const suffix = ring.identity.id;
    const idealSchema = algebraPolynomialIdealSchema(ring);
    const polynomialSchema = algebraPolynomialSchema(ring);
    const setSchema = defineAlgebraRuntimeSchema<AlgebraConstructibleSet<P, C, I>>({
        id: `algebra.constructible-set/${suffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'algebra-constructible-set' ||
                !Array.isArray(value.pieces)) {
                throw new Error(`constructible set expected at ${path}`);
            }
            return algebraConstructibleSet(ring, value.pieces.map((piece, index) => {
                if (!record(piece) || piece.kind !== 'algebra-locally-closed-piece') {
                    throw new Error(`locally closed piece expected at ${path}.pieces[${index}]`);
                }
                return algebraLocallyClosedPiece(
                    idealSchema.normalize(piece.sourceIdeal, `${path}.pieces[${index}].sourceIdeal`),
                    polynomialSchema.normalize(piece.open, `${path}.pieces[${index}].open`)
                );
            }));
        }
    });
    const binarySchema = defineAlgebraRuntimeSchema<
        AlgebraConstructibleBinaryInput<P, C, I>
    >({
        id: `algebra.constructible-binary/${suffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`constructible pair expected at ${path}`);
            return Object.freeze({
                left: setSchema.normalize(value.left, `${path}.left`),
                right: setSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const equivalenceSchema = defineAlgebraRuntimeSchema<
        AlgebraConstructibleEquivalence<P, C, I>
    >({
        id: `algebra.constructible-equivalence/${suffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'algebra-constructible-equivalence' ||
                typeof value.equivalent !== 'boolean') {
                throw new Error(`constructible equivalence expected at ${path}`);
            }
            return value as unknown as AlgebraConstructibleEquivalence<P, C, I>;
        }
    });
    const inclusionSchema = defineAlgebraRuntimeSchema<
        AlgebraConstructibleInclusion<P, C, I>
    >({
        id: `algebra.constructible-inclusion/${suffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'algebra-constructible-inclusion') {
                throw new Error(`constructible inclusion expected at ${path}`);
            }
            return algebraConstructibleInclusion(
                setSchema.normalize(value.source, `${path}.source`),
                setSchema.normalize(value.target, `${path}.target`)
            );
        }
    });
    const define = <O>(id: string, output: AlgebraRuntimeSchema<O>) =>
        defineCategoryOperation({
            id: `algebra.category.constructible.${id}/${suffix}`,
            revision: ring.identity.revision,
            input: binarySchema,
            output
        });
    const union = define('union', setSchema);
    const intersection = define('intersection', setSchema);
    const difference = define('difference', setSchema);
    const equivalence = define('equivalence', equivalenceSchema);
    const registry = createCategoryOperationRegistry([
        defineCategoryMethod({ id: 'algebra.constructible.union.primitive', operation: union,
            kind: 'primitive', execute: input => algebraConstructibleUnion(input.left, input.right) }),
        defineCategoryMethod({ id: 'algebra.constructible.intersection.primitive', operation: intersection,
            kind: 'primitive', execute: input => algebraConstructibleIntersection(input.left, input.right) }),
        defineCategoryMethod({ id: 'algebra.constructible.difference.primitive', operation: difference,
            kind: 'primitive', execute: input => algebraConstructibleDifference(input.left, input.right) }),
        defineCategoryMethod({ id: 'algebra.constructible.equivalence.primitive', operation: equivalence,
            kind: 'primitive', execute: input => algebraConstructibleEquivalence(input.left, input.right) })
    ]);
    const category = defineComputableCategory({
        id: `algebra.category.constructible/${suffix}`,
        revision: ring.identity.revision,
        objectSchema: setSchema,
        morphismSchema: inclusionSchema,
        operations: registry,
        source: value => value.source,
        target: value => value.target,
        identityMorphism: value => algebraConstructibleInclusion(value, value),
        compose(after, before) {
            if (!algebraConstructibleEquivalence(before.target, after.source).equivalent) {
                return fail('NON_COMPOSABLE_INCLUSIONS', 'constructibleCompose',
                    'Inclusion middle objects are not equal');
            }
            return algebraConstructibleInclusion(before.source, after.target);
        },
        equalObjects: (left, right) => algebraConstructibleEquivalence(left, right).equivalent,
        equalMorphisms: (left, right) =>
            algebraConstructibleEquivalence(left.source, right.source).equivalent &&
            algebraConstructibleEquivalence(left.target, right.target).equivalent
    });
    return Object.freeze({
        category,
        setSchema,
        binarySchema,
        operations: Object.freeze({ union, intersection, difference, equivalence })
    });
}

export interface AlgebraConstructibleNativeOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly union: AlgebraOperation<AlgebraConstructibleBinaryInput<P, C, I>, AlgebraConstructibleSet<P, C, I>>;
    readonly intersection: AlgebraOperation<AlgebraConstructibleBinaryInput<P, C, I>, AlgebraConstructibleSet<P, C, I>>;
    readonly difference: AlgebraOperation<AlgebraConstructibleBinaryInput<P, C, I>, AlgebraConstructibleSet<P, C, I>>;
    readonly equivalence: AlgebraOperation<AlgebraConstructibleBinaryInput<P, C, I>, AlgebraConstructibleEquivalence<P, C, I>>;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export interface AlgebraConstructibleModel<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly runtime: AlgebraConstructibleComputableCategory<P, C, I>;
    readonly towerModel: AlgebraConstructibleTowerModel<P, C, I>;
    readonly native: AlgebraConstructibleNativeOperations<P, C, I>;
    readonly lowerings: readonly CategoryOperationLowering[];
}

export function algebraConstructibleModel<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraConstructibleModel<P, C, I> {
    const runtime = algebraConstructibleComputableCategory(ring);
    const towerModel = algebraConstructibleTowerModel(ring);
    const make = <O>(operation: CategoryOperation<AlgebraConstructibleBinaryInput<P, C, I>, O>) =>
        defineAlgebraOperation({
            id: operation.id.replace('algebra.category.', 'algebra.'),
            revision: operation.revision,
            input: operation.input,
            output: operation.output
        });
    const union = make(runtime.operations.union);
    const intersection = make(runtime.operations.intersection);
    const difference = make(runtime.operations.difference);
    const equivalence = make(runtime.operations.equivalence);
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({ operation: union,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/constructible-union', 'v1'),
            execute: input => algebraConstructibleUnion(input.left, input.right) }),
        defineAlgebraReferenceImplementation({ operation: intersection,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/constructible-intersection', 'v1'),
            execute: input => algebraConstructibleIntersection(input.left, input.right) }),
        defineAlgebraReferenceImplementation({ operation: difference,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/constructible-difference', 'v1'),
            execute: input => algebraConstructibleDifference(input.left, input.right) }),
        defineAlgebraReferenceImplementation({ operation: equivalence,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/constructible-equivalence', 'v1'),
            execute: input => algebraConstructibleEquivalence(input.left, input.right) })
    ]);
    const native = Object.freeze({ union, intersection, difference, equivalence, implementations });
    const lowerings = Object.freeze([
        { categoryOperation: runtime.operations.union, algebraOperation: union },
        { categoryOperation: runtime.operations.intersection, algebraOperation: intersection },
        { categoryOperation: runtime.operations.difference, algebraOperation: difference },
        { categoryOperation: runtime.operations.equivalence, algebraOperation: equivalence }
    ] as CategoryOperationLowering[]);
    return Object.freeze({ runtime, towerModel, native, lowerings });
}

export const compileAlgebraConstructibleProgram = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    model: AlgebraConstructibleModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: model.runtime.category as unknown as ComputableCategory<unknown, unknown>,
    tower: model.towerModel.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.towerModel.reinterpretation]
});

export const createAlgebraConstructibleEngine = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    model: AlgebraConstructibleModel<P, C, I>
): AlgebraEngine => createAlgebraTypeScriptReferenceEngine({
    id: `algebra.typescript-reference.constructible/${model.towerModel.ring.identity.id}`,
    revision: ALGEBRA_CONSTRUCTIBLE_CATEGORY_PROFILE.revision,
    implementations: model.native.implementations
});
