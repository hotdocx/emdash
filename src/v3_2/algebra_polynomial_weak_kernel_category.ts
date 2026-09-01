/** Additive finite-free polynomial category with computational weak kernels. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraEngine,
    AlgebraOperation,
    algebraAlgorithmIdentity,
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
    COMPUTATIONAL_WEAK_KERNEL_DOCTRINE,
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
    AlgebraPolynomialRing,
    algebraPolynomialOne,
    algebraPolynomialZero
} from './algebra_polynomial';
import {
    AlgebraPolynomialFreeModule,
    AlgebraPolynomialModuleVector,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapAdd,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapNegate,
    algebraPolynomialModuleMapZero
} from './algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialWeakKernel,
    AlgebraPolynomialWeakKernelFactorization,
    algebraPolynomialModuleMapWeakKernel,
    algebraPolynomialWeakKernelFactor
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_WEAK_KERNEL_CATEGORY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-weak-kernel-category-v1' as const,
    doctrine: COMPUTATIONAL_WEAK_KERNEL_DOCTRINE.id,
    representation: 'finite-free-polynomial-column-matrices' as const,
    weakKernelProvider: 'original-column-groebner-syzygies' as const,
    claimsKernel: false as const,
    claimsAbelianStructure: false as const,
    performsIo: false as const
});

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPolynomialWeakKernelZeroInput {
    readonly kind: 'algebra-polynomial-weak-kernel-zero-input';
}

export const ALGEBRA_POLYNOMIAL_WEAK_KERNEL_ZERO_INPUT = Object.freeze({
    kind: 'algebra-polynomial-weak-kernel-zero-input' as const
});

export interface AlgebraPolynomialFreeModulePair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraPolynomialFreeModule<P, C, I>;
    readonly right: AlgebraPolynomialFreeModule<P, C, I>;
}

export interface AlgebraPolynomialModuleMapPair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraPolynomialModuleMap<P, C, I>;
    readonly right: AlgebraPolynomialModuleMap<P, C, I>;
}

export interface AlgebraPolynomialModuleMapEndpoints<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly source: AlgebraPolynomialFreeModule<P, C, I>;
    readonly target: AlgebraPolynomialFreeModule<P, C, I>;
}

export interface AlgebraPolynomialWeakKernelLiftInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
    readonly test: AlgebraPolynomialModuleMap<P, C, I>;
    readonly maximumReductionSteps?: number;
}

export interface AlgebraPolynomialFiniteFreeBiproduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-finite-free-biproduct';
    readonly left: AlgebraPolynomialFreeModule<P, C, I>;
    readonly right: AlgebraPolynomialFreeModule<P, C, I>;
    readonly object: AlgebraPolynomialFreeModule<P, C, I>;
    readonly injectionLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly injectionRight: AlgebraPolynomialModuleMap<P, C, I>;
    readonly projectionLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly projectionRight: AlgebraPolynomialModuleMap<P, C, I>;
}

const assertSameRing = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialFreeModule<P, C, I>,
    right: AlgebraPolynomialFreeModule<P, C, I>,
    path: string
): void => {
    if (!sameAlgebraParent(left.ring, right.ring)) {
        throw new Error(`Polynomial free modules use different rings at ${path}`);
    }
};

const zeroVector = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    module: AlgebraPolynomialFreeModule<P, C, I>
): AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
    module,
    Array.from({ length: module.rank }, () =>
        algebraPolynomialZero(module.ring)
    )
);

const basisVector = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    module: AlgebraPolynomialFreeModule<P, C, I>,
    index: number
): AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
    module,
    Array.from({ length: module.rank }, (_, position) =>
        position === index
            ? algebraPolynomialOne(module.ring)
            : algebraPolynomialZero(module.ring)
    )
);

const embedVector = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    vector: AlgebraPolynomialModuleVector<P, C, I>,
    target: AlgebraPolynomialFreeModule<P, C, I>,
    leftRank: number,
    side: 'left' | 'right'
): AlgebraPolynomialModuleVector<P, C, I> => algebraPolynomialModuleVector(
    target,
    side === 'left'
        ? [
            ...vector.components,
            ...Array.from(
                { length: target.rank - vector.parent.rank },
                () => algebraPolynomialZero(target.ring)
            )
        ]
        : [
            ...Array.from(
                { length: leftRank },
                () => algebraPolynomialZero(target.ring)
            ),
            ...vector.components
        ]
);

export function algebraPolynomialFiniteFreeDirectSumObject<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialFreeModule<P, C, I>,
    right: AlgebraPolynomialFreeModule<P, C, I>
): AlgebraPolynomialFreeModule<P, C, I> {
    assertSameRing(left, right, 'finiteFreeDirectSum');
    return algebraPolynomialFreeModule(
        left.ring,
        left.rank + right.rank,
        'term-over-position'
    );
}

export function algebraPolynomialFiniteFreeDirectSumMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>
): AlgebraPolynomialModuleMap<P, C, I> {
    assertSameRing(left.source, right.source, 'finiteFreeDirectSumMap.source');
    assertSameRing(left.target, right.target, 'finiteFreeDirectSumMap.target');
    const source = algebraPolynomialFiniteFreeDirectSumObject(
        left.source,
        right.source
    );
    const target = algebraPolynomialFiniteFreeDirectSumObject(
        left.target,
        right.target
    );
    return algebraPolynomialModuleMap(source, target, [
        ...left.columns.map(column => embedVector(
            column,
            target,
            left.target.rank,
            'left'
        )),
        ...right.columns.map(column => embedVector(
            column,
            target,
            left.target.rank,
            'right'
        ))
    ]);
}

export function algebraPolynomialFiniteFreeBiproduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialFreeModule<P, C, I>,
    right: AlgebraPolynomialFreeModule<P, C, I>
): AlgebraPolynomialFiniteFreeBiproduct<P, C, I> {
    const object = algebraPolynomialFiniteFreeDirectSumObject(left, right);
    return Object.freeze({
        kind: 'algebra-polynomial-finite-free-biproduct',
        left,
        right,
        object,
        injectionLeft: algebraPolynomialModuleMap(
            left,
            object,
            Array.from({ length: left.rank }, (_, index) =>
                basisVector(object, index)
            )
        ),
        injectionRight: algebraPolynomialModuleMap(
            right,
            object,
            Array.from({ length: right.rank }, (_, index) =>
                basisVector(object, left.rank + index)
            )
        ),
        projectionLeft: algebraPolynomialModuleMap(
            object,
            left,
            Array.from({ length: object.rank }, (_, index) =>
                index < left.rank ? basisVector(left, index) : zeroVector(left)
            )
        ),
        projectionRight: algebraPolynomialModuleMap(
            object,
            right,
            Array.from({ length: object.rank }, (_, index) =>
                index < left.rank
                    ? zeroVector(right)
                    : basisVector(right, index - left.rank)
            )
        )
    });
}

export interface AlgebraPolynomialWeakKernelCategoryOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly zeroMorphism: CategoryOperation<
        AlgebraPolynomialModuleMapEndpoints<P, C, I>,
        AlgebraPolynomialModuleMap<P, C, I>
    >;
    readonly addMorphisms: CategoryOperation<
        AlgebraPolynomialModuleMapPair<P, C, I>,
        AlgebraPolynomialModuleMap<P, C, I>
    >;
    readonly negateMorphism: CategoryOperation<
        AlgebraPolynomialModuleMap<P, C, I>,
        AlgebraPolynomialModuleMap<P, C, I>
    >;
    readonly zeroObject: CategoryOperation<
        AlgebraPolynomialWeakKernelZeroInput,
        AlgebraPolynomialFreeModule<P, C, I>
    >;
    readonly biproduct: CategoryOperation<
        AlgebraPolynomialFreeModulePair<P, C, I>,
        AlgebraPolynomialFiniteFreeBiproduct<P, C, I>
    >;
    readonly directSumMorphism: CategoryOperation<
        AlgebraPolynomialModuleMapPair<P, C, I>,
        AlgebraPolynomialModuleMap<P, C, I>
    >;
    readonly weakKernel: CategoryOperation<
        AlgebraPolynomialModuleMap<P, C, I>,
        AlgebraPolynomialWeakKernel<P, C, I>
    >;
    readonly weakKernelObject: CategoryOperation<
        AlgebraPolynomialModuleMap<P, C, I>,
        AlgebraPolynomialFreeModule<P, C, I>
    >;
    readonly weakKernelMorphism: CategoryOperation<
        AlgebraPolynomialModuleMap<P, C, I>,
        AlgebraPolynomialModuleMap<P, C, I>
    >;
    readonly weakKernelLift: CategoryOperation<
        AlgebraPolynomialWeakKernelLiftInput<P, C, I>,
        AlgebraPolynomialWeakKernelFactorization<P, C, I>
    >;
}

export interface AlgebraPolynomialWeakKernelNativeOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations: Readonly<{
        [K in keyof AlgebraPolynomialWeakKernelCategoryOperations<P, C, I>]:
            AlgebraOperation<unknown, unknown>;
    }>;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export interface AlgebraPolynomialWeakKernelCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraPolynomialFreeModule<P, C, I>,
        AlgebraPolynomialModuleMap<P, C, I>
    >;
    readonly operations: AlgebraPolynomialWeakKernelCategoryOperations<P, C, I>;
    readonly native: AlgebraPolynomialWeakKernelNativeOperations<P, C, I>;
    readonly qualification: DoctrineQualification;
    readonly tower: CategoricalTower;
    readonly reinterpretation: ComputationalReinterpretation<
        AlgebraPolynomialFreeModule<P, C, I>,
        AlgebraPolynomialFreeModule<P, C, I>
    >;
    readonly lowerings: readonly CategoryOperationLowering[];
}

export function algebraPolynomialWeakKernelCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialWeakKernelCategoryModel<P, C, I> {
    const revision = ALGEBRA_POLYNOMIAL_WEAK_KERNEL_CATEGORY_PROFILE.revision;
    const objectSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreeModule<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-object/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'polynomial-free-module' ||
                !record(value.identity)) {
                throw new Error(`polynomial free module expected at ${path}`);
            }
            const module = value as unknown as AlgebraPolynomialFreeModule<P, C, I>;
            if (!sameAlgebraParent(module.ring, ring)) {
                throw new Error(`foreign polynomial ring at ${path}`);
            }
            return module;
        }
    });
    const mapSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleMap<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-map/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'algebra-polynomial-module-map') {
                throw new Error(`polynomial module map expected at ${path}`);
            }
            const map = value as unknown as AlgebraPolynomialModuleMap<P, C, I>;
            objectSchema.normalize(map.source, `${path}.source`);
            objectSchema.normalize(map.target, `${path}.target`);
            return algebraPolynomialModuleMap(map.source, map.target, map.columns);
        }
    });
    const pairSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleMapPair<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-map-pair/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`module-map pair expected at ${path}`);
            return Object.freeze({
                left: mapSchema.normalize(value.left, `${path}.left`),
                right: mapSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const endpointSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleMapEndpoints<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-endpoints/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`module endpoints expected at ${path}`);
            return Object.freeze({
                source: objectSchema.normalize(value.source, `${path}.source`),
                target: objectSchema.normalize(value.target, `${path}.target`)
            });
        }
    });
    const objectPairSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreeModulePair<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-object-pair/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`module pair expected at ${path}`);
            return Object.freeze({
                left: objectSchema.normalize(value.left, `${path}.left`),
                right: objectSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const zeroInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialWeakKernelZeroInput
    >({
        id: `algebra.category.polynomial-finite-free-zero-input/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-weak-kernel-zero-input') {
                throw new Error(`zero-object input expected at ${path}`);
            }
            return ALGEBRA_POLYNOMIAL_WEAK_KERNEL_ZERO_INPUT;
        }
    });
    const biproductSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFiniteFreeBiproduct<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-biproduct/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-finite-free-biproduct') {
                throw new Error(`finite-free biproduct expected at ${path}`);
            }
            return algebraPolynomialFiniteFreeBiproduct(
                objectSchema.normalize(value.left, `${path}.left`),
                objectSchema.normalize(value.right, `${path}.right`)
            );
        }
    });
    const weakKernelSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialWeakKernel<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-weak-kernel/${ring.identity.id}`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'algebra-polynomial-weak-kernel') {
                throw new Error(`computational weak kernel expected at ${path}`);
            }
            return algebraPolynomialModuleMapWeakKernel(
                mapSchema.normalize(value.map, `${path}.map`)
            );
        }
    });
    const liftInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialWeakKernelLiftInput<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-weak-kernel-lift-input/` +
            ring.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`weak-kernel lift input expected at ${path}`);
            const maximumReductionSteps = value.maximumReductionSteps;
            if (maximumReductionSteps !== undefined &&
                (!Number.isSafeInteger(maximumReductionSteps) ||
                    (maximumReductionSteps as number) <= 0)) {
                throw new Error(`invalid weak-kernel lift limit at ${path}`);
            }
            return Object.freeze({
                map: mapSchema.normalize(value.map, `${path}.map`),
                test: mapSchema.normalize(value.test, `${path}.test`),
                ...(maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: maximumReductionSteps as number })
            });
        }
    });
    const factorSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialWeakKernelFactorization<P, C, I>
    >({
        id: `algebra.category.polynomial-finite-free-weak-kernel-factor/` +
            ring.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-weak-kernel-factorization') {
                throw new Error(`weak-kernel factorization expected at ${path}`);
            }
            const map = mapSchema.normalize(
                (value.weakKernel as { map?: unknown } | undefined)?.map,
                `${path}.weakKernel.map`
            );
            const test = mapSchema.normalize(value.test, `${path}.test`);
            return algebraPolynomialWeakKernelFactor(
                algebraPolynomialModuleMapWeakKernel(map),
                test
            );
        }
    });
    const prefix = `algebra.category.polynomial-finite-free/${ring.identity.id}`;
    const operation = <Input, Output>(
        id: string,
        input: ReturnType<typeof defineAlgebraRuntimeSchema<Input>>,
        output: ReturnType<typeof defineAlgebraRuntimeSchema<Output>>
    ): CategoryOperation<Input, Output> => defineCategoryOperation({
        id: `${prefix}/${id}`,
        revision,
        input,
        output
    });
    const zeroMorphism = operation('zero-morphism', endpointSchema, mapSchema);
    const addMorphisms = operation('add-morphisms', pairSchema, mapSchema);
    const negateMorphism = operation('negate-morphism', mapSchema, mapSchema);
    const zeroObject = operation('zero-object', zeroInputSchema, objectSchema);
    const biproduct = operation('biproduct', objectPairSchema, biproductSchema);
    const directSumMorphism = operation('direct-sum-morphism', pairSchema, mapSchema);
    const weakKernel = operation('weak-kernel', mapSchema, weakKernelSchema);
    const weakKernelObject = operation('weak-kernel-object', mapSchema, objectSchema);
    const weakKernelMorphism = operation('weak-kernel-morphism', mapSchema, mapSchema);
    const weakKernelLift = operation('weak-kernel-lift', liftInputSchema, factorSchema);
    const operations = Object.freeze({
        zeroMorphism,
        addMorphisms,
        negateMorphism,
        zeroObject,
        biproduct,
        directSumMorphism,
        weakKernel,
        weakKernelObject,
        weakKernelMorphism,
        weakKernelLift
    });
    const methods = [
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.zero.primitive',
            operation: zeroMorphism, kind: 'primitive',
            execute: value => algebraPolynomialModuleMapZero(value.source, value.target) }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.add.primitive',
            operation: addMorphisms, kind: 'primitive',
            execute: value => algebraPolynomialModuleMapAdd(value.left, value.right) }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.negate.primitive',
            operation: negateMorphism, kind: 'primitive',
            execute: algebraPolynomialModuleMapNegate }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.zero-object.primitive',
            operation: zeroObject, kind: 'primitive',
            execute: () => algebraPolynomialFreeModule(ring, 0) }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.biproduct.primitive',
            operation: biproduct, kind: 'primitive',
            execute: value => algebraPolynomialFiniteFreeBiproduct(value.left, value.right) }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.direct-sum.primitive',
            operation: directSumMorphism, kind: 'primitive',
            execute: value => algebraPolynomialFiniteFreeDirectSumMap(value.left, value.right) }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.weak-kernel.primitive',
            operation: weakKernel, kind: 'primitive',
            execute: value => algebraPolynomialModuleMapWeakKernel(value) }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.weak-kernel-object.derived',
            operation: weakKernelObject, kind: 'derived', prerequisites: [weakKernel],
            execute: async (value, context) => (await context.call(weakKernel, value)).object }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.weak-kernel-morphism.derived',
            operation: weakKernelMorphism, kind: 'derived', prerequisites: [weakKernel],
            execute: async (value, context) => (await context.call(weakKernel, value)).morphism }),
        defineCategoryMethod({ id: 'algebra.polynomial-finite-free.weak-kernel-lift.derived',
            operation: weakKernelLift, kind: 'derived', prerequisites: [weakKernel],
            execute: async (value, context) => algebraPolynomialWeakKernelFactor(
                await context.call(weakKernel, value.map),
                value.test,
                value.maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: value.maximumReductionSteps }
            ) })
    ];
    const category = defineComputableCategory({
        id: `algebra.category.polynomial-finite-free/${ring.identity.id}`,
        revision,
        objectSchema,
        morphismSchema: mapSchema,
        operations: createCategoryOperationRegistry(methods),
        source: map => map.source,
        target: map => map.target,
        identityMorphism: algebraPolynomialModuleMapIdentity,
        compose: algebraPolynomialModuleMapCompose,
        equalObjects: (left, right) => sameAlgebraParent(left, right),
        equalMorphisms: algebraPolynomialModuleMapEquals
    });
    const bindings = [
        { role: 'zero-morphism', operation: zeroMorphism },
        { role: 'add-morphisms', operation: addMorphisms },
        { role: 'negate-morphism', operation: negateMorphism },
        { role: 'zero-object', operation: zeroObject },
        { role: 'biproduct', operation: biproduct },
        { role: 'weak-kernel', operation: weakKernel },
        { role: 'weak-kernel-object', operation: weakKernelObject },
        { role: 'weak-kernel-morphism', operation: weakKernelMorphism },
        { role: 'weak-kernel-lift', operation: weakKernelLift }
    ];
    const qualification = qualifyCategoryDoctrine(
        category as unknown as ComputableCategory<unknown, unknown>,
        ALGEBRA_BASE_DOCTRINES,
        COMPUTATIONAL_WEAK_KERNEL_DOCTRINE.id,
        bindings
    );
    if (qualification.status !== 'qualified') {
        throw new Error(`Weak-kernel qualification missing: ${qualification.missingRoles.join(', ')}`);
    }
    const additiveConstructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-finite-free-additive',
        inputDoctrineId: 'category',
        outputDoctrineId: 'additive-category',
        introducedRoles: [
            'zero-morphism', 'add-morphisms', 'negate-morphism',
            'zero-object', 'biproduct'
        ],
        objectLayer: 'polynomial-free-module-rank',
        morphismLayer: 'polynomial-column-matrix',
        dualConstructorId: 'category-constructor.polynomial-finite-free-additive',
        loweringRules: []
    });
    const weakKernelConstructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-computational-weak-kernels',
        inputDoctrineId: 'additive-category',
        outputDoctrineId: COMPUTATIONAL_WEAK_KERNEL_DOCTRINE.id,
        introducedRoles: [
            'weak-kernel', 'weak-kernel-object',
            'weak-kernel-morphism', 'weak-kernel-lift'
        ],
        objectLayer: 'original-column-syzygy-module',
        morphismLayer: 'selected-syzygy-and-factor-matrices',
        dualConstructorId:
            'category-constructor.polynomial-computational-weak-cokernels',
        loweringRules: []
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-finite-free-weak-kernels/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        'category',
        [additiveConstructor, weakKernelConstructor]
    );
    const modelCategoryId = `algebra.category.polynomial-finite-free-model/${ring.identity.id}`;
    const reinterpretation = defineComputationalReinterpretation({
        id: `algebra.reinterpretation.polynomial-finite-free/${ring.identity.id}`,
        publicCategoryId: category.identity.id,
        modelingCategoryId: modelCategoryId,
        toModel: (value: AlgebraPolynomialFreeModule<P, C, I>) => value,
        fromModel: (value: AlgebraPolynomialFreeModule<P, C, I>) => value,
        loweringRules: [{ id: 'polynomial-finite-free.direct', kind: 'reinterpretation',
            source: modelCategoryId, target: category.identity.id }]
    });
    const nativeOperation = <Input, Output>(source: CategoryOperation<Input, Output>) =>
        defineAlgebraOperation({
            id: source.id.replace('algebra.category.', 'algebra.'),
            revision: source.revision,
            input: source.input,
            output: source.output
        });
    const nativeOperations = Object.freeze(Object.fromEntries(
        Object.entries(operations).map(([name, source]) => [
            name,
            nativeOperation(source as CategoryOperation<unknown, unknown>)
        ])
    ) as unknown as AlgebraPolynomialWeakKernelNativeOperations<P, C, I>['operations']);
    const implementations = Object.freeze(Object.entries(nativeOperations).map(
        ([name, nativeOperationValue]) => {
            const method = methods.find(candidate => candidate.operation.id ===
                operations[name as keyof typeof operations].id)!;
            return defineAlgebraReferenceImplementation({
                operation: nativeOperationValue,
                algorithm: algebraAlgorithmIdentity(
                    `algebra.typescript-reference/polynomial-finite-free-${name}`,
                    'v1'
                ),
                execute: (value, context) => method.execute(value, {
                    call: async (requested, input) => {
                        const requestedName = Object.entries(operations).find(
                            ([, operationValue]) => operationValue.id === requested.id
                        )?.[0] as keyof typeof operations | undefined;
                        if (requestedName === undefined) {
                            throw new Error(`Unknown weak-kernel prerequisite ${requested.id}`);
                        }
                        const requestedNative = nativeOperations[requestedName];
                        const requestedImplementation = implementations.find(
                            implementation => implementation.operation.identity.id ===
                                requestedNative.identity.id
                        );
                        if (requestedImplementation === undefined) {
                            throw new Error(`Missing weak-kernel prerequisite ${requested.id}`);
                        }
                        return (await requestedImplementation.execute(input, context)).value as never;
                    }
                })
            });
        }
    ));
    const native = Object.freeze({ operations: nativeOperations, implementations });
    const lowerings = Object.freeze(Object.entries(operations).map(([name, source]) => ({
        categoryOperation: source,
        algebraOperation: nativeOperations[name as keyof typeof nativeOperations]
    })) as CategoryOperationLowering[]);
    return Object.freeze({
        category,
        operations,
        native,
        qualification,
        tower,
        reinterpretation,
        lowerings
    });
}

export const compileAlgebraPolynomialWeakKernelProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialWeakKernelCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: model.category as unknown as ComputableCategory<unknown, unknown>,
    tower: model.tower,
    lowerings: model.lowerings,
    reinterpretations: [model.reinterpretation]
});

export const createAlgebraPolynomialWeakKernelEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialWeakKernelCategoryModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.polynomial-finite-free-weak-kernels/` +
            model.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_WEAK_KERNEL_CATEGORY_PROFILE.revision,
        implementations: model.native.implementations
    });
