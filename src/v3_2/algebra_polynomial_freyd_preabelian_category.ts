/** Operational pre-Abelian polynomial Freyd category from constructive kernels/cokernels. */

import {
    AlgebraElement,
    AlgebraParent
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
    DoctrineQualification,
    PREABELIAN_DOCTRINE,
    qualifyCategoryDoctrine
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
    AlgebraPolynomialFreydCategoryModel,
    algebraPolynomialFreydCategoryModel
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydKernel,
    AlgebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernel,
    AlgebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_FREYD_PREABELIAN_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-preabelian-v1' as const,
    doctrine: PREABELIAN_DOCTRINE.id,
    kernelProvider: 'two-polynomial-weak-pullbacks' as const,
    cokernelProvider: 'adjoin-target-relations' as const,
    claimsAbelianStructure: false as const,
    performsIo: false as const
});

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPolynomialFreydKernelLiftInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly maximumReductionSteps?: number;
}

export interface AlgebraPolynomialFreydCokernelColiftInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydPreAbelianOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kernel: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydKernel<P, C, I>
    >;
    readonly kernelObject: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly kernelEmbedding: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly kernelLift: CategoryOperation<
        AlgebraPolynomialFreydKernelLiftInput<P, C, I>,
        AlgebraPolynomialFreydKernelLift<P, C, I>
    >;
    readonly cokernel: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydCokernel<P, C, I>
    >;
    readonly cokernelObject: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly cokernelProjection: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly cokernelColift: CategoryOperation<
        AlgebraPolynomialFreydCokernelColiftInput<P, C, I>,
        AlgebraPolynomialFreydCokernelColift<P, C, I>
    >;
}

export interface AlgebraPolynomialFreydPreAbelianNativeOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations: {
        readonly [K in keyof AlgebraPolynomialFreydPreAbelianOperations<P, C, I>]:
            AlgebraPolynomialFreydPreAbelianOperations<P, C, I>[K] extends
                CategoryOperation<infer Input, infer Output>
                ? AlgebraOperation<Input, Output>
                : never;
    };
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export interface AlgebraPolynomialFreydPreAbelianCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly base: AlgebraPolynomialFreydCategoryModel<P, C, I>;
    readonly category: ComputableCategory<
        AlgebraPresentedPolynomialModule<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly operations: AlgebraPolynomialFreydPreAbelianOperations<P, C, I>;
    readonly native:
        AlgebraPolynomialFreydPreAbelianNativeOperations<P, C, I>;
    readonly qualification: DoctrineQualification;
    readonly tower: CategoricalTower;
    readonly lowerings: readonly CategoryOperationLowering[];
}

const eraseCategory = <O, M>(category: ComputableCategory<O, M>):
    ComputableCategory<unknown, unknown> =>
    category as unknown as ComputableCategory<unknown, unknown>;

export function algebraPolynomialFreydPreAbelianCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialFreydPreAbelianCategoryModel<P, C, I> {
    if ((ring.coefficientDomain as { field?: unknown }).field !== true) {
        throw new Error(
            'Polynomial Freyd pre-Abelian capability requires field coefficients'
        );
    }
    const base = algebraPolynomialFreydCategoryModel(ring);
    const objectSchema = base.category.objectSchema;
    const morphismSchema = base.category.morphismSchema;
    const revision = ALGEBRA_POLYNOMIAL_FREYD_PREABELIAN_PROFILE.revision;
    const prefix = `algebra.category.polynomial-freyd-preabelian/` +
        ring.identity.id;

    const kernelSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydKernel<P, C, I>
    >({
        id: `${prefix}/kernel-result`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-freyd-kernel') {
                throw new Error(`Freyd kernel expected at ${path}`);
            }
            return value as unknown as AlgebraPolynomialFreydKernel<P, C, I>;
        }
    });
    const cokernelSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydCokernel<P, C, I>
    >({
        id: `${prefix}/cokernel-result`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-freyd-cokernel') {
                throw new Error(`Freyd cokernel expected at ${path}`);
            }
            return value as unknown as AlgebraPolynomialFreydCokernel<P, C, I>;
        }
    });
    const kernelLiftInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydKernelLiftInput<P, C, I>
    >({
        id: `${prefix}/kernel-lift-input`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`kernel lift input expected at ${path}`);
            const maximumReductionSteps = value.maximumReductionSteps;
            if (
                maximumReductionSteps !== undefined &&
                (!Number.isSafeInteger(maximumReductionSteps) ||
                    (maximumReductionSteps as number) <= 0)
            ) throw new Error(`invalid kernel lift bound at ${path}`);
            return Object.freeze({
                morphism: morphismSchema.normalize(
                    value.morphism,
                    `${path}.morphism`
                ),
                test: morphismSchema.normalize(value.test, `${path}.test`),
                ...(maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: maximumReductionSteps as number })
            });
        }
    });
    const kernelLiftSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydKernelLift<P, C, I>
    >({
        id: `${prefix}/kernel-lift-result`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-freyd-kernel-lift') {
                throw new Error(`Freyd kernel lift expected at ${path}`);
            }
            return value as unknown as AlgebraPolynomialFreydKernelLift<P, C, I>;
        }
    });
    const cokernelColiftInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydCokernelColiftInput<P, C, I>
    >({
        id: `${prefix}/cokernel-colift-input`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`cokernel colift input expected at ${path}`);
            }
            return Object.freeze({
                morphism: morphismSchema.normalize(
                    value.morphism,
                    `${path}.morphism`
                ),
                test: morphismSchema.normalize(value.test, `${path}.test`)
            });
        }
    });
    const cokernelColiftSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydCokernelColift<P, C, I>
    >({
        id: `${prefix}/cokernel-colift-result`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !==
                'algebra-polynomial-freyd-cokernel-colift') {
                throw new Error(`Freyd cokernel colift expected at ${path}`);
            }
            return value as unknown as AlgebraPolynomialFreydCokernelColift<P, C, I>;
        }
    });

    const kernel = defineCategoryOperation({
        id: `${prefix}/kernel`, revision,
        input: morphismSchema, output: kernelSchema
    });
    const kernelObject = defineCategoryOperation({
        id: `${prefix}/kernel-object`, revision,
        input: morphismSchema, output: objectSchema
    });
    const kernelEmbedding = defineCategoryOperation({
        id: `${prefix}/kernel-embedding`, revision,
        input: morphismSchema, output: morphismSchema
    });
    const kernelLift = defineCategoryOperation({
        id: `${prefix}/kernel-lift`, revision,
        input: kernelLiftInputSchema, output: kernelLiftSchema
    });
    const cokernel = defineCategoryOperation({
        id: `${prefix}/cokernel`, revision,
        input: morphismSchema, output: cokernelSchema
    });
    const cokernelObject = defineCategoryOperation({
        id: `${prefix}/cokernel-object`, revision,
        input: morphismSchema, output: objectSchema
    });
    const cokernelProjection = defineCategoryOperation({
        id: `${prefix}/cokernel-projection`, revision,
        input: morphismSchema, output: morphismSchema
    });
    const cokernelColift = defineCategoryOperation({
        id: `${prefix}/cokernel-colift`, revision,
        input: cokernelColiftInputSchema, output: cokernelColiftSchema
    });
    const operations = Object.freeze({
        kernel,
        kernelObject,
        kernelEmbedding,
        kernelLift,
        cokernel,
        cokernelObject,
        cokernelProjection,
        cokernelColift
    });
    const newMethods = [
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.kernel.primitive',
            operation: kernel,
            kind: 'primitive',
            execute: morphism => algebraPolynomialFreydKernel(morphism)
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.kernel-object.derived',
            operation: kernelObject,
            kind: 'derived',
            prerequisites: [kernel],
            execute: async (morphism, context) =>
                (await context.call(kernel, morphism)).object
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.kernel-embedding.derived',
            operation: kernelEmbedding,
            kind: 'derived',
            prerequisites: [kernel],
            execute: async (morphism, context) =>
                (await context.call(kernel, morphism)).embedding
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.kernel-lift.derived',
            operation: kernelLift,
            kind: 'derived',
            prerequisites: [kernel],
            execute: async (input, context) => algebraPolynomialFreydKernelLift(
                await context.call(kernel, input.morphism),
                input.test,
                input.maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: input.maximumReductionSteps }
            )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.cokernel.primitive',
            operation: cokernel,
            kind: 'primitive',
            execute: algebraPolynomialFreydCokernel
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.cokernel-object.derived',
            operation: cokernelObject,
            kind: 'derived',
            prerequisites: [cokernel],
            execute: async (morphism, context) =>
                (await context.call(cokernel, morphism)).object
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.cokernel-projection.derived',
            operation: cokernelProjection,
            kind: 'derived',
            prerequisites: [cokernel],
            execute: async (morphism, context) =>
                (await context.call(cokernel, morphism)).projection
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-preabelian.cokernel-colift.derived',
            operation: cokernelColift,
            kind: 'derived',
            prerequisites: [cokernel],
            execute: async (input, context) =>
                algebraPolynomialFreydCokernelColift(
                    await context.call(cokernel, input.morphism),
                    input.test
                )
        })
    ];
    const category = defineComputableCategory({
        id: prefix,
        revision,
        objectSchema,
        morphismSchema,
        operations: createCategoryOperationRegistry([
            ...base.category.operations.methods,
            ...newMethods
        ]),
        source: morphism => base.category.source(morphism),
        target: morphism => base.category.target(morphism),
        identityMorphism: object => base.category.identityMorphism(object),
        compose: (after, before) => base.category.compose(after, before),
        equalObjects: (left, right) => base.category.equalObjects(left, right),
        equalMorphisms: (left, right) => base.category.equalMorphisms(left, right)
    });
    const qualification = qualifyCategoryDoctrine(
        eraseCategory(category),
        ALGEBRA_BASE_DOCTRINES,
        PREABELIAN_DOCTRINE.id,
        [
            { role: 'zero-morphism', operation: base.operations.zeroMorphism },
            { role: 'add-morphisms', operation: base.operations.addMorphisms },
            { role: 'negate-morphism', operation: base.operations.negateMorphism },
            { role: 'zero-object', operation: base.operations.zeroObject },
            { role: 'biproduct', operation: base.operations.biproduct },
            { role: 'kernel', operation: kernel },
            { role: 'kernel-object', operation: kernelObject },
            { role: 'kernel-embedding', operation: kernelEmbedding },
            { role: 'kernel-lift', operation: kernelLift },
            { role: 'cokernel', operation: cokernel },
            { role: 'cokernel-object', operation: cokernelObject },
            { role: 'cokernel-projection', operation: cokernelProjection },
            { role: 'cokernel-colift', operation: cokernelColift }
        ]
    );
    if (qualification.status !== 'qualified') {
        throw new Error(
            `Polynomial Freyd pre-Abelian qualification missing: ` +
            qualification.missingRoles.join(', ')
        );
    }
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-freyd-preabelian',
        inputDoctrineId: 'additive-category',
        outputDoctrineId: 'preabelian-category',
        introducedRoles: [
            'kernel', 'kernel-object', 'kernel-embedding', 'kernel-lift',
            'cokernel', 'cokernel-object', 'cokernel-projection',
            'cokernel-colift'
        ],
        objectLayer: 'unchanged-polynomial-presentation',
        morphismLayer: 'unchanged-target-factorization-quotient',
        dualConstructorId: 'category-constructor.polynomial-freyd-preabelian',
        loweringRules: [{
            id: 'polynomial-freyd-preabelian.constructive-universals',
            kind: 'operation-lowering',
            source: 'kernel-cokernel-role-family',
            target: 'typescript-polynomial-freyd-universals'
        }]
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-freyd-preabelian/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        base.tower.baseDoctrineId,
        [...base.tower.constructors, constructor]
    );

    const nativeOperation = <Input, Output>(
        operation: CategoryOperation<Input, Output>
    ): AlgebraOperation<Input, Output> => defineAlgebraOperation({
        id: operation.id.replace('algebra.category.', 'algebra.'),
        revision: operation.revision,
        input: operation.input,
        output: operation.output
    });
    const nativeOperations = Object.freeze({
        kernel: nativeOperation(kernel),
        kernelObject: nativeOperation(kernelObject),
        kernelEmbedding: nativeOperation(kernelEmbedding),
        kernelLift: nativeOperation(kernelLift),
        cokernel: nativeOperation(cokernel),
        cokernelObject: nativeOperation(cokernelObject),
        cokernelProjection: nativeOperation(cokernelProjection),
        cokernelColift: nativeOperation(cokernelColift)
    });
    const algorithm = (operation: AlgebraOperation<unknown, unknown>) =>
        algebraAlgorithmIdentity(
            `algebra.typescript-reference/${operation.identity.id}`,
            revision
        );
    const implementation = <Input, Output>(
        operation: AlgebraOperation<Input, Output>,
        execute: (input: Input) => Output
    ): AlgebraReferenceImplementation => defineAlgebraReferenceImplementation({
        operation,
        algorithm: algorithm(operation as AlgebraOperation<unknown, unknown>),
        execute
    });
    const implementations = Object.freeze([
        implementation(nativeOperations.kernel, algebraPolynomialFreydKernel),
        implementation(nativeOperations.kernelObject,
            morphism => algebraPolynomialFreydKernel(morphism).object),
        implementation(nativeOperations.kernelEmbedding,
            morphism => algebraPolynomialFreydKernel(morphism).embedding),
        implementation(nativeOperations.kernelLift, input =>
            algebraPolynomialFreydKernelLift(
                algebraPolynomialFreydKernel(input.morphism),
                input.test,
                input.maximumReductionSteps === undefined
                    ? {}
                    : { maximumReductionSteps: input.maximumReductionSteps }
            )),
        implementation(nativeOperations.cokernel, algebraPolynomialFreydCokernel),
        implementation(nativeOperations.cokernelObject,
            morphism => algebraPolynomialFreydCokernel(morphism).object),
        implementation(nativeOperations.cokernelProjection,
            morphism => algebraPolynomialFreydCokernel(morphism).projection),
        implementation(nativeOperations.cokernelColift, input =>
            algebraPolynomialFreydCokernelColift(
                algebraPolynomialFreydCokernel(input.morphism),
                input.test
            ))
    ]);
    const native = Object.freeze({
        operations: nativeOperations,
        implementations
    }) as AlgebraPolynomialFreydPreAbelianNativeOperations<P, C, I>;
    const newLowerings = (Object.keys(operations) as
        (keyof typeof operations)[]).map(key => Object.freeze({
            categoryOperation: operations[key],
            algebraOperation: nativeOperations[key]
        }) as CategoryOperationLowering);
    const lowerings = Object.freeze([
        ...base.lowerings,
        ...newLowerings
    ]);
    return Object.freeze({
        base,
        category,
        operations,
        native,
        qualification,
        tower,
        lowerings
    });
}

export const compileAlgebraPolynomialFreydPreAbelianProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialFreydPreAbelianCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: eraseCategory(model.category),
    tower: model.tower,
    lowerings: model.lowerings
});

export const createAlgebraPolynomialFreydPreAbelianEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialFreydPreAbelianCategoryModel<P, C, I>):
    AlgebraEngine => createAlgebraTypeScriptReferenceEngine({
    id: `algebra.typescript-reference.polynomial-freyd-preabelian/` +
        model.base.category.identity.id,
    revision: ALGEBRA_POLYNOMIAL_FREYD_PREABELIAN_PROFILE.revision,
    implementations: [
        ...model.base.native.implementations,
        ...model.base.nativeAdditiveOperations.implementations,
        ...model.native.implementations
    ]
});
