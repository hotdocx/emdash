/** Operational Abelian polynomial Freyd category from constructive normality. */

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
    ABELIAN_DOCTRINE,
    ALGEBRA_BASE_DOCTRINES,
    DoctrineQualification,
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
    AlgebraPolynomialFreydKernel
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernel
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraPolynomialFreydColiftAlongEpimorphism,
    AlgebraPolynomialFreydEpimorphismWitness,
    AlgebraPolynomialFreydLiftAlongMonomorphism,
    AlgebraPolynomialFreydMonomorphismWitness,
    algebraPolynomialFreydColiftAlongEpimorphism,
    algebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydLiftAlongMonomorphism,
    algebraPolynomialFreydMonomorphismWitness
} from './algebra_polynomial_freyd_normality';
import {
    AlgebraPolynomialFreydImageCoimageIsomorphism,
    algebraPolynomialFreydImages
} from './algebra_polynomial_freyd_images';
import {
    AlgebraPolynomialFreydPreAbelianCategoryModel,
    algebraPolynomialFreydPreAbelianCategoryModel
} from './algebra_polynomial_freyd_preabelian_category';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_POLYNOMIAL_FREYD_ABELIAN_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-abelian-v1' as const,
    doctrine: ABELIAN_DOCTRINE.id,
    normality: 'posur-constructions-3.14-and-3.15' as const,
    imageCoimage: 'derived-canonical-comparison' as const,
    claimsClosedFormalInstance: false as const,
    performsIo: false as const
});

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraPolynomialFreydNormalFactorInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly maximumReductionSteps?: number;
}

export interface AlgebraPolynomialFreydAbelianOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly monomorphismWitness: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>
    >;
    readonly epimorphismWitness: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>
    >;
    readonly liftAlongMonomorphism: CategoryOperation<
        AlgebraPolynomialFreydNormalFactorInput<P, C, I>,
        AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>
    >;
    readonly coliftAlongEpimorphism: CategoryOperation<
        AlgebraPolynomialFreydNormalFactorInput<P, C, I>,
        AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>
    >;
    readonly image: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydKernel<P, C, I>
    >;
    readonly imageObject: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly imageEmbedding: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly coastrictionToImage: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly coimage: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydCokernel<P, C, I>
    >;
    readonly coimageObject: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPresentedPolynomialModule<P, C, I>
    >;
    readonly coimageProjection: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly astrictionFromCoimage: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly coimageImageComparison: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly coimageImageIsomorphism: CategoryOperation<
        AlgebraPolynomialPresentationMorphism<P, C, I>,
        AlgebraPolynomialFreydImageCoimageIsomorphism<P, C, I>
    >;
}

export interface AlgebraPolynomialFreydAbelianNativeOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations: {
        readonly [K in keyof AlgebraPolynomialFreydAbelianOperations<P, C, I>]:
            AlgebraPolynomialFreydAbelianOperations<P, C, I>[K] extends
                CategoryOperation<infer Input, infer Output>
                ? AlgebraOperation<Input, Output>
                : never;
    };
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export interface AlgebraPolynomialFreydAbelianCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly base: AlgebraPolynomialFreydPreAbelianCategoryModel<P, C, I>;
    readonly category: ComputableCategory<
        AlgebraPresentedPolynomialModule<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly operations: AlgebraPolynomialFreydAbelianOperations<P, C, I>;
    readonly native: AlgebraPolynomialFreydAbelianNativeOperations<P, C, I>;
    readonly qualification: DoctrineQualification;
    readonly tower: CategoricalTower;
    readonly lowerings: readonly CategoryOperationLowering[];
}

const eraseCategory = <O, M>(category: ComputableCategory<O, M>):
    ComputableCategory<unknown, unknown> =>
    category as unknown as ComputableCategory<unknown, unknown>;

export function algebraPolynomialFreydAbelianCategoryModel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>):
    AlgebraPolynomialFreydAbelianCategoryModel<P, C, I> {
    const base = algebraPolynomialFreydPreAbelianCategoryModel(ring);
    const objectSchema = base.category.objectSchema;
    const morphismSchema = base.category.morphismSchema;
    const revision = ALGEBRA_POLYNOMIAL_FREYD_ABELIAN_PROFILE.revision;
    const prefix = `algebra.category.polynomial-freyd-abelian/` +
        ring.identity.id;
    const kindSchema = <T>(id: string, kind: string) =>
        defineAlgebraRuntimeSchema<T>({
            id: `${prefix}/${id}`,
            revision,
            normalize(value: unknown, path: string) {
                if (!record(value) || value.kind !== kind) {
                    throw new Error(`${kind} expected at ${path}`);
                }
                return value as T;
            }
        });
    const monomorphismSchema = kindSchema<
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>
    >('monomorphism-witness-result',
        'algebra-polynomial-freyd-monomorphism-witness');
    const epimorphismSchema = kindSchema<
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>
    >('epimorphism-witness-result',
        'algebra-polynomial-freyd-epimorphism-witness');
    const monoLiftSchema = kindSchema<
        AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>
    >('lift-along-monomorphism-result',
        'algebra-polynomial-freyd-lift-along-monomorphism');
    const epiColiftSchema = kindSchema<
        AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>
    >('colift-along-epimorphism-result',
        'algebra-polynomial-freyd-colift-along-epimorphism');
    const kernelSchema = kindSchema<AlgebraPolynomialFreydKernel<P, C, I>>(
        'image-result', 'algebra-polynomial-freyd-kernel'
    );
    const cokernelSchema = kindSchema<AlgebraPolynomialFreydCokernel<P, C, I>>(
        'coimage-result', 'algebra-polynomial-freyd-cokernel'
    );
    const isomorphismSchema = kindSchema<
        AlgebraPolynomialFreydImageCoimageIsomorphism<P, C, I>
    >('coimage-image-isomorphism-result',
        'algebra-polynomial-freyd-image-coimage-isomorphism');
    const factorInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydNormalFactorInput<P, C, I>
    >({
        id: `${prefix}/normal-factor-input`,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`normal-factor input expected at ${path}`);
            }
            const maximumReductionSteps = value.maximumReductionSteps;
            if (
                maximumReductionSteps !== undefined &&
                (!Number.isSafeInteger(maximumReductionSteps) ||
                    (maximumReductionSteps as number) <= 0)
            ) throw new Error(`invalid normal-factor bound at ${path}`);
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
    const operation = <Input, Output>(
        id: string,
        input: Parameters<typeof defineCategoryOperation<Input, Output>>[0]['input'],
        output: Parameters<typeof defineCategoryOperation<Input, Output>>[0]['output']
    ) => defineCategoryOperation({ id: `${prefix}/${id}`, revision, input, output });
    const monomorphismWitness = operation(
        'monomorphism-witness', morphismSchema, monomorphismSchema
    );
    const epimorphismWitness = operation(
        'epimorphism-witness', morphismSchema, epimorphismSchema
    );
    const liftAlongMonomorphism = operation(
        'lift-along-monomorphism', factorInputSchema, monoLiftSchema
    );
    const coliftAlongEpimorphism = operation(
        'colift-along-epimorphism', factorInputSchema, epiColiftSchema
    );
    const coimageImageIsomorphism = operation(
        'coimage-image-isomorphism', morphismSchema, isomorphismSchema
    );
    const image = operation('image', morphismSchema, kernelSchema);
    const imageObject = operation('image-object', morphismSchema, objectSchema);
    const imageEmbedding = operation(
        'image-embedding', morphismSchema, morphismSchema
    );
    const coastrictionToImage = operation(
        'coastriction-to-image', morphismSchema, morphismSchema
    );
    const coimage = operation('coimage', morphismSchema, cokernelSchema);
    const coimageObject = operation('coimage-object', morphismSchema, objectSchema);
    const coimageProjection = operation(
        'coimage-projection', morphismSchema, morphismSchema
    );
    const astrictionFromCoimage = operation(
        'astriction-from-coimage', morphismSchema, morphismSchema
    );
    const coimageImageComparison = operation(
        'coimage-image-comparison', morphismSchema, morphismSchema
    );
    const operations = Object.freeze({
        monomorphismWitness,
        epimorphismWitness,
        liftAlongMonomorphism,
        coliftAlongEpimorphism,
        image,
        imageObject,
        imageEmbedding,
        coastrictionToImage,
        coimage,
        coimageObject,
        coimageProjection,
        astrictionFromCoimage,
        coimageImageComparison,
        coimageImageIsomorphism
    });
    const factorOptions = (input: AlgebraPolynomialFreydNormalFactorInput<P, C, I>) =>
        input.maximumReductionSteps === undefined
            ? {}
            : { maximumReductionSteps: input.maximumReductionSteps };
    const methods = [
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.monomorphism-witness.primitive',
            operation: monomorphismWitness,
            kind: 'primitive',
            execute: morphism =>
                algebraPolynomialFreydMonomorphismWitness(morphism)
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.epimorphism-witness.primitive',
            operation: epimorphismWitness,
            kind: 'primitive',
            execute: algebraPolynomialFreydEpimorphismWitness
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.lift-mono.derived',
            operation: liftAlongMonomorphism,
            kind: 'derived',
            prerequisites: [monomorphismWitness],
            execute: async (input, context) =>
                algebraPolynomialFreydLiftAlongMonomorphism(
                    await context.call(monomorphismWitness, input.morphism),
                    input.test,
                    factorOptions(input)
                )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.colift-epi.derived',
            operation: coliftAlongEpimorphism,
            kind: 'derived',
            prerequisites: [epimorphismWitness],
            execute: async (input, context) =>
                algebraPolynomialFreydColiftAlongEpimorphism(
                    await context.call(epimorphismWitness, input.morphism),
                    input.test,
                    factorOptions(input)
                )
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.image-coimage-iso.primitive',
            operation: coimageImageIsomorphism,
            kind: 'primitive',
            execute: algebraPolynomialFreydImages
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.image.derived',
            operation: image,
            kind: 'derived',
            prerequisites: [coimageImageIsomorphism],
            execute: async (f, context) =>
                (await context.call(coimageImageIsomorphism, f)).comparison.image
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.image-object.derived',
            operation: imageObject,
            kind: 'derived',
            prerequisites: [image],
            execute: async (f, context) => (await context.call(image, f)).object
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.image-embedding.derived',
            operation: imageEmbedding,
            kind: 'derived',
            prerequisites: [image],
            execute: async (f, context) =>
                (await context.call(image, f)).embedding
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.coastriction.derived',
            operation: coastrictionToImage,
            kind: 'derived',
            prerequisites: [coimageImageIsomorphism],
            execute: async (f, context) =>
                (await context.call(coimageImageIsomorphism, f))
                    .comparison.coastrictionToImage
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.coimage.derived',
            operation: coimage,
            kind: 'derived',
            prerequisites: [coimageImageIsomorphism],
            execute: async (f, context) =>
                (await context.call(coimageImageIsomorphism, f)).comparison.coimage
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.coimage-object.derived',
            operation: coimageObject,
            kind: 'derived',
            prerequisites: [coimage],
            execute: async (f, context) => (await context.call(coimage, f)).object
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.coimage-projection.derived',
            operation: coimageProjection,
            kind: 'derived',
            prerequisites: [coimage],
            execute: async (f, context) =>
                (await context.call(coimage, f)).projection
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.astriction.derived',
            operation: astrictionFromCoimage,
            kind: 'derived',
            prerequisites: [coimageImageIsomorphism],
            execute: async (f, context) =>
                (await context.call(coimageImageIsomorphism, f))
                    .comparison.astrictionFromCoimage
        }),
        defineCategoryMethod({
            id: 'algebra.polynomial-freyd-abelian.comparison.derived',
            operation: coimageImageComparison,
            kind: 'derived',
            prerequisites: [coimageImageIsomorphism],
            execute: async (f, context) =>
                (await context.call(coimageImageIsomorphism, f))
                    .comparison.comparison
        })
    ];
    const category = defineComputableCategory({
        id: prefix,
        revision,
        objectSchema,
        morphismSchema,
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
    const bindings = [
        { role: 'zero-morphism', operation: base.base.operations.zeroMorphism },
        { role: 'add-morphisms', operation: base.base.operations.addMorphisms },
        { role: 'negate-morphism', operation: base.base.operations.negateMorphism },
        { role: 'zero-object', operation: base.base.operations.zeroObject },
        { role: 'biproduct', operation: base.base.operations.biproduct },
        { role: 'kernel', operation: base.operations.kernel },
        { role: 'kernel-object', operation: base.operations.kernelObject },
        { role: 'kernel-embedding', operation: base.operations.kernelEmbedding },
        { role: 'kernel-lift', operation: base.operations.kernelLift },
        { role: 'cokernel', operation: base.operations.cokernel },
        { role: 'cokernel-object', operation: base.operations.cokernelObject },
        { role: 'cokernel-projection', operation: base.operations.cokernelProjection },
        { role: 'cokernel-colift', operation: base.operations.cokernelColift },
        { role: 'monomorphism-witness', operation: monomorphismWitness },
        { role: 'epimorphism-witness', operation: epimorphismWitness },
        { role: 'lift-along-monomorphism', operation: liftAlongMonomorphism },
        { role: 'colift-along-epimorphism', operation: coliftAlongEpimorphism },
        { role: 'image', operation: image },
        { role: 'image-object', operation: imageObject },
        { role: 'image-embedding', operation: imageEmbedding },
        { role: 'coastriction-to-image', operation: coastrictionToImage },
        { role: 'coimage', operation: coimage },
        { role: 'coimage-object', operation: coimageObject },
        { role: 'coimage-projection', operation: coimageProjection },
        { role: 'astriction-from-coimage', operation: astrictionFromCoimage },
        { role: 'coimage-image-comparison', operation: coimageImageComparison },
        { role: 'coimage-image-isomorphism', operation: coimageImageIsomorphism }
    ];
    const qualification = qualifyCategoryDoctrine(
        eraseCategory(category),
        ALGEBRA_BASE_DOCTRINES,
        ABELIAN_DOCTRINE.id,
        bindings
    );
    if (qualification.status !== 'qualified') {
        throw new Error(
            `Polynomial Freyd Abelian qualification missing: ` +
            qualification.missingRoles.join(', ')
        );
    }
    const constructor = defineCategoryConstructorDescriptor({
        id: 'category-constructor.polynomial-freyd-abelian',
        inputDoctrineId: 'preabelian-category',
        outputDoctrineId: 'abelian-category',
        introducedRoles: [
            'monomorphism-witness', 'epimorphism-witness',
            'lift-along-monomorphism', 'colift-along-epimorphism',
            'image', 'image-object', 'image-embedding',
            'coastriction-to-image',
            'coimage', 'coimage-object', 'coimage-projection',
            'astriction-from-coimage',
            'coimage-image-comparison', 'coimage-image-isomorphism'
        ],
        objectLayer: 'unchanged-polynomial-presentation',
        morphismLayer: 'unchanged-target-factorization-quotient',
        dualConstructorId: 'category-constructor.polynomial-freyd-abelian',
        loweringRules: [{
            id: 'polynomial-freyd-abelian.constructive-normality',
            kind: 'operation-lowering',
            source: 'normality-and-image-role-family',
            target: 'typescript-polynomial-freyd-normality'
        }]
    });
    const tower = buildCategoricalTower(
        `algebra.tower.polynomial-freyd-abelian/${ring.identity.id}`,
        ALGEBRA_BASE_DOCTRINES,
        base.tower.baseDoctrineId,
        [...base.tower.constructors, constructor]
    );
    const nativeOperation = <Input, Output>(
        categoryOperation: CategoryOperation<Input, Output>
    ): AlgebraOperation<Input, Output> => defineAlgebraOperation({
        id: categoryOperation.id.replace('algebra.category.', 'algebra.'),
        revision: categoryOperation.revision,
        input: categoryOperation.input,
        output: categoryOperation.output
    });
    const nativeOperations = Object.freeze({
        monomorphismWitness: nativeOperation(monomorphismWitness),
        epimorphismWitness: nativeOperation(epimorphismWitness),
        liftAlongMonomorphism: nativeOperation(liftAlongMonomorphism),
        coliftAlongEpimorphism: nativeOperation(coliftAlongEpimorphism),
        image: nativeOperation(image),
        imageObject: nativeOperation(imageObject),
        imageEmbedding: nativeOperation(imageEmbedding),
        coastrictionToImage: nativeOperation(coastrictionToImage),
        coimage: nativeOperation(coimage),
        coimageObject: nativeOperation(coimageObject),
        coimageProjection: nativeOperation(coimageProjection),
        astrictionFromCoimage: nativeOperation(astrictionFromCoimage),
        coimageImageComparison: nativeOperation(coimageImageComparison),
        coimageImageIsomorphism: nativeOperation(coimageImageIsomorphism)
    });
    const algorithm = (op: AlgebraOperation<unknown, unknown>) =>
        algebraAlgorithmIdentity(
            `algebra.typescript-reference/${op.identity.id}`,
            revision
        );
    const implementation = <Input, Output>(
        op: AlgebraOperation<Input, Output>,
        execute: (input: Input) => Output
    ): AlgebraReferenceImplementation => defineAlgebraReferenceImplementation({
        operation: op,
        algorithm: algorithm(op as AlgebraOperation<unknown, unknown>),
        execute
    });
    const whole = algebraPolynomialFreydImages;
    const implementations = Object.freeze([
        implementation(nativeOperations.monomorphismWitness,
            algebraPolynomialFreydMonomorphismWitness),
        implementation(nativeOperations.epimorphismWitness,
            algebraPolynomialFreydEpimorphismWitness),
        implementation(nativeOperations.liftAlongMonomorphism, input =>
            algebraPolynomialFreydLiftAlongMonomorphism(
                algebraPolynomialFreydMonomorphismWitness(input.morphism),
                input.test,
                factorOptions(input)
            )),
        implementation(nativeOperations.coliftAlongEpimorphism, input =>
            algebraPolynomialFreydColiftAlongEpimorphism(
                algebraPolynomialFreydEpimorphismWitness(input.morphism),
                input.test,
                factorOptions(input)
            )),
        implementation(nativeOperations.coimageImageIsomorphism, whole),
        implementation(nativeOperations.image, f => whole(f).comparison.image),
        implementation(nativeOperations.imageObject,
            f => whole(f).comparison.image.object),
        implementation(nativeOperations.imageEmbedding,
            f => whole(f).comparison.image.embedding),
        implementation(nativeOperations.coastrictionToImage,
            f => whole(f).comparison.coastrictionToImage),
        implementation(nativeOperations.coimage,
            f => whole(f).comparison.coimage),
        implementation(nativeOperations.coimageObject,
            f => whole(f).comparison.coimage.object),
        implementation(nativeOperations.coimageProjection,
            f => whole(f).comparison.coimage.projection),
        implementation(nativeOperations.astrictionFromCoimage,
            f => whole(f).comparison.astrictionFromCoimage),
        implementation(nativeOperations.coimageImageComparison,
            f => whole(f).comparison.comparison)
    ]);
    const native = Object.freeze({
        operations: nativeOperations,
        implementations
    }) as AlgebraPolynomialFreydAbelianNativeOperations<P, C, I>;
    const newLowerings = (Object.keys(operations) as
        (keyof typeof operations)[]).map(key => Object.freeze({
            categoryOperation: operations[key],
            algebraOperation: nativeOperations[key]
        }) as CategoryOperationLowering);
    const lowerings = Object.freeze([...base.lowerings, ...newLowerings]);
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

export const compileAlgebraPolynomialFreydAbelianProgram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    model: AlgebraPolynomialFreydAbelianCategoryModel<P, C, I>,
    program: CategoricalProgram
): CategoricalCompilation => compileCategoricalProgram({
    program,
    category: eraseCategory(model.category),
    tower: model.tower,
    lowerings: model.lowerings
});

export const createAlgebraPolynomialFreydAbelianEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(model: AlgebraPolynomialFreydAbelianCategoryModel<P, C, I>): AlgebraEngine =>
    createAlgebraTypeScriptReferenceEngine({
        id: `algebra.typescript-reference.polynomial-freyd-abelian/` +
            model.base.base.category.identity.id,
        revision: ALGEBRA_POLYNOMIAL_FREYD_ABELIAN_PROFILE.revision,
        implementations: [
            ...model.base.base.native.implementations,
            ...model.base.base.nativeAdditiveOperations.implementations,
            ...model.base.native.implementations,
            ...model.native.implementations
        ]
    });
