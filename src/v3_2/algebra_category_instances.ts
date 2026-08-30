/** Concrete ring and field-module instances of the computable-category core. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraCommutativeRingDomain,
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    algebraMatrixEquals
} from './algebra_matrix';
import {
    AlgebraModuleCokernel,
    AlgebraModuleKernel,
    AlgebraModuleMorphism,
    AlgebraPresentedModule,
    algebraModuleCokernel,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleKernel,
    algebraModuleMorphism,
    algebraPresentedModule
} from './algebra_module';
import {
    CategoryOperation,
    ComputableCategory,
    createCategoryOperationRegistry,
    defineCategoryMethod,
    defineCategoryOperation,
    defineComputableCategory
} from './algebra_category';

export const ALGEBRA_CATEGORY_INSTANCES_PROFILE = Object.freeze({
    revision: 'emdash-computable-category-instances-v1' as const,
    ringCategory: 'one-object-category-with-ring-element-endomorphisms' as const,
    moduleCategory: 'field-linear-presented-modules' as const,
    wholeConstructionOwner: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraRingCategoryObject<P extends AlgebraParent> {
    readonly kind: 'algebra-ring-category-object';
    readonly parent: P;
}

export function algebraRingComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(domain: AlgebraCommutativeRingDomain<P, C, I>): ComputableCategory<
    AlgebraRingCategoryObject<P>,
    C
> {
    const object = Object.freeze({
        kind: 'algebra-ring-category-object' as const,
        parent: domain.parent
    });
    const objectSchema = defineAlgebraRuntimeSchema({
        id: `algebra.category.ring-object/${domain.parent.identity.id}`,
        revision: domain.parent.identity.revision,
        normalize(value: unknown) {
            if (
                typeof value !== 'object' ||
                value === null ||
                (value as { kind?: unknown }).kind !==
                    'algebra-ring-category-object' ||
                !sameAlgebraParent(
                    (value as AlgebraRingCategoryObject<P>).parent,
                    domain.parent
                )
            ) throw new Error('foreign ring-category object');
            return object;
        }
    });
    return defineComputableCategory({
        id: `algebra.category.ring/${domain.parent.identity.id}`,
        revision: domain.parent.identity.revision,
        objectSchema,
        morphismSchema: domain.schema,
        operations: createCategoryOperationRegistry([]),
        source: () => object,
        target: () => object,
        identityMorphism: () => domain.one,
        compose: (after, before) => domain.multiply(after, before),
        equalObjects: (left, right) => sameAlgebraParent(
            left.parent,
            right.parent
        ),
        equalMorphisms: (left, right) => domain.equals(left, right)
    });
}

const sameModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraPresentedModule<P, C, I>, right: AlgebraPresentedModule<P, C, I>) =>
    left.generators === right.generators &&
    sameAlgebraParent(left.field.parent, right.field.parent) &&
    algebraMatrixEquals(left.relations, right.relations);

export interface AlgebraModuleCategoryOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kernel: CategoryOperation<
        AlgebraModuleMorphism<P, C, I>,
        AlgebraModuleKernel<P, C, I>
    >;
    readonly kernelObject: CategoryOperation<
        AlgebraModuleMorphism<P, C, I>,
        AlgebraPresentedModule<P, C, I>
    >;
    readonly cokernel: CategoryOperation<
        AlgebraModuleMorphism<P, C, I>,
        AlgebraModuleCokernel<P, C, I>
    >;
    readonly cokernelObject: CategoryOperation<
        AlgebraModuleMorphism<P, C, I>,
        AlgebraPresentedModule<P, C, I>
    >;
}

export interface AlgebraModuleComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraPresentedModule<P, C, I>,
        AlgebraModuleMorphism<P, C, I>
    >;
    readonly operations: AlgebraModuleCategoryOperations<P, C, I>;
}

export function algebraModuleComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(field: AlgebraFieldDomain<P, C, I>): AlgebraModuleComputableCategory<P, C, I> {
    const moduleSchema: AlgebraRuntimeSchema<AlgebraPresentedModule<P, C, I>> =
        defineAlgebraRuntimeSchema({
            id: `algebra.category.module-object/${field.parent.identity.id}`,
            revision: field.parent.identity.revision,
            normalize(value: unknown) {
                if (
                    typeof value !== 'object' ||
                    value === null ||
                    (value as { kind?: unknown }).kind !==
                        'algebra-presented-module'
                ) throw new Error('presented module expected');
                const module = value as AlgebraPresentedModule<P, C, I>;
                if (!sameAlgebraParent(module.field.parent, field.parent)) {
                    throw new Error('foreign module field');
                }
                return algebraPresentedModule(
                    field,
                    module.generators,
                    module.relations
                );
            }
        });
    const morphismSchema: AlgebraRuntimeSchema<AlgebraModuleMorphism<P, C, I>> =
        defineAlgebraRuntimeSchema({
            id: `algebra.category.module-morphism/${field.parent.identity.id}`,
            revision: field.parent.identity.revision,
            normalize(value: unknown) {
                if (
                    typeof value !== 'object' ||
                    value === null ||
                    (value as { kind?: unknown }).kind !==
                        'algebra-module-morphism'
                ) throw new Error('module morphism expected');
                const morphism = value as AlgebraModuleMorphism<P, C, I>;
                return algebraModuleMorphism(
                    moduleSchema.normalize(morphism.source, 'source'),
                    moduleSchema.normalize(morphism.target, 'target'),
                    morphism.matrix,
                    morphism.relationWitness
                );
            }
        });
    const kernelSchema = defineAlgebraRuntimeSchema<AlgebraModuleKernel<P, C, I>>({
        id: `algebra.category.module-kernel/${field.parent.identity.id}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown) {
            if (
                typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-module-kernel'
            ) throw new Error('module kernel expected');
            return value as AlgebraModuleKernel<P, C, I>;
        }
    });
    const cokernelSchema = defineAlgebraRuntimeSchema<
        AlgebraModuleCokernel<P, C, I>
    >({
        id: `algebra.category.module-cokernel/${field.parent.identity.id}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown) {
            if (
                typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-module-cokernel'
            ) throw new Error('module cokernel expected');
            return value as AlgebraModuleCokernel<P, C, I>;
        }
    });
    const suffix = field.parent.identity.id;
    const kernel = defineCategoryOperation({
        id: `algebra.category.module.kernel/${suffix}`,
        revision: field.parent.identity.revision,
        input: morphismSchema,
        output: kernelSchema
    });
    const kernelObject = defineCategoryOperation({
        id: `algebra.category.module.kernel-object/${suffix}`,
        revision: field.parent.identity.revision,
        input: morphismSchema,
        output: moduleSchema
    });
    const cokernel = defineCategoryOperation({
        id: `algebra.category.module.cokernel/${suffix}`,
        revision: field.parent.identity.revision,
        input: morphismSchema,
        output: cokernelSchema
    });
    const cokernelObject = defineCategoryOperation({
        id: `algebra.category.module.cokernel-object/${suffix}`,
        revision: field.parent.identity.revision,
        input: morphismSchema,
        output: moduleSchema
    });
    const registry = createCategoryOperationRegistry([
        defineCategoryMethod({
            id: 'algebra.module.kernel.primitive',
            operation: kernel,
            kind: 'primitive',
            execute: algebraModuleKernel
        }),
        defineCategoryMethod({
            id: 'algebra.module.kernel-object.derived',
            operation: kernelObject,
            kind: 'derived',
            prerequisites: [kernel],
            execute: async (morphism, context) => (
                await context.call(kernel, morphism)
            ).object
        }),
        defineCategoryMethod({
            id: 'algebra.module.cokernel.primitive',
            operation: cokernel,
            kind: 'primitive',
            execute: algebraModuleCokernel
        }),
        defineCategoryMethod({
            id: 'algebra.module.cokernel-object.derived',
            operation: cokernelObject,
            kind: 'derived',
            prerequisites: [cokernel],
            execute: async (morphism, context) => (
                await context.call(cokernel, morphism)
            ).object
        })
    ]);
    return Object.freeze({
        category: defineComputableCategory({
            id: `algebra.category.modules/${suffix}`,
            revision: field.parent.identity.revision,
            objectSchema: moduleSchema,
            morphismSchema,
            operations: registry,
            source: morphism => morphism.source,
            target: morphism => morphism.target,
            identityMorphism: algebraModuleIdentity,
            compose: algebraModuleCompose,
            equalObjects: sameModule,
            equalMorphisms: (left, right) =>
                sameModule(left.source, right.source) &&
                sameModule(left.target, right.target) &&
                algebraMatrixEquals(left.matrix, right.matrix) &&
                algebraMatrixEquals(
                    left.relationWitness,
                    right.relationWitness
                )
        }),
        operations: Object.freeze({
            kernel,
            kernelObject,
            cokernel,
            cokernelObject
        })
    });
}
