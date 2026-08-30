/** Native whole-construction operations for field-linear presented modules. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    algebraAlgorithmIdentity,
    defineAlgebraOperation
} from './algebra_engine';
import {
    AlgebraModuleCokernel,
    AlgebraModuleKernel,
    AlgebraModuleMorphism,
    algebraModuleCokernel,
    algebraModuleKernel
} from './algebra_module';
import {
    AlgebraModuleComputableCategory
} from './algebra_category_instances';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_MODULE_REFERENCE_OPERATIONS_PROFILE = Object.freeze({
    revision: 'emdash-algebra-module-reference-operations-v1' as const,
    algorithmRevision: 'typescript-field-module-reference-v1' as const,
    wholeConstructionOwner: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraModuleReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kernel: AlgebraOperation<
        AlgebraModuleMorphism<P, C, I>,
        AlgebraModuleKernel<P, C, I>
    >;
    readonly cokernel: AlgebraOperation<
        AlgebraModuleMorphism<P, C, I>,
        AlgebraModuleCokernel<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const algorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_MODULE_REFERENCE_OPERATIONS_PROFILE.algorithmRevision
);

export function algebraModuleReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    runtime: AlgebraModuleComputableCategory<P, C, I>
): AlgebraModuleReferenceOperations<P, C, I> {
    const suffix = runtime.category.identity.id;
    const kernel = defineAlgebraOperation({
        id: `algebra.module.kernel/${suffix}`,
        revision: runtime.category.identity.revision,
        input: runtime.operations.kernel.input,
        output: runtime.operations.kernel.output
    });
    const cokernel = defineAlgebraOperation({
        id: `algebra.module.cokernel/${suffix}`,
        revision: runtime.category.identity.revision,
        input: runtime.operations.cokernel.input,
        output: runtime.operations.cokernel.output
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: kernel,
            algorithm: algorithm(kernel.identity.id),
            execute: algebraModuleKernel
        }),
        defineAlgebraReferenceImplementation({
            operation: cokernel,
            algorithm: algorithm(cokernel.identity.id),
            execute: algebraModuleCokernel
        })
    ]);
    return Object.freeze({ kernel, cokernel, implementations });
}
