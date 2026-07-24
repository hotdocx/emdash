/**
 * Direct TypeScript surface AST and rigid ELAB-0 context types.
 *
 * The context is intentionally small: it knows enough about categories,
 * objects, functors, arrows, and ordinary transfors to recover the implicit
 * slots of the first owner family. It performs no categorical conversion.
 */

import {
    BinderMode,
    KernelExpression,
    SourceSpan,
    assertSafeIdentifier,
    binderMode,
    formatSourceSpan,
    kernelApplication,
    kernelExpressionEquals,
    kernelLocal,
    kernelSymbol,
    provenance
} from './kernel';

export type SurfaceBindingType =
    | { tag: 'category' }
    | { tag: 'object'; category: string }
    | { tag: 'functor'; sourceCategory: string; targetCategory: string }
    | {
        tag: 'hom';
        category: string;
        sourceObject: string;
        targetObject: string;
    }
    | {
        tag: 'transfor';
        sourceCategory: string;
        targetCategory: string;
        sourceFunctor: string;
        targetFunctor: string;
    };

export const categoryType = (): SurfaceBindingType => ({ tag: 'category' });

export const objectType = (category: string): SurfaceBindingType => ({
    tag: 'object',
    category
});

export const functorType = (
    sourceCategory: string,
    targetCategory: string
): SurfaceBindingType => ({
    tag: 'functor',
    sourceCategory,
    targetCategory
});

export const homType = (
    category: string,
    sourceObject: string,
    targetObject: string
): SurfaceBindingType => ({
    tag: 'hom',
    category,
    sourceObject,
    targetObject
});

export const transforType = (
    sourceCategory: string,
    targetCategory: string,
    sourceFunctor: string,
    targetFunctor: string
): SurfaceBindingType => ({
    tag: 'transfor',
    sourceCategory,
    targetCategory,
    sourceFunctor,
    targetFunctor
});

export interface SurfaceBinding {
    name: string;
    type: SurfaceBindingType;
    mode: BinderMode;
    span: SourceSpan;
}

export const surfaceBinding = (
    name: string,
    type: SurfaceBindingType,
    span: SourceSpan,
    mode: BinderMode = binderMode('explicit', 'functorial')
): SurfaceBinding => ({ name, type, mode, span });

export type CoreType =
    | { tag: 'category' }
    | { tag: 'object'; category: KernelExpression }
    | {
        tag: 'functor';
        sourceCategory: KernelExpression;
        targetCategory: KernelExpression;
    }
    | {
        tag: 'hom';
        category: KernelExpression;
        sourceObject: KernelExpression;
        targetObject: KernelExpression;
    }
    | {
        tag: 'transfor';
        sourceCategory: KernelExpression;
        targetCategory: KernelExpression;
        sourceFunctor: KernelExpression;
        targetFunctor: KernelExpression;
    };

export interface ResolvedSurfaceBinding extends SurfaceBinding {
    reference: KernelExpression;
    coreType: CoreType;
    kernelType: KernelExpression;
}

export type SurfaceContextErrorCode =
    | 'DUPLICATE_BINDING'
    | 'UNKNOWN_DEPENDENCY'
    | 'WRONG_DEPENDENCY_TYPE'
    | 'ENDPOINT_CATEGORY_MISMATCH'
    | 'FUNCTOR_CATEGORY_MISMATCH';

export class SurfaceContextError extends Error {
    constructor(
        public readonly code: SurfaceContextErrorCode,
        public readonly span: SourceSpan,
        message: string
    ) {
        super(`${message} at ${formatSourceSpan(span)}`);
        this.name = 'SurfaceContextError';
    }
}

const derived = (detail: string, span: SourceSpan) =>
    provenance('derived', detail, span);

export function coreTypeToKernelType(
    type: CoreType,
    span: SourceSpan,
    detail: string
): KernelExpression {
    const nodeProvenance = derived(detail, span);

    switch (type.tag) {
        case 'category':
            return kernelSymbol('Cat', nodeProvenance);
        case 'object':
            return kernelApplication('tau', [{
                value: kernelApplication('Obj', [{
                    value: type.category
                }], nodeProvenance)
            }], nodeProvenance);
        case 'functor':
            return kernelApplication('tau', [{
                value: kernelApplication('Functor', [
                    { value: type.sourceCategory },
                    { value: type.targetCategory }
                ], nodeProvenance)
            }], nodeProvenance);
        case 'hom':
            return kernelApplication('tau', [{
                value: kernelApplication('Hom', [
                    { value: type.category },
                    { value: type.sourceObject },
                    { value: type.targetObject }
                ], nodeProvenance)
            }], nodeProvenance);
        case 'transfor':
            return kernelApplication('tau', [{
                value: kernelApplication('Transf', [
                    { value: type.sourceCategory },
                    { value: type.targetCategory },
                    { value: type.sourceFunctor },
                    { value: type.targetFunctor }
                ], nodeProvenance)
            }], nodeProvenance);
        default: {
            const exhaustive: never = type;
            return exhaustive;
        }
    }
}

export function coreTypeEquals(left: CoreType, right: CoreType): boolean {
    if (left.tag !== right.tag) return false;

    switch (left.tag) {
        case 'category':
            return true;
        case 'object': {
            const other = right as Extract<CoreType, { tag: 'object' }>;
            return kernelExpressionEquals(left.category, other.category);
        }
        case 'functor': {
            const other = right as Extract<CoreType, { tag: 'functor' }>;
            return kernelExpressionEquals(
                left.sourceCategory,
                other.sourceCategory
            ) && kernelExpressionEquals(
                left.targetCategory,
                other.targetCategory
            );
        }
        case 'hom': {
            const other = right as Extract<CoreType, { tag: 'hom' }>;
            return kernelExpressionEquals(left.category, other.category) &&
                kernelExpressionEquals(
                    left.sourceObject,
                    other.sourceObject
                ) &&
                kernelExpressionEquals(
                    left.targetObject,
                    other.targetObject
                );
        }
        case 'transfor': {
            const other = right as Extract<CoreType, { tag: 'transfor' }>;
            return kernelExpressionEquals(
                left.sourceCategory,
                other.sourceCategory
            ) && kernelExpressionEquals(
                left.targetCategory,
                other.targetCategory
            ) && kernelExpressionEquals(
                left.sourceFunctor,
                other.sourceFunctor
            ) && kernelExpressionEquals(
                left.targetFunctor,
                other.targetFunctor
            );
        }
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
}

export class SurfaceContext {
    private readonly bindingMap = new Map<string, ResolvedSurfaceBinding>();
    public readonly bindings: readonly ResolvedSurfaceBinding[];

    constructor(bindings: readonly SurfaceBinding[]) {
        const resolved: ResolvedSurfaceBinding[] = [];
        for (const binding of bindings) {
            assertSafeIdentifier(binding.name, 'Surface binding');
            if (this.bindingMap.has(binding.name)) {
                throw new SurfaceContextError(
                    'DUPLICATE_BINDING',
                    binding.span,
                    `Duplicate surface binding '${binding.name}'`
                );
            }

            const reference = kernelLocal(
                binding.name,
                provenance(
                    'surface',
                    `surface binding ${binding.name}`,
                    binding.span
                )
            );
            const coreType = this.resolveBindingType(binding);
            const resolvedBinding: ResolvedSurfaceBinding = {
                ...binding,
                reference,
                coreType,
                kernelType: coreTypeToKernelType(
                    coreType,
                    binding.span,
                    `type of surface binding ${binding.name}`
                )
            };
            resolved.push(resolvedBinding);
            this.bindingMap.set(binding.name, resolvedBinding);
        }
        this.bindings = resolved;
    }

    lookup(name: string): ResolvedSurfaceBinding | undefined {
        return this.bindingMap.get(name);
    }

    private dependency(name: string, owner: SurfaceBinding): ResolvedSurfaceBinding {
        const dependency = this.bindingMap.get(name);
        if (!dependency) {
            throw new SurfaceContextError(
                'UNKNOWN_DEPENDENCY',
                owner.span,
                `Binding '${owner.name}' refers to unknown earlier binding '${name}'`
            );
        }
        return dependency;
    }

    private expectCategory(
        name: string,
        owner: SurfaceBinding
    ): ResolvedSurfaceBinding {
        const binding = this.dependency(name, owner);
        if (binding.coreType.tag !== 'category') {
            throw new SurfaceContextError(
                'WRONG_DEPENDENCY_TYPE',
                owner.span,
                `Binding '${owner.name}' expects '${name}' to be a category`
            );
        }
        return binding;
    }

    private expectObject(
        name: string,
        category: KernelExpression,
        owner: SurfaceBinding
    ): ResolvedSurfaceBinding {
        const binding = this.dependency(name, owner);
        if (binding.coreType.tag !== 'object') {
            throw new SurfaceContextError(
                'WRONG_DEPENDENCY_TYPE',
                owner.span,
                `Binding '${owner.name}' expects '${name}' to be an object`
            );
        }
        if (!kernelExpressionEquals(binding.coreType.category, category)) {
            throw new SurfaceContextError(
                'ENDPOINT_CATEGORY_MISMATCH',
                owner.span,
                `Endpoint '${name}' of '${owner.name}' is in the wrong category`
            );
        }
        return binding;
    }

    private expectFunctor(
        name: string,
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        owner: SurfaceBinding
    ): ResolvedSurfaceBinding {
        const binding = this.dependency(name, owner);
        if (binding.coreType.tag !== 'functor') {
            throw new SurfaceContextError(
                'WRONG_DEPENDENCY_TYPE',
                owner.span,
                `Binding '${owner.name}' expects '${name}' to be a functor`
            );
        }
        if (!kernelExpressionEquals(
            binding.coreType.sourceCategory,
            sourceCategory
        ) || !kernelExpressionEquals(
            binding.coreType.targetCategory,
            targetCategory
        )) {
            throw new SurfaceContextError(
                'FUNCTOR_CATEGORY_MISMATCH',
                owner.span,
                `Functor '${name}' of '${owner.name}' has the wrong categories`
            );
        }
        return binding;
    }

    private resolveBindingType(binding: SurfaceBinding): CoreType {
        switch (binding.type.tag) {
            case 'category':
                return { tag: 'category' };
            case 'object': {
                const category = this.expectCategory(
                    binding.type.category,
                    binding
                );
                return {
                    tag: 'object',
                    category: category.reference
                };
            }
            case 'functor': {
                const source = this.expectCategory(
                    binding.type.sourceCategory,
                    binding
                );
                const target = this.expectCategory(
                    binding.type.targetCategory,
                    binding
                );
                return {
                    tag: 'functor',
                    sourceCategory: source.reference,
                    targetCategory: target.reference
                };
            }
            case 'hom': {
                const category = this.expectCategory(
                    binding.type.category,
                    binding
                );
                const source = this.expectObject(
                    binding.type.sourceObject,
                    category.reference,
                    binding
                );
                const target = this.expectObject(
                    binding.type.targetObject,
                    category.reference,
                    binding
                );
                return {
                    tag: 'hom',
                    category: category.reference,
                    sourceObject: source.reference,
                    targetObject: target.reference
                };
            }
            case 'transfor': {
                const sourceCategory = this.expectCategory(
                    binding.type.sourceCategory,
                    binding
                );
                const targetCategory = this.expectCategory(
                    binding.type.targetCategory,
                    binding
                );
                const sourceFunctor = this.expectFunctor(
                    binding.type.sourceFunctor,
                    sourceCategory.reference,
                    targetCategory.reference,
                    binding
                );
                const targetFunctor = this.expectFunctor(
                    binding.type.targetFunctor,
                    sourceCategory.reference,
                    targetCategory.reference,
                    binding
                );
                return {
                    tag: 'transfor',
                    sourceCategory: sourceCategory.reference,
                    targetCategory: targetCategory.reference,
                    sourceFunctor: sourceFunctor.reference,
                    targetFunctor: targetFunctor.reference
                };
            }
            default: {
                const exhaustive: never = binding.type;
                return exhaustive;
            }
        }
    }
}

export type SurfaceTerm =
    | {
        tag: 'reference';
        name: string;
        span: SourceSpan;
    }
    | {
        tag: 'fapp0';
        functor: SurfaceTerm;
        object: SurfaceTerm;
        span: SourceSpan;
    }
    | {
        tag: 'fapp1_fapp0';
        functor: SurfaceTerm;
        arrow: SurfaceTerm;
        span: SourceSpan;
    }
    | {
        tag: 'tapp1_fapp0';
        transformation: SurfaceTerm;
        arrow: SurfaceTerm;
        span: SourceSpan;
    };

export const surfaceReference = (
    name: string,
    span: SourceSpan
): SurfaceTerm => ({
    tag: 'reference',
    name,
    span
});

export const surfaceFapp0 = (
    functor: SurfaceTerm,
    object: SurfaceTerm,
    span: SourceSpan
): SurfaceTerm => ({
    tag: 'fapp0',
    functor,
    object,
    span
});

export const surfaceFapp1 = (
    functor: SurfaceTerm,
    arrow: SurfaceTerm,
    span: SourceSpan
): SurfaceTerm => ({
    tag: 'fapp1_fapp0',
    functor,
    arrow,
    span
});

export const surfaceTapp1 = (
    transformation: SurfaceTerm,
    arrow: SurfaceTerm,
    span: SourceSpan
): SurfaceTerm => ({
    tag: 'tapp1_fapp0',
    transformation,
    arrow,
    span
});
