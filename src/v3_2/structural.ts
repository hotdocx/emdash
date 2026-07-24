/**
 * Meta-level structural maps for persistent dependent Core telescopes.
 *
 * These operations rearrange De Bruijn scopes and rebuild local binding
 * telescopes. They are intentionally separate from ordinary categorical
 * structural functors, displayed structural owners, and shape reindexing.
 */

import {
    CoreBindingInput,
    CoreContext,
    CoreContextError,
    CoreLocalBinding
} from './context';
import {
    KernelExpression,
    KernelScopeError,
    Provenance,
    kernelExpressionEquals,
    kernelRemapAmbientIndices
} from './kernel';

export type CoreTelescopeStructuralKind =
    | 'weakening'
    | 'exchange'
    | 'contraction';

/**
 * A simultaneous source-to-target map in nearest-first De Bruijn order.
 *
 * `ambientIndexMap[i]` is the target-context index of source-context index
 * `i`. Weakening maps into a deeper target, exchange permutes two images, and
 * contraction maps two source variables to one target variable.
 */
export interface CoreTelescopeStructuralMap {
    readonly kind: CoreTelescopeStructuralKind;
    readonly source: CoreContext;
    readonly target: CoreContext;
    readonly ambientIndexMap: readonly number[];
    apply(expression: KernelExpression): KernelExpression;
}

const bindingInput = (
    binding: CoreLocalBinding,
    type = binding.type
): CoreBindingInput => ({
    name: binding.name,
    type,
    mode: binding.mode,
    provenance: binding.provenance
});

const rebuildPrefix = (
    source: CoreContext,
    length: number
): CoreContext => {
    let target = CoreContext.empty(source.environment);
    for (let position = 0; position < length; position++) {
        target = target.extend(bindingInput(source.telescope[position]));
    }
    return target;
};

const createStructuralMap = (
    kind: CoreTelescopeStructuralKind,
    source: CoreContext,
    target: CoreContext,
    ambientIndexMap: readonly number[]
): CoreTelescopeStructuralMap => {
    if (ambientIndexMap.length !== source.depth) {
        throw new Error(
            `Internal ${kind} map has ${ambientIndexMap.length} images for ` +
            `a source telescope of depth ${source.depth}`
        );
    }
    for (const targetIndex of ambientIndexMap) {
        if (
            !Number.isSafeInteger(targetIndex) ||
            targetIndex < 0 ||
            targetIndex >= target.depth
        ) {
            throw new Error(
                `Internal ${kind} map contains target index ${targetIndex} ` +
                `outside telescope depth ${target.depth}`
            );
        }
    }

    const frozenIndexMap = Object.freeze([...ambientIndexMap]);
    return Object.freeze({
        kind,
        source,
        target,
        ambientIndexMap: frozenIndexMap,
        apply(expression: KernelExpression): KernelExpression {
            source.assertScoped(expression);
            const result = kernelRemapAmbientIndices(
                expression,
                target.depth,
                frozenIndexMap
            );
            target.assertScoped(result);
            return result;
        }
    });
};

const assertAdjacentPosition = (
    source: CoreContext,
    outerPosition: number,
    operationProvenance: Provenance,
    operation: 'exchange' | 'contraction'
): void => {
    if (
        Number.isSafeInteger(outerPosition) &&
        outerPosition >= 0 &&
        outerPosition + 1 < source.depth
    ) {
        return;
    }
    throw new CoreContextError(
        'INVALID_STRUCTURAL_POSITION',
        operationProvenance,
        `Core telescope ${operation} requires an outermost-first position ` +
        `with two adjacent binders; received ${outerPosition} at depth ` +
        `${source.depth}`
    );
};

const exchangeIndexMap = (
    sourceDepth: number,
    outerPosition: number
): readonly number[] => {
    const newerIndex = sourceDepth - outerPosition - 2;
    const olderIndex = newerIndex + 1;
    return Array.from({ length: sourceDepth }, (_, sourceIndex) => {
        if (sourceIndex === newerIndex) return olderIndex;
        if (sourceIndex === olderIndex) return newerIndex;
        return sourceIndex;
    });
};

const contractionIndexMap = (
    sourceDepth: number,
    outerPosition: number
): readonly number[] => {
    const newerIndex = sourceDepth - outerPosition - 2;
    const olderIndex = newerIndex + 1;
    return Array.from({ length: sourceDepth }, (_, sourceIndex) => {
        if (sourceIndex < newerIndex) return sourceIndex;
        if (sourceIndex === newerIndex || sourceIndex === olderIndex) {
            return newerIndex;
        }
        return sourceIndex - 1;
    });
};

/**
 * Extend a telescope and map every source expression under the new, unused
 * nearest binder.
 */
export const coreTelescopeWeakening = (
    source: CoreContext,
    input: CoreBindingInput
): CoreTelescopeStructuralMap => {
    const target = source.extend(input);
    const ambientIndexMap = Array.from(
        { length: source.depth },
        (_, sourceIndex) => sourceIndex + 1
    );
    return createStructuralMap(
        'weakening',
        source,
        target,
        ambientIndexMap
    );
};

/**
 * Exchange adjacent binders at outermost-first positions `p` and `p + 1`.
 *
 * If the newer binder's type uses the older binder, moving it outward would
 * be invalid and is rejected at the dependent occurrence. Types of all later
 * bindings are transported through the same permutation.
 */
export const coreTelescopeExchange = (
    source: CoreContext,
    outerPosition: number,
    operationProvenance: Provenance
): CoreTelescopeStructuralMap => {
    assertAdjacentPosition(
        source,
        outerPosition,
        operationProvenance,
        'exchange'
    );

    const older = source.telescope[outerPosition];
    const newer = source.telescope[outerPosition + 1];
    const dropOlderMap = Array.from(
        { length: outerPosition + 1 },
        (_, sourceIndex) => sourceIndex === 0 ? null : sourceIndex - 1
    );

    let movedNewerType: KernelExpression;
    try {
        movedNewerType = kernelRemapAmbientIndices(
            newer.type,
            outerPosition,
            dropOlderMap
        );
    } catch (error: unknown) {
        if (
            !(error instanceof KernelScopeError) ||
            error.code !== 'DROPPED_BOUND_VARIABLE'
        ) {
            throw error;
        }
        throw new CoreContextError(
            'DEPENDENT_EXCHANGE',
            error.provenance,
            `Cannot exchange Core local binders '${older.name}' and ` +
            `'${newer.name}': the type of '${newer.name}' depends on ` +
            `'${older.name}'`,
            error
        );
    }

    let target = rebuildPrefix(source, outerPosition);
    target = target.extend(bindingInput(newer, movedNewerType));

    const weakenOlderMap = Array.from(
        { length: outerPosition },
        (_, sourceIndex) => sourceIndex + 1
    );
    const movedOlderType = kernelRemapAmbientIndices(
        older.type,
        outerPosition + 1,
        weakenOlderMap
    );
    target = target.extend(bindingInput(older, movedOlderType));

    for (
        let sourcePosition = outerPosition + 2;
        sourcePosition < source.depth;
        sourcePosition++
    ) {
        const binding = source.telescope[sourcePosition];
        const movedType = kernelRemapAmbientIndices(
            binding.type,
            sourcePosition,
            exchangeIndexMap(sourcePosition, outerPosition)
        );
        target = target.extend(bindingInput(binding, movedType));
    }

    return createStructuralMap(
        'exchange',
        source,
        target,
        exchangeIndexMap(source.depth, outerPosition)
    );
};

/**
 * Contract adjacent binders by identifying the newer one with the older one.
 *
 * The newer binder must have exactly the older binder's type weakened into
 * its owning scope, and both binder modes must agree. This is deliberately a
 * structural check; later definitional equality belongs to the trusted
 * evaluator/comparison tranche. All later binding types are transported
 * through the explicit non-injective ambient index map.
 */
export const coreTelescopeContraction = (
    source: CoreContext,
    outerPosition: number,
    operationProvenance: Provenance
): CoreTelescopeStructuralMap => {
    assertAdjacentPosition(
        source,
        outerPosition,
        operationProvenance,
        'contraction'
    );

    const older = source.telescope[outerPosition];
    const newer = source.telescope[outerPosition + 1];
    const sameMode =
        older.mode.plicity === newer.mode.plicity &&
        older.mode.variation === newer.mode.variation;
    const weakenOlderMap = Array.from(
        { length: outerPosition },
        (_, sourceIndex) => sourceIndex + 1
    );
    const expectedNewerType = kernelRemapAmbientIndices(
        older.type,
        outerPosition + 1,
        weakenOlderMap
    );

    if (!sameMode || !kernelExpressionEquals(newer.type, expectedNewerType)) {
        const mismatch = !sameMode
            ? 'their binder modes differ'
            : `the type of '${newer.name}' is not the weakened type of ` +
                `'${older.name}'`;
        throw new CoreContextError(
            'INVALID_CONTRACTION',
            newer.provenance,
            `Cannot contract Core local binders '${older.name}' and ` +
            `'${newer.name}': ${mismatch}`
        );
    }

    let target = rebuildPrefix(source, outerPosition + 1);
    for (
        let sourcePosition = outerPosition + 2;
        sourcePosition < source.depth;
        sourcePosition++
    ) {
        const binding = source.telescope[sourcePosition];
        const movedType = kernelRemapAmbientIndices(
            binding.type,
            sourcePosition - 1,
            contractionIndexMap(sourcePosition, outerPosition)
        );
        target = target.extend(bindingInput(binding, movedType));
    }

    return createStructuralMap(
        'contraction',
        source,
        target,
        contractionIndexMap(source.depth, outerPosition)
    );
};
