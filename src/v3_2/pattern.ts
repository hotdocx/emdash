/**
 * Pure higher-order pattern inversion for contextual emdash Core metas.
 *
 * A pattern occurrence `?m[spine]` is invertible exactly when every spine
 * entry is a distinct variable from the occurrence context. The inverse is a
 * scope map from the occurrence context back to the meta creation context.
 * This module performs no assignment and grants no runtime conversion.
 */

import {
    KernelExpression,
    KernelMetaVariable,
    KernelScopeError,
    Provenance,
    kernelExpressionEquals,
    kernelInstantiateSpine,
    kernelRemapAmbientIndices
} from './kernel';

export type CorePatternStuckReason =
    | 'NON_VARIABLE_PATTERN_SPINE'
    | 'REPEATED_PATTERN_VARIABLE';

export interface CorePatternSolution {
    readonly outcome: 'solution';
    readonly solution: KernelExpression;
    /**
     * `sourceToCreation[i]` is the creation-context variable selected by
     * occurrence-context variable `i`, or null when the variable is outside
     * the pattern spine.
     */
    readonly sourceToCreation: readonly (number | null)[];
}

export interface CorePatternStuck {
    readonly outcome: 'stuck';
    readonly reason: CorePatternStuckReason;
    readonly provenance: Provenance;
}

export interface CorePatternScopeEscape {
    readonly outcome: 'scope-escape';
    readonly error: KernelScopeError;
}

export type CorePatternInversion =
    | CorePatternSolution
    | CorePatternStuck
    | CorePatternScopeEscape;

/**
 * Invert one contextual meta occurrence against a rigid term.
 *
 * The caller owns meta identity/arity/context-lineage checks. This function
 * validates only the Miller-pattern spine and the rigid term's dependency on
 * that spine.
 */
export function invertCoreMetaPattern(
    meta: KernelMetaVariable,
    creationDepth: number,
    occurrenceDepth: number,
    rigid: KernelExpression
): CorePatternInversion {
    if (meta.spine.length !== creationDepth) {
        throw new Error(
            `Core pattern ?m${meta.identity.index} has spine length ` +
            `${meta.spine.length}, expected creation depth ${creationDepth}`
        );
    }

    const sourceToCreation: Array<number | null> =
        Array.from({ length: occurrenceDepth }, () => null);
    const seenSourceIndices = new Set<number>();

    for (let creationIndex = 0;
        creationIndex < meta.spine.length;
        creationIndex++
    ) {
        const item = meta.spine[creationIndex];
        if (
            item.tag !== 'bound' ||
            item.index < 0 ||
            item.index >= occurrenceDepth
        ) {
            return Object.freeze({
                outcome: 'stuck',
                reason: 'NON_VARIABLE_PATTERN_SPINE',
                provenance: item.provenance
            });
        }
        if (seenSourceIndices.has(item.index)) {
            return Object.freeze({
                outcome: 'stuck',
                reason: 'REPEATED_PATTERN_VARIABLE',
                provenance: item.provenance
            });
        }
        seenSourceIndices.add(item.index);
        sourceToCreation[item.index] = creationIndex;
    }

    let solution: KernelExpression;
    try {
        solution = kernelRemapAmbientIndices(
            rigid,
            creationDepth,
            sourceToCreation
        );
    } catch (error: unknown) {
        if (
            error instanceof KernelScopeError &&
            error.code === 'DROPPED_BOUND_VARIABLE'
        ) {
            return Object.freeze({
                outcome: 'scope-escape',
                error
            });
        }
        throw error;
    }

    const roundTrip = kernelInstantiateSpine(solution, meta.spine);
    if (!kernelExpressionEquals(roundTrip, rigid)) {
        throw new Error(
            `Core pattern inversion for ?m${meta.identity.index} failed its ` +
            'substitution round trip'
        );
    }

    return Object.freeze({
        outcome: 'solution',
        solution,
        sourceToCreation: Object.freeze(sourceToCreation)
    });
}
