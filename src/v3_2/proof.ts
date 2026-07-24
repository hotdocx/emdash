/**
 * Generic proof-state inspection over backend-neutral emdash Core.
 *
 * Proof goals are session-owned metavariables reachable from a root Core
 * expression or from the type of another reachable goal.  This module knows
 * only the generic Core constructors; it contains no category-owner cases,
 * global definition lookup, or mutable hole references.
 */

import {
    KernelExpression,
    KernelMetaIdentity,
    Provenance,
    formatSourceSpan
} from './kernel';
import {
    CoreElaborationSession,
    CoreMetaEntry
} from './session';

export interface CoreProofGoal {
    readonly identity: KernelMetaIdentity;
    readonly contextDepth: number;
    readonly type: KernelExpression;
    readonly declarationProvenance: Provenance;
    readonly firstOccurrenceProvenance: Provenance;
    readonly occurrenceCount: number;
}

export interface CoreProofState {
    readonly status: 'complete' | 'incomplete';
    readonly term: KernelExpression;
    readonly goals: readonly CoreProofGoal[];
}

interface MutableGoal {
    readonly entry: CoreMetaEntry;
    readonly firstOccurrenceProvenance: Provenance;
    occurrenceCount: number;
}

const formatMode = (
    mode: {
        readonly plicity: 'explicit' | 'implicit';
        readonly variation: 'functorial' | 'natural' | 'object-only';
    }
): string => `${mode.plicity}/${mode.variation}`;

/**
 * A deterministic backend-neutral diagnostic rendering.
 *
 * This is intentionally not Lambdapi syntax: raw metas must never be emitted
 * to that backend.
 */
export function formatCoreProofExpression(
    expression: KernelExpression
): string {
    switch (expression.tag) {
        case 'universe':
            return 'TYPE';
        case 'reference':
            return expression.name;
        case 'bound':
            return `#${expression.index}`;
        case 'meta':
            return `?m${expression.identity.index}[` +
                expression.spine
                    .map(formatCoreProofExpression)
                    .join(', ') +
                ']';
        case 'application':
            return `${expression.owner}(` +
                expression.arguments.map(argument =>
                    `${argument.plicity}:` +
                    formatCoreProofExpression(argument.value)
                ).join(', ') +
                ')';
        case 'call':
            return `${formatCoreProofExpression(expression.callee)}(` +
                expression.arguments.map(argument =>
                    `${argument.plicity}:` +
                    formatCoreProofExpression(argument.value)
                ).join(', ') +
                ')';
        case 'pi':
            return `Pi ${expression.binder.name}` +
                `[${formatMode(expression.binder.mode)}] : ` +
                `${formatCoreProofExpression(expression.binder.type)}. ` +
                formatCoreProofExpression(expression.body);
        case 'lambda':
            return `lambda ${expression.binder.name}` +
                `[${formatMode(expression.binder.mode)}] : ` +
                `${formatCoreProofExpression(expression.binder.type)}. ` +
                formatCoreProofExpression(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

const children = (
    expression: KernelExpression
): readonly KernelExpression[] => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return [];
        case 'meta':
            return expression.spine;
        case 'application':
            return expression.arguments.map(argument => argument.value);
        case 'call':
            return [
                expression.callee,
                ...expression.arguments.map(argument => argument.value)
            ];
        case 'pi':
        case 'lambda':
            return [
                expression.binder.type,
                expression.body
            ];
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

/**
 * Inspect the goals reachable from `root`.
 *
 * Ordering is deterministic depth-first first occurrence. Repeated
 * occurrences are counted once in the goal list, solved metas are followed
 * through zonking, and unrelated metas allocated in the same session are not
 * reported.
 */
export function inspectCoreProofState(
    session: CoreElaborationSession,
    root: KernelExpression
): CoreProofState {
    const term = session.zonk(root);
    const goals = new Map<number, MutableGoal>();
    const expandedTypes = new Set<number>();
    const activePath = new Set<KernelExpression>();

    const visit = (expression: KernelExpression): void => {
        if (activePath.has(expression)) return;
        activePath.add(expression);

        if (expression.tag === 'meta') {
            const entry = session.metavariable(expression);
            const existing = goals.get(expression.identity.index);
            if (existing) {
                existing.occurrenceCount++;
            } else {
                goals.set(expression.identity.index, {
                    entry,
                    firstOccurrenceProvenance: expression.provenance,
                    occurrenceCount: 1
                });
            }

            if (!expandedTypes.has(expression.identity.index)) {
                expandedTypes.add(expression.identity.index);
                visit(session.zonk(entry.type));
            }
        }

        for (const child of children(expression)) {
            visit(child);
        }
        activePath.delete(expression);
    };

    visit(term);

    const frozenGoals = Object.freeze(
        [...goals.values()].map(goal => Object.freeze({
            identity: goal.entry.identity,
            contextDepth: goal.entry.creationDepth,
            type: session.zonk(goal.entry.type),
            declarationProvenance: goal.entry.provenance,
            firstOccurrenceProvenance: goal.firstOccurrenceProvenance,
            occurrenceCount: goal.occurrenceCount
        }))
    );

    return Object.freeze({
        status: frozenGoals.length === 0 ? 'complete' : 'incomplete',
        term,
        goals: frozenGoals
    });
}

export function formatCoreProofState(state: CoreProofState): string {
    if (state.status === 'complete') return 'Proof complete';

    return state.goals.map(goal => {
        const location = goal.firstOccurrenceProvenance.span
            ? ` at ${formatSourceSpan(goal.firstOccurrenceProvenance.span)}`
            : '';
        const occurrences = goal.occurrenceCount === 1
            ? '1 occurrence'
            : `${goal.occurrenceCount} occurrences`;
        return `Goal ?m${goal.identity.index}${location} ` +
            `[depth ${goal.contextDepth}; ${occurrences}]\n` +
            `  |- ${formatCoreProofExpression(goal.type)}`;
    }).join('\n\n');
}
