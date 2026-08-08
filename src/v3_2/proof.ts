/**
 * Generic proof-state inspection over backend-neutral emdash Core.
 *
 * Proof goals are session-owned metavariables reachable from a root Core
 * expression or from the type of another reachable goal.  This module knows
 * only the generic Core constructors; it contains no category-owner cases,
 * global definition lookup, or mutable hole references.
 */

import {
    CoreContext
} from './context';
import {
    CoreChecker,
    isCoreKind
} from './checker';
import {
    KernelExpression,
    KernelMetaIdentity,
    Provenance,
    formatSourceSpan,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelInstantiate,
    kernelLambda,
    kernelMeta,
    provenance
} from './kernel';
import {
    CoreElaborationSession,
    CoreMetaEntry
} from './session';

export interface CoreProofGoal {
    readonly identity: KernelMetaIdentity;
    readonly contextDepth: number;
    readonly context: CoreContext;
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
    expression: KernelExpression,
    metaName?: (identity: KernelMetaIdentity) => string | undefined
): string {
    switch (expression.tag) {
        case 'universe':
            return 'TYPE';
        case 'reference':
            return expression.name;
        case 'bound':
            return `#${expression.index}`;
        case 'meta':
            return `?${metaName?.(expression.identity) ??
                `m${expression.identity.index}`}[` +
                expression.spine
                    .map(item => formatCoreProofExpression(item, metaName))
                    .join(', ') +
                ']';
        case 'application':
            return `${expression.owner}(` +
                expression.arguments.map(argument =>
                    `${argument.plicity}:` +
                    formatCoreProofExpression(argument.value, metaName)
                ).join(', ') +
                ')';
        case 'call':
            return `${formatCoreProofExpression(
                expression.callee,
                metaName
            )}(` +
                expression.arguments.map(argument =>
                    `${argument.plicity}:` +
                    formatCoreProofExpression(argument.value, metaName)
                ).join(', ') +
                ')';
        case 'pi':
            return `Pi ${expression.binder.name}` +
                `[${formatMode(expression.binder.mode)}] : ` +
                `${formatCoreProofExpression(
                    expression.binder.type,
                    metaName
                )}. ` +
                formatCoreProofExpression(expression.body, metaName);
        case 'lambda':
            return `lambda ${expression.binder.name}` +
                `[${formatMode(expression.binder.mode)}] : ` +
                `${formatCoreProofExpression(
                    expression.binder.type,
                    metaName
                )}. ` +
                formatCoreProofExpression(expression.body, metaName);
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
            context: goal.entry.context,
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

export type CoreProofRefinementErrorCode =
    | 'GOAL_NOT_REACHABLE'
    | 'INTRO_EXPECTED_PI'
    | 'APPLY_EXPECTED_FUNCTION';

export class CoreProofRefinementError extends Error {
    constructor(
        public readonly code: CoreProofRefinementErrorCode,
        public readonly provenance: Provenance,
        message: string
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreProofRefinementError';
    }
}

export type CoreProofTactic = 'exact' | 'intro' | 'apply';

export interface CoreProofRefinementResult {
    readonly tactic: CoreProofTactic;
    readonly refinedGoal: CoreProofGoal;
    readonly introducedGoals: readonly CoreProofGoal[];
    readonly state: CoreProofState;
}

const derived = (
    detail: string,
    nodeProvenance: Provenance
): Provenance => provenance(
    'derived',
    detail,
    nodeProvenance.span
);

/**
 * Checked, session-local refinement of goals reachable from one Core root.
 *
 * The root stays immutable. Solutions live only in the checker's session,
 * and every tactic is failure-atomic through `withTransaction`.
 */
export class CoreProofRefiner {
    constructor(
        public readonly checker: CoreChecker,
        public readonly root: KernelExpression
    ) {
        this.inspect();
    }

    get session(): CoreElaborationSession {
        return this.checker.session;
    }

    inspect(): CoreProofState {
        return inspectCoreProofState(this.session, this.root);
    }

    private reachableGoal(
        state: CoreProofState,
        identity: KernelMetaIdentity,
        nodeProvenance: Provenance
    ): CoreProofGoal {
        const goal = state.goals.find(candidate =>
            candidate.identity.session === identity.session &&
            candidate.identity.index === identity.index
        );
        if (goal) return goal;
        throw new CoreProofRefinementError(
            'GOAL_NOT_REACHABLE',
            nodeProvenance,
            `Metavariable ?m${identity.index} is not an unsolved goal ` +
            'reachable from this proof root'
        );
    }

    private canonicalGoal(
        goal: CoreProofGoal,
        nodeProvenance: Provenance
    ) {
        return kernelMeta(
            goal.identity,
            Array.from(
                { length: goal.contextDepth },
                (_, index) => kernelBound(index, nodeProvenance)
            ),
            nodeProvenance
        );
    }

    private refine(
        tactic: CoreProofTactic,
        identity: KernelMetaIdentity,
        nodeProvenance: Provenance,
        build: (goal: CoreProofGoal) => KernelExpression
    ): CoreProofRefinementResult {
        return this.session.withTransaction(() => {
            const before = this.inspect();
            const goal = this.reachableGoal(
                before,
                identity,
                nodeProvenance
            );
            const solution = build(goal);
            this.session.solve(
                this.canonicalGoal(goal, nodeProvenance),
                solution
            );

            const state = this.inspect();
            const priorGoals = new Set(
                before.goals.map(candidate => candidate.identity.index)
            );
            const introducedGoals = Object.freeze(
                state.goals.filter(candidate =>
                    !priorGoals.has(candidate.identity.index)
                )
            );
            return Object.freeze({
                tactic,
                refinedGoal: goal,
                introducedGoals,
                state
            });
        });
    }

    exact(
        identity: KernelMetaIdentity,
        solution: KernelExpression
    ): CoreProofRefinementResult {
        return this.refine(
            'exact',
            identity,
            solution.provenance,
            goal => this.checker.check(
                goal.context,
                solution,
                goal.type
            ).term
        );
    }

    intro(
        identity: KernelMetaIdentity,
        nodeProvenance: Provenance,
        name?: string
    ): CoreProofRefinementResult {
        return this.refine(
            'intro',
            identity,
            nodeProvenance,
            goal => {
                const expected = this.session.zonk(goal.type);
                if (expected.tag !== 'pi') {
                    throw new CoreProofRefinementError(
                        'INTRO_EXPECTED_PI',
                        nodeProvenance,
                        `Cannot introduce a binder for a goal whose type is ` +
                        formatCoreProofExpression(expected)
                    );
                }

                const binderName = name ?? expected.binder.name;
                const bodyContext = goal.context.extend({
                    name: binderName,
                    type: expected.binder.type,
                    mode: expected.binder.mode,
                    provenance: nodeProvenance
                });
                const bodyGoal = this.session.freshMeta(
                    bodyContext,
                    expected.body,
                    derived(
                        `intro subgoal for ?m${identity.index}`,
                        nodeProvenance
                    )
                );
                const refinement = kernelLambda(
                    kernelBinder(
                        binderName,
                        expected.binder.type,
                        expected.binder.mode,
                        nodeProvenance
                    ),
                    bodyGoal,
                    nodeProvenance
                );
                return this.checker.checkRefinement(
                    goal.context,
                    refinement,
                    expected
                ).term;
            }
        );
    }

    apply(
        identity: KernelMetaIdentity,
        callee: KernelExpression,
        nodeProvenance: Provenance = callee.provenance
    ): CoreProofRefinementResult {
        return this.refine(
            'apply',
            identity,
            nodeProvenance,
            goal => {
                const inferred = this.checker.infer(
                    goal.context,
                    callee
                );
                if (
                    isCoreKind(inferred.type) ||
                    inferred.type.tag !== 'pi'
                ) {
                    throw new CoreProofRefinementError(
                        'APPLY_EXPECTED_FUNCTION',
                        nodeProvenance,
                        `Cannot apply a Core term whose type is ` +
                        (isCoreKind(inferred.type)
                            ? 'KIND'
                            : formatCoreProofExpression(inferred.type))
                    );
                }

                let currentType: KernelExpression = inferred.type;
                const arguments_: {
                    plicity: 'explicit' | 'implicit';
                    value: KernelExpression;
                    provenance: Provenance;
                }[] = [];
                let argumentIndex = 0;

                while (currentType.tag === 'pi') {
                    const argumentProvenance = derived(
                        `apply subgoal ${argumentIndex} for ` +
                        `?m${identity.index}`,
                        nodeProvenance
                    );
                    const argument = this.session.freshMeta(
                        goal.context,
                        currentType.binder.type,
                        argumentProvenance
                    );
                    arguments_.push({
                        plicity: currentType.binder.mode.plicity,
                        value: argument,
                        provenance: argumentProvenance
                    });
                    currentType = this.session.zonk(kernelInstantiate(
                        currentType.body,
                        argument
                    ));
                    argumentIndex++;
                }

                const application = kernelCall(
                    inferred.term,
                    arguments_,
                    nodeProvenance
                );
                return this.checker.checkRefinement(
                    goal.context,
                    application,
                    goal.type
                ).term;
            }
        );
    }
}
