/**
 * Portable direct coupling between stable named open proof goals.
 *
 * Graph construction consumes disposable session-owned Core, but its output
 * contains only source goal IDs, reachability, and structural occurrence
 * counts. It is separate from the canonical proof-state artifact.
 */

import {
    KernelExpression
} from './kernel';
import {
    CoreProofGoal
} from './proof';
import {
    CoreElaborationSession
} from './session';

export const CORE_PROOF_GOAL_COUPLING_PROFILE = Object.freeze({
    revision: 'emdash-proof-goal-coupling-v1' as const,
    graphRevision: 'emdash-proof-goal-coupling-graph-v1' as const,
    edgeDirection: 'dependent-to-prerequisite' as const,
    dependencyClosure: 'direct' as const,
    dependencySources: Object.freeze([
        'target',
        'context-binding-type'
    ] as const),
    nodeOrder: 'proof-goal-order' as const,
    edgeOrder: 'dependent-then-prerequisite-node-order' as const,
    addsProofStateFields: false as const,
    retainsSessionIdentity: false as const,
    retainsCallbacks: false as const,
    performsSemanticChecks: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export interface CoreProofGoalCouplingNode {
    readonly id: string;
    readonly reachability: CoreProofGoal['reachability'];
}

export interface CoreProofGoalCouplingEdge {
    readonly dependentGoalId: string;
    readonly prerequisiteGoalId: string;
    readonly targetOccurrenceCount: number;
    readonly contextOccurrenceCount: number;
}

export interface CoreProofGoalCouplingGraph {
    readonly revision:
        typeof CORE_PROOF_GOAL_COUPLING_PROFILE.graphRevision;
    readonly nodes: readonly CoreProofGoalCouplingNode[];
    readonly edges: readonly CoreProofGoalCouplingEdge[];
}

export type CoreProofGoalCouplingErrorCode =
    | 'DUPLICATE_GOAL'
    | 'INVALID_GOAL_ID'
    | 'MISSING_GOAL_ID'
    | 'CYCLIC_EXPRESSION';

export class CoreProofGoalCouplingError extends Error {
    constructor(
        public readonly code: CoreProofGoalCouplingErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreProofGoalCouplingError';
    }
}

const expressionChildren = (
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
            return [expression.binder.type, expression.body];
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const collectOpenMetaOccurrences = (
    expression: KernelExpression,
    openGoalIdsByIndex: ReadonlyMap<number, string>,
    path: string
): ReadonlyMap<number, number> => {
    const counts = new Map<number, number>();
    const active = new Set<KernelExpression>();

    const visit = (node: KernelExpression, nodePath: string): void => {
        if (active.has(node)) {
            throw new CoreProofGoalCouplingError(
                'CYCLIC_EXPRESSION',
                nodePath,
                'Proof-goal coupling input contains a cyclic Core expression'
            );
        }
        active.add(node);

        if (node.tag === 'meta') {
            if (!openGoalIdsByIndex.has(node.identity.index)) {
                throw new CoreProofGoalCouplingError(
                    'MISSING_GOAL_ID',
                    nodePath,
                    'An open Core meta has no stable proof-goal ID'
                );
            }
            counts.set(
                node.identity.index,
                (counts.get(node.identity.index) ?? 0) + 1
            );
        }

        expressionChildren(node).forEach((child, index) =>
            visit(child, `${nodePath}.child[${index}]`)
        );
        active.delete(node);
    };

    visit(expression, path);
    return counts;
};

interface MutableDependencyCounts {
    target: number;
    context: number;
}

const SAFE_GOAL_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;

const addCounts = (
    destination: Map<number, MutableDependencyCounts>,
    source: ReadonlyMap<number, number>,
    field: keyof MutableDependencyCounts
): void => {
    source.forEach((count, index) => {
        const current = destination.get(index) ?? {
            target: 0,
            context: 0
        };
        current[field] += count;
        destination.set(index, current);
    });
};

/**
 * Derive direct dependencies before the disposable checker session is lost.
 */
export function createCoreProofGoalCouplingGraph(
    session: CoreElaborationSession,
    goals: readonly CoreProofGoal[],
    stableGoalIdsByMetaIndex: ReadonlyMap<number, string>
): CoreProofGoalCouplingGraph {
    const openGoalIdsByIndex = new Map<number, string>();
    const seenIds = new Set<string>();

    const nodes = Object.freeze(goals.map((goal, index) => {
        if (openGoalIdsByIndex.has(goal.identity.index)) {
            throw new CoreProofGoalCouplingError(
                'DUPLICATE_GOAL',
                `goals[${index}]`,
                'Proof-goal coupling input repeats an open Core goal'
            );
        }
        const id = stableGoalIdsByMetaIndex.get(goal.identity.index);
        if (id === undefined) {
            throw new CoreProofGoalCouplingError(
                'MISSING_GOAL_ID',
                `goals[${index}]`,
                'Open Core goal has no stable proof-goal ID'
            );
        }
        if (!SAFE_GOAL_ID.test(id)) {
            throw new CoreProofGoalCouplingError(
                'INVALID_GOAL_ID',
                `goals[${index}]`,
                `Proof-goal ID '${id}' is not stable and portable`
            );
        }
        if (seenIds.has(id)) {
            throw new CoreProofGoalCouplingError(
                'DUPLICATE_GOAL',
                `goals[${index}]`,
                `Stable proof-goal ID '${id}' occurs more than once`
            );
        }
        openGoalIdsByIndex.set(goal.identity.index, id);
        seenIds.add(id);
        return Object.freeze({
            id,
            reachability: goal.reachability
        });
    }));

    const edges: CoreProofGoalCouplingEdge[] = [];
    goals.forEach((goal, dependentIndex) => {
        const countsByPrerequisite = new Map<
            number,
            MutableDependencyCounts
        >();
        addCounts(
            countsByPrerequisite,
            collectOpenMetaOccurrences(
                session.zonk(goal.type),
                openGoalIdsByIndex,
                `goals[${dependentIndex}].target`
            ),
            'target'
        );
        goal.context.telescope.forEach((binding, contextIndex) =>
            addCounts(
                countsByPrerequisite,
                collectOpenMetaOccurrences(
                    session.zonk(binding.type),
                    openGoalIdsByIndex,
                    `goals[${dependentIndex}].context[${contextIndex}].type`
                ),
                'context'
            )
        );

        goals.forEach(prerequisite => {
            if (prerequisite.identity.index === goal.identity.index) return;
            const counts = countsByPrerequisite.get(
                prerequisite.identity.index
            );
            if (counts === undefined) return;
            edges.push(Object.freeze({
                dependentGoalId: openGoalIdsByIndex.get(
                    goal.identity.index
                )!,
                prerequisiteGoalId: openGoalIdsByIndex.get(
                    prerequisite.identity.index
                )!,
                targetOccurrenceCount: counts.target,
                contextOccurrenceCount: counts.context
            }));
        });
    });

    return Object.freeze({
        revision: CORE_PROOF_GOAL_COUPLING_PROFILE.graphRevision,
        nodes,
        edges: Object.freeze(edges)
    });
}

/** Deterministic, diff-friendly portable graph serialization. */
export const serializeCoreProofGoalCouplingGraph = (
    graph: CoreProofGoalCouplingGraph
): string => `${JSON.stringify(graph, null, 2)}\n`;

/** Compact exact text view; scheduling and transitive closure stay separate. */
export function formatCoreProofGoalCouplingGraph(
    graph: CoreProofGoalCouplingGraph
): string {
    if (graph.nodes.length === 0) {
        return 'Proof goal coupling graph: no open goals';
    }

    return graph.nodes.flatMap(node => {
        const edges = graph.edges.filter(edge =>
            edge.dependentGoalId === node.id
        );
        return [
            `Goal ${node.id} [${node.reachability}]`,
            ...(edges.length === 0
                ? ['  requires: none']
                : edges.map(edge =>
                    `  requires ${edge.prerequisiteGoalId} ` +
                    `[target ${edge.targetOccurrenceCount}; ` +
                    `context ${edge.contextOccurrenceCount}]`
                ))
        ];
    }).join('\n');
}
