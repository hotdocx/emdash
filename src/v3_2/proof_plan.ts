/**
 * Serializable proof plans and stable named goals over checked emdash Core.
 *
 * Plans are inert data. Execution delegates every semantic refinement to an
 * existing `CoreProofRefiner`; this module adds no Core constructor, checker
 * rule, category-owner case, global registry, or backend dependency.
 */

import {
    BinderMode,
    KernelExpression,
    KernelMetaIdentity,
    Provenance,
    SourceSpan,
    formatSourceSpan,
    kernelExpressionEquals
} from './kernel';
import {
    CoreProofGoal,
    CoreProofRefiner,
    CoreProofState,
    CoreProofTactic,
    formatCoreProofExpression
} from './proof';

export const CORE_PROOF_PLAN_MACRO_PROFILE = Object.freeze({
    revision: 'emdash-proof-plan-macros-v1' as const,
    selectedConstructor: 'explicit-callee' as const,
    constructorLowering: 'apply' as const,
    lowersToBasePlanTags: true as const,
    basePlanTags: Object.freeze([
        'exact',
        'intro',
        'apply',
        'hole'
    ] as const),
    addsCoreExpressionTags: false as const,
    addsProofPlanTags: false as const,
    retainsCallbacks: false as const,
    retainsMetavariables: false as const,
    performsSemanticChecks: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export interface CoreProofGoalExpectation {
    /** Exact expected local-context depth. */
    readonly contextDepth?: number;
    /** Exact expected zonked Core target in the goal's context. */
    readonly target?: KernelExpression;
}

interface CoreProofPlanNodeBase {
    readonly id?: string;
    readonly provenance: Provenance;
}

export interface CoreProofPlanExact extends CoreProofPlanNodeBase {
    readonly tag: 'exact';
    readonly solution: KernelExpression;
}

export interface CoreProofPlanIntro extends CoreProofPlanNodeBase {
    readonly tag: 'intro';
    readonly name?: string;
    readonly body: CoreProofPlan;
}

export interface CoreProofPlanApply extends CoreProofPlanNodeBase {
    readonly tag: 'apply';
    readonly callee: KernelExpression;
    /** Plans for the ordered unresolved goals introduced by `apply`. */
    readonly premises: readonly CoreProofPlan[];
}

export interface CoreProofPlanHole extends CoreProofPlanNodeBase {
    readonly tag: 'hole';
    readonly goalId: string;
    readonly expectation?: CoreProofGoalExpectation;
}

export type CoreProofPlan =
    | CoreProofPlanExact
    | CoreProofPlanIntro
    | CoreProofPlanApply
    | CoreProofPlanHole;

export interface CoreProofPlanNodeOptions {
    readonly id?: string;
    readonly provenance?: Provenance;
}

export interface CoreProofPlanIntroOptions
    extends CoreProofPlanNodeOptions {
    readonly name?: string;
}

export interface CoreProofPlanHoleOptions
    extends CoreProofPlanNodeOptions {
    readonly provenance: Provenance;
    readonly expectation?: CoreProofGoalExpectation;
}

export const coreProofPlanExact = (
    solution: KernelExpression,
    options: CoreProofPlanNodeOptions = {}
): CoreProofPlanExact => Object.freeze({
    tag: 'exact',
    id: options.id,
    provenance: options.provenance ?? solution.provenance,
    solution
});

export const coreProofPlanIntro = (
    body: CoreProofPlan,
    options: CoreProofPlanIntroOptions = {}
): CoreProofPlanIntro => Object.freeze({
    tag: 'intro',
    id: options.id,
    provenance: options.provenance ?? body.provenance,
    name: options.name,
    body
});

export const coreProofPlanApply = (
    callee: KernelExpression,
    premises: readonly CoreProofPlan[],
    options: CoreProofPlanNodeOptions = {}
): CoreProofPlanApply => Object.freeze({
    tag: 'apply',
    id: options.id,
    provenance: options.provenance ?? callee.provenance,
    callee,
    premises: Object.freeze([...premises])
});

export const coreProofPlanHole = (
    goalId: string,
    options: CoreProofPlanHoleOptions
): CoreProofPlanHole => Object.freeze({
    tag: 'hole',
    id: options.id,
    provenance: options.provenance,
    goalId,
    expectation: options.expectation
        ? Object.freeze({ ...options.expectation })
        : undefined
});

/**
 * User-facing constructor syntax with no second semantic implementation.
 * Constructor selection stays explicit; checking remains ordinary `apply`.
 */
export const coreProofPlanConstructor = (
    callee: KernelExpression,
    premises: readonly CoreProofPlan[],
    options: CoreProofPlanNodeOptions = {}
): CoreProofPlanApply => coreProofPlanApply(callee, premises, options);

export type CoreProofPlanErrorCode =
    | 'INVALID_ID'
    | 'DUPLICATE_NODE_ID'
    | 'DUPLICATE_GOAL_ID'
    | 'CYCLIC_PLAN'
    | 'NON_SERIALIZABLE_EXPRESSION'
    | 'INVALID_EXPECTATION'
    | 'GOAL_NOT_REACHABLE'
    | 'GOAL_ARITY_MISMATCH'
    | 'GOAL_ALREADY_LABELED'
    | 'GOAL_EXPECTATION_MISMATCH'
    | 'UNLABELED_GOAL';

export class CoreProofPlanError extends Error {
    constructor(
        public readonly code: CoreProofPlanErrorCode,
        public readonly nodeId: string,
        public readonly provenance: Provenance,
        message: string
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreProofPlanError';
    }
}

const SAFE_PLAN_ID = /^[A-Za-z][A-Za-z0-9._-]*$/;

const effectiveNodeId = (
    plan: CoreProofPlan,
    structuralPath: string
): string => plan.id ?? structuralPath;

/**
 * Validate source identities and tree shape before any proof state changes.
 */
export function validateCoreProofPlan(plan: CoreProofPlan): void {
    const nodeIds = new Set<string>();
    const goalIds = new Set<string>();
    const active = new Set<CoreProofPlan>();
    const activeExpressions = new Set<KernelExpression>();

    const fail = (
        code: CoreProofPlanErrorCode,
        node: CoreProofPlan,
        structuralPath: string,
        message: string
    ): never => {
        throw new CoreProofPlanError(
            code,
            effectiveNodeId(node, structuralPath),
            node.provenance,
            message
        );
    };

    const visit = (
        node: CoreProofPlan,
        structuralPath: string
    ): void => {
        if (active.has(node)) {
            fail(
                'CYCLIC_PLAN',
                node,
                structuralPath,
                `Proof plan contains a cycle at '${structuralPath}'`
            );
        }
        active.add(node);

        if (node.id && !SAFE_PLAN_ID.test(node.id)) {
            fail(
                'INVALID_ID',
                node,
                structuralPath,
                `Proof node ID '${node.id}' is not stable and portable`
            );
        }

        const nodeId = effectiveNodeId(node, structuralPath);
        if (nodeIds.has(nodeId)) {
            fail(
                'DUPLICATE_NODE_ID',
                node,
                structuralPath,
                `Duplicate proof node ID '${nodeId}'`
            );
        }
        nodeIds.add(nodeId);

        const validateExpression = (
            expression: KernelExpression,
            role: string
        ): void => {
            if (activeExpressions.has(expression)) {
                fail(
                    'NON_SERIALIZABLE_EXPRESSION',
                    node,
                    structuralPath,
                    `${role} contains a cyclic Core expression`
                );
            }
            activeExpressions.add(expression);

            switch (expression.tag) {
                case 'universe':
                case 'reference':
                case 'bound':
                    break;
                case 'meta':
                    fail(
                        'NON_SERIALIZABLE_EXPRESSION',
                        node,
                        structuralPath,
                        `${role} contains a process-local Core ` +
                        'metavariable; use a named proof-plan hole'
                    );
                    break;
                case 'application':
                    expression.arguments.forEach(argument =>
                        validateExpression(argument.value, role)
                    );
                    break;
                case 'call':
                    validateExpression(expression.callee, role);
                    expression.arguments.forEach(argument =>
                        validateExpression(argument.value, role)
                    );
                    break;
                case 'pi':
                case 'lambda':
                    validateExpression(expression.binder.type, role);
                    validateExpression(expression.body, role);
                    break;
                default: {
                    const exhaustive: never = expression;
                    return exhaustive;
                }
            }

            activeExpressions.delete(expression);
        };

        switch (node.tag) {
            case 'exact':
                validateExpression(node.solution, 'Exact solution');
                break;
            case 'intro':
                visit(node.body, `${structuralPath}.body`);
                break;
            case 'apply':
                validateExpression(node.callee, 'Applied Core expression');
                node.premises.forEach((premise, index) =>
                    visit(premise, `${structuralPath}.premise.${index}`)
                );
                break;
            case 'hole': {
                if (!SAFE_PLAN_ID.test(node.goalId)) {
                    fail(
                        'INVALID_ID',
                        node,
                        structuralPath,
                        `Proof goal ID '${node.goalId}' is not stable and ` +
                        'portable'
                    );
                }
                if (goalIds.has(node.goalId)) {
                    fail(
                        'DUPLICATE_GOAL_ID',
                        node,
                        structuralPath,
                        `Duplicate proof goal ID '${node.goalId}'`
                    );
                }
                goalIds.add(node.goalId);

                const depth = node.expectation?.contextDepth;
                if (
                    depth !== undefined &&
                    (!Number.isSafeInteger(depth) || depth < 0)
                ) {
                    fail(
                        'INVALID_EXPECTATION',
                        node,
                        structuralPath,
                        'Expected context depth must be a nonnegative safe ' +
                        'integer'
                    );
                }
                if (node.expectation?.target) {
                    validateExpression(
                        node.expectation.target,
                        'Expected goal target'
                    );
                }
                break;
            }
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }

        active.delete(node);
    };

    visit(plan, 'root');
}

export interface CoreProofPlanTraceStep {
    readonly nodeId: string;
    readonly operation: CoreProofTactic | 'hole';
    readonly statusAfter: CoreProofState['status'];
    readonly introducedGoalCount: number;
    readonly goalId?: string;
}

export interface CoreProofPlanSourcePositionSnapshot {
    readonly line: number;
    readonly column: number;
}

export interface CoreProofPlanSourceSpanSnapshot {
    readonly file: string;
    readonly start: CoreProofPlanSourcePositionSnapshot;
    readonly end: CoreProofPlanSourcePositionSnapshot;
}

export interface CoreProofPlanProvenanceSnapshot {
    readonly origin: Provenance['origin'];
    readonly detail: string;
    readonly span?: CoreProofPlanSourceSpanSnapshot;
}

export interface CoreProofPlanContextBindingSnapshot {
    /** De Bruijn index in the final goal context. */
    readonly index: number;
    readonly name: string;
    readonly plicity: BinderMode['plicity'];
    readonly variation: BinderMode['variation'];
    readonly type: string;
}

export interface CoreProofPlanGoalSnapshot {
    readonly id: string;
    readonly contextDepth: number;
    /** Outermost-to-innermost local bindings. */
    readonly context: readonly CoreProofPlanContextBindingSnapshot[];
    readonly target: string;
    readonly occurrenceCount: number;
    readonly declarationProvenance: CoreProofPlanProvenanceSnapshot;
    readonly firstOccurrenceProvenance: CoreProofPlanProvenanceSnapshot;
}

export interface CoreProofPlanStateSnapshot {
    readonly revision: 'emdash-proof-state-v1';
    readonly status: CoreProofState['status'];
    readonly term: string;
    readonly goals: readonly CoreProofPlanGoalSnapshot[];
    readonly trace: readonly CoreProofPlanTraceStep[];
}

export interface CoreProofPlanExecution {
    /** In-memory checked state; use `snapshot` for serialization. */
    readonly state: CoreProofState;
    readonly term: KernelExpression;
    readonly trace: readonly CoreProofPlanTraceStep[];
    readonly snapshot: CoreProofPlanStateSnapshot;
}

interface LabeledGoal {
    readonly goalId: string;
    readonly nodeId: string;
}

const sameIdentity = (
    left: KernelMetaIdentity,
    right: KernelMetaIdentity
): boolean => left.session === right.session && left.index === right.index;

const snapshotSpan = (
    span: SourceSpan
): CoreProofPlanSourceSpanSnapshot => Object.freeze({
    file: span.file,
    start: Object.freeze({ ...span.start }),
    end: Object.freeze({ ...span.end })
});

const snapshotProvenance = (
    nodeProvenance: Provenance,
    publicMetaName: (index: number) => string | undefined
): CoreProofPlanProvenanceSnapshot => Object.freeze({
    origin: nodeProvenance.origin,
    detail: nodeProvenance.detail.replace(
        /\?m(\d+)/g,
        (_, rawIndex: string) =>
            `?${publicMetaName(Number(rawIndex)) ?? 'internal'}`
    ),
    span: nodeProvenance.span
        ? snapshotSpan(nodeProvenance.span)
        : undefined
});

const traceStep = (
    nodeId: string,
    operation: CoreProofPlanTraceStep['operation'],
    state: CoreProofState,
    introducedGoalCount: number,
    goalId?: string
): CoreProofPlanTraceStep => Object.freeze({
    nodeId,
    operation,
    statusAfter: state.status,
    introducedGoalCount,
    goalId
});

const reachableGoal = (
    refiner: CoreProofRefiner,
    identity: KernelMetaIdentity,
    node: CoreProofPlan,
    nodeId: string
): CoreProofGoal => {
    const goal = refiner.inspect().goals.find(candidate =>
        sameIdentity(candidate.identity, identity)
    );
    if (goal) return goal;
    throw new CoreProofPlanError(
        'GOAL_NOT_REACHABLE',
        nodeId,
        node.provenance,
        `Proof node '${nodeId}' targets a goal that is no longer reachable`
    );
};

const assertExpectation = (
    refiner: CoreProofRefiner,
    goal: CoreProofGoal,
    hole: CoreProofPlanHole,
    nodeId: string
): void => {
    const expectation = hole.expectation;
    if (!expectation) return;

    if (
        expectation.contextDepth !== undefined &&
        expectation.contextDepth !== goal.contextDepth
    ) {
        throw new CoreProofPlanError(
            'GOAL_EXPECTATION_MISMATCH',
            nodeId,
            hole.provenance,
            `Named goal '${hole.goalId}' has context depth ` +
            `${goal.contextDepth}, expected ${expectation.contextDepth}`
        );
    }

    if (!expectation.target) return;
    goal.context.assertScoped(expectation.target);
    const actual = refiner.session.zonk(goal.type);
    const expected = refiner.session.zonk(expectation.target);
    if (kernelExpressionEquals(actual, expected)) return;

    throw new CoreProofPlanError(
        'GOAL_EXPECTATION_MISMATCH',
        nodeId,
        hole.provenance,
        `Named goal '${hole.goalId}' has target ` +
        `${formatCoreProofExpression(actual)}, expected ` +
        formatCoreProofExpression(expected)
    );
};

/**
 * Replay one immutable plan against one explicitly selected proof goal.
 */
export function executeCoreProofPlan(
    refiner: CoreProofRefiner,
    rootIdentity: KernelMetaIdentity,
    plan: CoreProofPlan
): CoreProofPlanExecution {
    validateCoreProofPlan(plan);

    const trace: CoreProofPlanTraceStep[] = [];
    const labelsByMeta = new Map<number, LabeledGoal>();
    const nodeNamesByMeta = new Map<number, string>();
    nodeNamesByMeta.set(
        rootIdentity.index,
        effectiveNodeId(plan, 'root')
    );

    const run = (
        identity: KernelMetaIdentity,
        node: CoreProofPlan,
        structuralPath: string
    ): void => {
        const nodeId = effectiveNodeId(node, structuralPath);

        switch (node.tag) {
            case 'exact': {
                reachableGoal(refiner, identity, node, nodeId);
                const result = refiner.exact(identity, node.solution);
                trace.push(traceStep(
                    nodeId,
                    'exact',
                    result.state,
                    result.introducedGoals.length
                ));
                return;
            }
            case 'intro': {
                reachableGoal(refiner, identity, node, nodeId);
                const result = refiner.session.withTransaction(() => {
                    const introduced = refiner.intro(
                        identity,
                        node.provenance,
                        node.name
                    );
                    if (introduced.introducedGoals.length !== 1) {
                        throw new CoreProofPlanError(
                            'GOAL_ARITY_MISMATCH',
                            nodeId,
                            node.provenance,
                            `Proof intro '${nodeId}' produced ` +
                            `${introduced.introducedGoals.length} goals; ` +
                            'expected exactly one body goal'
                        );
                    }
                    return introduced;
                });
                trace.push(traceStep(
                    nodeId,
                    'intro',
                    result.state,
                    result.introducedGoals.length
                ));
                nodeNamesByMeta.set(
                    result.introducedGoals[0].identity.index,
                    effectiveNodeId(node.body, `${structuralPath}.body`)
                );
                run(
                    result.introducedGoals[0].identity,
                    node.body,
                    `${structuralPath}.body`
                );
                return;
            }
            case 'apply': {
                reachableGoal(refiner, identity, node, nodeId);
                const result = refiner.session.withTransaction(() => {
                    const applied = refiner.apply(
                        identity,
                        node.callee,
                        node.provenance
                    );
                    if (
                        applied.introducedGoals.length !==
                        node.premises.length
                    ) {
                        throw new CoreProofPlanError(
                            'GOAL_ARITY_MISMATCH',
                            nodeId,
                            node.provenance,
                            `Proof apply '${nodeId}' produced ` +
                            `${applied.introducedGoals.length} unresolved ` +
                            `goals, but the plan supplies ` +
                            `${node.premises.length} premises`
                        );
                    }
                    return applied;
                });
                trace.push(traceStep(
                    nodeId,
                    'apply',
                    result.state,
                    result.introducedGoals.length
                ));
                result.introducedGoals.forEach((goal, index) =>
                    nodeNamesByMeta.set(
                        goal.identity.index,
                        effectiveNodeId(
                            node.premises[index],
                            `${structuralPath}.premise.${index}`
                        )
                    )
                );
                node.premises.forEach((premise, index) => run(
                    result.introducedGoals[index].identity,
                    premise,
                    `${structuralPath}.premise.${index}`
                ));
                return;
            }
            case 'hole': {
                const goal = reachableGoal(
                    refiner,
                    identity,
                    node,
                    nodeId
                );
                assertExpectation(refiner, goal, node, nodeId);
                if (labelsByMeta.has(identity.index)) {
                    throw new CoreProofPlanError(
                        'GOAL_ALREADY_LABELED',
                        nodeId,
                        node.provenance,
                        `Goal at proof node '${nodeId}' already has a ` +
                        'stable source label'
                    );
                }
                labelsByMeta.set(identity.index, Object.freeze({
                    goalId: node.goalId,
                    nodeId
                }));
                trace.push(traceStep(
                    nodeId,
                    'hole',
                    refiner.inspect(),
                    0,
                    node.goalId
                ));
                return;
            }
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }
    };

    run(rootIdentity, plan, 'root');

    const state = refiner.inspect();
    for (const goal of state.goals) {
        if (labelsByMeta.has(goal.identity.index)) continue;
        throw new CoreProofPlanError(
            'UNLABELED_GOAL',
            'root',
            goal.firstOccurrenceProvenance,
            'Proof-plan execution left an open goal without a stable ' +
            'source-level hole ID'
        );
    }

    const stableMetaName = (
        identity: KernelMetaIdentity
    ): string | undefined =>
        labelsByMeta.get(identity.index)?.goalId ??
        nodeNamesByMeta.get(identity.index);

    const stableMetaNameByIndex = (index: number): string | undefined =>
        labelsByMeta.get(index)?.goalId ?? nodeNamesByMeta.get(index);

    const goals = Object.freeze(state.goals.map(goal => {
        const label = labelsByMeta.get(goal.identity.index)!;
        const context = Object.freeze(goal.context.telescope.map(
            (_, position) => {
                const index = goal.contextDepth - position - 1;
                const lookup = goal.context.lookupIndex(
                    index,
                    goal.firstOccurrenceProvenance
                );
                if (!lookup) {
                    throw new CoreProofPlanError(
                        'GOAL_EXPECTATION_MISMATCH',
                        label.nodeId,
                        goal.firstOccurrenceProvenance,
                        `Cannot serialize local context position ${position}`
                    );
                }
                return Object.freeze({
                    index,
                    name: lookup.name,
                    plicity: lookup.mode.plicity,
                    variation: lookup.mode.variation,
                    type: formatCoreProofExpression(
                        refiner.session.zonk(lookup.type),
                        stableMetaName
                    )
                });
            }
        ));
        return Object.freeze({
            id: label.goalId,
            contextDepth: goal.contextDepth,
            context,
            target: formatCoreProofExpression(
                refiner.session.zonk(goal.type),
                stableMetaName
            ),
            occurrenceCount: goal.occurrenceCount,
            declarationProvenance: snapshotProvenance(
                goal.declarationProvenance,
                stableMetaNameByIndex
            ),
            firstOccurrenceProvenance: snapshotProvenance(
                goal.firstOccurrenceProvenance,
                stableMetaNameByIndex
            )
        });
    }));

    const frozenTrace = Object.freeze([...trace]);
    const snapshot: CoreProofPlanStateSnapshot = Object.freeze({
        revision: 'emdash-proof-state-v1',
        status: state.status,
        term: formatCoreProofExpression(state.term, stableMetaName),
        goals,
        trace: frozenTrace
    });

    return Object.freeze({
        state,
        term: state.term,
        trace: frozenTrace,
        snapshot
    });
}

/** Deterministic, diff-friendly serialization of the public state surface. */
export const serializeCoreProofPlanState = (
    snapshot: CoreProofPlanStateSnapshot
): string => `${JSON.stringify(snapshot, null, 2)}\n`;
