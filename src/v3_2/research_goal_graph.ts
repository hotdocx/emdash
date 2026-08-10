/**
 * Browser-safe research-planning goals with evidence-typed derived status.
 *
 * This module is a policy evaluator beside mathematical proof authority. It
 * freshly replays exact supplied proof source for theorem evidence, treats
 * human attribution as caller-supplied, and keeps AI proposals advisory.
 */

import {
    serializeCoreExpression
} from './core_serialization';
import {
    KernelExpression,
    kernelAssertScoped
} from './kernel';
import {
    CoreLfProofDevelopmentSourceSnapshot,
    reconstructCoreLfProofDevelopmentSourceSnapshot
} from './lf_proof_development_source';
import {
    CoreLfProofReplayDiagnostic,
    projectCoreLfProofReplayDiagnostic
} from './lf_proof_maintenance';
import {
    compileCoreLfDeclarationWorkspace,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    compileCoreLfWorkspaceProofDocument
} from './lf_workspace_proof';
import {
    CoreProofGoalCouplingGraph
} from './proof_goal_graph';
import {
    CoreProofPlanStateSnapshot
} from './proof_plan';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export const CORE_RESEARCH_GOAL_GRAPH_PROFILE = Object.freeze({
    revision: 'emdash-research-goal-graph-v1' as const,
    definitionRevision: 'emdash-research-goal-definition-v1' as const,
    obligationRevision: 'emdash-research-goal-obligation-v1' as const,
    evidenceRevision: 'emdash-research-goal-evidence-v1' as const,
    assessmentRevision: 'emdash-research-goal-assessment-v1' as const,
    nodeResultRevision: 'emdash-research-goal-node-result-v1' as const,
    evaluationRevision: 'emdash-research-goal-evaluation-v1' as const,
    logicProfile: 'emdash-research-planning-v1' as const,
    nodeKinds: Object.freeze([
        'theorem-goal',
        'task-goal',
        'decision-goal'
    ] as const),
    dependencyKinds: Object.freeze(['requires', 'one-of'] as const),
    evidenceKinds: Object.freeze([
        'checked-proof',
        'human-approval',
        'ai-proposal'
    ] as const),
    statuses: Object.freeze([
        'open',
        'blocked',
        'satisfied',
        'rejected'
    ] as const),
    edgeDirection: 'dependent-to-prerequisite' as const,
    dependencyPolicy: 'acyclic-requires-and-grouped-one-of' as const,
    theoremPolicy: 'fresh-selected-proof-replay' as const,
    humanAttributionAuthority: 'caller-supplied-unverified' as const,
    aiProposalAuthority: 'advisory-only' as const,
    evidenceBinding: 'exact-canonical-obligation-text' as const,
    statusPolicy: 'derived-no-mutable-done-field' as const,
    maxNodes: 1_024,
    maxEdges: 8_192,
    maxEvidence: 8_192,
    maxTitleLength: 1_024,
    maxStatementLength: 4_096,
    maxProposalLength: 16_384,
    sourceHashesRecomputed: false as const,
    verifiesHumanIdentity: false as const,
    executesExternalActions: false as const,
    performsIo: false as const,
    acquiresTime: false as const,
    computesCryptographicHashes: false as const,
    invokesAgent: false as const,
    invokesLambdapi: false as const,
    retainsCallbacks: false as const,
    retainsSessionState: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export type CoreResearchGoalGraphErrorCode =
    | 'INVALID_DEFINITION'
    | 'INVALID_NODE'
    | 'DUPLICATE_NODE'
    | 'NODE_LIMIT_EXCEEDED'
    | 'INVALID_EDGE'
    | 'DUPLICATE_EDGE'
    | 'EDGE_LIMIT_EXCEEDED'
    | 'UNKNOWN_NODE'
    | 'DEPENDENCY_CYCLE'
    | 'VACUOUS_TASK'
    | 'INVALID_EVIDENCE'
    | 'DUPLICATE_EVIDENCE'
    | 'EVIDENCE_LIMIT_EXCEEDED'
    | 'AMBIGUOUS_APPROVAL'
    | 'PROOF_SOURCE_FAILED'
    | 'UNSUPPORTED_PROOF_REPLAY';

export class CoreResearchGoalGraphError extends Error {
    constructor(
        public readonly code: CoreResearchGoalGraphErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreResearchGoalGraphError';
    }
}

const fail = (
    code: CoreResearchGoalGraphErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreResearchGoalGraphError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_LOCAL_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const freezePortable = <T>(
    value: T,
    path: string,
    code: CoreResearchGoalGraphErrorCode = 'INVALID_DEFINITION'
): T => {
    let text: string | undefined;
    try {
        text = JSON.stringify(value);
    } catch (error: unknown) {
        return fail(
            code,
            path,
            'Research-goal data cannot be serialized',
            error
        );
    }
    if (text === undefined) {
        return fail(
            code,
            path,
            'Research-goal data cannot be undefined'
        );
    }
    const projected = JSON.parse(text) as T;
    try {
        serializeCoreLfWorkspaceCanonicalJson(projected, path);
    } catch (error: unknown) {
        return fail(
            code,
            path,
            'Research-goal data is not canonical portable data',
            error
        );
    }
    return deepFreeze(projected);
};

const assertId = (
    value: unknown,
    path: string,
    code: CoreResearchGoalGraphErrorCode = 'INVALID_NODE'
): string => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return value;
    return fail(code, path, 'Expected a stable portable identity');
};

const assertLocalId = (
    value: unknown,
    path: string
): string => {
    if (typeof value === 'string' && SAFE_LOCAL_ID.test(value)) return value;
    return fail('INVALID_EDGE', path, 'Expected a stable local group identity');
};

const assertRevision = (
    value: unknown,
    path: string,
    code: CoreResearchGoalGraphErrorCode = 'INVALID_NODE'
): string => {
    if (typeof value === 'string' && SAFE_REVISION.test(value)) return value;
    return fail(code, path, 'Expected a stable portable revision');
};

const normalizeText = (
    value: unknown,
    path: string,
    maxLength: number,
    multiline: boolean,
    code: CoreResearchGoalGraphErrorCode = 'INVALID_NODE'
): string => {
    if (
        typeof value !== 'string' ||
        value.length === 0 ||
        value.length > maxLength ||
        value.trim() !== value ||
        (
            multiline
                ? /[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f]/u
                : /[\u0000-\u001f\u007f]/u
        ).test(value)
    ) {
        return fail(
            code,
            path,
            'Expected bounded, trimmed, portable text'
        );
    }
    return value;
};

const SAFE_CORE_IDENTIFIER = /^[A-Za-z][A-Za-z0-9_]*$/u;

const expressionArguments = (
    value: unknown,
    path: string,
    expectedPlicities?: readonly ('explicit' | 'implicit')[]
): readonly KernelExpression[] => {
    if (!Array.isArray(value)) {
        return fail(
            'INVALID_NODE',
            path,
            'Core expression arguments must be an array'
        );
    }
    const children: KernelExpression[] = [];
    for (let index = 0; index < value.length; index += 1) {
        if (!Object.prototype.hasOwnProperty.call(value, index)) {
            return fail(
                'INVALID_NODE',
                `${path}[${index}]`,
                'Core expression arguments cannot be sparse'
            );
        }
        const argument = value[index] as unknown;
        if (argument === null || typeof argument !== 'object') {
            return fail(
                'INVALID_NODE',
                `${path}[${index}]`,
                'Core expression argument must be a data record'
            );
        }
        const record = argument as Record<string, unknown>;
        if (record.plicity !== 'explicit' && record.plicity !== 'implicit') {
            return fail(
                'INVALID_NODE',
                `${path}[${index}].plicity`,
                'Core expression argument has unsupported plicity'
            );
        }
        if (
            expectedPlicities !== undefined &&
            record.plicity !== expectedPlicities[index]
        ) {
            return fail(
                'INVALID_NODE',
                `${path}[${index}].plicity`,
                'Core owner argument plicity differs from its schema'
            );
        }
        children.push(record.value as KernelExpression);
    }
    return children;
};

const expressionChildren = (
    expression: KernelExpression,
    path: string
): readonly KernelExpression[] => {
    const record = expression as unknown as Record<string, unknown>;
    switch (record.tag) {
        case 'universe':
            return [];
        case 'reference':
            if (
                record.namespace !== 'free' ||
                typeof record.name !== 'string' ||
                !SAFE_CORE_IDENTIFIER.test(record.name)
            ) {
                return fail(
                    'INVALID_NODE',
                    path,
                    'Core free reference is malformed'
                );
            }
            return [];
        case 'bound':
            if (
                typeof record.index !== 'number' ||
                !Number.isSafeInteger(record.index) ||
                record.index < 0
            ) {
                return fail(
                    'INVALID_NODE',
                    `${path}.index`,
                    'Core bound-variable index must be nonnegative and safe'
                );
            }
            return [];
        case 'meta':
            return fail(
                'INVALID_NODE',
                path,
                'Theorem statement cannot contain process-local metas'
            );
        case 'application':
            if (
                typeof record.owner !== 'string' ||
                !Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    record.owner
                )
            ) {
                return fail(
                    'INVALID_NODE',
                    `${path}.owner`,
                    'Core owner identity is unsupported'
                );
            }
            if (
                !Array.isArray(record.arguments) ||
                record.arguments.length !==
                    CORE_OWNER_SCHEMAS[record.owner as CoreOwnerId].slots.length
            ) {
                return fail(
                    'INVALID_NODE',
                    `${path}.arguments`,
                    'Core owner application has the wrong arity'
                );
            }
            return expressionArguments(
                record.arguments,
                `${path}.arguments`,
                CORE_OWNER_SCHEMAS[record.owner as CoreOwnerId].slots.map(
                    slot => slot.plicity
                )
            );
        case 'call':
            if (!Array.isArray(record.arguments) || record.arguments.length === 0) {
                return fail(
                    'INVALID_NODE',
                    `${path}.arguments`,
                    'Core generic call requires at least one argument'
                );
            }
            return [
                record.callee as KernelExpression,
                ...expressionArguments(record.arguments, `${path}.arguments`)
            ];
        case 'pi':
        case 'lambda': {
            if (record.binder === null || typeof record.binder !== 'object') {
                return fail(
                    'INVALID_NODE',
                    `${path}.binder`,
                    'Core binder must be a data record'
                );
            }
            const binder = record.binder as Record<string, unknown>;
            if (
                binder.mode === null ||
                typeof binder.mode !== 'object'
            ) {
                return fail(
                    'INVALID_NODE',
                    `${path}.binder.mode`,
                    'Core binder mode must be a data record'
                );
            }
            const mode = binder.mode as Record<string, unknown>;
            if (
                (mode.plicity !== 'explicit' && mode.plicity !== 'implicit') ||
                (
                    mode.variation !== 'functorial' &&
                    mode.variation !== 'natural' &&
                    mode.variation !== 'object-only'
                )
            ) {
                return fail(
                    'INVALID_NODE',
                    `${path}.binder.mode`,
                    'Core binder mode is unsupported'
                );
            }
            return [
                binder.type as KernelExpression,
                record.body as KernelExpression
            ];
        }
        default:
            return fail(
                'INVALID_NODE',
                `${path}.tag`,
                'Core expression tag is unsupported'
            );
    }
};

const assertClosedMetaFree = (
    expression: KernelExpression,
    path: string
): void => {
    const active = new Set<KernelExpression>();
    const complete = new Set<KernelExpression>();
    const visit = (node: KernelExpression, nodePath: string): void => {
        if (node === null || typeof node !== 'object') {
            return fail(
                'INVALID_NODE',
                nodePath,
                'Theorem statement must be a Core expression record'
            );
        }
        if (complete.has(node)) return;
        if (active.has(node)) {
            return fail(
                'INVALID_NODE',
                nodePath,
                'Theorem statement cannot contain a cyclic Core expression'
            );
        }
        active.add(node);
        expressionChildren(node, nodePath).forEach((child, index) =>
            visit(child, `${nodePath}.${node.tag}.${index}`)
        );
        active.delete(node);
        complete.add(node);
    };
    visit(expression, path);
    try {
        kernelAssertScoped(expression, 0);
    } catch (error: unknown) {
        fail(
            'INVALID_NODE',
            path,
            'Theorem statement must be closed and structurally valid',
            error
        );
    }
};

export interface CoreResearchGoalProofIdentity {
    readonly moduleId: string;
    readonly declarationId: string;
}

export interface CoreResearchGoalNodeBaseInput {
    readonly id: string;
    readonly revision: string;
    readonly title: string;
}

export interface CoreResearchTheoremGoalNodeInput
extends CoreResearchGoalNodeBaseInput {
    readonly kind: 'theorem-goal';
    readonly proof: CoreResearchGoalProofIdentity;
    readonly expectedType: KernelExpression;
}

export interface CoreResearchTaskGoalNodeInput
extends CoreResearchGoalNodeBaseInput {
    readonly kind: 'task-goal';
    readonly policy:
        | { readonly kind: 'all-prerequisites' }
        | {
            readonly kind: 'all-named-approvers';
            readonly approverIds: readonly string[];
        };
}

export interface CoreResearchDecisionGoalNodeInput
extends CoreResearchGoalNodeBaseInput {
    readonly kind: 'decision-goal';
    readonly policy: {
        readonly kind: 'all-named-approvers';
        readonly approverIds: readonly string[];
    };
}

export type CoreResearchGoalNodeInput =
    | CoreResearchTheoremGoalNodeInput
    | CoreResearchTaskGoalNodeInput
    | CoreResearchDecisionGoalNodeInput;

interface CoreResearchGoalNodeBase {
    readonly id: string;
    readonly revision: string;
    readonly title: string;
}

export interface CoreResearchTheoremGoalNode
extends CoreResearchGoalNodeBase {
    readonly kind: 'theorem-goal';
    readonly proof: CoreResearchGoalProofIdentity;
    readonly expectedType: KernelExpression;
    readonly expectedTypeText: string;
    readonly policy: 'checked-proof';
}

export interface CoreResearchTaskGoalNode
extends CoreResearchGoalNodeBase {
    readonly kind: 'task-goal';
    readonly policy:
        | { readonly kind: 'all-prerequisites' }
        | {
            readonly kind: 'all-named-approvers';
            readonly approverIds: readonly string[];
        };
}

export interface CoreResearchDecisionGoalNode
extends CoreResearchGoalNodeBase {
    readonly kind: 'decision-goal';
    readonly policy: {
        readonly kind: 'all-named-approvers';
        readonly approverIds: readonly string[];
    };
}

export type CoreResearchGoalNode =
    | CoreResearchTheoremGoalNode
    | CoreResearchTaskGoalNode
    | CoreResearchDecisionGoalNode;

const normalizeApprovers = (
    input: readonly string[],
    path: string
): readonly string[] => {
    if (!Array.isArray(input) || input.length === 0) {
        return fail(
            'INVALID_NODE',
            path,
            'Named-approver policy requires at least one actor ID'
        );
    }
    const seen = new Set<string>();
    const approvers = input.map((actor, index) => {
        const normalized = assertId(actor, `${path}[${index}]`);
        if (seen.has(normalized)) {
            return fail(
                'INVALID_NODE',
                `${path}[${index}]`,
                'Named approver occurs more than once'
            );
        }
        seen.add(normalized);
        return normalized;
    }).sort(compareText);
    return Object.freeze(approvers);
};

const normalizeProofIdentity = (
    proof: CoreResearchGoalProofIdentity,
    path: string
): CoreResearchGoalProofIdentity => {
    if (proof === null || typeof proof !== 'object') {
        return fail(
            'INVALID_NODE',
            path,
            'Theorem proof identity must be a data record'
        );
    }
    return Object.freeze({
        moduleId: assertId(proof.moduleId, `${path}.moduleId`),
        declarationId: assertId(
            proof.declarationId,
            `${path}.declarationId`
        )
    });
};

const normalizeNode = (
    input: CoreResearchGoalNodeInput,
    path: string
): CoreResearchGoalNode => {
    if (input === null || typeof input !== 'object') {
        return fail('INVALID_NODE', path, 'Goal node must be a data record');
    }
    const base = {
        id: assertId(input.id, `${path}.id`),
        revision: assertRevision(input.revision, `${path}.revision`),
        title: normalizeText(
            input.title,
            `${path}.title`,
            CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxTitleLength,
            false
        )
    };
    switch (input.kind) {
        case 'theorem-goal': {
            assertClosedMetaFree(input.expectedType, `${path}.expectedType`);
            return freezePortable({
                ...base,
                kind: 'theorem-goal' as const,
                proof: normalizeProofIdentity(input.proof, `${path}.proof`),
                expectedType: input.expectedType,
                expectedTypeText: serializeCoreExpression(input.expectedType),
                policy: 'checked-proof' as const
            }, path);
        }
        case 'task-goal': {
            if (input.policy === null || typeof input.policy !== 'object') {
                return fail(
                    'INVALID_NODE',
                    `${path}.policy`,
                    'Task policy must be a data record'
                );
            }
            if (input.policy.kind === 'all-prerequisites') {
                return freezePortable({
                    ...base,
                    kind: 'task-goal' as const,
                    policy: { kind: 'all-prerequisites' as const }
                }, path);
            }
            if (input.policy.kind === 'all-named-approvers') {
                return freezePortable({
                    ...base,
                    kind: 'task-goal' as const,
                    policy: {
                        kind: 'all-named-approvers' as const,
                        approverIds: normalizeApprovers(
                            input.policy.approverIds,
                            `${path}.policy.approverIds`
                        )
                    }
                }, path);
            }
            return fail(
                'INVALID_NODE',
                `${path}.policy.kind`,
                'Task policy kind is unsupported'
            );
        }
        case 'decision-goal': {
            if (
                input.policy === null ||
                typeof input.policy !== 'object' ||
                input.policy.kind !== 'all-named-approvers'
            ) {
                return fail(
                    'INVALID_NODE',
                    `${path}.policy`,
                    'Decision policy must require all named approvers'
                );
            }
            return freezePortable({
                ...base,
                kind: 'decision-goal' as const,
                policy: {
                    kind: 'all-named-approvers' as const,
                    approverIds: normalizeApprovers(
                        input.policy.approverIds,
                        `${path}.policy.approverIds`
                    )
                }
            }, path);
        }
        default: {
            return fail(
                'INVALID_NODE',
                `${path}.kind`,
                'Goal node kind is unsupported'
            );
        }
    }
};

export interface CoreResearchGoalRequiresEdge {
    readonly kind: 'requires';
    readonly dependentId: string;
    readonly prerequisiteId: string;
}

export interface CoreResearchGoalOneOfEdge {
    readonly kind: 'one-of';
    readonly dependentId: string;
    readonly groupId: string;
    readonly prerequisiteId: string;
}

export type CoreResearchGoalDependencyEdge =
    | CoreResearchGoalRequiresEdge
    | CoreResearchGoalOneOfEdge;

const normalizeEdge = (
    input: CoreResearchGoalDependencyEdge,
    path: string
): CoreResearchGoalDependencyEdge => {
    if (input === null || typeof input !== 'object') {
        return fail('INVALID_EDGE', path, 'Dependency edge must be a record');
    }
    const base = {
        dependentId: assertId(
            input.dependentId,
            `${path}.dependentId`,
            'INVALID_EDGE'
        ),
        prerequisiteId: assertId(
            input.prerequisiteId,
            `${path}.prerequisiteId`,
            'INVALID_EDGE'
        )
    };
    if (base.dependentId === base.prerequisiteId) {
        return fail(
            'INVALID_EDGE',
            path,
            'Dependency edge cannot target its own dependent'
        );
    }
    if (input.kind === 'requires') {
        return Object.freeze({ kind: 'requires' as const, ...base });
    }
    if (input.kind === 'one-of') {
        return Object.freeze({
            kind: 'one-of' as const,
            ...base,
            groupId: assertLocalId(input.groupId, `${path}.groupId`)
        });
    }
    return fail(
        'INVALID_EDGE',
        `${path}.kind`,
        'Dependency edge kind is unsupported'
    );
};

const edgeKey = (edge: CoreResearchGoalDependencyEdge): string =>
    `${edge.dependentId}\u0000${edge.kind}\u0000` +
    `${edge.kind === 'one-of' ? edge.groupId : ''}\u0000` +
    edge.prerequisiteId;

const compareEdges = (
    left: CoreResearchGoalDependencyEdge,
    right: CoreResearchGoalDependencyEdge
): number => compareText(edgeKey(left), edgeKey(right));

export interface CoreResearchGoalGraphDefinitionInput {
    readonly revision: string;
    readonly nodes: readonly CoreResearchGoalNodeInput[];
    readonly edges?: readonly CoreResearchGoalDependencyEdge[];
}

export interface CoreResearchGoalGraphDefinition {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.definitionRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly logicProfile:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile;
    readonly graphRevision: string;
    readonly nodes: readonly CoreResearchGoalNode[];
    readonly edges: readonly CoreResearchGoalDependencyEdge[];
}

interface PreparedDefinition {
    readonly definition: CoreResearchGoalGraphDefinition;
    readonly nodesById: ReadonlyMap<string, CoreResearchGoalNode>;
    readonly outgoing: ReadonlyMap<
        string,
        readonly CoreResearchGoalDependencyEdge[]
    >;
}

const dependencyCycle = (
    nodeIds: readonly string[],
    outgoing: ReadonlyMap<string, readonly CoreResearchGoalDependencyEdge[]>
): readonly string[] | undefined => {
    const state = new Map<string, 'visiting' | 'complete'>();
    const stack: string[] = [];
    const visit = (nodeId: string): readonly string[] | undefined => {
        const existing = state.get(nodeId);
        if (existing === 'complete') return undefined;
        if (existing === 'visiting') {
            const start = stack.indexOf(nodeId);
            return Object.freeze([...stack.slice(start), nodeId]);
        }
        state.set(nodeId, 'visiting');
        stack.push(nodeId);
        for (const edge of outgoing.get(nodeId) ?? []) {
            const cycle = visit(edge.prerequisiteId);
            if (cycle !== undefined) return cycle;
        }
        stack.pop();
        state.set(nodeId, 'complete');
        return undefined;
    };
    for (const nodeId of nodeIds) {
        const cycle = visit(nodeId);
        if (cycle !== undefined) return cycle;
    }
    return undefined;
};

const prepareDefinitionInput = (
    input: CoreResearchGoalGraphDefinitionInput
): PreparedDefinition => {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_DEFINITION',
            'definition',
            'Goal-graph definition input must be a record'
        );
    }
    const graphRevision = assertRevision(
        input.revision,
        'definition.graphRevision',
        'INVALID_DEFINITION'
    );
    if (!Array.isArray(input.nodes) || input.nodes.length === 0) {
        return fail(
            'INVALID_DEFINITION',
            'definition.nodes',
            'Goal-graph definition requires at least one node'
        );
    }
    if (input.nodes.length > CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxNodes) {
        return fail(
            'NODE_LIMIT_EXCEEDED',
            'definition.nodes',
            'Goal-graph definition exceeds the node bound'
        );
    }
    const nodesById = new Map<string, CoreResearchGoalNode>();
    const nodes = input.nodes.map((node, index) => {
        const normalized = normalizeNode(node, `definition.nodes[${index}]`);
        if (nodesById.has(normalized.id)) {
            return fail(
                'DUPLICATE_NODE',
                `definition.nodes[${index}].id`,
                'Goal node identity occurs more than once'
            );
        }
        nodesById.set(normalized.id, normalized);
        return normalized;
    }).sort((left, right) => compareText(left.id, right.id));
    const edgeInput = input.edges ?? [];
    if (!Array.isArray(edgeInput)) {
        return fail(
            'INVALID_EDGE',
            'definition.edges',
            'Goal dependency edges must be an array'
        );
    }
    if (edgeInput.length > CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxEdges) {
        return fail(
            'EDGE_LIMIT_EXCEEDED',
            'definition.edges',
            'Goal-graph definition exceeds the edge bound'
        );
    }
    const seenEdges = new Set<string>();
    const edges = edgeInput.map((edge, index) => {
        const normalized = normalizeEdge(edge, `definition.edges[${index}]`);
        if (
            !nodesById.has(normalized.dependentId) ||
            !nodesById.has(normalized.prerequisiteId)
        ) {
            return fail(
                'UNKNOWN_NODE',
                `definition.edges[${index}]`,
                'Dependency edge refers to an unknown goal node'
            );
        }
        const key = edgeKey(normalized);
        if (seenEdges.has(key)) {
            return fail(
                'DUPLICATE_EDGE',
                `definition.edges[${index}]`,
                'Goal dependency edge occurs more than once'
            );
        }
        seenEdges.add(key);
        return normalized;
    }).sort(compareEdges);
    const outgoingMutable = new Map<
        string,
        CoreResearchGoalDependencyEdge[]
    >();
    edges.forEach(edge => {
        const current = outgoingMutable.get(edge.dependentId) ?? [];
        current.push(edge);
        outgoingMutable.set(edge.dependentId, current);
    });
    const outgoing = new Map([...outgoingMutable].map(([nodeId, values]) => [
        nodeId,
        Object.freeze(values.sort(compareEdges))
    ] as const));
    nodes.forEach(node => {
        if (
            node.kind === 'task-goal' &&
            node.policy.kind === 'all-prerequisites' &&
            (outgoing.get(node.id)?.length ?? 0) === 0
        ) {
            fail(
                'VACUOUS_TASK',
                `definition.nodes.${node.id}.policy`,
                'All-prerequisites task requires at least one dependency'
            );
        }
    });
    const cycle = dependencyCycle(nodes.map(node => node.id), outgoing);
    if (cycle !== undefined) {
        return fail(
            'DEPENDENCY_CYCLE',
            'definition.edges',
            `Goal dependency cycle: ${cycle.join(' -> ')}`
        );
    }
    const definition = freezePortable({
        revision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.definitionRevision,
        profileRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
        logicProfile: CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile,
        graphRevision,
        nodes,
        edges
    }, 'researchGoalGraphDefinition');
    return {
        definition,
        nodesById: new Map(definition.nodes.map(node => [node.id, node])),
        outgoing: new Map(definition.nodes.map(node => [
            node.id,
            Object.freeze(definition.edges.filter(edge =>
                edge.dependentId === node.id
            ))
        ]))
    };
};

/** Construct one canonical finite research-goal definition. */
export function createCoreResearchGoalGraphDefinition(
    input: CoreResearchGoalGraphDefinitionInput
): CoreResearchGoalGraphDefinition {
    return prepareDefinitionInput(input).definition;
}

export const serializeCoreResearchGoalGraphDefinition = (
    definition: CoreResearchGoalGraphDefinition
): string => serializeCoreLfWorkspaceCanonicalJson(
    definition,
    'researchGoalGraphDefinition'
);

const nodeAsInput = (
    node: CoreResearchGoalNode
): CoreResearchGoalNodeInput => {
    if (node === null || typeof node !== 'object') {
        return fail(
            'INVALID_NODE',
            'definition.nodes',
            'Goal node artifact must be a data record'
        );
    }
    switch (node.kind) {
        case 'theorem-goal':
            return {
                id: node.id,
                revision: node.revision,
                title: node.title,
                kind: node.kind,
                proof: node.proof,
                expectedType: node.expectedType
            };
        case 'task-goal':
            return {
                id: node.id,
                revision: node.revision,
                title: node.title,
                kind: node.kind,
                policy: node.policy
            };
        case 'decision-goal':
            return {
                id: node.id,
                revision: node.revision,
                title: node.title,
                kind: node.kind,
                policy: node.policy
            };
        default:
            return fail(
                'INVALID_NODE',
                'definition.nodes.kind',
                'Goal node artifact kind is unsupported'
            );
    }
};

const prepareDefinitionArtifact = (
    definition: CoreResearchGoalGraphDefinition
): PreparedDefinition => {
    if (
        definition === null ||
        typeof definition !== 'object' ||
        definition.revision !==
            CORE_RESEARCH_GOAL_GRAPH_PROFILE.definitionRevision ||
        definition.profileRevision !==
            CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision ||
        definition.logicProfile !==
            CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile ||
        !Array.isArray(definition.nodes) ||
        !Array.isArray(definition.edges)
    ) {
        return fail(
            'INVALID_DEFINITION',
            'definition',
            'Goal-graph definition uses unsupported profile data'
        );
    }
    const prepared = prepareDefinitionInput({
        revision: definition.graphRevision,
        nodes: definition.nodes.map(nodeAsInput),
        edges: definition.edges
    });
    if (
        serializeCoreResearchGoalGraphDefinition(prepared.definition) !==
            serializeCoreResearchGoalGraphDefinition(definition)
    ) {
        return fail(
            'INVALID_DEFINITION',
            'definition',
            'Goal-graph definition differs from canonical reconstruction'
        );
    }
    return prepared;
};

export interface CoreResearchGoalObligationDependency {
    readonly edge: CoreResearchGoalDependencyEdge;
    readonly prerequisite: CoreResearchGoalNode;
}

export interface CoreResearchGoalObligation {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.obligationRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly node: CoreResearchGoalNode;
    readonly dependencies: readonly CoreResearchGoalObligationDependency[];
}

const obligationFromPrepared = (
    prepared: PreparedDefinition,
    nodeId: string
): CoreResearchGoalObligation => {
    const node = prepared.nodesById.get(nodeId);
    if (node === undefined) {
        return fail(
            'UNKNOWN_NODE',
            'obligation.nodeId',
            `Goal definition has no node '${nodeId}'`
        );
    }
    return freezePortable({
        revision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.obligationRevision,
        profileRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
        node,
        dependencies: (prepared.outgoing.get(nodeId) ?? []).map(edge => ({
            edge,
            prerequisite: prepared.nodesById.get(edge.prerequisiteId)!
        }))
    }, 'researchGoalObligation');
};

/** Exact acceptance surface to which evidence is bound. */
export function createCoreResearchGoalObligation(
    definition: CoreResearchGoalGraphDefinition,
    nodeId: string
): CoreResearchGoalObligation {
    return obligationFromPrepared(
        prepareDefinitionArtifact(definition),
        assertId(nodeId, 'obligation.nodeId', 'UNKNOWN_NODE')
    );
}

export const serializeCoreResearchGoalObligation = (
    obligation: CoreResearchGoalObligation
): string => serializeCoreLfWorkspaceCanonicalJson(
    obligation,
    'researchGoalObligation'
);

interface CoreResearchGoalEvidenceInputBase {
    readonly id: string;
    readonly subjectNodeId: string;
}

export interface CoreResearchCheckedProofEvidenceInput
extends CoreResearchGoalEvidenceInputBase {
    readonly kind: 'checked-proof';
    readonly source: CoreLfProofDevelopmentSourceSnapshot;
}

export interface CoreResearchHumanApprovalEvidenceInput
extends CoreResearchGoalEvidenceInputBase {
    readonly kind: 'human-approval';
    readonly actorId: string;
    readonly disposition: 'approve' | 'reject';
    readonly statement: string;
}

export interface CoreResearchAiProposalEvidenceInput
extends CoreResearchGoalEvidenceInputBase {
    readonly kind: 'ai-proposal';
    readonly provider: {
        readonly id: string;
        readonly revision: string;
    };
    readonly proposal: string;
}

export type CoreResearchGoalEvidenceInput =
    | CoreResearchCheckedProofEvidenceInput
    | CoreResearchHumanApprovalEvidenceInput
    | CoreResearchAiProposalEvidenceInput;

interface CoreResearchGoalEvidenceBase {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.evidenceRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly id: string;
    readonly subject: {
        readonly nodeId: string;
        readonly obligationText: string;
    };
}

export interface CoreResearchCheckedProofEvidence
extends CoreResearchGoalEvidenceBase {
    readonly kind: 'checked-proof';
    readonly source: CoreLfProofDevelopmentSourceSnapshot;
    readonly sourceHashesRecomputed: false;
}

export interface CoreResearchHumanApprovalEvidence
extends CoreResearchGoalEvidenceBase {
    readonly kind: 'human-approval';
    readonly actorId: string;
    readonly disposition: 'approve' | 'reject';
    readonly statement: string;
    readonly attributionAuthority:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.humanAttributionAuthority;
}

export interface CoreResearchAiProposalEvidence
extends CoreResearchGoalEvidenceBase {
    readonly kind: 'ai-proposal';
    readonly provider: {
        readonly id: string;
        readonly revision: string;
    };
    readonly proposal: string;
    readonly authority:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.aiProposalAuthority;
}

export type CoreResearchGoalEvidence =
    | CoreResearchCheckedProofEvidence
    | CoreResearchHumanApprovalEvidence
    | CoreResearchAiProposalEvidence;

const evidenceSubject = (
    prepared: PreparedDefinition,
    nodeId: string
): CoreResearchGoalEvidenceBase['subject'] => {
    const obligation = obligationFromPrepared(prepared, nodeId);
    return Object.freeze({
        nodeId,
        obligationText: serializeCoreResearchGoalObligation(obligation)
    });
};

type CoreResearchGoalEvidencePayload =
    | Omit<
        CoreResearchCheckedProofEvidence,
        'revision' | 'profileRevision'
    >
    | Omit<
        CoreResearchHumanApprovalEvidence,
        'revision' | 'profileRevision'
    >
    | Omit<
        CoreResearchAiProposalEvidence,
        'revision' | 'profileRevision'
    >;

const buildEvidence = (
    value: CoreResearchGoalEvidencePayload
): CoreResearchGoalEvidence => freezePortable<CoreResearchGoalEvidence>({
    revision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.evidenceRevision,
    profileRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
    ...value
} as CoreResearchGoalEvidence, 'researchGoalEvidence', 'INVALID_EVIDENCE');

/** Bind one exact proof, approval, or advisory proposal to a goal obligation. */
export function createCoreResearchGoalEvidence(
    definition: CoreResearchGoalGraphDefinition,
    input: CoreResearchGoalEvidenceInput
): CoreResearchGoalEvidence {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_EVIDENCE',
            'evidence',
            'Goal evidence input must be a data record'
        );
    }
    const prepared = prepareDefinitionArtifact(definition);
    const id = assertId(input.id, 'evidence.id', 'INVALID_EVIDENCE');
    const nodeId = assertId(
        input.subjectNodeId,
        'evidence.subjectNodeId',
        'INVALID_EVIDENCE'
    );
    if (!prepared.nodesById.has(nodeId)) {
        return fail(
            'UNKNOWN_NODE',
            'evidence.subjectNodeId',
            `Goal evidence targets unknown node '${nodeId}'`
        );
    }
    const subject = evidenceSubject(prepared, nodeId);
    switch (input.kind) {
        case 'checked-proof': {
            let source: CoreLfProofDevelopmentSourceSnapshot;
            try {
                source = reconstructCoreLfProofDevelopmentSourceSnapshot(
                    input.source
                ).snapshot;
            } catch (error: unknown) {
                return fail(
                    'INVALID_EVIDENCE',
                    'evidence.source',
                    'Checked-proof evidence source is not canonical',
                    error
                );
            }
            return buildEvidence({
                id,
                subject,
                kind: 'checked-proof',
                source,
                sourceHashesRecomputed: false
            });
        }
        case 'human-approval': {
            if (
                input.disposition !== 'approve' &&
                input.disposition !== 'reject'
            ) {
                return fail(
                    'INVALID_EVIDENCE',
                    'evidence.disposition',
                    'Human approval must approve or reject'
                );
            }
            return buildEvidence({
                id,
                subject,
                kind: 'human-approval',
                actorId: assertId(
                    input.actorId,
                    'evidence.actorId',
                    'INVALID_EVIDENCE'
                ),
                disposition: input.disposition,
                statement: normalizeText(
                    input.statement,
                    'evidence.statement',
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxStatementLength,
                    true,
                    'INVALID_EVIDENCE'
                ),
                attributionAuthority:
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE
                        .humanAttributionAuthority
            });
        }
        case 'ai-proposal': {
            if (
                input.provider === null ||
                typeof input.provider !== 'object'
            ) {
                return fail(
                    'INVALID_EVIDENCE',
                    'evidence.provider',
                    'AI provider identity must be a data record'
                );
            }
            return buildEvidence({
                id,
                subject,
                kind: 'ai-proposal',
                provider: {
                    id: assertId(
                        input.provider.id,
                        'evidence.provider.id',
                        'INVALID_EVIDENCE'
                    ),
                    revision: assertRevision(
                        input.provider.revision,
                        'evidence.provider.revision',
                        'INVALID_EVIDENCE'
                    )
                },
                proposal: normalizeText(
                    input.proposal,
                    'evidence.proposal',
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxProposalLength,
                    true,
                    'INVALID_EVIDENCE'
                ),
                authority: CORE_RESEARCH_GOAL_GRAPH_PROFILE.aiProposalAuthority
            });
        }
        default:
            return fail(
                'INVALID_EVIDENCE',
                'evidence.kind',
                'Goal evidence kind is unsupported'
            );
    }
}

export const serializeCoreResearchGoalEvidence = (
    evidence: CoreResearchGoalEvidence
): string => serializeCoreLfWorkspaceCanonicalJson(
    evidence,
    'researchGoalEvidence'
);

const normalizeEvidenceArtifact = (
    evidence: CoreResearchGoalEvidence,
    path: string
): CoreResearchGoalEvidence => {
    if (
        evidence === null ||
        typeof evidence !== 'object' ||
        evidence.revision !== CORE_RESEARCH_GOAL_GRAPH_PROFILE.evidenceRevision ||
        evidence.profileRevision !== CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision ||
        evidence.subject === null ||
        typeof evidence.subject !== 'object'
    ) {
        return fail(
            'INVALID_EVIDENCE',
            path,
            'Goal evidence uses unsupported or malformed profile data'
        );
    }
    const id = assertId(evidence.id, `${path}.id`, 'INVALID_EVIDENCE');
    const subject = {
        nodeId: assertId(
            evidence.subject.nodeId,
            `${path}.subject.nodeId`,
            'INVALID_EVIDENCE'
        ),
        obligationText: typeof evidence.subject.obligationText === 'string' &&
            evidence.subject.obligationText.length > 0
            ? evidence.subject.obligationText
            : fail(
                'INVALID_EVIDENCE',
                `${path}.subject.obligationText`,
                'Goal evidence requires exact nonempty obligation text'
            )
    };
    let normalized: CoreResearchGoalEvidence;
    switch (evidence.kind) {
        case 'checked-proof': {
            if (evidence.sourceHashesRecomputed !== false) {
                return fail(
                    'INVALID_EVIDENCE',
                    `${path}.sourceHashesRecomputed`,
                    'Checked-proof evidence cannot claim recomputed hashes'
                );
            }
            let source: CoreLfProofDevelopmentSourceSnapshot;
            try {
                source = reconstructCoreLfProofDevelopmentSourceSnapshot(
                    evidence.source
                ).snapshot;
            } catch (error: unknown) {
                return fail(
                    'INVALID_EVIDENCE',
                    `${path}.source`,
                    'Checked-proof evidence source is not canonical',
                    error
                );
            }
            normalized = buildEvidence({
                id,
                subject,
                kind: 'checked-proof',
                source,
                sourceHashesRecomputed: false
            });
            break;
        }
        case 'human-approval': {
            if (
                evidence.attributionAuthority !==
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE
                        .humanAttributionAuthority ||
                (
                    evidence.disposition !== 'approve' &&
                    evidence.disposition !== 'reject'
                )
            ) {
                return fail(
                    'INVALID_EVIDENCE',
                    path,
                    'Human approval evidence is malformed'
                );
            }
            normalized = buildEvidence({
                id,
                subject,
                kind: 'human-approval',
                actorId: assertId(
                    evidence.actorId,
                    `${path}.actorId`,
                    'INVALID_EVIDENCE'
                ),
                disposition: evidence.disposition,
                statement: normalizeText(
                    evidence.statement,
                    `${path}.statement`,
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxStatementLength,
                    true,
                    'INVALID_EVIDENCE'
                ),
                attributionAuthority:
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE
                        .humanAttributionAuthority
            });
            break;
        }
        case 'ai-proposal': {
            if (
                evidence.authority !==
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE.aiProposalAuthority ||
                evidence.provider === null ||
                typeof evidence.provider !== 'object'
            ) {
                return fail(
                    'INVALID_EVIDENCE',
                    path,
                    'AI proposal evidence is malformed'
                );
            }
            normalized = buildEvidence({
                id,
                subject,
                kind: 'ai-proposal',
                provider: {
                    id: assertId(
                        evidence.provider.id,
                        `${path}.provider.id`,
                        'INVALID_EVIDENCE'
                    ),
                    revision: assertRevision(
                        evidence.provider.revision,
                        `${path}.provider.revision`,
                        'INVALID_EVIDENCE'
                    )
                },
                proposal: normalizeText(
                    evidence.proposal,
                    `${path}.proposal`,
                    CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxProposalLength,
                    true,
                    'INVALID_EVIDENCE'
                ),
                authority: CORE_RESEARCH_GOAL_GRAPH_PROFILE.aiProposalAuthority
            });
            break;
        }
        default:
            return fail(
                'INVALID_EVIDENCE',
                `${path}.kind`,
                'Goal evidence kind is unsupported'
            );
    }
    if (
        serializeCoreResearchGoalEvidence(normalized) !==
            serializeCoreResearchGoalEvidence(evidence)
    ) {
        return fail(
            'INVALID_EVIDENCE',
            path,
            'Goal evidence differs from canonical reconstruction'
        );
    }
    return normalized;
};

export type CoreResearchGoalEvidenceOutcome =
    | 'stale'
    | 'advisory'
    | 'inapplicable-policy'
    | 'unauthorized-actor'
    | 'human-approved'
    | 'human-rejected'
    | 'checked-proof-complete'
    | 'checked-proof-incomplete'
    | 'checked-proof-rejected'
    | 'checked-proof-absent'
    | 'checked-proof-type-mismatch';

export interface CoreResearchGoalLocalDiagnostic {
    readonly family: 'research-goal';
    readonly code: 'PROOF_NOT_FOUND' | 'THEOREM_STATEMENT_MISMATCH';
    readonly path: string;
}

export type CoreResearchGoalEvidenceDiagnostic =
    | CoreResearchGoalLocalDiagnostic
    | CoreLfProofReplayDiagnostic;

export interface CoreResearchGoalOpenProofGoal {
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goalId: string;
}

export interface CoreResearchGoalEvidenceAssessment {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.assessmentRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly evidenceId: string;
    readonly nodeId: string;
    readonly evidenceKind: CoreResearchGoalEvidence['kind'];
    readonly outcome: CoreResearchGoalEvidenceOutcome;
    readonly diagnostic?: CoreResearchGoalEvidenceDiagnostic;
    readonly state?: CoreProofPlanStateSnapshot;
    readonly goalGraph?: CoreProofGoalCouplingGraph;
    readonly openGoals?: readonly CoreResearchGoalOpenProofGoal[];
    readonly sourceHashesRecomputed?: false;
}

const assessment = (
    evidence: CoreResearchGoalEvidence,
    outcome: CoreResearchGoalEvidenceOutcome,
    extras: Omit<
        CoreResearchGoalEvidenceAssessment,
        | 'revision'
        | 'profileRevision'
        | 'evidenceId'
        | 'nodeId'
        | 'evidenceKind'
        | 'outcome'
    > = {}
): CoreResearchGoalEvidenceAssessment => freezePortable({
    revision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.assessmentRevision,
    profileRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
    evidenceId: evidence.id,
    nodeId: evidence.subject.nodeId,
    evidenceKind: evidence.kind,
    outcome,
    ...extras
}, 'researchGoalEvidenceAssessment');

const assessmentForEvidence = (
    prepared: PreparedDefinition,
    evidence: CoreResearchGoalEvidence
): CoreResearchGoalEvidenceAssessment => {
    const node = prepared.nodesById.get(evidence.subject.nodeId)!;
    const currentObligationText = serializeCoreResearchGoalObligation(
        obligationFromPrepared(prepared, node.id)
    );
    if (evidence.subject.obligationText !== currentObligationText) {
        return assessment(evidence, 'stale');
    }
    if (evidence.kind === 'ai-proposal') {
        return assessment(evidence, 'advisory');
    }
    if (evidence.kind === 'human-approval') {
        if (
            node.kind === 'theorem-goal' ||
            node.policy.kind !== 'all-named-approvers'
        ) {
            return assessment(evidence, 'inapplicable-policy');
        }
        if (!node.policy.approverIds.includes(evidence.actorId)) {
            return assessment(evidence, 'unauthorized-actor');
        }
        return assessment(
            evidence,
            evidence.disposition === 'approve'
                ? 'human-approved'
                : 'human-rejected'
        );
    }
    if (node.kind !== 'theorem-goal') {
        return assessment(evidence, 'inapplicable-policy', {
            sourceHashesRecomputed: false
        });
    }
    let reconstructed: ReturnType<
        typeof reconstructCoreLfProofDevelopmentSourceSnapshot
    >;
    try {
        reconstructed = reconstructCoreLfProofDevelopmentSourceSnapshot(
            evidence.source
        );
    } catch (error: unknown) {
        return fail(
            'PROOF_SOURCE_FAILED',
            `evidence.${evidence.id}.source`,
            'Checked-proof evidence source reconstruction failed',
            error
        );
    }
    const proof = reconstructed.plan.proofs.find(candidate =>
        candidate.moduleId === node.proof.moduleId &&
        candidate.declarationId === node.proof.declarationId
    );
    if (proof === undefined) {
        return assessment(evidence, 'checked-proof-absent', {
            diagnostic: {
                family: 'research-goal',
                code: 'PROOF_NOT_FOUND',
                path: `evidence.${evidence.id}.source.proofs`
            },
            sourceHashesRecomputed: false
        });
    }
    if (serializeCoreExpression(proof.type) !== node.expectedTypeText) {
        return assessment(evidence, 'checked-proof-type-mismatch', {
            diagnostic: {
                family: 'research-goal',
                code: 'THEOREM_STATEMENT_MISMATCH',
                path: `evidence.${evidence.id}.source.proof.type`
            },
            sourceHashesRecomputed: false
        });
    }
    let workspace: ReturnType<typeof compileCoreLfDeclarationWorkspace>;
    try {
        workspace = compileCoreLfDeclarationWorkspace(
            reconstructed.plan.workspace
        );
    } catch (error: unknown) {
        return fail(
            'PROOF_SOURCE_FAILED',
            `evidence.${evidence.id}.source.workspace`,
            'Checked-proof declaration workspace failed to compile',
            error
        );
    }
    try {
        const compilation = compileCoreLfWorkspaceProofDocument(
            workspace,
            proof
        );
        const state = compilation.artifact.proofArtifact.state;
        if (state.status === 'complete') {
            return assessment(evidence, 'checked-proof-complete', {
                state,
                goalGraph: compilation.proofCompilation.goalGraph,
                openGoals: [],
                sourceHashesRecomputed: false
            });
        }
        return assessment(evidence, 'checked-proof-incomplete', {
            state,
            goalGraph: compilation.proofCompilation.goalGraph,
            openGoals: state.goals.map(goal => ({
                moduleId: node.proof.moduleId,
                declarationId: node.proof.declarationId,
                goalId: goal.id
            })),
            sourceHashesRecomputed: false
        });
    } catch (error: unknown) {
        const diagnostic = projectCoreLfProofReplayDiagnostic(error);
        if (diagnostic === undefined) {
            return fail(
                'UNSUPPORTED_PROOF_REPLAY',
                `evidence.${evidence.id}.source.proof`,
                'Checked-proof replay raised an unclassified error',
                error
            );
        }
        return assessment(evidence, 'checked-proof-rejected', {
            diagnostic,
            sourceHashesRecomputed: false
        });
    }
};

export type CoreResearchGoalStatus =
    | 'open'
    | 'blocked'
    | 'satisfied'
    | 'rejected';

export interface CoreResearchGoalUnsatisfiedOneOfGroup {
    readonly groupId: string;
    readonly alternativeIds: readonly string[];
}

export interface CoreResearchGoalNodeResult {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.nodeResultRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly nodeId: string;
    readonly nodeKind: CoreResearchGoalNode['kind'];
    readonly status: CoreResearchGoalStatus;
    readonly satisfyingEvidenceIds: readonly string[];
    readonly rejectingEvidenceIds: readonly string[];
    readonly insufficientEvidenceIds: readonly string[];
    readonly staleEvidenceIds: readonly string[];
    readonly advisoryEvidenceIds: readonly string[];
    readonly inapplicableEvidenceIds: readonly string[];
    readonly unsatisfiedRequiredIds: readonly string[];
    readonly unsatisfiedOneOfGroups:
        readonly CoreResearchGoalUnsatisfiedOneOfGroup[];
}

export interface CoreResearchGoalEvaluationCounts {
    readonly nodes: number;
    readonly evidence: number;
    readonly open: number;
    readonly blocked: number;
    readonly satisfied: number;
    readonly rejected: number;
    readonly staleEvidence: number;
    readonly advisoryEvidence: number;
}

export interface CoreResearchGoalGraphEvaluation {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.evaluationRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly logicProfile:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile;
    readonly definition: CoreResearchGoalGraphDefinition;
    readonly evidence: readonly CoreResearchGoalEvidence[];
    readonly assessments: readonly CoreResearchGoalEvidenceAssessment[];
    readonly evaluationOrder: readonly string[];
    readonly results: readonly CoreResearchGoalNodeResult[];
    readonly counts: CoreResearchGoalEvaluationCounts;
    readonly meaning: 'policy-derived-from-exact-supplied-data';
    readonly mutableDoneField: false;
    readonly sourceHashesRecomputed: false;
    readonly humanAttributionVerified: false;
    readonly executesExternalActions: false;
}

export interface CoreResearchGoalGraphEvaluationInput {
    readonly definition: CoreResearchGoalGraphDefinition;
    readonly evidence?: readonly CoreResearchGoalEvidence[];
}

const prepareEvidence = (
    prepared: PreparedDefinition,
    input: readonly CoreResearchGoalEvidence[]
): readonly CoreResearchGoalEvidence[] => {
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_EVIDENCE',
            'evaluation.evidence',
            'Goal evidence must be an array'
        );
    }
    if (input.length > CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxEvidence) {
        return fail(
            'EVIDENCE_LIMIT_EXCEEDED',
            'evaluation.evidence',
            'Goal evaluation exceeds the evidence bound'
        );
    }
    const seen = new Set<string>();
    const approvalKeys = new Set<string>();
    return Object.freeze(input.map((item, index) => {
        const evidence = normalizeEvidenceArtifact(
            item,
            `evaluation.evidence[${index}]`
        );
        if (seen.has(evidence.id)) {
            return fail(
                'DUPLICATE_EVIDENCE',
                `evaluation.evidence[${index}].id`,
                'Goal evidence identity occurs more than once'
            );
        }
        seen.add(evidence.id);
        if (!prepared.nodesById.has(evidence.subject.nodeId)) {
            return fail(
                'UNKNOWN_NODE',
                `evaluation.evidence[${index}].subject.nodeId`,
                'Goal evidence targets an unknown node'
            );
        }
        if (evidence.kind === 'human-approval') {
            const key = `${evidence.subject.nodeId}\u0000` +
                `${evidence.subject.obligationText}\u0000${evidence.actorId}`;
            if (approvalKeys.has(key)) {
                return fail(
                    'AMBIGUOUS_APPROVAL',
                    `evaluation.evidence[${index}]`,
                    'Actor supplies multiple approvals for one exact obligation'
                );
            }
            approvalKeys.add(key);
        }
        return evidence;
    }).sort((left, right) => compareText(left.id, right.id)));
};

const statusCount = (
    results: readonly CoreResearchGoalNodeResult[],
    status: CoreResearchGoalStatus
): number => results.filter(result => result.status === status).length;

/** Freshly derive research-goal status from exact definition and evidence. */
export function evaluateCoreResearchGoalGraph(
    input: CoreResearchGoalGraphEvaluationInput
): CoreResearchGoalGraphEvaluation {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_DEFINITION',
            'evaluation',
            'Goal evaluation input must be a data record'
        );
    }
    const prepared = prepareDefinitionArtifact(input.definition);
    const evidence = prepareEvidence(prepared, input.evidence ?? []);
    const assessments = Object.freeze(evidence.map(item =>
        assessmentForEvidence(prepared, item)
    ));
    const assessmentsByNode = new Map(prepared.definition.nodes.map(node => [
        node.id,
        assessments.filter(item => item.nodeId === node.id)
    ] as const));
    const resultsById = new Map<string, CoreResearchGoalNodeResult>();
    const evaluationOrder: string[] = [];

    const evaluateNode = (nodeId: string): CoreResearchGoalNodeResult => {
        const existing = resultsById.get(nodeId);
        if (existing !== undefined) return existing;
        const node = prepared.nodesById.get(nodeId)!;
        const outgoing = prepared.outgoing.get(nodeId) ?? [];
        const prerequisiteResults = new Map(outgoing.map(edge => [
            edge.prerequisiteId,
            evaluateNode(edge.prerequisiteId)
        ] as const));
        const required = outgoing.filter(edge => edge.kind === 'requires');
        const oneOfEdges = outgoing.filter(
            (edge): edge is CoreResearchGoalOneOfEdge => edge.kind === 'one-of'
        );
        const unsatisfiedRequiredIds = required
            .filter(edge =>
                prerequisiteResults.get(edge.prerequisiteId)?.status !==
                    'satisfied'
            )
            .map(edge => edge.prerequisiteId)
            .sort(compareText);
        const groups = new Map<string, string[]>();
        oneOfEdges.forEach(edge => {
            const alternatives = groups.get(edge.groupId) ?? [];
            alternatives.push(edge.prerequisiteId);
            groups.set(edge.groupId, alternatives);
        });
        const unsatisfiedOneOfGroups = [...groups.entries()]
            .filter(([, alternatives]) => !alternatives.some(id =>
                prerequisiteResults.get(id)?.status === 'satisfied'
            ))
            .map(([groupId, alternatives]) => ({
                groupId,
                alternativeIds: Object.freeze([...alternatives].sort(compareText))
            }))
            .sort((left, right) => compareText(left.groupId, right.groupId));
        const nodeAssessments = assessmentsByNode.get(nodeId) ?? [];
        const ids = (outcomes: readonly CoreResearchGoalEvidenceOutcome[]) =>
            nodeAssessments.filter(item => outcomes.includes(item.outcome))
                .map(item => item.evidenceId)
                .sort(compareText);
        const satisfyingEvidenceIds = ids([
            'checked-proof-complete',
            'human-approved'
        ]);
        const rejectingEvidenceIds = ids(['human-rejected']);
        const insufficientEvidenceIds = ids([
            'checked-proof-incomplete',
            'checked-proof-rejected',
            'checked-proof-absent',
            'checked-proof-type-mismatch'
        ]);
        const staleEvidenceIds = ids(['stale']);
        const advisoryEvidenceIds = ids(['advisory']);
        const inapplicableEvidenceIds = ids([
            'inapplicable-policy',
            'unauthorized-actor'
        ]);

        let localSatisfied = false;
        let localRejected = false;
        if (node.kind === 'theorem-goal') {
            localSatisfied = nodeAssessments.some(item =>
                item.outcome === 'checked-proof-complete'
            );
        } else if (node.policy.kind === 'all-prerequisites') {
            localSatisfied = true;
        } else {
            const approvalByActor = new Map<string, 'approve' | 'reject'>();
            evidence.forEach(item => {
                if (
                    item.kind !== 'human-approval' ||
                    item.subject.nodeId !== nodeId
                ) return;
                const itemAssessment = nodeAssessments.find(candidate =>
                    candidate.evidenceId === item.id
                );
                if (
                    itemAssessment?.outcome === 'human-approved' ||
                    itemAssessment?.outcome === 'human-rejected'
                ) {
                    approvalByActor.set(item.actorId, item.disposition);
                }
            });
            localRejected = node.policy.approverIds.some(actorId =>
                approvalByActor.get(actorId) === 'reject'
            );
            localSatisfied = node.policy.approverIds.every(actorId =>
                approvalByActor.get(actorId) === 'approve'
            );
        }
        const dependencyBlocked = unsatisfiedRequiredIds.length > 0 ||
            unsatisfiedOneOfGroups.length > 0;
        const status: CoreResearchGoalStatus = localRejected
            ? 'rejected'
            : dependencyBlocked
                ? 'blocked'
                : localSatisfied
                    ? 'satisfied'
                    : 'open';
        const result = freezePortable({
            revision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.nodeResultRevision,
            profileRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
            nodeId,
            nodeKind: node.kind,
            status,
            satisfyingEvidenceIds,
            rejectingEvidenceIds,
            insufficientEvidenceIds,
            staleEvidenceIds,
            advisoryEvidenceIds,
            inapplicableEvidenceIds,
            unsatisfiedRequiredIds,
            unsatisfiedOneOfGroups
        }, 'researchGoalNodeResult');
        resultsById.set(nodeId, result);
        evaluationOrder.push(nodeId);
        return result;
    };

    prepared.definition.nodes.forEach(node => evaluateNode(node.id));
    const results = Object.freeze(prepared.definition.nodes.map(node =>
        resultsById.get(node.id)!
    ));
    const counts: CoreResearchGoalEvaluationCounts = {
        nodes: results.length,
        evidence: evidence.length,
        open: statusCount(results, 'open'),
        blocked: statusCount(results, 'blocked'),
        satisfied: statusCount(results, 'satisfied'),
        rejected: statusCount(results, 'rejected'),
        staleEvidence: assessments.filter(item => item.outcome === 'stale')
            .length,
        advisoryEvidence: assessments.filter(
            item => item.outcome === 'advisory'
        ).length
    };
    return freezePortable({
        revision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.evaluationRevision,
        profileRevision: CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
        logicProfile: CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile,
        definition: prepared.definition,
        evidence,
        assessments,
        evaluationOrder,
        results,
        counts,
        meaning: 'policy-derived-from-exact-supplied-data' as const,
        mutableDoneField: false as const,
        sourceHashesRecomputed: false as const,
        humanAttributionVerified: false as const,
        executesExternalActions: false as const
    }, 'researchGoalGraphEvaluation');
}

export const serializeCoreResearchGoalGraphEvaluation = (
    evaluation: CoreResearchGoalGraphEvaluation
): string => serializeCoreLfWorkspaceCanonicalJson(
    evaluation,
    'researchGoalGraphEvaluation'
);
