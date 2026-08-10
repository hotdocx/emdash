/**
 * Browser-safe, privacy-minimized views of evaluated research-goal graphs.
 *
 * This module projects freshly replayed goal evaluations to canonical data for
 * renderers and lightweight hosts. It does not reclassify evidence, verify an
 * actor, recompute a source hash, execute an action, or retain evidence
 * payloads and proof source.
 */

import {
    CORE_RESEARCH_GOAL_GRAPH_PROFILE,
    CoreResearchGoalDependencyEdge,
    CoreResearchGoalGraphEvaluation,
    CoreResearchGoalProofIdentity,
    CoreResearchGoalStatus,
    CoreResearchGoalUnsatisfiedOneOfGroup,
    evaluateCoreResearchGoalGraph,
    serializeCoreResearchGoalGraphEvaluation
} from './research_goal_graph';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_RESEARCH_GOAL_VIEW_PROFILE = Object.freeze({
    revision: 'emdash-research-goal-view-v1' as const,
    artifactRevision: 'emdash-research-goal-view-artifact-v1' as const,
    sourceGoalProfileRevision:
        CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision,
    sourceEvaluationRevision:
        CORE_RESEARCH_GOAL_GRAPH_PROFILE.evaluationRevision,
    sourceLogicProfile:
        CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile,
    meaning:
        'portable-projection-of-policy-derived-supplied-data' as const,
    edgeDirection:
        CORE_RESEARCH_GOAL_GRAPH_PROFILE.edgeDirection,
    maxNodes: CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxNodes,
    maxEdges: CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxEdges,
    maxTitleLength: CORE_RESEARCH_GOAL_GRAPH_PROFILE.maxTitleLength,
    portableProjectionOnly: true as const,
    mutableDoneField: false as const,
    sourceHashesRecomputed: false as const,
    humanAttributionVerified: false as const,
    executesExternalActions: false as const,
    retainsProofSource: false as const,
    retainsEvidencePayloads: false as const,
    retainsActorIdentities: false as const,
    performsIo: false as const,
    acquiresTime: false as const,
    computesCryptographicHashes: false as const,
    invokesLambdapi: false as const,
    nodeBuiltinDependency: false as const
});

export type CoreResearchGoalViewErrorCode =
    | 'INVALID_EVALUATION'
    | 'INVALID_VIEW'
    | 'NONCANONICAL_VIEW'
    | 'INVALID_VIEW_TEXT'
    | 'NONCANONICAL_VIEW_TEXT';

export class CoreResearchGoalViewError extends Error {
    constructor(
        public readonly code: CoreResearchGoalViewErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreResearchGoalViewError';
    }
}

const fail = (
    code: CoreResearchGoalViewErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreResearchGoalViewError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_LOCAL_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const FORBIDDEN_RECORD_KEYS = new Set([
    '__proto__',
    'constructor',
    'prototype'
]);

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

const assertDataProperties = (
    value: object,
    path: string,
    array: boolean,
    code: CoreResearchGoalViewErrorCode
): void => {
    const stringKeys: string[] = [];
    for (const key of Reflect.ownKeys(value)) {
        const stringKey = typeof key === 'string'
            ? key
            : fail(
                code,
                path,
                'Portable research-goal view data cannot have symbol keys'
            );
        if (array && stringKey === 'length') continue;
        if (FORBIDDEN_RECORD_KEYS.has(stringKey)) {
            fail(
                code,
                `${path}.${stringKey}`,
                'Portable research-goal view data uses a forbidden key'
            );
        }
        const descriptor = Object.getOwnPropertyDescriptor(value, stringKey);
        if (
            descriptor === undefined ||
            !Object.prototype.hasOwnProperty.call(descriptor, 'value') ||
            descriptor.enumerable !== true
        ) {
            fail(
                code,
                `${path}.${stringKey}`,
                'Portable research-goal view fields must be enumerable data ' +
                    'properties'
            );
        }
        stringKeys.push(stringKey);
    }
    if (!array) return;
    const length = (value as readonly unknown[]).length;
    if (
        stringKeys.length !== length ||
        stringKeys.some((key, index) => key !== String(index))
    ) {
        fail(
            code,
            path,
            'Portable research-goal view arrays must be dense and cannot ' +
                'have extra properties'
        );
    }
};

const assertPortableData = (
    value: unknown,
    path: string,
    code: CoreResearchGoalViewErrorCode,
    ancestors: ReadonlySet<object> = new Set()
): void => {
    if (value === null) return;
    switch (typeof value) {
        case 'boolean':
        case 'string':
            return;
        case 'number':
            if (Number.isFinite(value)) return;
            return fail(
                code,
                path,
                'Portable research-goal view numbers must be finite'
            );
        case 'object':
            break;
        case 'bigint':
        case 'function':
        case 'symbol':
        case 'undefined':
            return fail(
                code,
                path,
                `Portable research-goal view data cannot contain ` +
                    typeof value
            );
        default:
            return fail(
                code,
                path,
                'Portable research-goal view data has an unsupported value'
            );
    }
    if (ancestors.has(value)) {
        return fail(
            code,
            path,
            'Portable research-goal view data cannot contain a cycle'
        );
    }
    const nextAncestors = new Set(ancestors);
    nextAncestors.add(value);
    if (Array.isArray(value)) {
        assertDataProperties(value, path, true, code);
        value.forEach((entry, index) => assertPortableData(
            entry,
            `${path}[${index}]`,
            code,
            nextAncestors
        ));
        return;
    }
    const prototype = Object.getPrototypeOf(value);
    if (prototype !== Object.prototype && prototype !== null) {
        return fail(
            code,
            path,
            'Portable research-goal view data requires plain records'
        );
    }
    assertDataProperties(value, path, false, code);
    Object.entries(value as Record<string, unknown>).forEach(([key, entry]) =>
        assertPortableData(entry, `${path}.${key}`, code, nextAncestors)
    );
};

const plainRecord = (value: unknown): value is Record<string, unknown> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        Array.isArray(value)
    ) return false;
    const prototype = Object.getPrototypeOf(value);
    return prototype === Object.prototype || prototype === null;
};

const recordAt = (
    value: unknown,
    path: string
): Record<string, unknown> => {
    if (!plainRecord(value)) {
        return fail('INVALID_VIEW', path, 'Expected a plain data record');
    }
    return value;
};

const arrayAt = (value: unknown, path: string): readonly unknown[] => {
    if (!Array.isArray(value)) {
        return fail('INVALID_VIEW', path, 'Expected an array');
    }
    return value;
};

const assertExactKeys = (
    record: Record<string, unknown>,
    expected: readonly string[],
    path: string
): void => {
    const actual = Object.keys(record).sort(compareText);
    const canonicalExpected = [...expected].sort(compareText);
    if (
        actual.length !== canonicalExpected.length ||
        actual.some((key, index) => key !== canonicalExpected[index])
    ) {
        fail(
            'INVALID_VIEW',
            path,
            'Research-goal view has missing or unsupported fields'
        );
    }
};

const idAt = (value: unknown, path: string): string => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return value;
    return fail('INVALID_VIEW', path, 'Expected a stable portable identity');
};

const localIdAt = (value: unknown, path: string): string => {
    if (typeof value === 'string' && SAFE_LOCAL_ID.test(value)) return value;
    return fail(
        'INVALID_VIEW',
        path,
        'Expected a stable portable local identity'
    );
};

const revisionAt = (value: unknown, path: string): string => {
    if (typeof value === 'string' && SAFE_REVISION.test(value)) return value;
    return fail('INVALID_VIEW', path, 'Expected a stable portable revision');
};

const titleAt = (value: unknown, path: string): string => {
    if (
        typeof value === 'string' &&
        value.length > 0 &&
        value.length <= CORE_RESEARCH_GOAL_VIEW_PROFILE.maxTitleLength &&
        value.trim() === value &&
        !/[\u0000-\u001f\u007f]/u.test(value)
    ) return value;
    return fail(
        'INVALID_VIEW',
        path,
        'Expected bounded, trimmed, single-line portable title text'
    );
};

const nonnegativeIntegerAt = (value: unknown, path: string): number => {
    if (
        typeof value === 'number' &&
        Number.isSafeInteger(value) &&
        value >= 0
    ) return value;
    return fail('INVALID_VIEW', path, 'Expected a nonnegative safe integer');
};

const literalAt = <T extends string | boolean>(
    value: unknown,
    expected: T,
    path: string
): T => {
    if (value === expected) return expected;
    return fail('INVALID_VIEW', path, `Expected fixed value ${String(expected)}`);
};

const sortedUniqueIdsAt = (
    value: unknown,
    path: string
): readonly string[] => {
    const ids = arrayAt(value, path).map((entry, index) =>
        idAt(entry, `${path}[${index}]`)
    );
    for (let index = 1; index < ids.length; index += 1) {
        if (compareText(ids[index - 1], ids[index]) >= 0) {
            fail(
                'INVALID_VIEW',
                `${path}[${index}]`,
                'Identity sets must be unique and canonically sorted'
            );
        }
    }
    return Object.freeze(ids);
};

const sameTextArray = (
    left: readonly string[],
    right: readonly string[]
): boolean => left.length === right.length &&
    left.every((value, index) => value === right[index]);

export interface CoreResearchGoalViewSource {
    readonly goalProfileRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.revision;
    readonly evaluationRevision:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.evaluationRevision;
    readonly logicProfile:
        typeof CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile;
    readonly graphRevision: string;
}

export interface CoreResearchGoalViewNodeBase {
    readonly id: string;
    readonly nodeRevision: string;
    readonly title: string;
    readonly kind: 'theorem-goal' | 'task-goal' | 'decision-goal';
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

export interface CoreResearchTheoremGoalViewNode
extends CoreResearchGoalViewNodeBase {
    readonly kind: 'theorem-goal';
    readonly proof: CoreResearchGoalProofIdentity;
}

export interface CoreResearchTaskGoalViewNode
extends CoreResearchGoalViewNodeBase {
    readonly kind: 'task-goal';
}

export interface CoreResearchDecisionGoalViewNode
extends CoreResearchGoalViewNodeBase {
    readonly kind: 'decision-goal';
}

export type CoreResearchGoalViewNode =
    | CoreResearchTheoremGoalViewNode
    | CoreResearchTaskGoalViewNode
    | CoreResearchDecisionGoalViewNode;

export interface CoreResearchGoalViewCounts {
    readonly nodes: number;
    readonly open: number;
    readonly blocked: number;
    readonly satisfied: number;
    readonly rejected: number;
}

export interface CoreResearchGoalView {
    readonly revision:
        typeof CORE_RESEARCH_GOAL_VIEW_PROFILE.artifactRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_GOAL_VIEW_PROFILE.revision;
    readonly source: CoreResearchGoalViewSource;
    readonly nodes: readonly CoreResearchGoalViewNode[];
    readonly edges: readonly CoreResearchGoalDependencyEdge[];
    readonly counts: CoreResearchGoalViewCounts;
    readonly meaning: typeof CORE_RESEARCH_GOAL_VIEW_PROFILE.meaning;
    readonly edgeDirection:
        typeof CORE_RESEARCH_GOAL_VIEW_PROFILE.edgeDirection;
    readonly portableProjectionOnly: true;
    readonly mutableDoneField: false;
    readonly sourceHashesRecomputed: false;
    readonly humanAttributionVerified: false;
    readonly executesExternalActions: false;
}

const VIEW_NODE_RESULT_FIELDS = Object.freeze([
    'id',
    'nodeRevision',
    'title',
    'kind',
    'status',
    'satisfyingEvidenceIds',
    'rejectingEvidenceIds',
    'insufficientEvidenceIds',
    'staleEvidenceIds',
    'advisoryEvidenceIds',
    'inapplicableEvidenceIds',
    'unsatisfiedRequiredIds',
    'unsatisfiedOneOfGroups'
] as const);

const normalizeProofIdentity = (
    value: unknown,
    path: string
): CoreResearchGoalProofIdentity => {
    const record = recordAt(value, path);
    assertExactKeys(record, ['moduleId', 'declarationId'], path);
    return Object.freeze({
        moduleId: idAt(record.moduleId, `${path}.moduleId`),
        declarationId: idAt(record.declarationId, `${path}.declarationId`)
    });
};

const normalizeOneOfGroups = (
    value: unknown,
    path: string
): readonly CoreResearchGoalUnsatisfiedOneOfGroup[] => {
    const groups = arrayAt(value, path).map((entry, index) => {
        const itemPath = `${path}[${index}]`;
        const record = recordAt(entry, itemPath);
        assertExactKeys(record, ['groupId', 'alternativeIds'], itemPath);
        const alternativeIds = sortedUniqueIdsAt(
            record.alternativeIds,
            `${itemPath}.alternativeIds`
        );
        if (alternativeIds.length === 0) {
            fail(
                'INVALID_VIEW',
                `${itemPath}.alternativeIds`,
                'Unsatisfied one-of group requires at least one alternative'
            );
        }
        return Object.freeze({
            groupId: localIdAt(record.groupId, `${itemPath}.groupId`),
            alternativeIds
        });
    });
    for (let index = 1; index < groups.length; index += 1) {
        if (compareText(groups[index - 1].groupId, groups[index].groupId) >= 0) {
            fail(
                'INVALID_VIEW',
                `${path}[${index}].groupId`,
                'One-of explanations must be unique and canonically sorted'
            );
        }
    }
    return Object.freeze(groups);
};

const statusAt = (value: unknown, path: string): CoreResearchGoalStatus => {
    if (
        value === 'open' ||
        value === 'blocked' ||
        value === 'satisfied' ||
        value === 'rejected'
    ) return value;
    return fail('INVALID_VIEW', path, 'Research-goal status is unsupported');
};

const normalizeViewNode = (
    value: unknown,
    path: string
): CoreResearchGoalViewNode => {
    const record = recordAt(value, path);
    const kind = record.kind;
    if (
        kind !== 'theorem-goal' &&
        kind !== 'task-goal' &&
        kind !== 'decision-goal'
    ) {
        return fail('INVALID_VIEW', `${path}.kind`, 'Goal kind is unsupported');
    }
    assertExactKeys(
        record,
        kind === 'theorem-goal'
            ? [...VIEW_NODE_RESULT_FIELDS, 'proof']
            : VIEW_NODE_RESULT_FIELDS,
        path
    );
    const common = {
        id: idAt(record.id, `${path}.id`),
        nodeRevision: revisionAt(
            record.nodeRevision,
            `${path}.nodeRevision`
        ),
        title: titleAt(record.title, `${path}.title`),
        kind,
        status: statusAt(record.status, `${path}.status`),
        satisfyingEvidenceIds: sortedUniqueIdsAt(
            record.satisfyingEvidenceIds,
            `${path}.satisfyingEvidenceIds`
        ),
        rejectingEvidenceIds: sortedUniqueIdsAt(
            record.rejectingEvidenceIds,
            `${path}.rejectingEvidenceIds`
        ),
        insufficientEvidenceIds: sortedUniqueIdsAt(
            record.insufficientEvidenceIds,
            `${path}.insufficientEvidenceIds`
        ),
        staleEvidenceIds: sortedUniqueIdsAt(
            record.staleEvidenceIds,
            `${path}.staleEvidenceIds`
        ),
        advisoryEvidenceIds: sortedUniqueIdsAt(
            record.advisoryEvidenceIds,
            `${path}.advisoryEvidenceIds`
        ),
        inapplicableEvidenceIds: sortedUniqueIdsAt(
            record.inapplicableEvidenceIds,
            `${path}.inapplicableEvidenceIds`
        ),
        unsatisfiedRequiredIds: sortedUniqueIdsAt(
            record.unsatisfiedRequiredIds,
            `${path}.unsatisfiedRequiredIds`
        ),
        unsatisfiedOneOfGroups: normalizeOneOfGroups(
            record.unsatisfiedOneOfGroups,
            `${path}.unsatisfiedOneOfGroups`
        )
    };
    if (kind === 'theorem-goal') {
        return Object.freeze({
            ...common,
            kind,
            proof: normalizeProofIdentity(record.proof, `${path}.proof`)
        });
    }
    return Object.freeze({ ...common, kind });
};

const edgeKey = (edge: CoreResearchGoalDependencyEdge): string =>
    `${edge.dependentId}\u0000${edge.kind}\u0000` +
    `${edge.kind === 'one-of' ? edge.groupId : ''}\u0000` +
    edge.prerequisiteId;

const normalizeViewEdge = (
    value: unknown,
    path: string
): CoreResearchGoalDependencyEdge => {
    const record = recordAt(value, path);
    if (record.kind === 'requires') {
        assertExactKeys(
            record,
            ['kind', 'dependentId', 'prerequisiteId'],
            path
        );
        const edge = {
            kind: 'requires' as const,
            dependentId: idAt(record.dependentId, `${path}.dependentId`),
            prerequisiteId: idAt(
                record.prerequisiteId,
                `${path}.prerequisiteId`
            )
        };
        if (edge.dependentId === edge.prerequisiteId) {
            return fail(
                'INVALID_VIEW',
                path,
                'Dependency edge cannot target its own dependent'
            );
        }
        return Object.freeze(edge);
    }
    if (record.kind === 'one-of') {
        assertExactKeys(
            record,
            ['kind', 'dependentId', 'groupId', 'prerequisiteId'],
            path
        );
        const edge = {
            kind: 'one-of' as const,
            dependentId: idAt(record.dependentId, `${path}.dependentId`),
            groupId: localIdAt(record.groupId, `${path}.groupId`),
            prerequisiteId: idAt(
                record.prerequisiteId,
                `${path}.prerequisiteId`
            )
        };
        if (edge.dependentId === edge.prerequisiteId) {
            return fail(
                'INVALID_VIEW',
                path,
                'Dependency edge cannot target its own dependent'
            );
        }
        return Object.freeze(edge);
    }
    return fail('INVALID_VIEW', `${path}.kind`, 'Edge kind is unsupported');
};

const assertAcyclic = (
    nodeIds: readonly string[],
    edges: readonly CoreResearchGoalDependencyEdge[]
): void => {
    const outgoing = new Map(nodeIds.map(id => [id, [] as string[]]));
    edges.forEach(edge => outgoing.get(edge.dependentId)!.push(
        edge.prerequisiteId
    ));
    const state = new Map<string, 'visiting' | 'complete'>();
    const visit = (id: string): void => {
        const existing = state.get(id);
        if (existing === 'complete') return;
        if (existing === 'visiting') {
            fail(
                'INVALID_VIEW',
                'view.edges',
                'Research-goal view dependency graph must be acyclic'
            );
        }
        state.set(id, 'visiting');
        (outgoing.get(id) ?? []).forEach(visit);
        state.set(id, 'complete');
    };
    nodeIds.forEach(visit);
};

const statusCount = (
    nodes: readonly CoreResearchGoalViewNode[],
    status: CoreResearchGoalStatus
): number => nodes.filter(node => node.status === status).length;

const normalizeCounts = (
    value: unknown,
    nodes: readonly CoreResearchGoalViewNode[]
): CoreResearchGoalViewCounts => {
    const record = recordAt(value, 'view.counts');
    assertExactKeys(
        record,
        ['nodes', 'open', 'blocked', 'satisfied', 'rejected'],
        'view.counts'
    );
    const supplied: CoreResearchGoalViewCounts = {
        nodes: nonnegativeIntegerAt(record.nodes, 'view.counts.nodes'),
        open: nonnegativeIntegerAt(record.open, 'view.counts.open'),
        blocked: nonnegativeIntegerAt(record.blocked, 'view.counts.blocked'),
        satisfied: nonnegativeIntegerAt(
            record.satisfied,
            'view.counts.satisfied'
        ),
        rejected: nonnegativeIntegerAt(
            record.rejected,
            'view.counts.rejected'
        )
    };
    const expected: CoreResearchGoalViewCounts = {
        nodes: nodes.length,
        open: statusCount(nodes, 'open'),
        blocked: statusCount(nodes, 'blocked'),
        satisfied: statusCount(nodes, 'satisfied'),
        rejected: statusCount(nodes, 'rejected')
    };
    if (
        supplied.nodes !== expected.nodes ||
        supplied.open !== expected.open ||
        supplied.blocked !== expected.blocked ||
        supplied.satisfied !== expected.satisfied ||
        supplied.rejected !== expected.rejected
    ) {
        return fail(
            'INVALID_VIEW',
            'view.counts',
            'Research-goal view counts differ from its node statuses'
        );
    }
    return Object.freeze(expected);
};

const assertExplanationIntegrity = (
    nodes: readonly CoreResearchGoalViewNode[],
    edges: readonly CoreResearchGoalDependencyEdge[]
): void => {
    const nodesById = new Map(nodes.map(node => [node.id, node] as const));
    const evidenceIds = new Set<string>();
    nodes.forEach(node => {
        const explanationSets = [
            node.satisfyingEvidenceIds,
            node.rejectingEvidenceIds,
            node.insufficientEvidenceIds,
            node.staleEvidenceIds,
            node.advisoryEvidenceIds,
            node.inapplicableEvidenceIds
        ];
        explanationSets.forEach(ids => ids.forEach(id => {
            if (evidenceIds.has(id)) {
                fail(
                    'INVALID_VIEW',
                    `view.nodes.${node.id}`,
                    `Evidence explanation '${id}' occurs more than once`
                );
            }
            evidenceIds.add(id);
        }));

        const outgoing = edges.filter(edge => edge.dependentId === node.id);
        const expectedRequired = outgoing
            .filter(edge => edge.kind === 'requires')
            .filter(edge =>
                nodesById.get(edge.prerequisiteId)?.status !== 'satisfied'
            )
            .map(edge => edge.prerequisiteId)
            .sort(compareText);
        if (!sameTextArray(node.unsatisfiedRequiredIds, expectedRequired)) {
            fail(
                'INVALID_VIEW',
                `view.nodes.${node.id}.unsatisfiedRequiredIds`,
                'Required-dependency explanation differs from view statuses'
            );
        }
        const alternativesByGroup = new Map<string, string[]>();
        outgoing.forEach(edge => {
            if (edge.kind !== 'one-of') return;
            const alternatives = alternativesByGroup.get(edge.groupId) ?? [];
            alternatives.push(edge.prerequisiteId);
            alternativesByGroup.set(edge.groupId, alternatives);
        });
        const expectedGroups = [...alternativesByGroup.entries()]
            .map(([groupId, alternatives]) => ({
                groupId,
                alternativeIds: [...alternatives].sort(compareText)
            }))
            .filter(group => !group.alternativeIds.some(id =>
                nodesById.get(id)?.status === 'satisfied'
            ))
            .sort((left, right) => compareText(left.groupId, right.groupId));
        if (
            expectedGroups.length !== node.unsatisfiedOneOfGroups.length ||
            expectedGroups.some((group, index) => {
                const supplied = node.unsatisfiedOneOfGroups[index];
                return group.groupId !== supplied.groupId ||
                    !sameTextArray(group.alternativeIds, supplied.alternativeIds);
            })
        ) {
            fail(
                'INVALID_VIEW',
                `view.nodes.${node.id}.unsatisfiedOneOfGroups`,
                'One-of dependency explanation differs from view statuses'
            );
        }
        const dependencyBlocked = expectedRequired.length > 0 ||
            expectedGroups.length > 0;
        if (
            (dependencyBlocked &&
                node.status !== 'blocked' &&
                node.status !== 'rejected') ||
            (!dependencyBlocked && node.status === 'blocked')
        ) {
            fail(
                'INVALID_VIEW',
                `view.nodes.${node.id}.status`,
                'Derived status conflicts with dependency explanations'
            );
        }
    });
};

const normalizeView = (value: unknown): CoreResearchGoalView => {
    assertPortableData(value, 'view', 'INVALID_VIEW');
    const record = recordAt(value, 'view');
    assertExactKeys(record, [
        'revision',
        'profileRevision',
        'source',
        'nodes',
        'edges',
        'counts',
        'meaning',
        'edgeDirection',
        'portableProjectionOnly',
        'mutableDoneField',
        'sourceHashesRecomputed',
        'humanAttributionVerified',
        'executesExternalActions'
    ], 'view');
    literalAt(
        record.revision,
        CORE_RESEARCH_GOAL_VIEW_PROFILE.artifactRevision,
        'view.revision'
    );
    literalAt(
        record.profileRevision,
        CORE_RESEARCH_GOAL_VIEW_PROFILE.revision,
        'view.profileRevision'
    );
    const sourceRecord = recordAt(record.source, 'view.source');
    assertExactKeys(sourceRecord, [
        'goalProfileRevision',
        'evaluationRevision',
        'logicProfile',
        'graphRevision'
    ], 'view.source');
    const source: CoreResearchGoalViewSource = Object.freeze({
        goalProfileRevision: literalAt(
            sourceRecord.goalProfileRevision,
            CORE_RESEARCH_GOAL_VIEW_PROFILE.sourceGoalProfileRevision,
            'view.source.goalProfileRevision'
        ),
        evaluationRevision: literalAt(
            sourceRecord.evaluationRevision,
            CORE_RESEARCH_GOAL_VIEW_PROFILE.sourceEvaluationRevision,
            'view.source.evaluationRevision'
        ),
        logicProfile: literalAt(
            sourceRecord.logicProfile,
            CORE_RESEARCH_GOAL_VIEW_PROFILE.sourceLogicProfile,
            'view.source.logicProfile'
        ),
        graphRevision: revisionAt(
            sourceRecord.graphRevision,
            'view.source.graphRevision'
        )
    });
    const nodeInput = arrayAt(record.nodes, 'view.nodes');
    if (
        nodeInput.length === 0 ||
        nodeInput.length > CORE_RESEARCH_GOAL_VIEW_PROFILE.maxNodes
    ) {
        return fail(
            'INVALID_VIEW',
            'view.nodes',
            'Research-goal view requires a bounded nonempty node set'
        );
    }
    const nodes = nodeInput.map((node, index) => normalizeViewNode(
        node,
        `view.nodes[${index}]`
    ));
    for (let index = 1; index < nodes.length; index += 1) {
        if (compareText(nodes[index - 1].id, nodes[index].id) >= 0) {
            return fail(
                'INVALID_VIEW',
                `view.nodes[${index}].id`,
                'Goal nodes must be unique and canonically ID-sorted'
            );
        }
    }
    const nodeIds = new Set(nodes.map(node => node.id));
    const edgeInput = arrayAt(record.edges, 'view.edges');
    if (edgeInput.length > CORE_RESEARCH_GOAL_VIEW_PROFILE.maxEdges) {
        return fail(
            'INVALID_VIEW',
            'view.edges',
            'Research-goal view exceeds the dependency-edge bound'
        );
    }
    const edges = edgeInput.map((edge, index) => normalizeViewEdge(
        edge,
        `view.edges[${index}]`
    ));
    for (let index = 0; index < edges.length; index += 1) {
        const edge = edges[index];
        if (
            !nodeIds.has(edge.dependentId) ||
            !nodeIds.has(edge.prerequisiteId)
        ) {
            return fail(
                'INVALID_VIEW',
                `view.edges[${index}]`,
                'Dependency edge refers to an unknown view node'
            );
        }
        if (
            index > 0 &&
            compareText(edgeKey(edges[index - 1]), edgeKey(edge)) >= 0
        ) {
            return fail(
                'INVALID_VIEW',
                `view.edges[${index}]`,
                'Dependency edges must be unique and canonically sorted'
            );
        }
    }
    assertAcyclic([...nodeIds], edges);
    assertExplanationIntegrity(nodes, edges);
    const counts = normalizeCounts(record.counts, nodes);
    const normalized: CoreResearchGoalView = {
        revision: CORE_RESEARCH_GOAL_VIEW_PROFILE.artifactRevision,
        profileRevision: CORE_RESEARCH_GOAL_VIEW_PROFILE.revision,
        source,
        nodes: Object.freeze(nodes),
        edges: Object.freeze(edges),
        counts,
        meaning: literalAt(
            record.meaning,
            CORE_RESEARCH_GOAL_VIEW_PROFILE.meaning,
            'view.meaning'
        ),
        edgeDirection: literalAt(
            record.edgeDirection,
            CORE_RESEARCH_GOAL_VIEW_PROFILE.edgeDirection,
            'view.edgeDirection'
        ),
        portableProjectionOnly: literalAt(
            record.portableProjectionOnly,
            true,
            'view.portableProjectionOnly'
        ),
        mutableDoneField: literalAt(
            record.mutableDoneField,
            false,
            'view.mutableDoneField'
        ),
        sourceHashesRecomputed: literalAt(
            record.sourceHashesRecomputed,
            false,
            'view.sourceHashesRecomputed'
        ),
        humanAttributionVerified: literalAt(
            record.humanAttributionVerified,
            false,
            'view.humanAttributionVerified'
        ),
        executesExternalActions: literalAt(
            record.executesExternalActions,
            false,
            'view.executesExternalActions'
        )
    };
    const suppliedText = serializeCoreLfWorkspaceCanonicalJson(
        value,
        'suppliedResearchGoalView'
    );
    const normalizedText = serializeCoreLfWorkspaceCanonicalJson(
        normalized,
        'researchGoalView'
    );
    if (suppliedText !== normalizedText) {
        return fail(
            'NONCANONICAL_VIEW',
            'view',
            'Research-goal view differs from canonical reconstruction'
        );
    }
    return deepFreeze(normalized);
};

const projectEvaluation = (
    evaluation: CoreResearchGoalGraphEvaluation
): CoreResearchGoalView => {
    const resultsById = new Map(evaluation.results.map(result => [
        result.nodeId,
        result
    ] as const));
    const nodes: CoreResearchGoalViewNode[] = evaluation.definition.nodes.map(
        node => {
            const result = resultsById.get(node.id)!;
            const common: CoreResearchGoalViewNodeBase = {
                id: node.id,
                nodeRevision: node.revision,
                title: node.title,
                kind: node.kind,
                status: result.status,
                satisfyingEvidenceIds: result.satisfyingEvidenceIds,
                rejectingEvidenceIds: result.rejectingEvidenceIds,
                insufficientEvidenceIds: result.insufficientEvidenceIds,
                staleEvidenceIds: result.staleEvidenceIds,
                advisoryEvidenceIds: result.advisoryEvidenceIds,
                inapplicableEvidenceIds: result.inapplicableEvidenceIds,
                unsatisfiedRequiredIds: result.unsatisfiedRequiredIds,
                unsatisfiedOneOfGroups: result.unsatisfiedOneOfGroups
            };
            return node.kind === 'theorem-goal'
                ? { ...common, kind: node.kind, proof: node.proof }
                : { ...common, kind: node.kind };
        }
    );
    return normalizeView({
        revision: CORE_RESEARCH_GOAL_VIEW_PROFILE.artifactRevision,
        profileRevision: CORE_RESEARCH_GOAL_VIEW_PROFILE.revision,
        source: {
            goalProfileRevision: evaluation.profileRevision,
            evaluationRevision: evaluation.revision,
            logicProfile: evaluation.logicProfile,
            graphRevision: evaluation.definition.graphRevision
        },
        nodes,
        edges: evaluation.definition.edges,
        counts: {
            nodes: evaluation.counts.nodes,
            open: evaluation.counts.open,
            blocked: evaluation.counts.blocked,
            satisfied: evaluation.counts.satisfied,
            rejected: evaluation.counts.rejected
        },
        meaning: CORE_RESEARCH_GOAL_VIEW_PROFILE.meaning,
        edgeDirection: CORE_RESEARCH_GOAL_VIEW_PROFILE.edgeDirection,
        portableProjectionOnly: true,
        mutableDoneField: false,
        sourceHashesRecomputed: false,
        humanAttributionVerified: false,
        executesExternalActions: false
    });
};

/** Freshly replay an exact evaluation before projecting its minimal view. */
export function createCoreResearchGoalView(
    evaluation: CoreResearchGoalGraphEvaluation
): CoreResearchGoalView {
    try {
        assertPortableData(
            evaluation,
            'evaluation',
            'INVALID_EVALUATION'
        );
        const fresh = evaluateCoreResearchGoalGraph({
            definition: evaluation.definition,
            evidence: evaluation.evidence
        });
        if (
            serializeCoreResearchGoalGraphEvaluation(evaluation) !==
                serializeCoreResearchGoalGraphEvaluation(fresh)
        ) {
            return fail(
                'INVALID_EVALUATION',
                'evaluation',
                'Supplied evaluation differs from fresh policy evaluation'
            );
        }
        return projectEvaluation(fresh);
    } catch (error: unknown) {
        if (error instanceof CoreResearchGoalViewError) throw error;
        return fail(
            'INVALID_EVALUATION',
            'evaluation',
            'Research-goal evaluation could not be freshly replayed',
            error
        );
    }
}

/** Validate unknown portable data and return one deeply frozen canonical view. */
export function validateCoreResearchGoalView(
    value: unknown
): CoreResearchGoalView {
    try {
        return normalizeView(value);
    } catch (error: unknown) {
        if (error instanceof CoreResearchGoalViewError) throw error;
        return fail(
            'INVALID_VIEW',
            'view',
            'Research-goal view validation failed',
            error
        );
    }
}

/** Parse exactly one canonical newline-terminated goal-view JSON record. */
export function parseCoreResearchGoalViewText(
    sourceText: string
): CoreResearchGoalView {
    if (typeof sourceText !== 'string' || sourceText.length === 0) {
        return fail(
            'INVALID_VIEW_TEXT',
            'sourceText',
            'Research-goal view text must be nonempty'
        );
    }
    let value: unknown;
    try {
        value = JSON.parse(sourceText);
    } catch (error: unknown) {
        return fail(
            'INVALID_VIEW_TEXT',
            'sourceText',
            'Research-goal view text is not exactly one JSON value',
            error
        );
    }
    const view = validateCoreResearchGoalView(value);
    if (serializeCoreResearchGoalView(view) !== sourceText) {
        return fail(
            'NONCANONICAL_VIEW_TEXT',
            'sourceText',
            'Research-goal view text must be exact canonical serializer output'
        );
    }
    return view;
}

/** Validate and emit deterministic newline-terminated canonical JSON. */
export function serializeCoreResearchGoalView(
    view: CoreResearchGoalView
): string {
    const canonical = validateCoreResearchGoalView(view);
    return serializeCoreLfWorkspaceCanonicalJson(
        canonical,
        'researchGoalView'
    );
}
