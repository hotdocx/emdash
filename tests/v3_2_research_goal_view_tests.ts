/** Focused GOAL-GRAPH-14B1 canonical research-goal view tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_RESEARCH_GOAL_VIEW_PROFILE,
    CoreResearchGoalGraphEvaluation,
    CoreResearchGoalView,
    CoreResearchGoalViewError,
    createCoreResearchGoalEvidence,
    createCoreResearchGoalGraphDefinition,
    createCoreResearchGoalView,
    evaluateCoreResearchGoalGraph,
    kernelUniverse,
    parseCoreResearchGoalViewText,
    provenance,
    serializeCoreResearchGoalGraphEvaluation,
    serializeCoreResearchGoalView,
    sourceSpan,
    validateCoreResearchGoalView
} from '../src/v3_2';

const at = provenance(
    'surface',
    'GOAL-GRAPH-14B1 private theorem statement provenance',
    sourceSpan(
        'tests/private/research_goal_view.fixture.ts',
        1,
        1,
        1,
        2
    )
);

const definition = () => createCoreResearchGoalGraphDefinition({
    revision: 'goal-view-fixture-v1',
    nodes: [
        {
            id: 'task.blocked',
            revision: 'task-blocked-v1',
            title: 'Wait for one acceptable route',
            kind: 'task-goal',
            policy: { kind: 'all-prerequisites' }
        },
        {
            id: 'decision.rejected',
            revision: 'decision-rejected-v1',
            title: 'Reject the unsuitable route',
            kind: 'decision-goal',
            policy: {
                kind: 'all-named-approvers',
                approverIds: ['reviewer.private']
            }
        },
        {
            id: 'theorem.open',
            revision: 'theorem-open-v1',
            title: 'Complete the central theorem',
            kind: 'theorem-goal',
            proof: {
                moduleId: 'fixture.private',
                declarationId: 'central'
            },
            expectedType: kernelUniverse(at)
        },
        {
            id: 'task.complete',
            revision: 'task-complete-v1',
            title: 'Record the accepted decision',
            kind: 'task-goal',
            policy: { kind: 'all-prerequisites' }
        },
        {
            id: 'task.advised',
            revision: 'task-advised-v1',
            title: 'Review the advisory proposal',
            kind: 'task-goal',
            policy: {
                kind: 'all-named-approvers',
                approverIds: ['reviewer.private']
            }
        },
        {
            id: 'decision.accepted',
            revision: 'decision-accepted-v1',
            title: 'Accept the suitable route',
            kind: 'decision-goal',
            policy: {
                kind: 'all-named-approvers',
                approverIds: ['reviewer.private']
            }
        }
    ],
    edges: [
        {
            kind: 'one-of',
            dependentId: 'task.blocked',
            groupId: 'available-route',
            prerequisiteId: 'task.advised'
        },
        {
            kind: 'requires',
            dependentId: 'task.complete',
            prerequisiteId: 'decision.accepted'
        },
        {
            kind: 'one-of',
            dependentId: 'task.blocked',
            groupId: 'available-route',
            prerequisiteId: 'theorem.open'
        }
    ]
});

const evaluation = (): CoreResearchGoalGraphEvaluation => {
    const graph = definition();
    return evaluateCoreResearchGoalGraph({
        definition: graph,
        evidence: [
            createCoreResearchGoalEvidence(graph, {
                id: 'evidence.reject',
                subjectNodeId: 'decision.rejected',
                kind: 'human-approval',
                actorId: 'reviewer.private',
                disposition: 'reject',
                statement: 'PRIVATE rejection explanation'
            }),
            createCoreResearchGoalEvidence(graph, {
                id: 'evidence.advice',
                subjectNodeId: 'task.advised',
                kind: 'ai-proposal',
                provider: {
                    id: 'provider.private',
                    revision: 'provider-private-v1'
                },
                proposal: 'PRIVATE advisory proposal body'
            }),
            createCoreResearchGoalEvidence(graph, {
                id: 'evidence.accept',
                subjectNodeId: 'decision.accepted',
                kind: 'human-approval',
                actorId: 'reviewer.private',
                disposition: 'approve',
                statement: 'PRIVATE approval explanation'
            })
        ]
    });
};

const deepClone = (view: CoreResearchGoalView): Record<string, unknown> =>
    JSON.parse(serializeCoreResearchGoalView(view)) as Record<string, unknown>;

const nodeRecords = (
    view: Record<string, unknown>
): Record<string, unknown>[] =>
    view.nodes as Record<string, unknown>[];

const edgeRecords = (
    view: Record<string, unknown>
): Record<string, unknown>[] =>
    view.edges as Record<string, unknown>[];

const expectViewError = (
    action: () => unknown,
    code: CoreResearchGoalViewError['code']
): void => assert.throws(
    action,
    error => error instanceof CoreResearchGoalViewError &&
        error.code === code &&
        error.path.length > 0
);

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('GOAL-GRAPH-14B1 canonical research-goal view', () => {
    it('projects all statuses and edge shapes without private payloads', () => {
        const view = createCoreResearchGoalView(evaluation());
        const byId = new Map(view.nodes.map(node => [node.id, node] as const));

        assert.equal(
            CORE_RESEARCH_GOAL_VIEW_PROFILE.revision,
            'emdash-research-goal-view-v1'
        );
        assert.deepEqual(view.nodes.map(node => node.id), [
            'decision.accepted',
            'decision.rejected',
            'task.advised',
            'task.blocked',
            'task.complete',
            'theorem.open'
        ]);
        assert.deepEqual(view.counts, {
            nodes: 6,
            open: 2,
            blocked: 1,
            satisfied: 2,
            rejected: 1
        });
        assert.equal(byId.get('decision.accepted')?.status, 'satisfied');
        assert.equal(byId.get('decision.rejected')?.status, 'rejected');
        assert.equal(byId.get('task.advised')?.status, 'open');
        assert.equal(byId.get('task.blocked')?.status, 'blocked');
        assert.equal(byId.get('task.complete')?.status, 'satisfied');
        assert.equal(byId.get('theorem.open')?.status, 'open');
        assert.deepEqual(
            byId.get('task.blocked')?.unsatisfiedOneOfGroups,
            [{
                groupId: 'available-route',
                alternativeIds: ['task.advised', 'theorem.open']
            }]
        );
        assert.deepEqual(
            byId.get('task.advised')?.advisoryEvidenceIds,
            ['evidence.advice']
        );
        assert.deepEqual(view.edges.map(edge => edge.kind), [
            'one-of',
            'one-of',
            'requires'
        ]);
        const theorem = byId.get('theorem.open');
        assert.equal(theorem?.kind, 'theorem-goal');
        if (theorem?.kind !== 'theorem-goal') assert.fail('missing theorem');
        assert.deepEqual(theorem.proof, {
            moduleId: 'fixture.private',
            declarationId: 'central'
        });
        assert.equal(view.portableProjectionOnly, true);
        assert.equal(view.mutableDoneField, false);
        assert.equal(view.sourceHashesRecomputed, false);
        assert.equal(view.humanAttributionVerified, false);
        assert.equal(view.executesExternalActions, false);

        const text = serializeCoreResearchGoalView(view);
        assert.equal(text.endsWith('\n'), true);
        assert.deepEqual(parseCoreResearchGoalViewText(text), view);
        assert.equal(serializeCoreResearchGoalView(
            validateCoreResearchGoalView(JSON.parse(text))
        ), text);
        for (const omitted of [
            'reviewer.private',
            'provider.private',
            'PRIVATE approval explanation',
            'PRIVATE rejection explanation',
            'PRIVATE advisory proposal body',
            'tests/private/research_goal_view.fixture.ts',
            'expectedType',
            'approverIds',
            'actorId',
            '"proposal":'
        ]) assert.equal(text.includes(omitted), false, omitted);
        assertDeepFrozen(view);
    });

    it('requires a fresh exact evaluator result before projection', () => {
        const canonical = evaluation();
        const tampered = JSON.parse(
            serializeCoreResearchGoalGraphEvaluation(canonical)
        ) as {
            results: Record<string, unknown>[];
        };
        tampered.results[0].status = 'open';
        expectViewError(
            () => createCoreResearchGoalView(
                tampered as unknown as CoreResearchGoalGraphEvaluation
            ),
            'INVALID_EVALUATION'
        );

        const withCallback = {
            ...canonical,
            callback: (): void => undefined
        };
        expectViewError(
            () => createCoreResearchGoalView(withCallback),
            'INVALID_EVALUATION'
        );
    });

    it('rejects graph, explanation, count, flag, and revision drift', () => {
        const view = createCoreResearchGoalView(evaluation());

        const reversed = deepClone(view);
        nodeRecords(reversed).reverse();
        expectViewError(
            () => validateCoreResearchGoalView(reversed),
            'INVALID_VIEW'
        );

        const duplicateEdge = deepClone(view);
        edgeRecords(duplicateEdge).splice(1, 0, edgeRecords(duplicateEdge)[0]);
        expectViewError(
            () => validateCoreResearchGoalView(duplicateEdge),
            'INVALID_VIEW'
        );

        const unknownEdge = deepClone(view);
        edgeRecords(unknownEdge)[0].prerequisiteId = 'unknown.goal';
        expectViewError(
            () => validateCoreResearchGoalView(unknownEdge),
            'INVALID_VIEW'
        );

        const cyclic = deepClone(view);
        edgeRecords(cyclic).push({
            kind: 'requires',
            dependentId: 'theorem.open',
            prerequisiteId: 'task.blocked'
        });
        edgeRecords(cyclic).sort((left, right) => {
            const key = (edge: Record<string, unknown>): string =>
                `${String(edge.dependentId)}\u0000${String(edge.kind)}` +
                `\u0000${String(edge.groupId ?? '')}` +
                `\u0000${String(edge.prerequisiteId)}`;
            return key(left).localeCompare(key(right));
        });
        expectViewError(
            () => validateCoreResearchGoalView(cyclic),
            'INVALID_VIEW'
        );

        const badExplanation = deepClone(view);
        const advised = nodeRecords(badExplanation).find(
            node => node.id === 'task.advised'
        );
        assert.ok(advised);
        advised.advisoryEvidenceIds = ['not an id'];
        expectViewError(
            () => validateCoreResearchGoalView(badExplanation),
            'INVALID_VIEW'
        );

        const wrongDependency = deepClone(view);
        const blocked = nodeRecords(wrongDependency).find(
            node => node.id === 'task.blocked'
        );
        assert.ok(blocked);
        blocked.unsatisfiedOneOfGroups = [];
        expectViewError(
            () => validateCoreResearchGoalView(wrongDependency),
            'INVALID_VIEW'
        );

        const wrongCount = deepClone(view);
        (wrongCount.counts as Record<string, unknown>).open = 99;
        expectViewError(
            () => validateCoreResearchGoalView(wrongCount),
            'INVALID_VIEW'
        );

        const wrongFlag = deepClone(view);
        wrongFlag.humanAttributionVerified = true;
        expectViewError(
            () => validateCoreResearchGoalView(wrongFlag),
            'INVALID_VIEW'
        );

        const wrongRevision = deepClone(view);
        wrongRevision.profileRevision = 'future-view-v2';
        expectViewError(
            () => validateCoreResearchGoalView(wrongRevision),
            'INVALID_VIEW'
        );
    });

    it('rejects noncanonical text and nonportable direct values', () => {
        const view = createCoreResearchGoalView(evaluation());
        const text = serializeCoreResearchGoalView(view);
        expectViewError(
            () => parseCoreResearchGoalViewText(`${text} `),
            'NONCANONICAL_VIEW_TEXT'
        );
        expectViewError(
            () => parseCoreResearchGoalViewText(`${text}{}`),
            'INVALID_VIEW_TEXT'
        );
        expectViewError(
            () => parseCoreResearchGoalViewText('{'),
            'INVALID_VIEW_TEXT'
        );

        const callback = deepClone(view);
        callback.callback = (): void => undefined;
        expectViewError(
            () => validateCoreResearchGoalView(callback),
            'INVALID_VIEW'
        );

        class HostView {}
        expectViewError(
            () => validateCoreResearchGoalView(new HostView()),
            'INVALID_VIEW'
        );

        const accessor = deepClone(view);
        Object.defineProperty(accessor, 'callback', {
            enumerable: true,
            get: () => 'hidden'
        });
        expectViewError(
            () => validateCoreResearchGoalView(accessor),
            'INVALID_VIEW'
        );

        const cyclic = deepClone(view);
        cyclic.callback = cyclic;
        expectViewError(
            () => validateCoreResearchGoalView(cyclic),
            'INVALID_VIEW'
        );
    });
});
