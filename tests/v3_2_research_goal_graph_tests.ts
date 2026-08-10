/** Focused GOAL-GRAPH-14A evidence-typed research planning tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfProofDevelopmentSourceSnapshot,
    CoreLfWorkspaceProofDocumentInput,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfProofDevelopment,
    createCoreLfProofDevelopmentSourceSnapshot,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    createCoreProofArtifactFingerprint,
    kernelFree,
    provenance,
    sourceSpan
} from '../src/v3_2';
import {
    CORE_RESEARCH_GOAL_GRAPH_PROFILE,
    CoreResearchGoalGraphDefinition,
    CoreResearchGoalGraphError,
    CoreResearchGoalNodeInput,
    createCoreResearchGoalEvidence,
    createCoreResearchGoalGraphDefinition,
    createCoreResearchGoalObligation,
    evaluateCoreResearchGoalGraph,
    serializeCoreResearchGoalGraphDefinition,
    serializeCoreResearchGoalGraphEvaluation,
    serializeCoreResearchGoalObligation
} from '../src/v3_2/research_goal_graph';

const moduleId = 'fixture.research_goal_graph';
const authorityPath = 'tests/fixtures/research_goal_graph.ts';
const p = coreLfQualifiedSymbol(moduleId, 'P');
const q = coreLfQualifiedSymbol(moduleId, 'Q');
const pWitness = coreLfQualifiedSymbol(moduleId, 'p');
const qWitness = coreLfQualifiedSymbol(moduleId, 'q');
const pCore = 'research_P';
const qCore = 'research_Q';
const pWitnessCore = 'research_p';
const qWitnessCore = 'research_q';

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;
const global = (
    symbol: { readonly moduleId: string; readonly name: string }
) => ({ tag: 'global' as const, symbol });
const transferSource = (sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});
const proofProvenance = (
    line: number,
    detail: string
) => provenance(
    'surface',
    detail,
    sourceSpan(authorityPath, line, 1, line, 2)
);

const declarationModule = () => {
    const declarations = [
        {
            order: 0,
            symbol: p,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol P : TYPE;')
        },
        {
            order: 1,
            symbol: q,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol Q : TYPE;')
        },
        {
            order: 2,
            symbol: pWitness,
            type: global(p),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol p : P;')
        },
        {
            order: 3,
            symbol: qWitness,
            type: global(q),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol q : Q;')
        }
    ];
    const module = createCoreLfModuleSpec({
        revision: 'research-goal-module-v1',
        moduleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('a'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'research-goal-policy-v1',
        moduleRevision: module.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: 'GOAL-GRAPH-14A standalone ordinary LF fixture'
        }))
    });
    const coreNames = new Map([
        [p.name, pCore],
        [q.name, qCore],
        [pWitness.name, pWitnessCore],
        [qWitness.name, qWitnessCore]
    ]);
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'research-goal-linkage-v1',
        moduleRevision: module.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            symbol: declaration.symbol,
            kind: 'free-declaration' as const,
            coreName: coreNames.get(declaration.symbol.name) as string,
            backendName: declaration.symbol.name
        }))
    });
    return { module, policy, linkage };
};

const fingerprint = (
    declarationId: string,
    version: string,
    digit: string
) => createCoreProofArtifactFingerprint({
    source: {
        id: `proofs/${declarationId}-${version}.ts`,
        sha256: hash(digit)
    },
    profileSha256: hash('d'),
    dependencies: [{ moduleId, interfaceSha256: hash('e') }]
});

const proof = (
    declarationId: string,
    typeCore: string,
    plan: CoreLfWorkspaceProofDocumentInput['plan'],
    line: number,
    version: string,
    digit: string
): CoreLfWorkspaceProofDocumentInput => ({
    moduleId,
    declarationId,
    type: kernelFree(
        typeCore,
        proofProvenance(line, `${declarationId} theorem statement`)
    ),
    plan,
    provenance: proofProvenance(line, `${declarationId} proof source`),
    fingerprint: fingerprint(declarationId, version, digit)
});

const sourceSnapshot = (
    variant: 'ordinary' | 'statement-mismatch' | 'absent'
): CoreLfProofDevelopmentSourceSnapshot => {
    const ordinaryProofs: CoreLfWorkspaceProofDocumentInput[] = [
        proof(
            'proved',
            pCore,
            coreProofPlanExact(kernelFree(
                pWitnessCore,
                proofProvenance(20, 'proved exact witness')
            )),
            20,
            variant,
            '1'
        ),
        proof(
            'incomplete',
            pCore,
            coreProofPlanHole('theorem_gap', {
                provenance: proofProvenance(21, 'incomplete theorem hole'),
                expectation: {
                    contextDepth: 0,
                    target: kernelFree(
                        pCore,
                        proofProvenance(21, 'incomplete expected target')
                    )
                }
            }),
            21,
            variant,
            '2'
        ),
        proof(
            'wrong',
            pCore,
            coreProofPlanExact(kernelFree(
                pCore,
                proofProvenance(22, 'deliberately wrong theorem term')
            )),
            22,
            variant,
            '3'
        )
    ];
    const proofs = variant === 'statement-mismatch'
        ? [
            proof(
                'proved',
                qCore,
                coreProofPlanExact(kernelFree(
                    qWitnessCore,
                    proofProvenance(23, 'mismatched but valid witness')
                )),
                23,
                variant,
                '4'
            ),
            ...ordinaryProofs.slice(1)
        ]
        : variant === 'absent'
            ? ordinaryProofs.slice(1)
            : ordinaryProofs;
    const workspace = createCoreLfDeclarationWorkspace({
        revision: 'research-goal-workspace-v1',
        modules: [declarationModule()]
    });
    return createCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopment({
            revision: `research-goal-development-${variant}`,
            workspace,
            proofs
        })
    );
};

const expectedP = () => kernelFree(
    pCore,
    proofProvenance(40, 'expected research theorem statement')
);

const nodes = (
    approvedTaskTitle = 'Write and review the abstract'
): CoreResearchGoalNodeInput[] => [
    {
        id: 'root',
        revision: 'root-v1',
        title: 'Prepare the research result',
        kind: 'task-goal',
        policy: { kind: 'all-prerequisites' }
    },
    {
        id: 'theorem.proved',
        revision: 'theorem-proved-v1',
        title: 'Prove the central lemma',
        kind: 'theorem-goal',
        proof: { moduleId, declarationId: 'proved' },
        expectedType: expectedP()
    },
    {
        id: 'theorem.incomplete',
        revision: 'theorem-incomplete-v1',
        title: 'Complete the open lemma',
        kind: 'theorem-goal',
        proof: { moduleId, declarationId: 'incomplete' },
        expectedType: expectedP()
    },
    {
        id: 'theorem.wrong',
        revision: 'theorem-wrong-v1',
        title: 'Repair the rejected lemma',
        kind: 'theorem-goal',
        proof: { moduleId, declarationId: 'wrong' },
        expectedType: expectedP()
    },
    {
        id: 'theorem.absent',
        revision: 'theorem-absent-v1',
        title: 'Supply the absent lemma',
        kind: 'theorem-goal',
        proof: { moduleId, declarationId: 'missing' },
        expectedType: expectedP()
    },
    {
        id: 'theorem.mismatch',
        revision: 'theorem-mismatch-v1',
        title: 'Keep the theorem statement fixed',
        kind: 'theorem-goal',
        proof: { moduleId, declarationId: 'proved' },
        expectedType: expectedP()
    },
    {
        id: 'task.approved',
        revision: 'task-approved-v1',
        title: approvedTaskTitle,
        kind: 'task-goal',
        policy: {
            kind: 'all-named-approvers',
            approverIds: ['bob', 'alice']
        }
    },
    {
        id: 'task.ai-only',
        revision: 'task-ai-v1',
        title: 'Select a motivating example',
        kind: 'task-goal',
        policy: {
            kind: 'all-named-approvers',
            approverIds: ['alice']
        }
    },
    {
        id: 'decision.choice',
        revision: 'decision-choice-v1',
        title: 'Choose the publication route',
        kind: 'decision-goal',
        policy: {
            kind: 'all-named-approvers',
            approverIds: ['alice']
        }
    },
    {
        id: 'decision.rejected',
        revision: 'decision-rejected-v1',
        title: 'Approve an unsuitable route',
        kind: 'decision-goal',
        policy: {
            kind: 'all-named-approvers',
            approverIds: ['alice']
        }
    }
];

const edges = [
    {
        kind: 'requires' as const,
        dependentId: 'root',
        prerequisiteId: 'theorem.proved'
    },
    {
        kind: 'requires' as const,
        dependentId: 'root',
        prerequisiteId: 'task.approved'
    },
    {
        kind: 'one-of' as const,
        dependentId: 'root',
        groupId: 'publication-path',
        prerequisiteId: 'task.ai-only'
    },
    {
        kind: 'one-of' as const,
        dependentId: 'root',
        groupId: 'publication-path',
        prerequisiteId: 'decision.choice'
    }
];

const definition = (
    approvedTaskTitle?: string
): CoreResearchGoalGraphDefinition =>
    createCoreResearchGoalGraphDefinition({
        revision: 'research-plan-v1',
        nodes: nodes(approvedTaskTitle),
        edges
    });

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectGoalError = (
    action: () => unknown,
    code: CoreResearchGoalGraphError['code']
): void => assert.throws(
    action,
    error => error instanceof CoreResearchGoalGraphError &&
        error.code === code &&
        error.path.length > 0
);

const humanEvidence = (
    graph: CoreResearchGoalGraphDefinition,
    id: string,
    nodeId: string,
    actorId: string,
    disposition: 'approve' | 'reject' = 'approve'
) => createCoreResearchGoalEvidence(graph, {
    id,
    subjectNodeId: nodeId,
    kind: 'human-approval',
    actorId,
    disposition,
    statement: `${actorId} ${disposition}s this exact obligation`
});

describe('GOAL-GRAPH-14A research planning profile', () => {
    it('constructs exact canonical obligations and rejects graph ambiguity', () => {
        const first = definition();
        const permuted = createCoreResearchGoalGraphDefinition({
            revision: 'research-plan-v1',
            nodes: [...nodes()].reverse(),
            edges: [...edges].reverse()
        });
        const obligation = createCoreResearchGoalObligation(
            first,
            'root'
        );

        assert.equal(
            serializeCoreResearchGoalGraphDefinition(first),
            serializeCoreResearchGoalGraphDefinition(permuted)
        );
        assert.deepEqual(first.nodes.map(node => node.id), [
            'decision.choice',
            'decision.rejected',
            'root',
            'task.ai-only',
            'task.approved',
            'theorem.absent',
            'theorem.incomplete',
            'theorem.mismatch',
            'theorem.proved',
            'theorem.wrong'
        ]);
        assert.equal(obligation.node.id, 'root');
        assert.deepEqual(
            obligation.dependencies.map(item => item.prerequisite.id),
            ['decision.choice', 'task.ai-only', 'task.approved', 'theorem.proved']
        );
        assert.equal(
            serializeCoreResearchGoalObligation(obligation),
            serializeCoreResearchGoalObligation(
                createCoreResearchGoalObligation(permuted, 'root')
            )
        );
        assertDeepFrozen(first);
        assertDeepFrozen(obligation);

        const sharedAlternative = createCoreResearchGoalGraphDefinition({
            revision: 'shared-alternative-v1',
            nodes: nodes(),
            edges: [
                {
                    kind: 'one-of',
                    dependentId: 'root',
                    groupId: 'route',
                    prerequisiteId: 'decision.choice'
                },
                {
                    kind: 'one-of',
                    dependentId: 'root',
                    groupId: 'review',
                    prerequisiteId: 'decision.choice'
                }
            ]
        });
        assert.equal(sharedAlternative.edges.length, 2);

        expectGoalError(
            () => createCoreResearchGoalGraphDefinition({
                revision: 'vacuous-v1',
                nodes: [{
                    id: 'vacuous',
                    revision: 'vacuous-v1',
                    title: 'Vacuous task',
                    kind: 'task-goal',
                    policy: { kind: 'all-prerequisites' }
                }]
            }),
            'VACUOUS_TASK'
        );
        expectGoalError(
            () => createCoreResearchGoalGraphDefinition({
                revision: 'cycle-v1',
                nodes: [
                    {
                        id: 'left',
                        revision: 'left-v1',
                        title: 'Left task',
                        kind: 'task-goal',
                        policy: { kind: 'all-prerequisites' }
                    },
                    {
                        id: 'right',
                        revision: 'right-v1',
                        title: 'Right task',
                        kind: 'task-goal',
                        policy: { kind: 'all-prerequisites' }
                    }
                ],
                edges: [
                    {
                        kind: 'requires',
                        dependentId: 'left',
                        prerequisiteId: 'right'
                    },
                    {
                        kind: 'requires',
                        dependentId: 'right',
                        prerequisiteId: 'left'
                    }
                ]
            }),
            'DEPENDENCY_CYCLE'
        );
        expectGoalError(
            () => createCoreResearchGoalGraphDefinition({
                revision: 'duplicate-edge-v1',
                nodes: nodes(),
                edges: [edges[0], edges[0]]
            }),
            'DUPLICATE_EDGE'
        );
        expectGoalError(
            () => createCoreResearchGoalGraphDefinition({
                revision: 'unknown-edge-v1',
                nodes: nodes(),
                edges: [{
                    kind: 'requires',
                    dependentId: 'root',
                    prerequisiteId: 'unknown'
                }]
            }),
            'UNKNOWN_NODE'
        );
        expectGoalError(
            () => createCoreResearchGoalObligation({
                ...first,
                nodes: [null]
            } as unknown as CoreResearchGoalGraphDefinition, 'root'),
            'INVALID_NODE'
        );
        expectGoalError(
            () => createCoreResearchGoalGraphDefinition({
                revision: 'malformed-expression-v1',
                nodes: [{
                    id: 'malformed.theorem',
                    revision: 'malformed-theorem-v1',
                    title: 'Reject a malformed theorem statement',
                    kind: 'theorem-goal',
                    proof: { moduleId, declarationId: 'proved' },
                    expectedType: {
                        tag: 'unsupported'
                    } as unknown as ReturnType<typeof expectedP>
                }]
            }),
            'INVALID_NODE'
        );
    });

    it('derives blocked then satisfied status without promoting AI advice', () => {
        const graph = definition();
        const source = sourceSnapshot('ordinary');
        const baseEvidence = [
            createCoreResearchGoalEvidence(graph, {
                id: 'proof.central',
                subjectNodeId: 'theorem.proved',
                kind: 'checked-proof',
                source
            }),
            humanEvidence(
                graph,
                'approval.abstract.alice',
                'task.approved',
                'alice'
            ),
            humanEvidence(
                graph,
                'approval.abstract.bob',
                'task.approved',
                'bob'
            ),
            createCoreResearchGoalEvidence(graph, {
                id: 'proposal.example',
                subjectNodeId: 'task.ai-only',
                kind: 'ai-proposal',
                provider: {
                    id: 'fixture-agent',
                    revision: 'fixture-agent-v1'
                },
                proposal: 'Use the smallest illustrative example.'
            }),
            humanEvidence(
                graph,
                'rejection.unsuitable',
                'decision.rejected',
                'alice',
                'reject'
            )
        ];
        const blocked = evaluateCoreResearchGoalGraph({
            definition: graph,
            evidence: [...baseEvidence].reverse()
        });
        const satisfied = evaluateCoreResearchGoalGraph({
            definition: graph,
            evidence: [
                ...baseEvidence,
                humanEvidence(
                    graph,
                    'approval.publication.alice',
                    'decision.choice',
                    'alice'
                )
            ]
        });
        const blockedById = new Map(blocked.results.map(result => [
            result.nodeId,
            result
        ]));
        const satisfiedById = new Map(satisfied.results.map(result => [
            result.nodeId,
            result
        ]));

        assert.equal(blockedById.get('theorem.proved')?.status, 'satisfied');
        assert.equal(blockedById.get('task.approved')?.status, 'satisfied');
        assert.equal(blockedById.get('task.ai-only')?.status, 'open');
        assert.deepEqual(
            blockedById.get('task.ai-only')?.advisoryEvidenceIds,
            ['proposal.example']
        );
        assert.equal(
            blockedById.get('decision.rejected')?.status,
            'rejected'
        );
        assert.equal(blockedById.get('root')?.status, 'blocked');
        assert.deepEqual(
            blockedById.get('root')?.unsatisfiedOneOfGroups,
            [{
                groupId: 'publication-path',
                alternativeIds: ['decision.choice', 'task.ai-only']
            }]
        );
        assert.equal(satisfiedById.get('decision.choice')?.status, 'satisfied');
        assert.equal(satisfiedById.get('root')?.status, 'satisfied');
        assert.deepEqual(blocked.counts, {
            nodes: 10,
            evidence: 5,
            open: 6,
            blocked: 1,
            satisfied: 2,
            rejected: 1,
            staleEvidence: 0,
            advisoryEvidence: 1
        });
        assert.deepEqual(satisfied.counts, {
            nodes: 10,
            evidence: 6,
            open: 5,
            blocked: 0,
            satisfied: 4,
            rejected: 1,
            staleEvidence: 0,
            advisoryEvidence: 1
        });
        assert.equal(blocked.mutableDoneField, false);
        assert.equal(blocked.sourceHashesRecomputed, false);
        assert.equal(blocked.humanAttributionVerified, false);
        assert.equal(blocked.executesExternalActions, false);
        assert.equal(
            serializeCoreResearchGoalGraphEvaluation(blocked),
            serializeCoreResearchGoalGraphEvaluation(
                evaluateCoreResearchGoalGraph({
                    definition: graph,
                    evidence: baseEvidence
                })
            )
        );
        assertDeepFrozen(blocked);
        assertDeepFrozen(satisfied);
    });

    it('keeps incomplete, rejected, absent, and changed proofs insufficient', () => {
        const graph = definition();
        const ordinary = sourceSnapshot('ordinary');
        const evidence = [
            createCoreResearchGoalEvidence(graph, {
                id: 'proof.incomplete',
                subjectNodeId: 'theorem.incomplete',
                kind: 'checked-proof',
                source: ordinary
            }),
            createCoreResearchGoalEvidence(graph, {
                id: 'proof.wrong',
                subjectNodeId: 'theorem.wrong',
                kind: 'checked-proof',
                source: ordinary
            }),
            createCoreResearchGoalEvidence(graph, {
                id: 'proof.absent',
                subjectNodeId: 'theorem.absent',
                kind: 'checked-proof',
                source: sourceSnapshot('absent')
            }),
            createCoreResearchGoalEvidence(graph, {
                id: 'proof.mismatch',
                subjectNodeId: 'theorem.mismatch',
                kind: 'checked-proof',
                source: sourceSnapshot('statement-mismatch')
            })
        ];
        const report = evaluateCoreResearchGoalGraph({
            definition: graph,
            evidence
        });
        const assessments = new Map(report.assessments.map(item => [
            item.evidenceId,
            item
        ]));
        const incomplete = assessments.get('proof.incomplete');
        assert.equal(incomplete?.outcome, 'checked-proof-incomplete');
        assert.deepEqual(incomplete?.openGoals, [{
            moduleId,
            declarationId: 'incomplete',
            goalId: 'theorem_gap'
        }]);
        assert.equal(
            incomplete?.goalGraph?.nodes[0]?.id,
            'theorem_gap'
        );
        const rejected = assessments.get('proof.wrong');
        assert.equal(rejected?.outcome, 'checked-proof-rejected');
        assert.equal(rejected?.diagnostic?.family, 'checker');
        assert.equal(
            rejected?.diagnostic === undefined
                ? true
                : 'message' in rejected.diagnostic,
            false
        );
        assert.equal(
            assessments.get('proof.absent')?.outcome,
            'checked-proof-absent'
        );
        assert.equal(
            assessments.get('proof.mismatch')?.outcome,
            'checked-proof-type-mismatch'
        );
        for (const nodeId of [
            'theorem.incomplete',
            'theorem.wrong',
            'theorem.absent',
            'theorem.mismatch'
        ]) {
            assert.equal(
                report.results.find(result => result.nodeId === nodeId)
                    ?.status,
                'open'
            );
        }
        assert.deepEqual(
            report.results.find(result =>
                result.nodeId === 'theorem.incomplete'
            )?.insufficientEvidenceIds,
            ['proof.incomplete']
        );
        assert.equal(
            serializeCoreResearchGoalGraphEvaluation(report).includes(
                '"message"'
            ),
            false
        );
    });

    it('exposes stale and inapplicable attestations and rejects ambiguity', () => {
        const original = definition();
        const edited = definition('Write, review, and revise the abstract');
        const stale = humanEvidence(
            original,
            'approval.stale',
            'task.approved',
            'alice'
        );
        const unauthorized = humanEvidence(
            edited,
            'approval.unauthorized',
            'task.approved',
            'eve'
        );
        const theoremApproval = humanEvidence(
            edited,
            'approval.theorem',
            'theorem.proved',
            'alice'
        );
        const proofForTask = createCoreResearchGoalEvidence(edited, {
            id: 'proof.for-task',
            subjectNodeId: 'task.ai-only',
            kind: 'checked-proof',
            source: sourceSnapshot('ordinary')
        });
        const report = evaluateCoreResearchGoalGraph({
            definition: edited,
            evidence: [stale, unauthorized, theoremApproval, proofForTask]
        });
        const outcomes = new Map(report.assessments.map(item => [
            item.evidenceId,
            item.outcome
        ]));

        assert.equal(outcomes.get('approval.stale'), 'stale');
        assert.equal(
            outcomes.get('approval.unauthorized'),
            'unauthorized-actor'
        );
        assert.equal(
            outcomes.get('approval.theorem'),
            'inapplicable-policy'
        );
        assert.equal(outcomes.get('proof.for-task'), 'inapplicable-policy');
        assert.equal(
            report.results.find(result => result.nodeId === 'task.approved')
                ?.status,
            'open'
        );
        assert.equal(report.counts.staleEvidence, 1);

        const first = humanEvidence(
            edited,
            'approval.duplicate.1',
            'task.approved',
            'alice'
        );
        const second = humanEvidence(
            edited,
            'approval.duplicate.2',
            'task.approved',
            'alice',
            'reject'
        );
        expectGoalError(
            () => evaluateCoreResearchGoalGraph({
                definition: edited,
                evidence: [first, second]
            }),
            'AMBIGUOUS_APPROVAL'
        );
        expectGoalError(
            () => createCoreResearchGoalEvidence(edited, {
                id: 'approval.empty-statement',
                subjectNodeId: 'task.approved',
                kind: 'human-approval',
                actorId: 'alice',
                disposition: 'approve',
                statement: ''
            }),
            'INVALID_EVIDENCE'
        );
    });

    it('states the narrow non-authority boundary exactly', () => {
        assert.deepEqual({
            logicProfile: CORE_RESEARCH_GOAL_GRAPH_PROFILE.logicProfile,
            sourceHashesRecomputed:
                CORE_RESEARCH_GOAL_GRAPH_PROFILE.sourceHashesRecomputed,
            verifiesHumanIdentity:
                CORE_RESEARCH_GOAL_GRAPH_PROFILE.verifiesHumanIdentity,
            executesExternalActions:
                CORE_RESEARCH_GOAL_GRAPH_PROFILE.executesExternalActions,
            performsIo: CORE_RESEARCH_GOAL_GRAPH_PROFILE.performsIo,
            invokesAgent: CORE_RESEARCH_GOAL_GRAPH_PROFILE.invokesAgent,
            invokesLambdapi:
                CORE_RESEARCH_GOAL_GRAPH_PROFILE.invokesLambdapi
        }, {
            logicProfile: 'emdash-research-planning-v1',
            sourceHashesRecomputed: false,
            verifiesHumanIdentity: false,
            executesExternalActions: false,
            performsIo: false,
            invokesAgent: false,
            invokesLambdapi: false
        });
    });
});
