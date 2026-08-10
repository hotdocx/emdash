/** Focused AGENT-EVAL-12A immutable proof-attempt benchmark tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfProofDevelopmentSourceSnapshot,
    CoreLfWorkspaceProofDocumentInput,
    compileCoreLfDeclarationWorkspace,
    compileCoreLfWorkspaceProofDocument,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanApply,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfProofDevelopment,
    createCoreLfProofDevelopmentSourceSnapshot,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    createCoreProofArtifactFingerprint,
    createCoreProofPlanHoleReplacement,
    kernelFree,
    provenance,
    proposeCoreLfProofRepairs,
    reconstructCoreLfProofDevelopmentSourceSnapshot,
    sourceSpan
} from '../src/v3_2';
import {
    CoreLfProofReplayDiagnostic,
    projectCoreLfProofReplayDiagnostic
} from '../src/v3_2/lf_proof_maintenance';
import {
    CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE,
    CoreLfProofAgentBenchmarkAttempt,
    CoreLfProofAgentBenchmarkCase,
    CoreLfProofAgentBenchmarkError,
    CoreLfProofAgentBenchmarkRun,
    createCoreLfProofAgentBenchmarkAttempt,
    createCoreLfProofAgentBenchmarkCase,
    createCoreLfProofAgentBenchmarkRun,
    createCoreLfProofAgentBenchmarkSuite,
    evaluateCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkCase,
    serializeCoreLfProofAgentBenchmarkReport,
    serializeCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkSuite
} from '../src/v3_2/lf_proof_agent_benchmark';

const moduleId = 'fixture.proof_agent_benchmark';
const authorityPath = 'tests/fixtures/proof_agent_benchmark.ts';
const proposition = coreLfQualifiedSymbol(moduleId, 'P');
const firstWitness = coreLfQualifiedSymbol(moduleId, 'p');
const secondWitness = coreLfQualifiedSymbol(moduleId, 'q');
const endomap = coreLfQualifiedSymbol(moduleId, 'f');
const inaccessible = coreLfQualifiedSymbol('fixture.not_imported', 'hidden');

const propositionCore = 'benchmark_P';
const firstWitnessCore = 'benchmark_p';
const secondWitnessCore = 'benchmark_q';
const endomapCore = 'benchmark_f';
const transferMode = {
    plicity: 'explicit' as const,
    variation: 'functorial' as const
};

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

const moduleFixture = () => {
    const declarations = [
        {
            order: 0,
            symbol: proposition,
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
            symbol: firstWitness,
            type: global(proposition),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol p : P;')
        },
        {
            order: 2,
            symbol: secondWitness,
            type: global(proposition),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol q : P;')
        },
        {
            order: 3,
            symbol: endomap,
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'argument',
                    mode: transferMode,
                    type: global(proposition)
                },
                body: global(proposition)
            },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource('symbol f (argument : P) : P;')
        }
    ];
    const module = createCoreLfModuleSpec({
        revision: 'proof-agent-benchmark-module-v1',
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
        revision: 'proof-agent-benchmark-policy-v1',
        moduleRevision: module.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: 'AGENT-EVAL-12A standalone ordinary LF fixture'
        }))
    });
    const coreNames = new Map([
        [proposition.name, propositionCore],
        [firstWitness.name, firstWitnessCore],
        [secondWitness.name, secondWitnessCore],
        [endomap.name, endomapCore]
    ]);
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'proof-agent-benchmark-linkage-v1',
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

const proofIds = [
    'baseline_exact',
    'external_exact',
    'incomplete_apply',
    'wrong_term',
    'abstention'
] as const;

type ProofId = typeof proofIds[number];

const goalId = (proofId: ProofId): string => `${proofId}_goal`;

const proofFingerprint = (
    proofId: ProofId,
    version: 'previous' | 'current'
) => createCoreProofArtifactFingerprint({
    source: {
        id: `proofs/${proofId}-${version}.ts`,
        sha256: hash(version === 'previous' ? 'b' : 'c')
    },
    profileSha256: hash('d'),
    dependencies: [{ moduleId, interfaceSha256: hash('e') }]
});

const proofDocument = (
    proofId: ProofId,
    version: 'previous' | 'current',
    line: number
): CoreLfWorkspaceProofDocumentInput => {
    const target = kernelFree(
        propositionCore,
        proofProvenance(line, `${proofId} target`)
    );
    return {
        moduleId,
        declarationId: proofId,
        type: target,
        plan: version === 'previous'
            ? coreProofPlanExact(kernelFree(
                firstWitnessCore,
                proofProvenance(line, `${proofId} previous witness`)
            ))
            : coreProofPlanHole(goalId(proofId), {
                provenance: proofProvenance(line, `${proofId} source hole`),
                expectation: { contextDepth: 0, target }
            }),
        provenance: proofProvenance(line, `${proofId} proof source`),
        fingerprint: proofFingerprint(proofId, version)
    };
};

const sourceSnapshot = (
    version: 'previous' | 'current'
): CoreLfProofDevelopmentSourceSnapshot => {
    const workspace = createCoreLfDeclarationWorkspace({
        revision: 'proof-agent-benchmark-workspace-v1',
        modules: [moduleFixture()]
    });
    return createCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopment({
            revision: `proof-agent-benchmark-development-${version}`,
            workspace,
            proofs: proofIds.map((proofId, index) =>
                proofDocument(proofId, version, 20 + index)
            )
        })
    );
};

interface BenchmarkFixture {
    readonly previous: CoreLfProofDevelopmentSourceSnapshot;
    readonly current: CoreLfProofDevelopmentSourceSnapshot;
    readonly cases: Readonly<Record<ProofId, CoreLfProofAgentBenchmarkCase>>;
}

let cachedFixture: BenchmarkFixture | undefined;

const fixture = (): BenchmarkFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const previous = sourceSnapshot('previous');
    const current = sourceSnapshot('current');
    const relevant = {
        baseline_exact: [firstWitness],
        external_exact: [secondWitness],
        incomplete_apply: [endomap, firstWitness],
        wrong_term: [firstWitness],
        abstention: [firstWitness]
    } satisfies Record<ProofId, readonly typeof firstWitness[]>;
    const cases = Object.fromEntries(proofIds.map(proofId => [
        proofId,
        createCoreLfProofAgentBenchmarkCase({
            id: `case.${proofId}`,
            previousSource: previous,
            currentSource: current,
            proof: { moduleId, declarationId: proofId },
            goalId: goalId(proofId),
            relevantPremises: relevant[proofId]
        })
    ])) as unknown as Readonly<Record<ProofId, CoreLfProofAgentBenchmarkCase>>;
    cachedFixture = { previous, current, cases };
    return cachedFixture;
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectBenchmarkError = (
    action: () => unknown,
    code: CoreLfProofAgentBenchmarkError['code']
): void => assert.throws(
    action,
    error => error instanceof CoreLfProofAgentBenchmarkError &&
        error.code === code &&
        error.path.length > 0
);

const patchAttempt = (
    benchmarkCase: CoreLfProofAgentBenchmarkCase,
    replacement: Parameters<typeof createCoreProofPlanHoleReplacement>[1],
    retrievedPremises: readonly typeof firstWitness[] = [],
    reportedUsage?: {
        readonly wallTimeMs?: number;
        readonly inputTokens?: number;
        readonly outputTokens?: number;
        readonly checkerCalls?: number;
    }
): CoreLfProofAgentBenchmarkAttempt =>
    createCoreLfProofAgentBenchmarkAttempt({
        benchmarkCase,
        retrievedPremises,
        ...(reportedUsage === undefined ? {} : { reportedUsage }),
        decision: {
            kind: 'patch',
            patch: createCoreProofPlanHoleReplacement(
                benchmarkCase.goalId,
                replacement
            )
        }
    });

const runFor = (
    attempts: readonly CoreLfProofAgentBenchmarkAttempt[]
): CoreLfProofAgentBenchmarkRun => createCoreLfProofAgentBenchmarkRun({
    revision: 'proof-agent-benchmark-run-v1',
    provider: {
        id: 'fixture-provider',
        revision: 'fixture-provider-v1'
    },
    allowedProfiles: ['external-plan-v1', 'obvious-proof-v1'],
    seed: 'fixture-seed-1',
    limits: {
        wallTimeMs: 10,
        inputTokens: 100,
        outputTokens: 100,
        checkerCalls: 5
    },
    attempts
});

describe('AGENT-EVAL-12A immutable proof-agent benchmark', () => {
    it('constructs canonical self-contained cases and suite ordering', () => {
        const { cases } = fixture();
        const suite = createCoreLfProofAgentBenchmarkSuite({
            revision: 'proof-agent-suite-v1',
            cases: [...proofIds].reverse().map(proofId => cases[proofId])
        });
        const ordered = createCoreLfProofAgentBenchmarkSuite({
            revision: 'proof-agent-suite-v1',
            cases: proofIds.map(proofId => cases[proofId])
        });

        assert.deepEqual(
            suite.cases.map(benchmarkCase => benchmarkCase.id),
            [...suite.cases.map(benchmarkCase => benchmarkCase.id)].sort()
        );
        assert.equal(
            serializeCoreLfProofAgentBenchmarkSuite(suite),
            serializeCoreLfProofAgentBenchmarkSuite(ordered)
        );
        const reconstructed = createCoreLfProofAgentBenchmarkCase({
            id: cases.baseline_exact.id,
            previousSource: cases.baseline_exact.previousSource,
            currentSource: cases.baseline_exact.currentSource,
            proof: cases.baseline_exact.proof,
            goalId: cases.baseline_exact.goalId,
            diffOptions: {
                expressionVisitLimit:
                    cases.baseline_exact.settings.expressionVisitLimit
            },
            premiseIndexOptions:
                cases.baseline_exact.settings.premiseIndex,
            relevantPremises: cases.baseline_exact.relevantPremises
        });
        assert.equal(
            serializeCoreLfProofAgentBenchmarkCase(cases.baseline_exact),
            serializeCoreLfProofAgentBenchmarkCase(reconstructed)
        );
        assert.equal(cases.baseline_exact.initial.state.status, 'incomplete');
        assert.equal(cases.baseline_exact.suppliedHashesRecomputed, false);
        assert.equal(
            cases.baseline_exact.relevantPremiseAuthority,
            'curator-label-accessibility-only'
        );
        assertDeepFrozen(suite);
    });

    it('scores provider, external, partial, rejected, and abstained attempts', () => {
        const { previous, current, cases } = fixture();
        const baselineProposal = proposeCoreLfProofRepairs({
            previousSource: previous,
            currentSource: current,
            proof: { moduleId, declarationId: 'baseline_exact' },
            goalId: cases.baseline_exact.goalId
        });
        const baselineCandidate = baselineProposal.provider.candidates.find(
            candidate => candidate.operation === 'exact' &&
                candidate.premise.symbol.name === firstWitness.name
        );
        assert.notEqual(baselineCandidate, undefined);
        const baseline = createCoreLfProofAgentBenchmarkAttempt({
            benchmarkCase: cases.baseline_exact,
            retrievedPremises: [endomap, firstWitness],
            reportedUsage: {
                wallTimeMs: 3,
                inputTokens: 10,
                outputTokens: 5,
                checkerCalls: 1
            },
            decision: {
                kind: 'patch',
                patch: baselineCandidate!.patch
            }
        });
        const external = patchAttempt(
            cases.external_exact,
            coreProofPlanExact(kernelFree(
                secondWitnessCore,
                proofProvenance(60, 'external exact witness')
            )),
            [firstWitness, secondWitness],
            {
                wallTimeMs: 4,
                inputTokens: 12,
                outputTokens: 6,
                checkerCalls: 1
            }
        );
        const incomplete = patchAttempt(
            cases.incomplete_apply,
            coreProofPlanApply(
                kernelFree(
                    endomapCore,
                    proofProvenance(61, 'external application callee')
                ),
                [coreProofPlanHole('incomplete_apply_premise', {
                    provenance: proofProvenance(61, 'application premise'),
                    expectation: {
                        contextDepth: 0,
                        target: kernelFree(
                            propositionCore,
                            proofProvenance(61, 'application premise target')
                        )
                    }
                })]
            ),
            [endomap, firstWitness],
            {
                wallTimeMs: 20,
                inputTokens: 14,
                outputTokens: 7,
                checkerCalls: 2
            }
        );
        const wrongReplacement = coreProofPlanExact(kernelFree(
            propositionCore,
            proofProvenance(62, 'deliberately wrong exact term')
        ));
        const wrong = patchAttempt(
            cases.wrong_term,
            wrongReplacement,
            [firstWitness],
            { inputTokens: 8, outputTokens: 4, checkerCalls: 1 }
        );
        const abstention = createCoreLfProofAgentBenchmarkAttempt({
            benchmarkCase: cases.abstention,
            decision: { kind: 'abstain' }
        });
        const suite = createCoreLfProofAgentBenchmarkSuite({
            revision: 'proof-agent-suite-v1',
            cases: proofIds.map(proofId => cases[proofId])
        });
        const run = runFor([
            wrong,
            baseline,
            abstention,
            incomplete,
            external
        ]);
        const report = evaluateCoreLfProofAgentBenchmarkRun({ suite, run });
        const repeated = evaluateCoreLfProofAgentBenchmarkRun({ suite, run });
        const byId = new Map(report.results.map(result => [
            result.caseId,
            result
        ]));

        assert.equal(
            byId.get('case.baseline_exact')?.outcome,
            'accepted-complete'
        );
        assert.equal(
            byId.get('case.external_exact')?.outcome,
            'accepted-complete'
        );
        assert.equal(
            byId.get('case.incomplete_apply')?.outcome,
            'accepted-incomplete'
        );
        const incompleteResult = byId.get('case.incomplete_apply');
        if (incompleteResult?.outcome === 'accepted-incomplete') {
            assert.deepEqual(
                incompleteResult.state.goals.map(goal => goal.id),
                ['incomplete_apply_premise']
            );
        }
        const rejected = byId.get('case.wrong_term');
        assert.equal(rejected?.outcome, 'rejected');
        if (rejected?.outcome === 'rejected') {
            assert.equal(rejected.diagnostic.family, 'checker');
            assert.equal('message' in rejected.diagnostic, false);
            const reconstructedCurrent =
                reconstructCoreLfProofDevelopmentSourceSnapshot(current);
            const workspace = compileCoreLfDeclarationWorkspace(
                reconstructedCurrent.plan.workspace
            );
            const proof = reconstructedCurrent.plan.proofs.find(candidate =>
                candidate.declarationId === 'wrong_term'
            );
            assert.notEqual(proof, undefined);
            let ownerDiagnostic: CoreLfProofReplayDiagnostic | undefined;
            try {
                compileCoreLfWorkspaceProofDocument(workspace, {
                    ...proof!,
                    plan: wrongReplacement
                });
            } catch (error: unknown) {
                ownerDiagnostic = projectCoreLfProofReplayDiagnostic(error);
            }
            assert.deepEqual(rejected.diagnostic, ownerDiagnostic);
        }
        assert.equal(byId.get('case.abstention')?.outcome, 'abstained');
        assert.deepEqual(report.metrics, {
            cases: 5,
            outcomes: {
                abstained: 1,
                acceptedComplete: 2,
                acceptedIncomplete: 1,
                rejected: 1
            },
            replays: {
                baselineProofReplays: 5,
                candidateProofReplays: 4
            },
            planNodes: {
                initialTotal: 5,
                replacementReportedCases: 4,
                replacementTotal: 5,
                resultReportedCases: 4,
                resultTotal: 5
            },
            retrieval: {
                relevantPremises: 6,
                retrievedPremises: 7,
                relevantRetrievedPremises: 5,
                irrelevantRetrievedPremises: 2,
                casesWithRelevantPremises: 5,
                casesWithRelevantRetrievedPremises: 4,
                firstRelevantRankTotal: 6
            },
            reportedUsage: {
                authority: 'provider-reported-unverified',
                wallTimeMs: { reportedCases: 3, total: 27 },
                inputTokens: { reportedCases: 4, total: 44 },
                outputTokens: { reportedCases: 4, total: 22 },
                checkerCalls: { reportedCases: 4, total: 5 },
                withinLimits: 3,
                exceededLimits: 1,
                unreported: 1
            }
        });
        assert.equal(report.artifactCurrent, false);
        assert.equal(report.materializesUpdatedSource, false);
        assert.equal(report.ratiosDerived, false);
        assert.equal(
            serializeCoreLfProofAgentBenchmarkReport(report),
            serializeCoreLfProofAgentBenchmarkReport(repeated)
        );
        assert.equal(
            serializeCoreLfProofAgentBenchmarkRun(run),
            serializeCoreLfProofAgentBenchmarkRun(runFor([
                baseline,
                external,
                incomplete,
                wrong,
                abstention
            ]))
        );
        assertDeepFrozen(report);
    });

    it('scores scope, goal, and patch failures with stable diagnostics', () => {
        const { cases } = fixture();
        const scenarios = [
            {
                attempt: patchAttempt(
                    cases.baseline_exact,
                    coreProofPlanExact(kernelFree(
                        firstWitnessCore,
                        proofProvenance(70, 'inaccessible retrieval proof')
                    )),
                    [inaccessible]
                ),
                family: 'benchmark',
                code: 'INACCESSIBLE_RETRIEVAL'
            },
            {
                attempt: createCoreLfProofAgentBenchmarkAttempt({
                    benchmarkCase: cases.baseline_exact,
                    decision: {
                        kind: 'patch',
                        patch: createCoreProofPlanHoleReplacement(
                            'different_goal',
                            coreProofPlanExact(kernelFree(
                                firstWitnessCore,
                                proofProvenance(71, 'wrong goal proof')
                            ))
                        )
                    }
                }),
                family: 'benchmark',
                code: 'PATCH_GOAL_MISMATCH'
            },
            {
                attempt: createCoreLfProofAgentBenchmarkAttempt({
                    benchmarkCase: cases.baseline_exact,
                    decision: {
                        kind: 'patch',
                        patch: {
                            ...createCoreProofPlanHoleReplacement(
                                cases.baseline_exact.goalId,
                                coreProofPlanExact(kernelFree(
                                    firstWitnessCore,
                                    proofProvenance(72, 'invalid patch proof')
                                ))
                            ),
                            revision: 'unsupported-patch-v9'
                        } as never
                    }
                }),
                family: 'proof-plan-patch',
                code: 'INVALID_PATCH'
            }
        ];

        for (const scenario of scenarios) {
            const suite = createCoreLfProofAgentBenchmarkSuite({
                revision: 'rejection-suite-v1',
                cases: [cases.baseline_exact]
            });
            const report = evaluateCoreLfProofAgentBenchmarkRun({
                suite,
                run: runFor([scenario.attempt])
            });
            const result = report.results[0];
            assert.equal(result.outcome, 'rejected');
            if (result.outcome === 'rejected') {
                assert.equal(result.diagnostic.family, scenario.family);
                assert.equal(result.diagnostic.code, scenario.code);
                assert.equal('message' in result.diagnostic, false);
            }
        }
    });

    it('rejects stale, incomplete, duplicate, and malformed orchestration', () => {
        const { cases } = fixture();
        const baseline = createCoreLfProofAgentBenchmarkAttempt({
            benchmarkCase: cases.baseline_exact,
            decision: { kind: 'abstain' }
        });
        const abstention = createCoreLfProofAgentBenchmarkAttempt({
            benchmarkCase: cases.abstention,
            decision: { kind: 'abstain' }
        });
        const baselineSuite = createCoreLfProofAgentBenchmarkSuite({
            revision: 'orchestration-suite-v1',
            cases: [cases.baseline_exact]
        });
        const staleAttempt = {
            ...baseline,
            caseText: `${baseline.caseText}\n`
        } as CoreLfProofAgentBenchmarkAttempt;

        expectBenchmarkError(
            () => evaluateCoreLfProofAgentBenchmarkRun({
                suite: baselineSuite,
                run: runFor([staleAttempt])
            }),
            'STALE_ATTEMPT'
        );
        expectBenchmarkError(
            () => evaluateCoreLfProofAgentBenchmarkRun({
                suite: baselineSuite,
                run: runFor([])
            }),
            'MISSING_ATTEMPT'
        );
        expectBenchmarkError(
            () => evaluateCoreLfProofAgentBenchmarkRun({
                suite: baselineSuite,
                run: runFor([abstention])
            }),
            'UNKNOWN_ATTEMPT_CASE'
        );
        expectBenchmarkError(
            () => runFor([baseline, baseline]),
            'DUPLICATE_ATTEMPT'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkSuite({
                revision: 'duplicate-suite-v1',
                cases: [cases.baseline_exact, cases.baseline_exact]
            }),
            'DUPLICATE_CASE'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkSuite({
                revision: 'malformed-case-suite-v1',
                cases: [{
                    ...cases.baseline_exact,
                    settings: null
                } as unknown as CoreLfProofAgentBenchmarkCase]
            }),
            'INVALID_CASE'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkSuite({
                revision: 'stale-case-suite-v1',
                cases: [{
                    ...cases.baseline_exact,
                    precondition: {
                        ...cases.baseline_exact.precondition,
                        inspectionText:
                            `${cases.baseline_exact.precondition.inspectionText} `
                    }
                }]
            }),
            'STALE_CASE'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkCase({
                id: 'case.duplicate_relevance',
                previousSource: cases.baseline_exact.previousSource,
                currentSource: cases.baseline_exact.currentSource,
                proof: cases.baseline_exact.proof,
                goalId: cases.baseline_exact.goalId,
                relevantPremises: [firstWitness, firstWitness]
            }),
            'DUPLICATE_RELEVANT_PREMISE'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkCase({
                id: 'case.inaccessible_relevance',
                previousSource: cases.baseline_exact.previousSource,
                currentSource: cases.baseline_exact.currentSource,
                proof: cases.baseline_exact.proof,
                goalId: cases.baseline_exact.goalId,
                relevantPremises: [inaccessible]
            }),
            'INACCESSIBLE_RELEVANT_PREMISE'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkAttempt({
                benchmarkCase: cases.baseline_exact,
                retrievedPremises: [firstWitness, firstWitness],
                decision: { kind: 'abstain' }
            }),
            'DUPLICATE_RETRIEVED_PREMISE'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkRun({
                revision: 'invalid-run-v1',
                provider: {
                    id: 'fixture-provider',
                    revision: 'fixture-provider-v1'
                },
                allowedProfiles: ['same-profile', 'same-profile'],
                seed: 'fixture-seed',
                attempts: [baseline]
            }),
            'INVALID_PROVIDER'
        );
        expectBenchmarkError(
            () => createCoreLfProofAgentBenchmarkRun({
                revision: 'invalid-run-v1',
                provider: {
                    id: 'fixture-provider',
                    revision: 'fixture-provider-v1'
                },
                allowedProfiles: ['profile-v1'],
                seed: 4 as unknown as string,
                attempts: [baseline]
            }),
            'INVALID_RUN'
        );
        expectBenchmarkError(
            () => evaluateCoreLfProofAgentBenchmarkRun({
                suite: baselineSuite,
                run: {
                    ...runFor([baseline]),
                    limits: null
                } as unknown as CoreLfProofAgentBenchmarkRun
            }),
            'INVALID_RUN'
        );
    });

    it('states the pure evaluator boundary exactly', () => {
        assert.deepEqual({
            invokesAgent: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.invokesAgent,
            invokesLambdapi:
                CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.invokesLambdapi,
            performsIo: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.performsIo,
            acquiresTime: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.acquiresTime,
            tokenizes: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.tokenizes,
            retainsCallbacks:
                CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.retainsCallbacks,
            artifactCurrent:
                CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.artifactCurrent
        }, {
            invokesAgent: false,
            invokesLambdapi: false,
            performsIo: false,
            acquiresTime: false,
            tokenizes: false,
            retainsCallbacks: false,
            artifactCurrent: false
        });
    });
});
