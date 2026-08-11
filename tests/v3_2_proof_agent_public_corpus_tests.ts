/** Focused AGENT-EVAL-12B1 representative public-corpus tests. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    serializeCoreLfProofAgentBenchmarkReport,
    serializeCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkSuite
} from '../src/v3_2/lf_proof_agent_benchmark';
import {
    parseCoreLfProofAgentBenchmarkReportText,
    parseCoreLfProofAgentBenchmarkRunText,
    parseCoreLfProofAgentBenchmarkSuiteText
} from '../src/v3_2/lf_proof_agent_interchange';
import {
    CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE,
    CoreLfProofAgentPublicCorpus,
    CoreLfProofAgentPublicCorpusError,
    createCoreLfProofAgentPublicCorpus,
    parseCoreLfProofAgentPublicCorpusText,
    serializeCoreLfProofAgentPublicCorpus
} from '../src/v3_2/lf_proof_agent_public_corpus';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from '../src/v3_2/lf_workspace';

const repositoryRoot = resolve(__dirname, '..');

interface CorpusFixture {
    readonly corpus: CoreLfProofAgentPublicCorpus;
    readonly text: string;
}

let cachedFixture: CorpusFixture | undefined;

const fixture = (): CorpusFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const corpus = createCoreLfProofAgentPublicCorpus();
    const text = serializeCoreLfProofAgentPublicCorpus(corpus);
    cachedFixture = { corpus, text };
    return cachedFixture;
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectCorpusError = (
    action: () => unknown,
    code: CoreLfProofAgentPublicCorpusError['code']
): void => assert.throws(
    action,
    error => error instanceof CoreLfProofAgentPublicCorpusError &&
        error.code === code &&
        error.path.length > 0
);

const entry = (id: string) => {
    const found = fixture().corpus.entries.find(candidate =>
        candidate.id === id
    );
    assert.notEqual(found, undefined, id);
    return found!;
};

const parsedEvidence = (id: string): Record<string, unknown> => {
    const reportText = entry(id).ownerEvidence.reportText;
    assert.notEqual(reportText, null, id);
    return JSON.parse(reportText!) as Record<string, unknown>;
};

const canonicalMutation = <T extends object>(
    sourceText: string,
    mutate: (value: T) => void
): string => {
    const value = JSON.parse(sourceText) as T;
    mutate(value);
    return serializeCoreLfWorkspaceCanonicalJson(value, 'tamperedCorpus');
};

describe('AGENT-EVAL-12B1 representative public proof-agent corpus', () => {
    it('constructs six exact tracks and ten track-then-ID ordered cases', () => {
        const { corpus } = fixture();
        assert.equal(corpus.revision, 'emdash-lf-proof-agent-public-corpus-v1');
        assert.equal(corpus.tracks.length, 6);
        assert.equal(corpus.entries.length, 10);
        assert.deepEqual(
            corpus.tracks.map(track => [
                track.id,
                track.minimumCases,
                track.selectedCases
            ]),
            [
                ['explicit-proof-construction', 2, 2],
                ['source-proof-management', 2, 2],
                ['bounded-automation', 2, 2],
                ['structures-classes-instances', 2, 2],
                ['maintenance-revision', 1, 1],
                ['lean4-manual-translation', 1, 1]
            ]
        );
        const trackIndex = new Map(corpus.tracks.map((track, index) => [
            track.id,
            index
        ]));
        const ordered = [...corpus.entries].sort((left, right) =>
            trackIndex.get(left.track)! - trackIndex.get(right.track)! ||
            left.id.localeCompare(right.id)
        );
        assert.deepEqual(corpus.entries, ordered);
        assert.equal(new Set(corpus.entries.map(item => item.id)).size, 10);
        assertDeepFrozen(corpus);
    });

    it('freshly accepts nine owner patches and honestly abstains once', () => {
        const { corpus } = fixture();
        assert.deepEqual(corpus.referenceReport.metrics.outcomes, {
            abstained: 1,
            acceptedComplete: 9,
            acceptedIncomplete: 0,
            rejected: 0
        });
        const outcomes = new Map(corpus.referenceReport.results.map(result => [
            result.caseId,
            result.outcome
        ]));
        for (const item of corpus.entries) {
            assert.equal(item.caseId, item.id);
            assert.equal(item.actualReferenceOutcome, outcomes.get(item.id));
            assert.equal(
                item.actualReferenceOutcome,
                item.expectedReferenceOutcome
            );
            assert.equal(item.referenceAttemptIsProofAuthority, false);
            assert.equal(
                item.ownerEvidence.evidenceClass,
                'owner-output-not-curator-label'
            );
        }
        const attempts = new Map(
            corpus.referenceReport.run.attempts.map(attempt => [
                attempt.caseId,
                attempt
            ])
        );
        for (const item of corpus.entries) {
            assert.equal(
                attempts.get(item.id)?.decision.kind,
                item.id === 'native.class.ambiguity-abstention'
                    ? 'abstain'
                    : 'patch'
            );
        }
    });

    it('retains executable refine, obvious, and simplifier owner evidence',
        () => {
            const refine = parsedEvidence('native.refine.coupled-goals') as {
                goalGraph: { edges: readonly unknown[] };
            };
            assert.equal(refine.goalGraph.edges.length, 1);

            const obvious = parsedEvidence(
                'native.automation.obvious-apply'
            ) as {
                root: {
                    candidates: readonly { operation: string }[];
                };
                completion: {
                    candidates: readonly { operation: string }[];
                };
            };
            assert.equal(
                obvious.root.candidates.some(candidate =>
                    candidate.operation === 'apply'
                ),
                true
            );
            assert.equal(
                obvious.completion.candidates.some(candidate =>
                    candidate.operation === 'exact'
                ),
                true
            );

            const simplifier = parsedEvidence(
                'native.automation.simplified-transport'
            ) as {
                rewriteCount: number;
                trace: readonly unknown[];
                transportTerm?: unknown;
                plan: { tag: string };
            };
            assert.equal(simplifier.rewriteCount, 1);
            assert.equal(simplifier.trace.length, 1);
            assert.notEqual(simplifier.transportTerm, undefined);
            assert.equal(simplifier.plan.tag, 'have');
        });

    it('retains finite shared-diamond and ambiguity synthesis reports', () => {
        const shared = parsedEvidence('native.class.shared-diamond') as {
            outcome: string;
            rootGoalId: string;
            goals: readonly {
                goalId: string;
                equivalentProviders?: readonly unknown[];
                candidates: readonly {
                    premises: readonly { disposition: string }[];
                }[];
            }[];
        };
        assert.equal(shared.outcome, 'solved');
        const sharedRoot = shared.goals.find(goal =>
            goal.goalId === shared.rootGoalId
        );
        assert.ok((sharedRoot?.equivalentProviders?.length ?? 0) >= 2);
        assert.ok(shared.goals.flatMap(goal => goal.candidates)
            .flatMap(candidate => candidate.premises)
            .some(premise => premise.disposition === 'table-hit'));

        const ambiguous = parsedEvidence(
            'native.class.ambiguity-abstention'
        ) as {
            outcome: string;
            rootGoalId: string;
            goals: readonly {
                goalId: string;
                selectedProvider?: unknown;
                candidates: readonly { outcome: string }[];
            }[];
        };
        assert.equal(ambiguous.outcome, 'ambiguous');
        const ambiguousRoot = ambiguous.goals.find(goal =>
            goal.goalId === ambiguous.rootGoalId
        );
        assert.equal(ambiguousRoot?.selectedProvider, undefined);
        assert.ok((ambiguousRoot?.candidates.filter(candidate =>
            candidate.outcome === 'ambiguous-success' ||
            candidate.outcome === 'success'
        ).length ?? 0) >= 2);
    });

    it('retains stale-safe maintenance and attributed manual Lean evidence',
        () => {
            const maintenance = parsedEvidence(
                'native.maintenance.changed-source'
            ) as {
                proposal: {
                    materializesUpdatedSource: boolean;
                    provider: { candidates: readonly unknown[] };
                };
                replay: {
                    meaning: string;
                    result: { status: string };
                };
            };
            assert.equal(maintenance.proposal.materializesUpdatedSource, false);
            assert.ok(maintenance.proposal.provider.candidates.length > 0);
            assert.equal(maintenance.replay.meaning, 'candidate-replayed');
            assert.equal(maintenance.replay.result.status, 'complete');

            const lean = parsedEvidence(
                'lean4.diamond1.explicit-translation'
            ) as {
                status: string;
                binders: readonly { disposition: string }[];
            };
            assert.equal(lean.status, 'elaborated');
            assert.equal(
                lean.binders.filter(binder =>
                    binder.disposition === 'synthesized'
                ).length,
                1
            );
            assert.deepEqual(fixture().corpus.leanAttribution, {
                repository: 'leanprover/lean4',
                checkpoint: 'f29e9e488ea8242c875806e4b0564820c2d553b2',
                sourcePath: 'tests/elab/diamond1.lean',
                sourceSha256:
                    'ca443749e65db8cb1e399446e1a9221cea0a944eda197852d2191dd767cdd3b6',
                license: 'Apache-2.0',
                correspondence:
                    'Foo/FooComm/FooAssoc/FooAC-diamond-to-explicit-class-evidence',
                manualTranslationOnly: true,
                parserParityClaimed: false
            });
        });

    it('round-trips the report and its nested suite/run via strict interchange',
        () => {
            const { referenceReport } = fixture().corpus;
            assert.deepEqual(
                parseCoreLfProofAgentBenchmarkSuiteText(
                    serializeCoreLfProofAgentBenchmarkSuite(
                        referenceReport.suite
                    )
                ),
                referenceReport.suite
            );
            assert.deepEqual(
                parseCoreLfProofAgentBenchmarkRunText(
                    serializeCoreLfProofAgentBenchmarkRun(referenceReport.run)
                ),
                referenceReport.run
            );
            assert.deepEqual(
                parseCoreLfProofAgentBenchmarkReportText(
                    serializeCoreLfProofAgentBenchmarkReport(referenceReport)
                ),
                referenceReport
            );
        });

    it('round-trips exact canonical corpus bytes to a deep-frozen rebuild',
        () => {
            const { corpus, text } = fixture();
            const parsed = parseCoreLfProofAgentPublicCorpusText(text);
            assert.deepEqual(parsed, corpus);
            assert.equal(serializeCoreLfProofAgentPublicCorpus(parsed), text);
            assertDeepFrozen(parsed);
        });

    it('rejects invalid, unsupported, unknown, and noncanonical text', () => {
        const { text } = fixture();
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText(''),
            'INVALID_CORPUS_TEXT'
        );
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText('{'),
            'INVALID_CORPUS_TEXT'
        );
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText(text.trimEnd()),
            'NONCANONICAL_CORPUS_TEXT'
        );
        const wrongRevision = canonicalMutation<{ revision: string }>(
            text,
            value => {
                value.revision = 'unsupported-corpus-v9';
            }
        );
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText(wrongRevision),
            'UNSUPPORTED_CORPUS_REVISION'
        );
        const unknown = canonicalMutation<Record<string, unknown>>(
            text,
            value => {
                value.hiddenLeaderboard = true;
            }
        );
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText(unknown),
            'INVALID_CORPUS_ARTIFACT'
        );
    });

    it('rejects drifted curation and forged nested evaluator results', () => {
        const { text } = fixture();
        const driftedEntry = canonicalMutation<{
            entries: Array<{ features: string[] }>;
        }>(text, value => {
            value.entries[0].features.push('unreviewed-claim');
        });
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText(driftedEntry),
            'STALE_CORPUS_ARTIFACT'
        );

        const forgedReport = canonicalMutation<{
            referenceReport: { metrics: { cases: number } };
        }>(text, value => {
            value.referenceReport.metrics.cases = 99;
        });
        expectCorpusError(
            () => parseCoreLfProofAgentPublicCorpusText(forgedReport),
            'INVALID_CORPUS_ARTIFACT'
        );
    });

    it('keeps 12B1 internal, browser-safe, and non-authoritative', () => {
        assert.deepEqual({
            publicBarrelExported:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE
                    .publicBarrelExported,
            nodeRunnerIncluded:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.nodeRunnerIncluded,
            invokesModel:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.invokesModel,
            invokesLambdapi:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.invokesLambdapi,
            performsIo:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.performsIo,
            nodeBuiltinDependency:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE
                    .nodeBuiltinDependency
        }, {
            publicBarrelExported: false,
            nodeRunnerIncluded: false,
            invokesModel: false,
            invokesLambdapi: false,
            performsIo: false,
            nodeBuiltinDependency: false
        });
        const implementation = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/lf_proof_agent_public_corpus.ts'
        ), 'utf8');
        const interchange = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/lf_proof_agent_interchange.ts'
        ), 'utf8');
        assert.doesNotMatch(implementation, /from ['"]node:/u);
        assert.doesNotMatch(interchange, /from ['"]node:/u);
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts',
            'packages/emdash/package.json'
        ]) {
            const source = readFileSync(resolve(repositoryRoot, relative),
                'utf8');
            assert.doesNotMatch(
                source,
                /lf_proof_agent_(?:public_corpus|interchange)/u,
                relative
            );
        }
        assert.equal(
            fixture().corpus.referenceAttemptsAreProofAuthority,
            false
        );
        assert.equal(fixture().corpus.curationLabelsAreKernelClaims, false);
    });
});
