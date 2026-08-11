/** Focused AGENT-EVAL-12B1 strict canonical interchange tests. */

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
    createCoreProofPlanHoleReplacement,
    kernelFree,
    provenance,
    sourceSpan
} from '../src/v3_2';
import {
    CoreLfProofAgentBenchmarkAttempt,
    CoreLfProofAgentBenchmarkCase,
    CoreLfProofAgentBenchmarkReport,
    CoreLfProofAgentBenchmarkRun,
    CoreLfProofAgentBenchmarkSuite,
    createCoreLfProofAgentBenchmarkAttempt,
    createCoreLfProofAgentBenchmarkCase,
    createCoreLfProofAgentBenchmarkRun,
    createCoreLfProofAgentBenchmarkSuite,
    evaluateCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkAttempt,
    serializeCoreLfProofAgentBenchmarkCase,
    serializeCoreLfProofAgentBenchmarkReport,
    serializeCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkSuite
} from '../src/v3_2/lf_proof_agent_benchmark';
import {
    CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE,
    CoreLfProofAgentInterchangeError,
    parseCoreLfProofAgentBenchmarkAttemptText,
    parseCoreLfProofAgentBenchmarkCaseText,
    parseCoreLfProofAgentBenchmarkReportText,
    parseCoreLfProofAgentBenchmarkRunText,
    parseCoreLfProofAgentBenchmarkSuiteText
} from '../src/v3_2/lf_proof_agent_interchange';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from '../src/v3_2/lf_workspace';

const moduleId = 'fixture.proof_agent_interchange';
const authorityPath = 'tests/fixtures/proof_agent_interchange.ts';
const proposition = coreLfQualifiedSymbol(moduleId, 'P');
const witness = coreLfQualifiedSymbol(moduleId, 'p');
const propositionCore = 'interchange_P';
const witnessCore = 'interchange_p';
const goalId = 'interchange_goal';

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;
const global = (
    symbol: { readonly moduleId: string; readonly name: string }
) => ({ tag: 'global' as const, symbol });
const proofProvenance = (line: number, detail: string) => provenance(
    'surface',
    detail,
    sourceSpan(authorityPath, line, 1, line, 2)
);

const moduleFixture = () => {
    const declarations = [{
        order: 0,
        symbol: proposition,
        type: { tag: 'type' as const },
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'ordinary' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: {
            authorityPath,
            sourceFragment: 'symbol P : TYPE;'
        }
    }, {
        order: 1,
        symbol: witness,
        type: global(proposition),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'ordinary' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: {
            authorityPath,
            sourceFragment: 'symbol p : P;'
        }
    }];
    const module = createCoreLfModuleSpec({
        revision: 'proof-agent-interchange-module-v1',
        moduleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('1'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'proof-agent-interchange-policy-v1',
        moduleRevision: module.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: 'AGENT-EVAL-12B1 standalone interchange fixture'
        }))
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'proof-agent-interchange-linkage-v1',
        moduleRevision: module.revision,
        entries: [{
            order: 0,
            symbol: proposition,
            kind: 'free-declaration',
            coreName: propositionCore,
            backendName: proposition.name
        }, {
            order: 1,
            symbol: witness,
            kind: 'free-declaration',
            coreName: witnessCore,
            backendName: witness.name
        }]
    });
    return { module, policy, linkage };
};

const proofDocument = (
    version: 'previous' | 'current'
): CoreLfWorkspaceProofDocumentInput => {
    const target = kernelFree(
        propositionCore,
        proofProvenance(20, 'interchange target')
    );
    return {
        moduleId,
        declarationId: 'proof',
        type: target,
        plan: version === 'previous'
            ? coreProofPlanExact(kernelFree(
                witnessCore,
                proofProvenance(21, 'previous witness')
            ))
            : coreProofPlanHole(goalId, {
                provenance: proofProvenance(22, 'current source hole'),
                expectation: { contextDepth: 0, target }
            }),
        provenance: proofProvenance(20, 'proof source'),
        fingerprint: createCoreProofArtifactFingerprint({
            source: {
                id: `proofs/interchange-${version}.ts`,
                sha256: hash(version === 'previous' ? '2' : '3')
            },
            profileSha256: hash('4'),
            dependencies: [{ moduleId, interfaceSha256: hash('5') }]
        })
    };
};

const sourceSnapshot = (
    version: 'previous' | 'current'
): CoreLfProofDevelopmentSourceSnapshot => {
    const workspace = createCoreLfDeclarationWorkspace({
        revision: 'proof-agent-interchange-workspace-v1',
        modules: [moduleFixture()]
    });
    return createCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopment({
            revision: `proof-agent-interchange-development-${version}`,
            workspace,
            proofs: [proofDocument(version)]
        })
    );
};

interface InterchangeFixture {
    readonly benchmarkCase: CoreLfProofAgentBenchmarkCase;
    readonly suite: CoreLfProofAgentBenchmarkSuite;
    readonly attempt: CoreLfProofAgentBenchmarkAttempt;
    readonly run: CoreLfProofAgentBenchmarkRun;
    readonly report: CoreLfProofAgentBenchmarkReport;
}

let cachedFixture: InterchangeFixture | undefined;

const fixture = (): InterchangeFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const benchmarkCase = createCoreLfProofAgentBenchmarkCase({
        id: 'interchange.exact',
        previousSource: sourceSnapshot('previous'),
        currentSource: sourceSnapshot('current'),
        proof: { moduleId, declarationId: 'proof' },
        goalId,
        relevantPremises: [witness]
    });
    const suite = createCoreLfProofAgentBenchmarkSuite({
        revision: 'proof-agent-interchange-suite-v1',
        cases: [benchmarkCase]
    });
    const attempt = createCoreLfProofAgentBenchmarkAttempt({
        benchmarkCase,
        retrievedPremises: [witness],
        reportedUsage: { checkerCalls: 1 },
        decision: {
            kind: 'patch',
            patch: createCoreProofPlanHoleReplacement(
                goalId,
                coreProofPlanExact(kernelFree(
                    witnessCore,
                    proofProvenance(30, 'reference exact witness')
                ))
            )
        }
    });
    const run = createCoreLfProofAgentBenchmarkRun({
        revision: 'proof-agent-interchange-run-v1',
        provider: {
            id: 'interchange-reference',
            revision: 'interchange-reference-v1'
        },
        allowedProfiles: ['explicit-plan-v1'],
        seed: 'interchange-seed-1',
        limits: { checkerCalls: 1 },
        attempts: [attempt]
    });
    const report = evaluateCoreLfProofAgentBenchmarkRun({ suite, run });
    cachedFixture = { benchmarkCase, suite, attempt, run, report };
    return cachedFixture;
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectInterchangeError = (
    action: () => unknown,
    code: CoreLfProofAgentInterchangeError['code'],
    pathPattern?: RegExp
): void => assert.throws(
    action,
    error => error instanceof CoreLfProofAgentInterchangeError &&
        error.code === code &&
        error.path.length > 0 &&
        (pathPattern === undefined || pathPattern.test(error.path))
);

const canonicalMutation = <T extends object>(
    sourceText: string,
    mutate: (value: T) => void
): string => {
    const value = JSON.parse(sourceText) as T;
    mutate(value);
    return serializeCoreLfWorkspaceCanonicalJson(value, 'tamperedArtifact');
};

describe('AGENT-EVAL-12B1 strict proof-agent interchange', () => {
    it('round-trips all five artifacts through fresh canonical authority', () => {
        const { benchmarkCase, suite, attempt, run, report } = fixture();
        const artifacts = [{
            parsed: parseCoreLfProofAgentBenchmarkCaseText(
                serializeCoreLfProofAgentBenchmarkCase(benchmarkCase)
            ),
            expected: benchmarkCase
        }, {
            parsed: parseCoreLfProofAgentBenchmarkSuiteText(
                serializeCoreLfProofAgentBenchmarkSuite(suite)
            ),
            expected: suite
        }, {
            parsed: parseCoreLfProofAgentBenchmarkAttemptText(
                serializeCoreLfProofAgentBenchmarkAttempt(attempt)
            ),
            expected: attempt
        }, {
            parsed: parseCoreLfProofAgentBenchmarkRunText(
                serializeCoreLfProofAgentBenchmarkRun(run)
            ),
            expected: run
        }, {
            parsed: parseCoreLfProofAgentBenchmarkReportText(
                serializeCoreLfProofAgentBenchmarkReport(report)
            ),
            expected: report
        }];

        artifacts.forEach(({ parsed, expected }) => {
            assert.deepEqual(parsed, expected);
            assertDeepFrozen(parsed);
        });
        assert.equal(report.results[0].outcome, 'accepted-complete');
    });

    it('requires exact canonical newline-terminated serializer bytes', () => {
        const caseText = serializeCoreLfProofAgentBenchmarkCase(
            fixture().benchmarkCase
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText(''),
            'INVALID_TEXT'
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText('{'),
            'INVALID_TEXT'
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText(caseText.trimEnd()),
            'NONCANONICAL_TEXT'
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText(
                `${JSON.stringify(JSON.parse(caseText), null, 2)}\n`
            ),
            'NONCANONICAL_TEXT'
        );
    });

    it('rejects unsupported revisions and unknown case fields', () => {
        const caseText = serializeCoreLfProofAgentBenchmarkCase(
            fixture().benchmarkCase
        );
        const wrongRevision = canonicalMutation<{
            revision: string;
        }>(caseText, value => {
            value.revision = 'unsupported-case-v9';
        });
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText(wrongRevision),
            'UNSUPPORTED_REVISION',
            /\.revision$/u
        );

        const unknownField = canonicalMutation<Record<string, unknown>>(
            caseText,
            value => {
                value.hiddenAnswer = true;
            }
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText(unknownField),
            'INVALID_ARTIFACT',
            /\.hiddenAnswer$/u
        );
    });

    it('rejects stale case preconditions before benchmark use', () => {
        const stale = canonicalMutation<{
            precondition: { inspectionText: string };
        }>(serializeCoreLfProofAgentBenchmarkCase(fixture().benchmarkCase),
            value => {
                value.precondition.inspectionText += ' ';
            }
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkCaseText(stale),
            'STALE_ARTIFACT',
            /^caseText$/u
        );
    });

    it('rejects unknown nested patch fields and stale attempt identity', () => {
        const attemptText = serializeCoreLfProofAgentBenchmarkAttempt(
            fixture().attempt
        );
        const nestedUnknown = canonicalMutation<{
            decision: {
                patch: { replacement: Record<string, unknown> };
            };
        }>(attemptText, value => {
            value.decision.patch.replacement.hiddenTactic = 'trust-me';
        });
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkAttemptText(nestedUnknown),
            'INVALID_ARTIFACT',
            /\.replacement\.hiddenTactic$/u
        );

        const staleIdentity = canonicalMutation<{ caseId: string }>(
            attemptText,
            value => {
                value.caseId = 'interchange.different';
            }
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkAttemptText(staleIdentity),
            'STALE_ARTIFACT',
            /^attemptText$/u
        );
    });

    it('rejects unknown run fields and reconstructs every nested attempt', () => {
        const runText = serializeCoreLfProofAgentBenchmarkRun(fixture().run);
        const unknownProviderField = canonicalMutation<{
            provider: Record<string, unknown>;
        }>(runText, value => {
            value.provider.credential = 'must-not-be-retained';
        });
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkRunText(unknownProviderField),
            'INVALID_ARTIFACT',
            /\.provider\.credential$/u
        );

        const staleNestedAttempt = canonicalMutation<{
            attempts: Array<{ caseId: string }>;
        }>(runText, value => {
            value.attempts[0].caseId = 'interchange.different';
        });
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkRunText(staleNestedAttempt),
            'STALE_ARTIFACT'
        );
    });

    it('freshly re-evaluates reports and rejects forged derived metrics', () => {
        const reportText = serializeCoreLfProofAgentBenchmarkReport(
            fixture().report
        );
        const forged = canonicalMutation<{
            metrics: { cases: number };
        }>(reportText, value => {
            value.metrics.cases = 99;
        });
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkReportText(forged),
            'STALE_ARTIFACT',
            /^reportText$/u
        );

        const unknown = canonicalMutation<Record<string, unknown>>(
            reportText,
            value => {
                value.authoritativeLeaderboardScore = 1;
            }
        );
        expectInterchangeError(
            () => parseCoreLfProofAgentBenchmarkReportText(unknown),
            'INVALID_ARTIFACT',
            /\.authoritativeLeaderboardScore$/u
        );
    });

    it('states the internal browser-safe non-authority boundary exactly', () => {
        assert.deepEqual({
            revisionPolicy:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.revisionPolicy,
            unknownFieldPolicy:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.unknownFieldPolicy,
            staleArtifactPolicy:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.staleArtifactPolicy,
            changesBenchmarkSemantics:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE
                    .changesBenchmarkSemantics,
            performsIo:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.performsIo,
            invokesModel:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.invokesModel,
            invokesLambdapi:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.invokesLambdapi,
            nodeBuiltinDependency:
                CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE
                    .nodeBuiltinDependency
        }, {
            revisionPolicy: 'exact-closed-revisions',
            unknownFieldPolicy: 'reject',
            staleArtifactPolicy: 'reject-before-use',
            changesBenchmarkSemantics: false,
            performsIo: false,
            invokesModel: false,
            invokesLambdapi: false,
            nodeBuiltinDependency: false
        });
    });
});
