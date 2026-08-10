/**
 * Browser-safe scoring of immutable proof-agent attempts.
 *
 * Agents and host adapters produce data; this module owns exact case identity,
 * accessible scope, inert patch application, fresh proof replay, and portable
 * integer metrics. It performs no model call, I/O, timing, tokenization, or
 * source persistence.
 */

import {
    CORE_LF_DEVELOPMENT_DIFF_PROFILE,
    CoreLfDevelopmentDiffOptions
} from './lf_development_diff';
import {
    CoreLfPremiseIndexOptions,
    CoreLfPremiseIndexSettings,
    createCoreLfAccessiblePremiseIndex
} from './lf_premise_index';
import {
    CoreLfProofDevelopmentSourceSnapshot,
    reconstructCoreLfProofDevelopmentSourceSnapshot,
    serializeCoreLfProofDevelopmentSourceSnapshot
} from './lf_proof_development_source';
import {
    CORE_LF_PROOF_MAINTENANCE_PROFILE,
    CoreLfProofMaintenanceIdentity,
    CoreLfProofReplayDiagnostic,
    inspectCoreLfProofMaintenance,
    projectCoreLfProofReplayDiagnostic,
    serializeCoreLfProofMaintenanceInspection
} from './lf_proof_maintenance';
import {
    CoreLfQualifiedSymbol,
    coreLfQualifiedSymbol
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationWorkspace,
    compileCoreLfDeclarationWorkspace,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreLfWorkspaceProofDocumentInput,
    compileCoreLfWorkspaceProofDocument
} from './lf_workspace_proof';
import {
    CoreProofGoalCouplingGraph
} from './proof_goal_graph';
import {
    CoreProofPlan,
    CoreProofPlanStateSnapshot
} from './proof_plan';
import {
    CORE_PROOF_PLAN_PATCH_PROFILE,
    CoreProofPlanPatch,
    CoreProofPlanPatchError,
    applyCoreProofPlanPatch
} from './proof_plan_patch';

export const CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-agent-benchmark-v1' as const,
    caseRevision: 'emdash-lf-proof-agent-benchmark-case-v1' as const,
    suiteRevision: 'emdash-lf-proof-agent-benchmark-suite-v1' as const,
    attemptRevision: 'emdash-lf-proof-agent-benchmark-attempt-v1' as const,
    runRevision: 'emdash-lf-proof-agent-benchmark-run-v1' as const,
    resultRevision: 'emdash-lf-proof-agent-benchmark-result-v1' as const,
    reportRevision: 'emdash-lf-proof-agent-benchmark-report-v1' as const,
    maintenanceProfileRevision:
        CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
    developmentDiffProfileRevision:
        CORE_LF_DEVELOPMENT_DIFF_PROFILE.revision,
    patchProfileRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
    caseOrder: 'exact-case-id' as const,
    attemptOrder: 'exact-case-id' as const,
    resultOrder: 'exact-case-id' as const,
    attemptPolicy: 'abstain-or-one-inert-hole-patch' as const,
    acceptancePolicy: 'fresh-exact-closure-proof-replay' as const,
    relevantPremiseAuthority: 'curator-label-accessibility-only' as const,
    reportedUsageAuthority: 'provider-reported-unverified' as const,
    scorePolicy: 'integer-counts-no-derived-ratios' as const,
    maxCases: 256,
    maxPremiseLabels: 4_096,
    maxPlanNodes: 100_000,
    maxReportedMetric: 1_000_000_000_000,
    artifactCurrent: false as const,
    materializesUpdatedSource: false as const,
    computesCryptographicHashes: false as const,
    invokesAgent: false as const,
    invokesLambdapi: false as const,
    performsIo: false as const,
    acquiresTime: false as const,
    tokenizes: false as const,
    retainsCallbacks: false as const,
    retainsSessionState: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export type CoreLfProofAgentBenchmarkErrorCode =
    | 'INVALID_CASE'
    | 'INITIAL_PROOF_NOT_OPEN'
    | 'INITIAL_GOAL_NOT_OPEN'
    | 'INACCESSIBLE_RELEVANT_PREMISE'
    | 'DUPLICATE_RELEVANT_PREMISE'
    | 'STALE_CASE'
    | 'INVALID_SUITE'
    | 'DUPLICATE_CASE'
    | 'CASE_LIMIT_EXCEEDED'
    | 'INVALID_ATTEMPT'
    | 'DUPLICATE_RETRIEVED_PREMISE'
    | 'STALE_ATTEMPT'
    | 'INVALID_RUN'
    | 'INVALID_PROVIDER'
    | 'INVALID_LIMIT'
    | 'DUPLICATE_ATTEMPT'
    | 'MISSING_ATTEMPT'
    | 'UNKNOWN_ATTEMPT_CASE'
    | 'ATTEMPT_LIMIT_EXCEEDED'
    | 'PLAN_NODE_LIMIT_EXCEEDED'
    | 'METRIC_OVERFLOW'
    | 'UNSUPPORTED_REPLAY_ERROR';

export class CoreLfProofAgentBenchmarkError extends Error {
    constructor(
        public readonly code: CoreLfProofAgentBenchmarkErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfProofAgentBenchmarkError';
    }
}

const fail = (
    code: CoreLfProofAgentBenchmarkErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreLfProofAgentBenchmarkError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SAFE_SEED = /^[^\u0000-\u001f\u007f]{1,128}$/u;

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const sameProof = (
    left: CoreLfProofMaintenanceIdentity,
    right: CoreLfProofMaintenanceIdentity
): boolean => left.moduleId === right.moduleId &&
    left.declarationId === right.declarationId;

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const cloneProof = (
    proof: CoreLfProofMaintenanceIdentity
): CoreLfProofMaintenanceIdentity => ({
    moduleId: proof.moduleId,
    declarationId: proof.declarationId
});

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

const freezePortable = <T>(value: T, path: string): T => {
    let text: string | undefined;
    try {
        text = JSON.stringify(value);
    } catch (error: unknown) {
        return fail(
            'INVALID_CASE',
            path,
            'Proof-agent benchmark data cannot be serialized',
            error
        );
    }
    if (text === undefined) {
        return fail(
            'INVALID_CASE',
            path,
            'Proof-agent benchmark data cannot be undefined'
        );
    }
    const projected = JSON.parse(text) as T;
    serializeCoreLfWorkspaceCanonicalJson(projected, path);
    return deepFreeze(projected);
};

const canonical = (value: unknown, path: string): string =>
    serializeCoreLfWorkspaceCanonicalJson(value, path);

const assertId = (value: string, path: string): void => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return;
    fail('INVALID_CASE', path, 'Expected a stable nonempty benchmark ID');
};

const assertRevision = (value: string, path: string): void => {
    if (typeof value === 'string' && SAFE_REVISION.test(value)) return;
    fail('INVALID_CASE', path, 'Expected a stable benchmark revision');
};

const normalizeSymbol = (
    input: CoreLfQualifiedSymbol,
    path: string
): CoreLfQualifiedSymbol => {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_CASE',
            path,
            'Premise identity must be a qualified symbol record'
        );
    }
    try {
        return coreLfQualifiedSymbol(input.moduleId, input.name);
    } catch (error: unknown) {
        return fail(
            'INVALID_CASE',
            path,
            'Premise identity is not a valid qualified symbol',
            error
        );
    }
};

const normalizeSymbols = (
    input: readonly CoreLfQualifiedSymbol[],
    path: string,
    duplicateCode:
        | 'DUPLICATE_RELEVANT_PREMISE'
        | 'DUPLICATE_RETRIEVED_PREMISE',
    sort: boolean
): readonly CoreLfQualifiedSymbol[] => {
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_CASE',
            path,
            'Premise identities must be an array'
        );
    }
    if (input.length > CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.maxPremiseLabels) {
        return fail(
            'INVALID_CASE',
            path,
            'Premise identity count exceeds the benchmark bound'
        );
    }
    const seen = new Set<string>();
    const symbols = input.map((symbol, index) => {
        const normalized = normalizeSymbol(symbol, `${path}[${index}]`);
        const key = symbolKey(normalized);
        if (seen.has(key)) {
            return fail(
                duplicateCode,
                `${path}[${index}]`,
                'Premise identity occurs more than once'
            );
        }
        seen.add(key);
        return normalized;
    });
    if (sort) symbols.sort((left, right) =>
        compareText(symbolKey(left), symbolKey(right))
    );
    return Object.freeze(symbols);
};

const planNodeCount = (
    plan: CoreProofPlan,
    path: string
): number => {
    const stack: CoreProofPlan[] = [plan];
    let count = 0;
    while (stack.length > 0) {
        const node = stack.pop()!;
        count++;
        if (count > CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.maxPlanNodes) {
            return fail(
                'PLAN_NODE_LIMIT_EXCEEDED',
                path,
                'Proof plan exceeds the benchmark node bound'
            );
        }
        switch (node.tag) {
            case 'exact':
            case 'hole':
                break;
            case 'intro':
                stack.push(node.body);
                break;
            case 'apply':
                for (let index = node.premises.length - 1; index >= 0; index--) {
                    stack.push(node.premises[index]);
                }
                break;
            case 'have':
                stack.push(node.body, node.proof);
                break;
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }
    }
    return count;
};

export interface CoreLfProofAgentBenchmarkCaseInput {
    readonly id: string;
    readonly previousSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly currentSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly proof: CoreLfProofMaintenanceIdentity;
    readonly goalId: string;
    readonly diffOptions?: CoreLfDevelopmentDiffOptions;
    readonly premiseIndexOptions?: CoreLfPremiseIndexOptions;
    readonly relevantPremises?: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfProofAgentBenchmarkCase {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.caseRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly maintenanceProfileRevision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.revision;
    readonly id: string;
    readonly previousSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly currentSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly proof: CoreLfProofMaintenanceIdentity;
    readonly goalId: string;
    readonly settings: {
        readonly expressionVisitLimit: number;
        readonly premiseIndex: CoreLfPremiseIndexSettings;
    };
    readonly precondition: {
        readonly previousSourceText: string;
        readonly currentSourceText: string;
        readonly inspectionText: string;
    };
    readonly initial: {
        readonly state: CoreProofPlanStateSnapshot;
        readonly goalGraph: CoreProofGoalCouplingGraph;
        readonly planNodeCount: number;
    };
    readonly relevantPremises: readonly CoreLfQualifiedSymbol[];
    readonly relevantPremiseAuthority:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.relevantPremiseAuthority;
    readonly suppliedHashesRecomputed: false;
}

interface PreparedCase {
    readonly benchmarkCase: CoreLfProofAgentBenchmarkCase;
    readonly workspace: CoreLfCompiledDeclarationWorkspace;
    readonly proof: CoreLfWorkspaceProofDocumentInput;
    readonly premiseIndex: ReturnType<
        typeof createCoreLfAccessiblePremiseIndex
    >;
}

const prepareCase = (
    input: CoreLfProofAgentBenchmarkCaseInput
): PreparedCase => {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_CASE',
            'case',
            'Benchmark case input must be a data record'
        );
    }
    assertId(input.id, 'case.id');
    const inspection = inspectCoreLfProofMaintenance({
        previousSource: input.previousSource,
        currentSource: input.currentSource,
        proof: input.proof,
        diffOptions: input.diffOptions
    });
    if (inspection.outcome !== 'checked-incomplete') {
        return fail(
            'INITIAL_PROOF_NOT_OPEN',
            'case.proof',
            `Benchmark case requires checked-incomplete replay, received ` +
                `'${inspection.outcome}'`
        );
    }
    if (!inspection.artifact.proofArtifact.state.goals.some(goal =>
        goal.id === input.goalId
    )) {
        return fail(
            'INITIAL_GOAL_NOT_OPEN',
            'case.goalId',
            'Benchmark goal is not open after fresh selected-proof replay'
        );
    }
    const current = reconstructCoreLfProofDevelopmentSourceSnapshot(
        input.currentSource
    );
    const proof = current.plan.proofs.find(candidate =>
        sameProof(candidate, input.proof)
    );
    if (proof === undefined) {
        return fail(
            'INVALID_CASE',
            'case.proof',
            'Fresh inspection and reconstructed source disagree on proof identity'
        );
    }
    const workspace = compileCoreLfDeclarationWorkspace(
        current.plan.workspace
    );
    const premiseIndex = createCoreLfAccessiblePremiseIndex(
        workspace,
        proof.moduleId,
        input.premiseIndexOptions ?? {}
    );
    const relevantPremises = normalizeSymbols(
        input.relevantPremises ?? [],
        'case.relevantPremises',
        'DUPLICATE_RELEVANT_PREMISE',
        true
    );
    relevantPremises.forEach((symbol, index) => {
        if (premiseIndex.resolve(symbol) !== undefined) return;
        fail(
            'INACCESSIBLE_RELEVANT_PREMISE',
            `case.relevantPremises[${index}]`,
            'Curated relevant premise is not accessible in the exact case scope'
        );
    });
    const benchmarkCase = freezePortable({
        revision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.caseRevision,
        profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        maintenanceProfileRevision:
            CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
        id: input.id,
        previousSource: input.previousSource,
        currentSource: input.currentSource,
        proof: cloneProof(input.proof),
        goalId: input.goalId,
        settings: {
            expressionVisitLimit:
                inspection.semanticDiff.visitBudget.expressionVisitLimit,
            premiseIndex: premiseIndex.snapshot.settings
        },
        precondition: {
            previousSourceText:
                serializeCoreLfProofDevelopmentSourceSnapshot(
                    input.previousSource
                ),
            currentSourceText:
                serializeCoreLfProofDevelopmentSourceSnapshot(
                    input.currentSource
                ),
            inspectionText:
                serializeCoreLfProofMaintenanceInspection(inspection)
        },
        initial: {
            state: inspection.artifact.proofArtifact.state,
            goalGraph: inspection.goalGraph,
            planNodeCount: planNodeCount(proof.plan, 'case.initial.plan')
        },
        relevantPremises,
        relevantPremiseAuthority:
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.relevantPremiseAuthority,
        suppliedHashesRecomputed: false as const
    }, 'proofAgentBenchmarkCase');
    return { benchmarkCase, workspace, proof, premiseIndex };
};

/** Construct one self-contained freshly checked benchmark case. */
export function createCoreLfProofAgentBenchmarkCase(
    input: CoreLfProofAgentBenchmarkCaseInput
): CoreLfProofAgentBenchmarkCase {
    return prepareCase(input).benchmarkCase;
}

/** Canonical exact-byte case identity used by every attempt. */
export const serializeCoreLfProofAgentBenchmarkCase = (
    benchmarkCase: CoreLfProofAgentBenchmarkCase
): string => serializeCoreLfWorkspaceCanonicalJson(
    benchmarkCase,
    'proofAgentBenchmarkCase'
);

const prepareCaseArtifact = (
    benchmarkCase: CoreLfProofAgentBenchmarkCase,
    path: string
): PreparedCase => {
    if (
        benchmarkCase === null ||
        typeof benchmarkCase !== 'object' ||
        benchmarkCase.revision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.caseRevision ||
        benchmarkCase.profileRevision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision ||
        benchmarkCase.maintenanceProfileRevision !==
            CORE_LF_PROOF_MAINTENANCE_PROFILE.revision ||
        benchmarkCase.settings === null ||
        typeof benchmarkCase.settings !== 'object' ||
        benchmarkCase.settings.premiseIndex === null ||
        typeof benchmarkCase.settings.premiseIndex !== 'object' ||
        benchmarkCase.precondition === null ||
        typeof benchmarkCase.precondition !== 'object' ||
        benchmarkCase.initial === null ||
        typeof benchmarkCase.initial !== 'object' ||
        !Array.isArray(benchmarkCase.relevantPremises) ||
        benchmarkCase.suppliedHashesRecomputed !== false
    ) {
        return fail(
            'INVALID_CASE',
            path,
            'Benchmark case uses unsupported or malformed profile data'
        );
    }
    try {
        canonical(benchmarkCase, path);
    } catch (error: unknown) {
        return fail(
            'INVALID_CASE',
            path,
            'Benchmark case is not portable canonical data',
            error
        );
    }
    const prepared = prepareCase({
        id: benchmarkCase.id,
        previousSource: benchmarkCase.previousSource,
        currentSource: benchmarkCase.currentSource,
        proof: benchmarkCase.proof,
        goalId: benchmarkCase.goalId,
        diffOptions: {
            expressionVisitLimit:
                benchmarkCase.settings.expressionVisitLimit
        },
        premiseIndexOptions: benchmarkCase.settings.premiseIndex,
        relevantPremises: benchmarkCase.relevantPremises
    });
    if (
        serializeCoreLfProofAgentBenchmarkCase(prepared.benchmarkCase) !==
            serializeCoreLfProofAgentBenchmarkCase(benchmarkCase)
    ) {
        return fail(
            'STALE_CASE',
            path,
            'Benchmark case differs from fresh exact reconstruction'
        );
    }
    return prepared;
};

export interface CoreLfProofAgentBenchmarkSuiteInput {
    readonly revision: string;
    readonly cases: readonly CoreLfProofAgentBenchmarkCase[];
}

export interface CoreLfProofAgentBenchmarkSuite {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.suiteRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly suiteRevision: string;
    readonly cases: readonly CoreLfProofAgentBenchmarkCase[];
}

interface PreparedSuite {
    readonly suite: CoreLfProofAgentBenchmarkSuite;
    readonly cases: readonly PreparedCase[];
}

const buildSuite = (
    suiteRevision: string,
    preparedCases: readonly PreparedCase[]
): CoreLfProofAgentBenchmarkSuite => freezePortable({
    revision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.suiteRevision,
    profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
    suiteRevision,
    cases: preparedCases.map(prepared => prepared.benchmarkCase)
        .sort((left, right) => compareText(left.id, right.id))
}, 'proofAgentBenchmarkSuite');

const prepareSuiteInput = (
    input: CoreLfProofAgentBenchmarkSuiteInput
): PreparedSuite => {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_SUITE',
            'suite',
            'Benchmark suite input must be a data record'
        );
    }
    assertRevision(input.revision, 'suite.suiteRevision');
    if (!Array.isArray(input.cases) || input.cases.length === 0) {
        return fail(
            'INVALID_SUITE',
            'suite.cases',
            'Benchmark suite requires at least one case'
        );
    }
    if (input.cases.length > CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.maxCases) {
        return fail(
            'CASE_LIMIT_EXCEEDED',
            'suite.cases',
            'Benchmark suite exceeds the finite case bound'
        );
    }
    const seen = new Set<string>();
    const cases = input.cases.map((benchmarkCase, index) => {
        const prepared = prepareCaseArtifact(
            benchmarkCase,
            `suite.cases[${index}]`
        );
        if (seen.has(prepared.benchmarkCase.id)) {
            return fail(
                'DUPLICATE_CASE',
                `suite.cases[${index}].id`,
                'Benchmark suite repeats a case ID'
            );
        }
        seen.add(prepared.benchmarkCase.id);
        return prepared;
    }).sort((left, right) => compareText(
        left.benchmarkCase.id,
        right.benchmarkCase.id
    ));
    return {
        suite: buildSuite(input.revision, cases),
        cases: Object.freeze(cases)
    };
};

/** Revalidate and canonically order one finite benchmark suite. */
export function createCoreLfProofAgentBenchmarkSuite(
    input: CoreLfProofAgentBenchmarkSuiteInput
): CoreLfProofAgentBenchmarkSuite {
    return prepareSuiteInput(input).suite;
}

export const serializeCoreLfProofAgentBenchmarkSuite = (
    suite: CoreLfProofAgentBenchmarkSuite
): string => serializeCoreLfWorkspaceCanonicalJson(
    suite,
    'proofAgentBenchmarkSuite'
);

const prepareSuiteArtifact = (
    suite: CoreLfProofAgentBenchmarkSuite
): PreparedSuite => {
    if (
        suite === null ||
        typeof suite !== 'object' ||
        suite.revision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.suiteRevision ||
        suite.profileRevision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision
    ) {
        return fail(
            'INVALID_SUITE',
            'suite',
            'Benchmark suite uses unsupported profile data'
        );
    }
    const prepared = prepareSuiteInput({
        revision: suite.suiteRevision,
        cases: suite.cases
    });
    if (
        serializeCoreLfProofAgentBenchmarkSuite(prepared.suite) !==
            serializeCoreLfProofAgentBenchmarkSuite(suite)
    ) {
        return fail(
            'INVALID_SUITE',
            'suite',
            'Benchmark suite differs from canonical reconstruction'
        );
    }
    return prepared;
};

export interface CoreLfProofAgentReportedUsage {
    readonly wallTimeMs?: number;
    readonly inputTokens?: number;
    readonly outputTokens?: number;
    readonly checkerCalls?: number;
}

export interface CoreLfProofAgentBenchmarkAttemptInput {
    readonly benchmarkCase: CoreLfProofAgentBenchmarkCase;
    readonly retrievedPremises?: readonly CoreLfQualifiedSymbol[];
    readonly reportedUsage?: CoreLfProofAgentReportedUsage;
    readonly decision:
        | { readonly kind: 'abstain' }
        | {
            readonly kind: 'patch';
            readonly patch: CoreProofPlanPatch;
        };
}

export interface CoreLfProofAgentBenchmarkAttempt {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.attemptRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly caseId: string;
    readonly caseText: string;
    readonly retrievedPremises: readonly CoreLfQualifiedSymbol[];
    readonly reportedUsage: CoreLfProofAgentReportedUsage | null;
    readonly reportedUsageAuthority:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority;
    readonly decision:
        | { readonly kind: 'abstain' }
        | {
            readonly kind: 'patch';
            readonly patch: CoreProofPlanPatch;
        };
}

const normalizeMetric = (
    value: number | undefined,
    path: string
): number | undefined => {
    if (value === undefined) return undefined;
    if (
        Number.isSafeInteger(value) &&
        value >= 0 &&
        value <= CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.maxReportedMetric
    ) return value;
    return fail(
        'INVALID_LIMIT',
        path,
        'Reported metric must be a bounded nonnegative safe integer'
    );
};

const normalizeUsage = (
    input: CoreLfProofAgentReportedUsage | undefined,
    path: string
): CoreLfProofAgentReportedUsage | null => {
    if (input === undefined) return null;
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_ATTEMPT',
            path,
            'Provider-reported usage must be a data record'
        );
    }
    const usage = {
        wallTimeMs: normalizeMetric(input.wallTimeMs, `${path}.wallTimeMs`),
        inputTokens: normalizeMetric(input.inputTokens, `${path}.inputTokens`),
        outputTokens: normalizeMetric(
            input.outputTokens,
            `${path}.outputTokens`
        ),
        checkerCalls: normalizeMetric(
            input.checkerCalls,
            `${path}.checkerCalls`
        )
    };
    if (Object.values(usage).every(value => value === undefined)) {
        return fail(
            'INVALID_ATTEMPT',
            path,
            'Provider-reported usage must report at least one metric'
        );
    }
    return freezePortable(usage, path);
};

const buildAttempt = (
    caseId: string,
    caseText: string,
    retrievedPremises: readonly CoreLfQualifiedSymbol[],
    reportedUsage: CoreLfProofAgentReportedUsage | null,
    decision: CoreLfProofAgentBenchmarkAttempt['decision']
): CoreLfProofAgentBenchmarkAttempt => freezePortable({
    revision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.attemptRevision,
    profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
    caseId,
    caseText,
    retrievedPremises,
    reportedUsage,
    reportedUsageAuthority:
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority,
    decision
}, 'proofAgentBenchmarkAttempt');

/** Bind one abstention or inert patch to an exact serialized case. */
export function createCoreLfProofAgentBenchmarkAttempt(
    input: CoreLfProofAgentBenchmarkAttemptInput
): CoreLfProofAgentBenchmarkAttempt {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_ATTEMPT',
            'attempt',
            'Benchmark attempt input must be a data record'
        );
    }
    const prepared = prepareCaseArtifact(
        input.benchmarkCase,
        'attempt.benchmarkCase'
    );
    const retrievedPremises = normalizeSymbols(
        input.retrievedPremises ?? [],
        'attempt.retrievedPremises',
        'DUPLICATE_RETRIEVED_PREMISE',
        false
    );
    if (
        input.decision === null ||
        typeof input.decision !== 'object' ||
        (
            input.decision.kind !== 'abstain' &&
            input.decision.kind !== 'patch'
        ) ||
        (
            input.decision.kind === 'patch' &&
            (
                input.decision.patch === null ||
                typeof input.decision.patch !== 'object'
            )
        )
    ) {
        return fail(
            'INVALID_ATTEMPT',
            'attempt.decision',
            'Attempt must abstain or provide one portable patch record'
        );
    }
    const decision = input.decision.kind === 'abstain'
        ? { kind: 'abstain' as const }
        : { kind: 'patch' as const, patch: input.decision.patch };
    return buildAttempt(
        prepared.benchmarkCase.id,
        serializeCoreLfProofAgentBenchmarkCase(prepared.benchmarkCase),
        retrievedPremises,
        normalizeUsage(input.reportedUsage, 'attempt.reportedUsage'),
        decision
    );
}

export const serializeCoreLfProofAgentBenchmarkAttempt = (
    attempt: CoreLfProofAgentBenchmarkAttempt
): string => serializeCoreLfWorkspaceCanonicalJson(
    attempt,
    'proofAgentBenchmarkAttempt'
);

const normalizeAttemptArtifact = (
    attempt: CoreLfProofAgentBenchmarkAttempt,
    path: string
): CoreLfProofAgentBenchmarkAttempt => {
    if (
        attempt === null ||
        typeof attempt !== 'object' ||
        attempt.revision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.attemptRevision ||
        attempt.profileRevision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision ||
        attempt.reportedUsageAuthority !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority
    ) {
        return fail(
            'INVALID_ATTEMPT',
            path,
            'Attempt uses unsupported or malformed profile data'
        );
    }
    assertId(attempt.caseId, `${path}.caseId`);
    if (typeof attempt.caseText !== 'string' || attempt.caseText.length === 0) {
        return fail(
            'INVALID_ATTEMPT',
            `${path}.caseText`,
            'Attempt must bind nonempty exact case text'
        );
    }
    const retrievedPremises = normalizeSymbols(
        attempt.retrievedPremises,
        `${path}.retrievedPremises`,
        'DUPLICATE_RETRIEVED_PREMISE',
        false
    );
    const usage = attempt.reportedUsage === null
        ? null
        : normalizeUsage(attempt.reportedUsage, `${path}.reportedUsage`);
    if (
        attempt.decision === null ||
        typeof attempt.decision !== 'object' ||
        (
            attempt.decision.kind !== 'abstain' &&
            attempt.decision.kind !== 'patch'
        ) ||
        (
            attempt.decision.kind === 'patch' &&
            (
                attempt.decision.patch === null ||
                typeof attempt.decision.patch !== 'object'
            )
        )
    ) {
        return fail(
            'INVALID_ATTEMPT',
            `${path}.decision`,
            'Attempt decision is malformed'
        );
    }
    const normalized = buildAttempt(
        attempt.caseId,
        attempt.caseText,
        retrievedPremises,
        usage,
        attempt.decision.kind === 'abstain'
            ? { kind: 'abstain' }
            : { kind: 'patch', patch: attempt.decision.patch }
    );
    if (
        serializeCoreLfProofAgentBenchmarkAttempt(normalized) !==
            serializeCoreLfProofAgentBenchmarkAttempt(attempt)
    ) {
        return fail(
            'INVALID_ATTEMPT',
            path,
            'Attempt differs from canonical reconstruction'
        );
    }
    return normalized;
};

export interface CoreLfProofAgentProviderIdentity {
    readonly id: string;
    readonly revision: string;
}

export interface CoreLfProofAgentRunLimitOptions {
    readonly wallTimeMs?: number;
    readonly inputTokens?: number;
    readonly outputTokens?: number;
    readonly checkerCalls?: number;
}

export interface CoreLfProofAgentRunLimits {
    readonly wallTimeMs: number | null;
    readonly inputTokens: number | null;
    readonly outputTokens: number | null;
    readonly checkerCalls: number | null;
}

export interface CoreLfProofAgentBenchmarkRunInput {
    readonly revision: string;
    readonly provider: CoreLfProofAgentProviderIdentity;
    readonly allowedProfiles: readonly string[];
    readonly seed: string;
    readonly limits?: CoreLfProofAgentRunLimitOptions;
    readonly attempts: readonly CoreLfProofAgentBenchmarkAttempt[];
}

export interface CoreLfProofAgentBenchmarkRun {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.runRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly runRevision: string;
    readonly provider: CoreLfProofAgentProviderIdentity;
    readonly allowedProfiles: readonly string[];
    readonly seed: string;
    readonly limits: CoreLfProofAgentRunLimits;
    readonly limitEnforcement: 'outer-adapter-not-attested';
    readonly attempts: readonly CoreLfProofAgentBenchmarkAttempt[];
}

const normalizeLimit = (
    value: number | undefined,
    path: string
): number | null => value === undefined
    ? null
    : normalizeMetric(value, path) as number;

const normalizeLimits = (
    input: CoreLfProofAgentRunLimitOptions | undefined
): CoreLfProofAgentRunLimits => {
    if (input !== undefined && (input === null || typeof input !== 'object')) {
        return fail(
            'INVALID_LIMIT',
            'run.limits',
            'Run limits must be a data record'
        );
    }
    const limits = input ?? {};
    return freezePortable({
        wallTimeMs: normalizeLimit(limits.wallTimeMs, 'run.limits.wallTimeMs'),
        inputTokens: normalizeLimit(
            limits.inputTokens,
            'run.limits.inputTokens'
        ),
        outputTokens: normalizeLimit(
            limits.outputTokens,
            'run.limits.outputTokens'
        ),
        checkerCalls: normalizeLimit(
            limits.checkerCalls,
            'run.limits.checkerCalls'
        )
    }, 'proofAgentBenchmarkRunLimits');
};

const normalizeProvider = (
    provider: CoreLfProofAgentProviderIdentity
): CoreLfProofAgentProviderIdentity => {
    if (provider === null || typeof provider !== 'object') {
        return fail(
            'INVALID_PROVIDER',
            'run.provider',
            'Provider identity must be a data record'
        );
    }
    if (
        typeof provider.id !== 'string' ||
        typeof provider.revision !== 'string' ||
        !SAFE_ID.test(provider.id) ||
        !SAFE_REVISION.test(provider.revision)
    ) {
        return fail(
            'INVALID_PROVIDER',
            'run.provider',
            'Provider requires stable ID and revision strings'
        );
    }
    return Object.freeze({ id: provider.id, revision: provider.revision });
};

const normalizeProfiles = (input: readonly string[]): readonly string[] => {
    if (!Array.isArray(input) || input.length === 0) {
        return fail(
            'INVALID_PROVIDER',
            'run.allowedProfiles',
            'Run requires at least one allowed profile ID'
        );
    }
    const seen = new Set<string>();
    const profiles = input.map((profile, index) => {
        if (typeof profile !== 'string' || !SAFE_REVISION.test(profile)) {
            return fail(
                'INVALID_PROVIDER',
                `run.allowedProfiles[${index}]`,
                'Allowed profile ID is not stable and portable'
            );
        }
        if (seen.has(profile)) {
            return fail(
                'INVALID_PROVIDER',
                `run.allowedProfiles[${index}]`,
                'Allowed profile ID occurs more than once'
            );
        }
        seen.add(profile);
        return profile;
    }).sort(compareText);
    return Object.freeze(profiles);
};

/** Normalize one provider run without invoking the provider. */
export function createCoreLfProofAgentBenchmarkRun(
    input: CoreLfProofAgentBenchmarkRunInput
): CoreLfProofAgentBenchmarkRun {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_RUN',
            'run',
            'Benchmark run input must be a data record'
        );
    }
    assertRevision(input.revision, 'run.runRevision');
    if (
        typeof input.seed !== 'string' ||
        !SAFE_SEED.test(input.seed) ||
        input.seed.trim() !== input.seed
    ) {
        return fail(
            'INVALID_RUN',
            'run.seed',
            'Run seed must be a nonempty trimmed printable string'
        );
    }
    if (!Array.isArray(input.attempts)) {
        return fail(
            'INVALID_RUN',
            'run.attempts',
            'Run attempts must be an array'
        );
    }
    if (input.attempts.length >
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.maxCases) {
        return fail(
            'ATTEMPT_LIMIT_EXCEEDED',
            'run.attempts',
            'Run exceeds the finite attempt bound'
        );
    }
    const seen = new Set<string>();
    const attempts = input.attempts.map((attempt, index) => {
        const normalized = normalizeAttemptArtifact(
            attempt,
            `run.attempts[${index}]`
        );
        if (seen.has(normalized.caseId)) {
            return fail(
                'DUPLICATE_ATTEMPT',
                `run.attempts[${index}].caseId`,
                'Run repeats an attempt case ID'
            );
        }
        seen.add(normalized.caseId);
        return normalized;
    }).sort((left, right) => compareText(left.caseId, right.caseId));
    return freezePortable({
        revision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.runRevision,
        profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        runRevision: input.revision,
        provider: normalizeProvider(input.provider),
        allowedProfiles: normalizeProfiles(input.allowedProfiles),
        seed: input.seed,
        limits: normalizeLimits(input.limits),
        limitEnforcement: 'outer-adapter-not-attested' as const,
        attempts,
    }, 'proofAgentBenchmarkRun');
}

export const serializeCoreLfProofAgentBenchmarkRun = (
    run: CoreLfProofAgentBenchmarkRun
): string => serializeCoreLfWorkspaceCanonicalJson(
    run,
    'proofAgentBenchmarkRun'
);

const normalizeRunArtifact = (
    run: CoreLfProofAgentBenchmarkRun
): CoreLfProofAgentBenchmarkRun => {
    if (
        run === null ||
        typeof run !== 'object' ||
        run.revision !== CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.runRevision ||
        run.profileRevision !== CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision ||
        run.limitEnforcement !== 'outer-adapter-not-attested' ||
        run.limits === null ||
        typeof run.limits !== 'object' ||
        !Array.isArray(run.attempts)
    ) {
        return fail(
            'INVALID_RUN',
            'run',
            'Run uses unsupported or malformed profile data'
        );
    }
    const normalized = createCoreLfProofAgentBenchmarkRun({
        revision: run.runRevision,
        provider: run.provider,
        allowedProfiles: run.allowedProfiles,
        seed: run.seed,
        limits: {
            ...(run.limits.wallTimeMs === null
                ? {}
                : { wallTimeMs: run.limits.wallTimeMs }),
            ...(run.limits.inputTokens === null
                ? {}
                : { inputTokens: run.limits.inputTokens }),
            ...(run.limits.outputTokens === null
                ? {}
                : { outputTokens: run.limits.outputTokens }),
            ...(run.limits.checkerCalls === null
                ? {}
                : { checkerCalls: run.limits.checkerCalls })
        },
        attempts: run.attempts
    });
    if (
        serializeCoreLfProofAgentBenchmarkRun(normalized) !==
            serializeCoreLfProofAgentBenchmarkRun(run)
    ) {
        return fail(
            'INVALID_RUN',
            'run',
            'Run differs from canonical reconstruction'
        );
    }
    return normalized;
};

export type CoreLfProofAgentBenchmarkOutcome =
    | 'abstained'
    | 'accepted-complete'
    | 'accepted-incomplete'
    | 'rejected';

export interface CoreLfProofAgentBenchmarkLocalDiagnostic {
    readonly family: 'benchmark';
    readonly code:
        | 'INACCESSIBLE_RETRIEVAL'
        | 'PATCH_GOAL_MISMATCH'
        | 'PLAN_NODE_LIMIT_EXCEEDED';
    readonly path: string;
}

export interface CoreLfProofAgentBenchmarkPatchDiagnostic {
    readonly family: 'proof-plan-patch';
    readonly code: string;
    readonly path: string;
}

export type CoreLfProofAgentBenchmarkDiagnostic =
    | CoreLfProofAgentBenchmarkLocalDiagnostic
    | CoreLfProofAgentBenchmarkPatchDiagnostic
    | CoreLfProofReplayDiagnostic;

export interface CoreLfProofAgentRetrievalMetrics {
    readonly relevantPremiseCount: number;
    readonly retrievedPremiseCount: number;
    readonly relevantRetrievedPremiseCount: number;
    readonly irrelevantRetrievedPremiseCount: number;
    readonly firstRelevantRank: number | null;
}

export interface CoreLfProofAgentPlanMetrics {
    readonly initialPlanNodeCount: number;
    readonly replacementPlanNodeCount: number | null;
    readonly resultPlanNodeCount: number | null;
}

export interface CoreLfProofAgentReplayMetrics {
    readonly baselineProofReplayCount: 1;
    readonly candidateProofReplayCount: 0 | 1;
}

export type CoreLfProofAgentReportedLimitStatus =
    | 'unreported'
    | 'reported-within-limits'
    | 'reported-limit-exceeded';

interface CoreLfProofAgentBenchmarkResultBase {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.resultRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly caseId: string;
    readonly outcome: CoreLfProofAgentBenchmarkOutcome;
    readonly retrieval: CoreLfProofAgentRetrievalMetrics;
    readonly plan: CoreLfProofAgentPlanMetrics;
    readonly replays: CoreLfProofAgentReplayMetrics;
    readonly reportedUsage: CoreLfProofAgentReportedUsage | null;
    readonly reportedUsageAuthority:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority;
    readonly reportedLimitStatus: CoreLfProofAgentReportedLimitStatus;
    readonly artifactCurrent: false;
    readonly materializesUpdatedSource: false;
}

export interface CoreLfProofAgentBenchmarkAbstainedResult
extends CoreLfProofAgentBenchmarkResultBase {
    readonly outcome: 'abstained';
}

export interface CoreLfProofAgentBenchmarkAcceptedResult
extends CoreLfProofAgentBenchmarkResultBase {
    readonly outcome: 'accepted-complete' | 'accepted-incomplete';
    readonly state: CoreProofPlanStateSnapshot;
    readonly goalGraph: CoreProofGoalCouplingGraph;
}

export interface CoreLfProofAgentBenchmarkRejectedResult
extends CoreLfProofAgentBenchmarkResultBase {
    readonly outcome: 'rejected';
    readonly diagnostic: CoreLfProofAgentBenchmarkDiagnostic;
}

export type CoreLfProofAgentBenchmarkResult =
    | CoreLfProofAgentBenchmarkAbstainedResult
    | CoreLfProofAgentBenchmarkAcceptedResult
    | CoreLfProofAgentBenchmarkRejectedResult;

const retrievalMetrics = (
    benchmarkCase: CoreLfProofAgentBenchmarkCase,
    attempt: CoreLfProofAgentBenchmarkAttempt
): CoreLfProofAgentRetrievalMetrics => {
    const relevant = new Set(benchmarkCase.relevantPremises.map(symbolKey));
    const relevantRanks = attempt.retrievedPremises
        .map((symbol, index) => relevant.has(symbolKey(symbol))
            ? index + 1
            : undefined
        )
        .filter((rank): rank is number => rank !== undefined);
    return {
        relevantPremiseCount: relevant.size,
        retrievedPremiseCount: attempt.retrievedPremises.length,
        relevantRetrievedPremiseCount: relevantRanks.length,
        irrelevantRetrievedPremiseCount:
            attempt.retrievedPremises.length - relevantRanks.length,
        firstRelevantRank: relevantRanks[0] ?? null
    };
};

const reportedLimitStatus = (
    usage: CoreLfProofAgentReportedUsage | null,
    limits: CoreLfProofAgentRunLimits
): CoreLfProofAgentReportedLimitStatus => {
    if (usage === null) return 'unreported';
    const keys = [
        'wallTimeMs',
        'inputTokens',
        'outputTokens',
        'checkerCalls'
    ] as const;
    return keys.some(key =>
        usage[key] !== undefined &&
        limits[key] !== null &&
        usage[key]! > limits[key]!
    )
        ? 'reported-limit-exceeded'
        : 'reported-within-limits';
};

const resultBase = (
    prepared: PreparedCase,
    attempt: CoreLfProofAgentBenchmarkAttempt,
    limits: CoreLfProofAgentRunLimits,
    candidateProofReplayCount: 0 | 1,
    replacementPlanNodeCount: number | null,
    resultPlanNodeCount: number | null
): Omit<CoreLfProofAgentBenchmarkResultBase, 'outcome'> => ({
    revision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.resultRevision,
    profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
    caseId: prepared.benchmarkCase.id,
    retrieval: retrievalMetrics(prepared.benchmarkCase, attempt),
    plan: {
        initialPlanNodeCount:
            prepared.benchmarkCase.initial.planNodeCount,
        replacementPlanNodeCount,
        resultPlanNodeCount
    },
    replays: {
        baselineProofReplayCount: 1,
        candidateProofReplayCount
    },
    reportedUsage: attempt.reportedUsage,
    reportedUsageAuthority:
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority,
    reportedLimitStatus: reportedLimitStatus(attempt.reportedUsage, limits),
    artifactCurrent: false,
    materializesUpdatedSource: false
});

const rejectedResult = (
    prepared: PreparedCase,
    attempt: CoreLfProofAgentBenchmarkAttempt,
    limits: CoreLfProofAgentRunLimits,
    diagnostic: CoreLfProofAgentBenchmarkDiagnostic,
    candidateProofReplayCount: 0 | 1,
    replacementPlanNodeCount: number | null,
    resultPlanNodeCount: number | null
): CoreLfProofAgentBenchmarkRejectedResult => freezePortable({
    ...resultBase(
        prepared,
        attempt,
        limits,
        candidateProofReplayCount,
        replacementPlanNodeCount,
        resultPlanNodeCount
    ),
    outcome: 'rejected' as const,
    diagnostic
}, 'proofAgentBenchmarkResult');

const evaluateAttempt = (
    prepared: PreparedCase,
    attempt: CoreLfProofAgentBenchmarkAttempt,
    limits: CoreLfProofAgentRunLimits
): CoreLfProofAgentBenchmarkResult => {
    if (
        attempt.caseText !==
            serializeCoreLfProofAgentBenchmarkCase(prepared.benchmarkCase)
    ) {
        return fail(
            'STALE_ATTEMPT',
            `run.attempts.${attempt.caseId}.caseText`,
            'Attempt targets a different benchmark case revision'
        );
    }
    const inaccessibleIndex = attempt.retrievedPremises.findIndex(symbol =>
        prepared.premiseIndex.resolve(symbol) === undefined
    );
    if (inaccessibleIndex >= 0) {
        return rejectedResult(
            prepared,
            attempt,
            limits,
            {
                family: 'benchmark',
                code: 'INACCESSIBLE_RETRIEVAL',
                path: `attempt.retrievedPremises[${inaccessibleIndex}]`
            },
            0,
            null,
            null
        );
    }
    if (attempt.decision.kind === 'abstain') {
        return freezePortable({
            ...resultBase(prepared, attempt, limits, 0, null, null),
            outcome: 'abstained' as const
        }, 'proofAgentBenchmarkResult');
    }
    if (attempt.decision.patch.goalId !== prepared.benchmarkCase.goalId) {
        return rejectedResult(
            prepared,
            attempt,
            limits,
            {
                family: 'benchmark',
                code: 'PATCH_GOAL_MISMATCH',
                path: 'attempt.decision.patch.goalId'
            },
            0,
            null,
            null
        );
    }
    let patchedPlan: CoreProofPlan;
    try {
        patchedPlan = applyCoreProofPlanPatch(
            prepared.proof.plan,
            attempt.decision.patch
        );
    } catch (error: unknown) {
        if (error instanceof CoreProofPlanPatchError) {
            return rejectedResult(
                prepared,
                attempt,
                limits,
                {
                    family: 'proof-plan-patch',
                    code: error.code,
                    path: error.path
                },
                0,
                null,
                null
            );
        }
        throw error;
    }
    let replacementNodes: number;
    let resultNodes: number;
    try {
        replacementNodes = planNodeCount(
            attempt.decision.patch.replacement,
            'attempt.decision.patch.replacement'
        );
        resultNodes = planNodeCount(patchedPlan, 'attempt.resultPlan');
    } catch (error: unknown) {
        if (
            error instanceof CoreLfProofAgentBenchmarkError &&
            error.code === 'PLAN_NODE_LIMIT_EXCEEDED'
        ) {
            return rejectedResult(
                prepared,
                attempt,
                limits,
                {
                    family: 'benchmark',
                    code: 'PLAN_NODE_LIMIT_EXCEEDED',
                    path: error.path
                },
                0,
                null,
                null
            );
        }
        throw error;
    }
    let compilation: ReturnType<typeof compileCoreLfWorkspaceProofDocument>;
    try {
        compilation = compileCoreLfWorkspaceProofDocument(
            prepared.workspace,
            {
                ...prepared.proof,
                plan: patchedPlan
            }
        );
    } catch (error: unknown) {
        const diagnostic = projectCoreLfProofReplayDiagnostic(error);
        if (diagnostic === undefined) {
            return fail(
                'UNSUPPORTED_REPLAY_ERROR',
                `run.attempts.${attempt.caseId}`,
                'Patched proof replay raised an unclassified error',
                error
            );
        }
        return rejectedResult(
            prepared,
            attempt,
            limits,
            diagnostic,
            1,
            replacementNodes,
            resultNodes
        );
    }
    const state = compilation.artifact.proofArtifact.state;
    return freezePortable({
        ...resultBase(
            prepared,
            attempt,
            limits,
            1,
            replacementNodes,
            resultNodes
        ),
        outcome: state.status === 'complete'
            ? 'accepted-complete' as const
            : 'accepted-incomplete' as const,
        state,
        goalGraph: compilation.proofCompilation.goalGraph
    }, 'proofAgentBenchmarkResult');
};

interface MetricTotal {
    readonly reportedCases: number;
    readonly total: number;
}

export interface CoreLfProofAgentBenchmarkMetrics {
    readonly cases: number;
    readonly outcomes: {
        readonly abstained: number;
        readonly acceptedComplete: number;
        readonly acceptedIncomplete: number;
        readonly rejected: number;
    };
    readonly replays: {
        readonly baselineProofReplays: number;
        readonly candidateProofReplays: number;
    };
    readonly planNodes: {
        readonly initialTotal: number;
        readonly replacementReportedCases: number;
        readonly replacementTotal: number;
        readonly resultReportedCases: number;
        readonly resultTotal: number;
    };
    readonly retrieval: {
        readonly relevantPremises: number;
        readonly retrievedPremises: number;
        readonly relevantRetrievedPremises: number;
        readonly irrelevantRetrievedPremises: number;
        readonly casesWithRelevantPremises: number;
        readonly casesWithRelevantRetrievedPremises: number;
        readonly firstRelevantRankTotal: number;
    };
    readonly reportedUsage: {
        readonly authority:
            typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority;
        readonly wallTimeMs: MetricTotal;
        readonly inputTokens: MetricTotal;
        readonly outputTokens: MetricTotal;
        readonly checkerCalls: MetricTotal;
        readonly withinLimits: number;
        readonly exceededLimits: number;
        readonly unreported: number;
    };
}

const safeSum = (left: number, right: number, path: string): number => {
    const sum = left + right;
    if (Number.isSafeInteger(sum)) return sum;
    return fail(
        'METRIC_OVERFLOW',
        path,
        'Benchmark metric aggregation exceeded safe integer range'
    );
};

const metricTotal = (
    results: readonly CoreLfProofAgentBenchmarkResult[],
    key: keyof CoreLfProofAgentReportedUsage
): MetricTotal => results.reduce<MetricTotal>((total, result) => {
    const value = result.reportedUsage?.[key];
    return value === undefined
        ? total
        : {
            reportedCases: total.reportedCases + 1,
            total: safeSum(
                total.total,
                value,
                `metrics.reportedUsage.${key}`
            )
        };
}, { reportedCases: 0, total: 0 });

const aggregateMetrics = (
    results: readonly CoreLfProofAgentBenchmarkResult[]
): CoreLfProofAgentBenchmarkMetrics => {
    const count = (outcome: CoreLfProofAgentBenchmarkOutcome): number =>
        results.filter(result => result.outcome === outcome).length;
    const sum = (
        values: readonly number[],
        path: string
    ): number => values.reduce(
        (total, value) => safeSum(total, value, path),
        0
    );
    const replacements = results.map(result =>
        result.plan.replacementPlanNodeCount
    ).filter((value): value is number => value !== null);
    const resultPlans = results.map(result =>
        result.plan.resultPlanNodeCount
    ).filter((value): value is number => value !== null);
    const firstRanks = results.map(result =>
        result.retrieval.firstRelevantRank
    ).filter((value): value is number => value !== null);
    return {
        cases: results.length,
        outcomes: {
            abstained: count('abstained'),
            acceptedComplete: count('accepted-complete'),
            acceptedIncomplete: count('accepted-incomplete'),
            rejected: count('rejected')
        },
        replays: {
            baselineProofReplays: sum(
                results.map(result =>
                    result.replays.baselineProofReplayCount
                ),
                'metrics.replays.baseline'
            ),
            candidateProofReplays: sum(
                results.map(result =>
                    result.replays.candidateProofReplayCount
                ),
                'metrics.replays.candidate'
            )
        },
        planNodes: {
            initialTotal: sum(
                results.map(result => result.plan.initialPlanNodeCount),
                'metrics.planNodes.initial'
            ),
            replacementReportedCases: replacements.length,
            replacementTotal: sum(
                replacements,
                'metrics.planNodes.replacement'
            ),
            resultReportedCases: resultPlans.length,
            resultTotal: sum(resultPlans, 'metrics.planNodes.result')
        },
        retrieval: {
            relevantPremises: sum(
                results.map(result =>
                    result.retrieval.relevantPremiseCount
                ),
                'metrics.retrieval.relevant'
            ),
            retrievedPremises: sum(
                results.map(result =>
                    result.retrieval.retrievedPremiseCount
                ),
                'metrics.retrieval.retrieved'
            ),
            relevantRetrievedPremises: sum(
                results.map(result =>
                    result.retrieval.relevantRetrievedPremiseCount
                ),
                'metrics.retrieval.relevantRetrieved'
            ),
            irrelevantRetrievedPremises: sum(
                results.map(result =>
                    result.retrieval.irrelevantRetrievedPremiseCount
                ),
                'metrics.retrieval.irrelevantRetrieved'
            ),
            casesWithRelevantPremises: results.filter(result =>
                result.retrieval.relevantPremiseCount > 0
            ).length,
            casesWithRelevantRetrievedPremises: firstRanks.length,
            firstRelevantRankTotal: sum(
                firstRanks,
                'metrics.retrieval.firstRelevantRank'
            )
        },
        reportedUsage: {
            authority:
                CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE
                    .reportedUsageAuthority,
            wallTimeMs: metricTotal(results, 'wallTimeMs'),
            inputTokens: metricTotal(results, 'inputTokens'),
            outputTokens: metricTotal(results, 'outputTokens'),
            checkerCalls: metricTotal(results, 'checkerCalls'),
            withinLimits: results.filter(result =>
                result.reportedLimitStatus === 'reported-within-limits'
            ).length,
            exceededLimits: results.filter(result =>
                result.reportedLimitStatus === 'reported-limit-exceeded'
            ).length,
            unreported: results.filter(result =>
                result.reportedLimitStatus === 'unreported'
            ).length
        }
    };
};

export interface CoreLfProofAgentBenchmarkReport {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly suite: CoreLfProofAgentBenchmarkSuite;
    readonly run: CoreLfProofAgentBenchmarkRun;
    readonly results: readonly CoreLfProofAgentBenchmarkResult[];
    readonly metrics: CoreLfProofAgentBenchmarkMetrics;
    readonly meaning: 'attempts-evaluated-not-source-committed';
    readonly ratiosDerived: false;
    readonly artifactCurrent: false;
    readonly materializesUpdatedSource: false;
}

export interface CoreLfProofAgentBenchmarkEvaluationInput {
    readonly suite: CoreLfProofAgentBenchmarkSuite;
    readonly run: CoreLfProofAgentBenchmarkRun;
}

/** Freshly score one complete provider run without invoking that provider. */
export function evaluateCoreLfProofAgentBenchmarkRun(
    input: CoreLfProofAgentBenchmarkEvaluationInput
): CoreLfProofAgentBenchmarkReport {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_RUN',
            'evaluation',
            'Benchmark evaluation input must be a data record'
        );
    }
    const preparedSuite = prepareSuiteArtifact(input.suite);
    const run = normalizeRunArtifact(input.run);
    const casesById = new Map(preparedSuite.cases.map(prepared =>
        [prepared.benchmarkCase.id, prepared]
    ));
    for (const attempt of run.attempts) {
        if (casesById.has(attempt.caseId)) continue;
        return fail(
            'UNKNOWN_ATTEMPT_CASE',
            `run.attempts.${attempt.caseId}`,
            'Run contains an attempt for an unknown suite case'
        );
    }
    const attemptsById = new Map(run.attempts.map(attempt =>
        [attempt.caseId, attempt]
    ));
    const results = preparedSuite.cases.map(prepared => {
        const attempt = attemptsById.get(prepared.benchmarkCase.id);
        if (attempt !== undefined) {
            return evaluateAttempt(prepared, attempt, run.limits);
        }
        return fail(
            'MISSING_ATTEMPT',
            `run.attempts.${prepared.benchmarkCase.id}`,
            'Run has no attempt for a suite case'
        );
    });
    return freezePortable({
        revision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportRevision,
        profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        suite: preparedSuite.suite,
        run,
        results,
        metrics: aggregateMetrics(results),
        meaning: 'attempts-evaluated-not-source-committed' as const,
        ratiosDerived: false as const,
        artifactCurrent: false as const,
        materializesUpdatedSource: false as const
    }, 'proofAgentBenchmarkReport');
}

export const serializeCoreLfProofAgentBenchmarkReport = (
    report: CoreLfProofAgentBenchmarkReport
): string => serializeCoreLfWorkspaceCanonicalJson(
    report,
    'proofAgentBenchmarkReport'
);
