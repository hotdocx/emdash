/**
 * Strict browser-safe interchange for immutable 12A proof-agent artifacts.
 *
 * The benchmark module remains the semantic authority. This module only
 * accepts exact canonical JSON, reconstructs artifacts through the existing
 * public 12A constructors/evaluator, and rejects unsupported fields or stale
 * derived data. It performs no I/O, model call, timing, hashing, or source
 * persistence.
 */

import {
    CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE,
    CoreLfProofAgentBenchmarkAttempt,
    CoreLfProofAgentBenchmarkCase,
    CoreLfProofAgentBenchmarkReport,
    CoreLfProofAgentBenchmarkRun,
    CoreLfProofAgentBenchmarkSuite,
    CoreLfProofAgentReportedUsage,
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
} from './lf_proof_agent_benchmark';
import {
    CoreLfQualifiedSymbol
} from './lf_transfer';
import {
    CoreProofPlan
} from './proof_plan';
import {
    CORE_PROOF_PLAN_PATCH_PROFILE,
    createCoreProofPlanHoleReplacement
} from './proof_plan_patch';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-agent-interchange-v1' as const,
    benchmarkProfileRevision:
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
    acceptedArtifacts: Object.freeze([
        'case',
        'suite',
        'attempt',
        'run',
        'report'
    ] as const),
    revisionPolicy: 'exact-closed-revisions' as const,
    unknownFieldPolicy: 'reject' as const,
    textPolicy: 'exact-canonical-newline-terminated-json' as const,
    staleArtifactPolicy: 'reject-before-use' as const,
    reportPolicy: 'fresh-12a-evaluation-exact-match' as const,
    deeplyFrozen: true as const,
    changesBenchmarkSemantics: false as const,
    performsIo: false as const,
    invokesModel: false as const,
    invokesLambdapi: false as const,
    computesCryptographicHashes: false as const,
    persistsSource: false as const,
    retainsSessionState: false as const,
    nodeBuiltinDependency: false as const
});

export type CoreLfProofAgentInterchangeErrorCode =
    | 'INVALID_TEXT'
    | 'INVALID_ARTIFACT'
    | 'UNSUPPORTED_REVISION'
    | 'STALE_ARTIFACT'
    | 'NONCANONICAL_TEXT';

export class CoreLfProofAgentInterchangeError extends Error {
    constructor(
        public readonly code: CoreLfProofAgentInterchangeErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfProofAgentInterchangeError';
    }
}

const fail = (
    code: CoreLfProofAgentInterchangeErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreLfProofAgentInterchangeError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

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
): Record<string, unknown> => plainRecord(value)
    ? value
    : fail('INVALID_ARTIFACT', path, 'Expected a plain data record');

const arrayAt = (value: unknown, path: string): readonly unknown[] =>
    Array.isArray(value)
        ? value
        : fail('INVALID_ARTIFACT', path, 'Expected an array');

const assertKeys = (
    record: Record<string, unknown>,
    required: readonly string[],
    path: string,
    optional: readonly string[] = []
): void => {
    const actual = Object.keys(record).sort(compareText);
    const allowed = new Set([...required, ...optional]);
    const unsupported = actual.find(key => !allowed.has(key));
    if (unsupported !== undefined) {
        fail(
            'INVALID_ARTIFACT',
            `${path}.${unsupported}`,
            'Artifact contains an unsupported field'
        );
    }
    const missing = required.find(key => !actual.includes(key));
    if (missing !== undefined) {
        fail(
            'INVALID_ARTIFACT',
            `${path}.${missing}`,
            'Artifact is missing a required field'
        );
    }
};

const assertLiteral = <T extends string | boolean>(
    value: unknown,
    expected: T,
    path: string
): T => value === expected
    ? expected
    : fail(
        'INVALID_ARTIFACT',
        path,
        `Expected exact literal ${JSON.stringify(expected)}`
    );

const assertRevision = <T extends string>(
    value: unknown,
    expected: T,
    path: string
): T => value === expected
    ? expected
    : fail(
        'UNSUPPORTED_REVISION',
        path,
        `Expected supported revision '${expected}'`
    );

const stringAt = (value: unknown, path: string): string =>
    typeof value === 'string'
        ? value
        : fail('INVALID_ARTIFACT', path, 'Expected a string');

const numberAt = (value: unknown, path: string): number =>
    typeof value === 'number' && Number.isFinite(value)
        ? value
        : fail('INVALID_ARTIFACT', path, 'Expected a finite number');

const canonicalValue = (value: unknown, path: string): string => {
    try {
        return serializeCoreLfWorkspaceCanonicalJson(value, path);
    } catch (error: unknown) {
        return fail(
            'INVALID_ARTIFACT',
            path,
            'Artifact contains nonportable data',
            error
        );
    }
};

const assertCanonicalReconstruction = (
    supplied: unknown,
    reconstructedText: string,
    path: string
): void => {
    if (canonicalValue(supplied, `${path}.supplied`) === reconstructedText) {
        return;
    }
    fail(
        'STALE_ARTIFACT',
        path,
        'Artifact differs from fresh canonical reconstruction'
    );
};

const wrapArtifact = <T>(path: string, action: () => T): T => {
    try {
        return action();
    } catch (error: unknown) {
        if (error instanceof CoreLfProofAgentInterchangeError) throw error;
        return fail(
            'INVALID_ARTIFACT',
            path,
            'Artifact could not be reconstructed by the 12A authority',
            error
        );
    }
};

const assertPoint = (value: unknown, path: string): void => {
    const record = recordAt(value, path);
    assertKeys(record, ['line', 'column'], path);
    numberAt(record.line, `${path}.line`);
    numberAt(record.column, `${path}.column`);
};

const assertProvenance = (value: unknown, path: string): void => {
    const record = recordAt(value, path);
    assertKeys(record, ['origin', 'detail'], path, ['span']);
    stringAt(record.origin, `${path}.origin`);
    stringAt(record.detail, `${path}.detail`);
    if (record.span === undefined) return;
    const span = recordAt(record.span, `${path}.span`);
    assertKeys(span, ['file', 'start', 'end'], `${path}.span`);
    stringAt(span.file, `${path}.span.file`);
    assertPoint(span.start, `${path}.span.start`);
    assertPoint(span.end, `${path}.span.end`);
};

const assertBinderMode = (value: unknown, path: string): void => {
    const record = recordAt(value, path);
    assertKeys(record, ['plicity', 'variation'], path);
    stringAt(record.plicity, `${path}.plicity`);
    stringAt(record.variation, `${path}.variation`);
};

const assertKernelArgument = (value: unknown, path: string): void => {
    const record = recordAt(value, path);
    assertKeys(record, ['plicity', 'value', 'provenance'], path);
    stringAt(record.plicity, `${path}.plicity`);
    assertKernelExpression(record.value, `${path}.value`);
    assertProvenance(record.provenance, `${path}.provenance`);
};

const assertKernelBinder = (value: unknown, path: string): void => {
    const record = recordAt(value, path);
    assertKeys(record, ['name', 'type', 'mode', 'provenance'], path);
    stringAt(record.name, `${path}.name`);
    assertKernelExpression(record.type, `${path}.type`);
    assertBinderMode(record.mode, `${path}.mode`);
    assertProvenance(record.provenance, `${path}.provenance`);
};

const assertKernelExpression = (value: unknown, path: string): void => {
    const record = recordAt(value, path);
    const tag = stringAt(record.tag, `${path}.tag`);
    switch (tag) {
        case 'universe':
            assertKeys(record, ['tag', 'provenance'], path);
            break;
        case 'reference':
            assertKeys(
                record,
                ['tag', 'namespace', 'name', 'provenance'],
                path
            );
            assertLiteral(record.namespace, 'free', `${path}.namespace`);
            stringAt(record.name, `${path}.name`);
            break;
        case 'bound':
            assertKeys(record, ['tag', 'index', 'provenance'], path);
            numberAt(record.index, `${path}.index`);
            break;
        case 'application':
            assertKeys(
                record,
                ['tag', 'owner', 'arguments', 'provenance'],
                path
            );
            stringAt(record.owner, `${path}.owner`);
            arrayAt(record.arguments, `${path}.arguments`).forEach(
                (argument, index) => assertKernelArgument(
                    argument,
                    `${path}.arguments[${index}]`
                )
            );
            break;
        case 'call':
            assertKeys(
                record,
                ['tag', 'callee', 'arguments', 'provenance'],
                path
            );
            assertKernelExpression(record.callee, `${path}.callee`);
            arrayAt(record.arguments, `${path}.arguments`).forEach(
                (argument, index) => assertKernelArgument(
                    argument,
                    `${path}.arguments[${index}]`
                )
            );
            break;
        case 'pi':
        case 'lambda':
            assertKeys(
                record,
                ['tag', 'binder', 'body', 'provenance'],
                path
            );
            assertKernelBinder(record.binder, `${path}.binder`);
            assertKernelExpression(record.body, `${path}.body`);
            break;
        case 'meta':
            return fail(
                'INVALID_ARTIFACT',
                `${path}.tag`,
                'Portable proof-plan patches cannot contain metavariables'
            );
        default:
            return fail(
                'INVALID_ARTIFACT',
                `${path}.tag`,
                `Unsupported Core expression tag '${tag}'`
            );
    }
    assertProvenance(record.provenance, `${path}.provenance`);
};

const assertProofPlan = (value: unknown, path: string): CoreProofPlan => {
    const record = recordAt(value, path);
    const tag = stringAt(record.tag, `${path}.tag`);
    switch (tag) {
        case 'exact':
            assertKeys(
                record,
                ['tag', 'provenance', 'solution'],
                path,
                ['id']
            );
            assertKernelExpression(record.solution, `${path}.solution`);
            break;
        case 'intro':
            assertKeys(
                record,
                ['tag', 'provenance', 'body'],
                path,
                ['id', 'name']
            );
            if (record.name !== undefined) {
                stringAt(record.name, `${path}.name`);
            }
            assertProofPlan(record.body, `${path}.body`);
            break;
        case 'apply':
            assertKeys(
                record,
                ['tag', 'provenance', 'callee', 'premises'],
                path,
                ['id']
            );
            assertKernelExpression(record.callee, `${path}.callee`);
            arrayAt(record.premises, `${path}.premises`).forEach(
                (premise, index) => assertProofPlan(
                    premise,
                    `${path}.premises[${index}]`
                )
            );
            break;
        case 'have': {
            assertKeys(
                record,
                ['tag', 'provenance', 'binding', 'proof', 'body'],
                path,
                ['id']
            );
            assertKernelBinder(record.binding, `${path}.binding`);
            assertProofPlan(record.proof, `${path}.proof`);
            assertProofPlan(record.body, `${path}.body`);
            break;
        }
        case 'hole': {
            assertKeys(
                record,
                ['tag', 'provenance', 'goalId'],
                path,
                ['id', 'expectation']
            );
            stringAt(record.goalId, `${path}.goalId`);
            if (record.expectation !== undefined) {
                const expectation = recordAt(
                    record.expectation,
                    `${path}.expectation`
                );
                assertKeys(
                    expectation,
                    [],
                    `${path}.expectation`,
                    ['contextDepth', 'target']
                );
                if (expectation.contextDepth !== undefined) {
                    numberAt(
                        expectation.contextDepth,
                        `${path}.expectation.contextDepth`
                    );
                }
                if (expectation.target !== undefined) {
                    assertKernelExpression(
                        expectation.target,
                        `${path}.expectation.target`
                    );
                }
            }
            break;
        }
        default:
            return fail(
                'INVALID_ARTIFACT',
                `${path}.tag`,
                `Unsupported proof-plan tag '${tag}'`
            );
    }
    if (record.id !== undefined) stringAt(record.id, `${path}.id`);
    assertProvenance(record.provenance, `${path}.provenance`);
    return value as CoreProofPlan;
};

const symbolAt = (value: unknown, path: string): CoreLfQualifiedSymbol => {
    const record = recordAt(value, path);
    assertKeys(record, ['moduleId', 'name'], path);
    return {
        moduleId: stringAt(record.moduleId, `${path}.moduleId`),
        name: stringAt(record.name, `${path}.name`)
    };
};

const parseCaseValue = (
    value: unknown,
    path: string
): CoreLfProofAgentBenchmarkCase => wrapArtifact(path, () => {
    const record = recordAt(value, path);
    assertKeys(record, [
        'revision',
        'profileRevision',
        'maintenanceProfileRevision',
        'id',
        'previousSource',
        'currentSource',
        'proof',
        'goalId',
        'settings',
        'precondition',
        'initial',
        'relevantPremises',
        'relevantPremiseAuthority',
        'suppliedHashesRecomputed'
    ], path);
    assertRevision(
        record.revision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.caseRevision,
        `${path}.revision`
    );
    assertRevision(
        record.profileRevision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        `${path}.profileRevision`
    );
    assertRevision(
        record.maintenanceProfileRevision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.maintenanceProfileRevision,
        `${path}.maintenanceProfileRevision`
    );
    const proof = recordAt(record.proof, `${path}.proof`);
    assertKeys(proof, ['moduleId', 'declarationId'], `${path}.proof`);
    const settings = recordAt(record.settings, `${path}.settings`);
    assertKeys(
        settings,
        ['expressionVisitLimit', 'premiseIndex'],
        `${path}.settings`
    );
    numberAt(
        settings.expressionVisitLimit,
        `${path}.settings.expressionVisitLimit`
    );
    const premiseIndex = recordAt(
        settings.premiseIndex,
        `${path}.settings.premiseIndex`
    );
    assertKeys(
        premiseIndex,
        ['typeVisitLimit', 'normalizationStepLimit'],
        `${path}.settings.premiseIndex`
    );
    const precondition = recordAt(record.precondition, `${path}.precondition`);
    assertKeys(
        precondition,
        ['previousSourceText', 'currentSourceText', 'inspectionText'],
        `${path}.precondition`
    );
    const initial = recordAt(record.initial, `${path}.initial`);
    assertKeys(
        initial,
        ['state', 'goalGraph', 'planNodeCount'],
        `${path}.initial`
    );
    const relevantPremises = arrayAt(
        record.relevantPremises,
        `${path}.relevantPremises`
    ).map((symbol, index) => symbolAt(
        symbol,
        `${path}.relevantPremises[${index}]`
    ));
    const reconstructed = createCoreLfProofAgentBenchmarkCase({
        id: stringAt(record.id, `${path}.id`),
        previousSource: record.previousSource as
            CoreLfProofAgentBenchmarkCase['previousSource'],
        currentSource: record.currentSource as
            CoreLfProofAgentBenchmarkCase['currentSource'],
        proof: {
            moduleId: stringAt(proof.moduleId, `${path}.proof.moduleId`),
            declarationId: stringAt(
                proof.declarationId,
                `${path}.proof.declarationId`
            )
        },
        goalId: stringAt(record.goalId, `${path}.goalId`),
        diffOptions: {
            expressionVisitLimit: numberAt(
                settings.expressionVisitLimit,
                `${path}.settings.expressionVisitLimit`
            )
        },
        premiseIndexOptions: {
            typeVisitLimit: numberAt(
                premiseIndex.typeVisitLimit,
                `${path}.settings.premiseIndex.typeVisitLimit`
            ),
            normalizationStepLimit: numberAt(
                premiseIndex.normalizationStepLimit,
                `${path}.settings.premiseIndex.normalizationStepLimit`
            )
        },
        relevantPremises
    });
    assertLiteral(
        record.relevantPremiseAuthority,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.relevantPremiseAuthority,
        `${path}.relevantPremiseAuthority`
    );
    assertLiteral(
        record.suppliedHashesRecomputed,
        false,
        `${path}.suppliedHashesRecomputed`
    );
    assertCanonicalReconstruction(
        value,
        serializeCoreLfProofAgentBenchmarkCase(reconstructed),
        path
    );
    return deepFreeze(reconstructed);
});

const parseSuiteValue = (
    value: unknown,
    path: string
): CoreLfProofAgentBenchmarkSuite => wrapArtifact(path, () => {
    const record = recordAt(value, path);
    assertKeys(
        record,
        ['revision', 'profileRevision', 'suiteRevision', 'cases'],
        path
    );
    assertRevision(
        record.revision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.suiteRevision,
        `${path}.revision`
    );
    assertRevision(
        record.profileRevision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        `${path}.profileRevision`
    );
    const cases = arrayAt(record.cases, `${path}.cases`).map(
        (benchmarkCase, index) => parseCaseValue(
            benchmarkCase,
            `${path}.cases[${index}]`
        )
    );
    const reconstructed = createCoreLfProofAgentBenchmarkSuite({
        revision: stringAt(record.suiteRevision, `${path}.suiteRevision`),
        cases
    });
    assertCanonicalReconstruction(
        value,
        serializeCoreLfProofAgentBenchmarkSuite(reconstructed),
        path
    );
    return deepFreeze(reconstructed);
});

const usageAt = (
    value: unknown,
    path: string
): CoreLfProofAgentReportedUsage | undefined => {
    if (value === null) return undefined;
    const record = recordAt(value, path);
    assertKeys(record, [], path, [
        'wallTimeMs',
        'inputTokens',
        'outputTokens',
        'checkerCalls'
    ]);
    const usage: {
        wallTimeMs?: number;
        inputTokens?: number;
        outputTokens?: number;
        checkerCalls?: number;
    } = {};
    const keys = [
        'wallTimeMs',
        'inputTokens',
        'outputTokens',
        'checkerCalls'
    ] as const;
    keys.forEach(key => {
        if (record[key] !== undefined) {
            usage[key] = numberAt(record[key], `${path}.${key}`);
        }
    });
    return usage;
};

const parseAttemptValue = (
    value: unknown,
    path: string
): CoreLfProofAgentBenchmarkAttempt => wrapArtifact(path, () => {
    const record = recordAt(value, path);
    assertKeys(record, [
        'revision',
        'profileRevision',
        'caseId',
        'caseText',
        'retrievedPremises',
        'reportedUsage',
        'reportedUsageAuthority',
        'decision'
    ], path);
    assertRevision(
        record.revision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.attemptRevision,
        `${path}.revision`
    );
    assertRevision(
        record.profileRevision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        `${path}.profileRevision`
    );
    const caseText = stringAt(record.caseText, `${path}.caseText`);
    const benchmarkCase = parseCoreLfProofAgentBenchmarkCaseText(caseText);
    const retrievedPremises = arrayAt(
        record.retrievedPremises,
        `${path}.retrievedPremises`
    ).map((symbol, index) => symbolAt(
        symbol,
        `${path}.retrievedPremises[${index}]`
    ));
    const decision = recordAt(record.decision, `${path}.decision`);
    const kind = stringAt(decision.kind, `${path}.decision.kind`);
    const reconstructedDecision = kind === 'abstain'
        ? (() => {
            assertKeys(decision, ['kind'], `${path}.decision`);
            return { kind: 'abstain' as const };
        })()
        : kind === 'patch'
            ? (() => {
                assertKeys(
                    decision,
                    ['kind', 'patch'],
                    `${path}.decision`
                );
                const patch = recordAt(
                    decision.patch,
                    `${path}.decision.patch`
                );
                assertKeys(
                    patch,
                    ['revision', 'kind', 'goalId', 'replacement'],
                    `${path}.decision.patch`
                );
                assertRevision(
                    patch.revision,
                    CORE_PROOF_PLAN_PATCH_PROFILE.revision,
                    `${path}.decision.patch.revision`
                );
                assertLiteral(
                    patch.kind,
                    'replace-hole',
                    `${path}.decision.patch.kind`
                );
                return {
                    kind: 'patch' as const,
                    patch: createCoreProofPlanHoleReplacement(
                        stringAt(
                            patch.goalId,
                            `${path}.decision.patch.goalId`
                        ),
                        assertProofPlan(
                            patch.replacement,
                            `${path}.decision.patch.replacement`
                        )
                    )
                };
            })()
            : fail(
                'INVALID_ARTIFACT',
                `${path}.decision.kind`,
                `Unsupported attempt decision '${kind}'`
            );
    assertLiteral(
        record.reportedUsageAuthority,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportedUsageAuthority,
        `${path}.reportedUsageAuthority`
    );
    const reportedUsage = usageAt(
        record.reportedUsage,
        `${path}.reportedUsage`
    );
    const reconstructed = createCoreLfProofAgentBenchmarkAttempt({
        benchmarkCase,
        retrievedPremises,
        ...(reportedUsage === undefined ? {} : { reportedUsage }),
        decision: reconstructedDecision
    });
    stringAt(record.caseId, `${path}.caseId`);
    assertCanonicalReconstruction(
        value,
        serializeCoreLfProofAgentBenchmarkAttempt(reconstructed),
        path
    );
    return deepFreeze(reconstructed);
});

const parseRunValue = (
    value: unknown,
    path: string
): CoreLfProofAgentBenchmarkRun => wrapArtifact(path, () => {
    const record = recordAt(value, path);
    assertKeys(record, [
        'revision',
        'profileRevision',
        'runRevision',
        'provider',
        'allowedProfiles',
        'seed',
        'limits',
        'limitEnforcement',
        'attempts'
    ], path);
    assertRevision(
        record.revision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.runRevision,
        `${path}.revision`
    );
    assertRevision(
        record.profileRevision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        `${path}.profileRevision`
    );
    assertLiteral(
        record.limitEnforcement,
        'outer-adapter-not-attested',
        `${path}.limitEnforcement`
    );
    const provider = recordAt(record.provider, `${path}.provider`);
    assertKeys(provider, ['id', 'revision'], `${path}.provider`);
    const allowedProfiles = arrayAt(
        record.allowedProfiles,
        `${path}.allowedProfiles`
    ).map((profile, index) => stringAt(
        profile,
        `${path}.allowedProfiles[${index}]`
    ));
    const limits = recordAt(record.limits, `${path}.limits`);
    assertKeys(limits, [
        'wallTimeMs',
        'inputTokens',
        'outputTokens',
        'checkerCalls'
    ], `${path}.limits`);
    const limitValue = (key: keyof typeof limits): number | undefined => {
        const valueAtKey = limits[key];
        return valueAtKey === null
            ? undefined
            : numberAt(valueAtKey, `${path}.limits.${key}`);
    };
    const attempts = arrayAt(record.attempts, `${path}.attempts`).map(
        (attempt, index) => parseAttemptValue(
            attempt,
            `${path}.attempts[${index}]`
        )
    );
    const reconstructed = createCoreLfProofAgentBenchmarkRun({
        revision: stringAt(record.runRevision, `${path}.runRevision`),
        provider: {
            id: stringAt(provider.id, `${path}.provider.id`),
            revision: stringAt(
                provider.revision,
                `${path}.provider.revision`
            )
        },
        allowedProfiles,
        seed: stringAt(record.seed, `${path}.seed`),
        limits: {
            ...(limits.wallTimeMs === null
                ? {}
                : { wallTimeMs: limitValue('wallTimeMs')! }),
            ...(limits.inputTokens === null
                ? {}
                : { inputTokens: limitValue('inputTokens')! }),
            ...(limits.outputTokens === null
                ? {}
                : { outputTokens: limitValue('outputTokens')! }),
            ...(limits.checkerCalls === null
                ? {}
                : { checkerCalls: limitValue('checkerCalls')! })
        },
        attempts
    });
    assertCanonicalReconstruction(
        value,
        serializeCoreLfProofAgentBenchmarkRun(reconstructed),
        path
    );
    return deepFreeze(reconstructed);
});

const parseReportValue = (
    value: unknown,
    path: string
): CoreLfProofAgentBenchmarkReport => wrapArtifact(path, () => {
    const record = recordAt(value, path);
    assertKeys(record, [
        'revision',
        'profileRevision',
        'suite',
        'run',
        'results',
        'metrics',
        'meaning',
        'ratiosDerived',
        'artifactCurrent',
        'materializesUpdatedSource'
    ], path);
    assertRevision(
        record.revision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.reportRevision,
        `${path}.revision`
    );
    assertRevision(
        record.profileRevision,
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        `${path}.profileRevision`
    );
    assertLiteral(
        record.meaning,
        'attempts-evaluated-not-source-committed',
        `${path}.meaning`
    );
    assertLiteral(record.ratiosDerived, false, `${path}.ratiosDerived`);
    assertLiteral(record.artifactCurrent, false, `${path}.artifactCurrent`);
    assertLiteral(
        record.materializesUpdatedSource,
        false,
        `${path}.materializesUpdatedSource`
    );
    const suite = parseSuiteValue(record.suite, `${path}.suite`);
    const run = parseRunValue(record.run, `${path}.run`);
    const reconstructed = evaluateCoreLfProofAgentBenchmarkRun({ suite, run });
    assertCanonicalReconstruction(
        value,
        serializeCoreLfProofAgentBenchmarkReport(reconstructed),
        path
    );
    return deepFreeze(reconstructed);
});

const parseCanonicalText = <T>(
    sourceText: string,
    path: string,
    reconstruct: (value: unknown, path: string) => T,
    serialize: (value: T) => string
): T => {
    if (typeof sourceText !== 'string' || sourceText.length === 0) {
        return fail(
            'INVALID_TEXT',
            path,
            'Interchange text must be nonempty'
        );
    }
    let value: unknown;
    try {
        value = JSON.parse(sourceText);
    } catch (error: unknown) {
        return fail(
            'INVALID_TEXT',
            path,
            'Interchange text is not exactly one JSON value',
            error
        );
    }
    const reconstructed = reconstruct(value, path);
    if (serialize(reconstructed) !== sourceText) {
        return fail(
            'NONCANONICAL_TEXT',
            path,
            'Interchange text must be exact canonical serializer output'
        );
    }
    return deepFreeze(reconstructed);
};

/** Parse and freshly reconstruct one exact canonical 12A case. */
export function parseCoreLfProofAgentBenchmarkCaseText(
    sourceText: string
): CoreLfProofAgentBenchmarkCase {
    return parseCanonicalText(
        sourceText,
        'caseText',
        parseCaseValue,
        serializeCoreLfProofAgentBenchmarkCase
    );
}

/** Parse and freshly reconstruct one exact canonical 12A suite. */
export function parseCoreLfProofAgentBenchmarkSuiteText(
    sourceText: string
): CoreLfProofAgentBenchmarkSuite {
    return parseCanonicalText(
        sourceText,
        'suiteText',
        parseSuiteValue,
        serializeCoreLfProofAgentBenchmarkSuite
    );
}

/** Parse and freshly reconstruct one exact canonical 12A attempt. */
export function parseCoreLfProofAgentBenchmarkAttemptText(
    sourceText: string
): CoreLfProofAgentBenchmarkAttempt {
    return parseCanonicalText(
        sourceText,
        'attemptText',
        parseAttemptValue,
        serializeCoreLfProofAgentBenchmarkAttempt
    );
}

/** Parse and freshly reconstruct one exact canonical 12A run. */
export function parseCoreLfProofAgentBenchmarkRunText(
    sourceText: string
): CoreLfProofAgentBenchmarkRun {
    return parseCanonicalText(
        sourceText,
        'runText',
        parseRunValue,
        serializeCoreLfProofAgentBenchmarkRun
    );
}

/** Parse and freshly re-evaluate one exact canonical 12A report. */
export function parseCoreLfProofAgentBenchmarkReportText(
    sourceText: string
): CoreLfProofAgentBenchmarkReport {
    return parseCanonicalText(
        sourceText,
        'reportText',
        parseReportValue,
        serializeCoreLfProofAgentBenchmarkReport
    );
}
