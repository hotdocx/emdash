/**
 * Bounded recursive synthesis of explicit checked LF instance evidence.
 *
 * Search consumes only an exact checked declaration base, Core context, and
 * immutable provider/visibility snapshots. Expected search failure is a
 * portable outcome; only malformed inputs or broken checked-artifact
 * invariants throw.
 */

import { CoreCheckerError } from './checker';
import { CoreContext } from './context';
import { serializeCoreExpressionAtDepth } from './core_serialization';
import {
    CoreLfClassInheritanceLayout,
    validateCoreLfClassInheritanceLayout
} from './lf_class_inheritance';
import {
    CoreLfClassParameterRole,
    CoreLfClassReference
} from './lf_class_schema';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfInstanceClassApplication,
    CoreLfInstanceProviderDeclaration,
    CoreLfInstanceRegistrySnapshot,
    CoreLfInstanceScopeCandidate,
    CoreLfInstanceScopeSnapshot,
    createCoreLfInstanceRegistrySnapshot,
    createCoreLfInstanceScopeSnapshot,
    serializeCoreLfInstanceRegistrySnapshot,
    serializeCoreLfInstanceScopeSnapshot
} from './lf_instance_scope';
import {
    CoreLfCatalogRuntime,
    coreLfCombinedNormalize,
    coreLfDefinitionalCompare
} from './lf_conversion';
import { CoreLfMixedDeclarationBaseContext } from './lf_transfer_mixed';
import { CoreLfQualifiedSymbol } from './lf_transfer';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import {
    KernelExpression,
    KernelMetaVariable,
    Plicity,
    kernelAmbientDependencies,
    kernelCall,
    kernelInstantiate,
    kernelUniverse,
    provenance
} from './kernel';

export const CORE_LF_INSTANCE_SYNTHESIS_PROFILE = Object.freeze({
    revision: 'emdash-lf-instance-synthesis-v1' as const,
    defaultLimits: Object.freeze({
        maxDepth: 32,
        maxTableEntries: 256,
        maxResultSize: 128,
        maxFuel: 4096,
        comparisonStepLimit: CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
    }),
    goalReadiness: 'all-arguments-ground' as const,
    providerChoice:
        'rank-then-priority-then-definitional-equivalence' as const,
    expectedOutcomes: Object.freeze([
        'solved',
        'missing',
        'stuck',
        'ambiguous',
        'limit-exceeded'
    ] as const),
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const
});

export type CoreLfInstanceSynthesisStatus =
    typeof CORE_LF_INSTANCE_SYNTHESIS_PROFILE.expectedOutcomes[number];

export type CoreLfInstanceSynthesisErrorCode =
    | 'INVALID_INPUT'
    | 'INVALID_CONTEXT'
    | 'INVALID_TARGET'
    | 'INVALID_LIMITS'
    | 'INVALID_REGISTRY'
    | 'INVALID_SCOPE'
    | 'INVALID_PROVIDER'
    | 'INVALID_CLASS_HEAD'
    | 'NON_PORTABLE_DATA'
    | 'INTERNAL_INVARIANT';

export class CoreLfInstanceSynthesisError extends Error {
    constructor(
        public readonly code: CoreLfInstanceSynthesisErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfInstanceSynthesisError';
    }
}

export interface CoreLfInstanceSynthesisLimits {
    readonly maxDepth: number;
    readonly maxTableEntries: number;
    readonly maxResultSize: number;
    readonly maxFuel: number;
    readonly comparisonStepLimit: number;
}

export interface CoreLfInstanceSynthesisLimitsInput {
    readonly maxDepth?: number;
    readonly maxTableEntries?: number;
    readonly maxResultSize?: number;
    readonly maxFuel?: number;
    readonly comparisonStepLimit?: number;
}

export interface CoreLfInstanceSynthesisInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly context: CoreContext;
    readonly runtimeProgram?: CoreLfCatalogRuntime;
    readonly targetClass: CoreLfClassInheritanceLayout;
    readonly target: KernelExpression;
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly scope: CoreLfInstanceScopeSnapshot;
    readonly limits?: CoreLfInstanceSynthesisLimitsInput;
}

export interface CoreLfInstanceSynthesisClassArgumentTrace {
    readonly ordinal: number;
    readonly role: CoreLfClassParameterRole;
    readonly plicity: Plicity;
    readonly value: string;
}

export interface CoreLfInstanceSynthesisTargetTrace {
    readonly class: CoreLfClassReference;
    readonly coreHeadName: string;
    readonly type: string;
    readonly normalizedType: string;
    readonly arguments:
        readonly CoreLfInstanceSynthesisClassArgumentTrace[];
}

export type CoreLfInstancePremiseDisposition =
    | 'expanded'
    | 'table-hit'
    | 'cycle'
    | 'not-ready';

export interface CoreLfInstancePremiseTrace {
    readonly binderOrdinal: number;
    readonly binderName: string;
    readonly class: CoreLfClassReference;
    readonly target: string;
    readonly disposition: CoreLfInstancePremiseDisposition;
    readonly outcome: CoreLfInstanceSynthesisStatus;
    readonly goalId?: string;
}

export interface CoreLfInstanceOrdinaryArgumentTrace {
    readonly binderOrdinal: number;
    readonly binderName: string;
    readonly value: string;
}

export type CoreLfInstanceCandidateTraceOutcome =
    | 'rejected'
    | 'success'
    | 'equivalent-success'
    | 'ambiguous-success'
    | 'stuck'
    | 'limit-exceeded'
    | 'skipped';

export interface CoreLfInstanceCandidateTrace {
    readonly providerId: CoreLfQualifiedSymbol;
    readonly rank: number;
    readonly priority: number;
    readonly outcome: CoreLfInstanceCandidateTraceOutcome;
    readonly reason: string;
    readonly ordinaryArguments:
        readonly CoreLfInstanceOrdinaryArgumentTrace[];
    readonly premises: readonly CoreLfInstancePremiseTrace[];
    readonly term?: string;
    readonly resultSize?: number;
    readonly equivalenceClass?: number;
}

export interface CoreLfInstanceGoalTrace {
    readonly goalId: string;
    readonly key: string;
    readonly depth: number;
    readonly target: CoreLfInstanceSynthesisTargetTrace;
    readonly outcome: CoreLfInstanceSynthesisStatus;
    readonly decisionRank?: number;
    readonly decisionPriority?: number;
    readonly selectedProvider?: CoreLfQualifiedSymbol;
    readonly equivalentProviders?: readonly CoreLfQualifiedSymbol[];
    readonly resultSize?: number;
    readonly candidates: readonly CoreLfInstanceCandidateTrace[];
}

export interface CoreLfInstanceSynthesisUsage {
    readonly fuelUsed: number;
    readonly candidateAttempts: number;
    readonly tableEntries: number;
    readonly maxDepthReached: number;
}

export interface CoreLfInstanceSynthesisScopeFingerprintMaterial {
    readonly registryCanonicalJson: string;
    readonly scopeCanonicalJson: string;
}

export interface CoreLfInstanceSynthesisRuntimeFingerprintMaterial {
    readonly revision?: string;
    readonly ruleIds: readonly string[];
}

export interface CoreLfInstanceSynthesisReport {
    readonly revision:
        typeof CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision;
    readonly limits: CoreLfInstanceSynthesisLimits;
    readonly usage: CoreLfInstanceSynthesisUsage;
    readonly registryRevision: string;
    readonly scopeRevision: string;
    readonly scopeFingerprintMaterial:
        CoreLfInstanceSynthesisScopeFingerprintMaterial;
    readonly runtimeFingerprintMaterial:
        CoreLfInstanceSynthesisRuntimeFingerprintMaterial;
    readonly rootGoalId: string;
    readonly target: CoreLfInstanceSynthesisTargetTrace;
    readonly outcome: CoreLfInstanceSynthesisStatus;
    readonly goals: readonly CoreLfInstanceGoalTrace[];
}

interface CoreLfInstanceSynthesisOutcomeBase {
    readonly status: CoreLfInstanceSynthesisStatus;
    readonly report: CoreLfInstanceSynthesisReport;
}

export interface CoreLfInstanceSynthesisSolved
extends CoreLfInstanceSynthesisOutcomeBase {
    readonly status: 'solved';
    readonly selected: CoreLfQualifiedSymbol;
    readonly term: KernelExpression;
    readonly type: KernelExpression;
    readonly resultSize: number;
}

export interface CoreLfInstanceSynthesisUnsolved
extends CoreLfInstanceSynthesisOutcomeBase {
    readonly status:
        | 'missing'
        | 'stuck'
        | 'ambiguous'
        | 'limit-exceeded';
}

export type CoreLfInstanceSynthesisOutcome =
    | CoreLfInstanceSynthesisSolved
    | CoreLfInstanceSynthesisUnsolved;

interface GoalTemplate {
    readonly class: CoreLfClassReference;
    readonly coreHeadName: string;
    readonly roles: readonly CoreLfClassParameterRole[];
    readonly plicities: readonly Plicity[];
}

interface PreparedGoal {
    readonly template: GoalTemplate;
    readonly type: KernelExpression;
    readonly normalizedType: KernelExpression;
    readonly arguments: readonly KernelExpression[];
    readonly targetTrace: CoreLfInstanceSynthesisTargetTrace;
    readonly goalKey: string;
    readonly tableKey: string;
}

interface GoalPreparationIssue {
    readonly status: 'stuck' | 'limit-exceeded';
    readonly reason: string;
    readonly targetTrace: CoreLfInstanceSynthesisTargetTrace;
    readonly goalKey: string;
    readonly tableKey: string;
}

type GoalPreparation = PreparedGoal | GoalPreparationIssue;

interface MutableCandidateTrace {
    providerId: CoreLfQualifiedSymbol;
    rank: number;
    priority: number;
    outcome: CoreLfInstanceCandidateTraceOutcome;
    reason: string;
    ordinaryArguments: CoreLfInstanceOrdinaryArgumentTrace[];
    premises: CoreLfInstancePremiseTrace[];
    term?: string;
    resultSize?: number;
    equivalenceClass?: number;
}

interface MutableGoalTrace {
    goalId: string;
    key: string;
    depth: number;
    target: CoreLfInstanceSynthesisTargetTrace;
    outcome: CoreLfInstanceSynthesisStatus;
    decisionRank?: number;
    decisionPriority?: number;
    selectedProvider?: CoreLfQualifiedSymbol;
    equivalentProviders?: CoreLfQualifiedSymbol[];
    resultSize?: number;
    candidates: MutableCandidateTrace[];
}

interface InternalSolved {
    readonly status: 'solved';
    readonly selected: CoreLfQualifiedSymbol;
    readonly term: KernelExpression;
    readonly size: number;
    readonly goalId: string;
}

interface InternalUnsolved {
    readonly status:
        | 'missing'
        | 'stuck'
        | 'ambiguous'
        | 'limit-exceeded';
    readonly goalId: string;
    readonly cycle?: boolean;
}

type InternalResolution = InternalSolved | InternalUnsolved;

interface ResolutionEdge {
    readonly resolution: InternalResolution;
    readonly disposition: Exclude<
        CoreLfInstancePremiseDisposition,
        'not-ready'
    >;
}

interface TableEntry {
    readonly goalId: string;
    state: 'visiting' | 'done';
    resolution?: InternalResolution;
}

interface CandidateSuccess {
    readonly status: 'success';
    readonly trace: MutableCandidateTrace;
    readonly term: KernelExpression;
    readonly provider: CoreLfInstanceProviderDeclaration;
    readonly size: number;
}

interface CandidateUnsolved {
    readonly status:
        | 'rejected'
        | 'stuck'
        | 'ambiguous'
        | 'limit-exceeded';
    readonly trace: MutableCandidateTrace;
}

type CandidateResolution = CandidateSuccess | CandidateUnsolved;

const fail = (
    code: CoreLfInstanceSynthesisErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfInstanceSynthesisError(
        code,
        path,
        message,
        underlying
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

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

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) return value.map(cloneData) as T;
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value as Record<string, unknown>)
                .filter(([, entry]) => entry !== undefined)
                .map(([key, entry]) => [key, cloneData(entry)])
        ) as T;
    }
    return value;
};

const freezeData = <T>(value: T): T => deepFreeze(cloneData(value));

const symbolKey = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}\u0000${value.name}`;

const displaySymbol = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}.${value.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const sameClass = (
    left: CoreLfClassReference,
    right: CoreLfClassReference
): boolean =>
    left.parameterCount === right.parameterCount &&
    sameSymbol(left.classId, right.classId);

const cloneSymbol = (
    value: CoreLfQualifiedSymbol
): CoreLfQualifiedSymbol => ({ ...value });

const cloneClass = (
    value: CoreLfClassReference
): CoreLfClassReference => ({
    classId: cloneSymbol(value.classId),
    parameterCount: value.parameterCount
});

const containsMeta = (expression: KernelExpression): boolean => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return false;
        case 'meta':
            return true;
        case 'application':
            return expression.arguments.some(argument =>
                containsMeta(argument.value)
            );
        case 'call':
            return containsMeta(expression.callee) ||
                expression.arguments.some(argument =>
                    containsMeta(argument.value)
                );
        case 'pi':
        case 'lambda':
            return containsMeta(expression.binder.type) ||
                containsMeta(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const checkedLimit = (
    value: unknown,
    path: string
): number => {
    if (!Number.isSafeInteger(value) || (value as number) < 0) {
        return fail(
            'INVALID_LIMITS',
            path,
            'Instance-synthesis limits must be nonnegative safe integers'
        );
    }
    return value as number;
};

const synthesisLimits = (
    input: CoreLfInstanceSynthesisLimitsInput | undefined
): CoreLfInstanceSynthesisLimits => {
    if (input !== undefined && !record(input)) {
        return fail(
            'INVALID_LIMITS',
            'input.limits',
            'Instance-synthesis limits must be an object when supplied'
        );
    }
    const defaults = CORE_LF_INSTANCE_SYNTHESIS_PROFILE.defaultLimits;
    return Object.freeze({
        maxDepth: checkedLimit(
            input?.maxDepth ?? defaults.maxDepth,
            'input.limits.maxDepth'
        ),
        maxTableEntries: checkedLimit(
            input?.maxTableEntries ?? defaults.maxTableEntries,
            'input.limits.maxTableEntries'
        ),
        maxResultSize: checkedLimit(
            input?.maxResultSize ?? defaults.maxResultSize,
            'input.limits.maxResultSize'
        ),
        maxFuel: checkedLimit(
            input?.maxFuel ?? defaults.maxFuel,
            'input.limits.maxFuel'
        ),
        comparisonStepLimit: checkedLimit(
            input?.comparisonStepLimit ?? defaults.comparisonStepLimit,
            'input.limits.comparisonStepLimit'
        )
    });
};

const runtimeFingerprintMaterial = (
    runtimeProgram: CoreLfCatalogRuntime | undefined
): CoreLfInstanceSynthesisRuntimeFingerprintMaterial => {
    if (runtimeProgram === undefined) return { ruleIds: [] };
    if (
        !record(runtimeProgram) ||
        typeof runtimeProgram.revision !== 'string' ||
        runtimeProgram.revision.length === 0 ||
        !Array.isArray(runtimeProgram.ruleIds) ||
        runtimeProgram.ruleIds.some(ruleId =>
            typeof ruleId !== 'string' || ruleId.length === 0
        ) ||
        new Set(runtimeProgram.ruleIds).size !== runtimeProgram.ruleIds.length ||
        typeof runtimeProgram.rewriteHead !== 'function'
    ) {
        return fail(
            'INVALID_INPUT',
            'input.runtimeProgram',
            'Instance synthesis runtime must be one reviewed catalog runtime'
        );
    }
    return {
        revision: runtimeProgram.revision,
        ruleIds: [...runtimeProgram.ruleIds]
    };
};

const installedClassCoreName = (
    declarations: CoreLfMixedDeclarationBaseContext,
    reference: CoreLfClassReference,
    path: string
): string => {
    const declaration = declarations.declaration(reference.classId);
    if (
        declaration === undefined ||
        declaration.link.kind !== 'free-declaration' ||
        !sameSymbol(declaration.symbol, reference.classId) ||
        !sameSymbol(declaration.link.symbol, reference.classId) ||
        !declaration.status.startsWith('installed-')
    ) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            `Class '${displaySymbol(reference.classId)}' is not one exact ` +
                'installed free declaration'
        );
    }
    return declaration.link.coreName;
};

const expressionArguments = (
    expression: KernelExpression,
    template: GoalTemplate,
    path: string
): readonly KernelExpression[] => {
    const callee = expression.tag === 'call'
        ? expression.callee
        : expression;
    const arguments_ = expression.tag === 'call'
        ? expression.arguments
        : [];
    if (
        callee.tag !== 'reference' ||
        callee.namespace !== 'free' ||
        callee.name !== template.coreHeadName ||
        arguments_.length !== template.class.parameterCount
    ) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            `Expected exact class head ` +
                `'${displaySymbol(template.class.classId)}' with ` +
                `${template.class.parameterCount} parameters`
        );
    }
    arguments_.forEach((argument, ordinal) => {
        if (argument.plicity !== template.plicities[ordinal]) {
            fail(
                'INVALID_CLASS_HEAD',
                `${path}.arguments[${ordinal}].plicity`,
                `Class argument ${ordinal} has ${argument.plicity} plicity, ` +
                    `expected ${template.plicities[ordinal]}`
            );
        }
    });
    return arguments_.map(argument => argument.value);
};

const targetTrace = (
    template: GoalTemplate,
    type: KernelExpression,
    normalizedType: KernelExpression,
    arguments_: readonly KernelExpression[],
    ambientDepth: number
): CoreLfInstanceSynthesisTargetTrace => ({
    class: cloneClass(template.class),
    coreHeadName: template.coreHeadName,
    type: serializeCoreExpressionAtDepth(type, ambientDepth),
    normalizedType: serializeCoreExpressionAtDepth(
        normalizedType,
        ambientDepth
    ),
    arguments: arguments_.map((argument, ordinal) => ({
        ordinal,
        role: template.roles[ordinal],
        plicity: template.plicities[ordinal],
        value: serializeCoreExpressionAtDepth(argument, ambientDepth)
    }))
});

const templateFromApplication = (
    declarations: CoreLfMixedDeclarationBaseContext,
    application: CoreLfInstanceClassApplication,
    path: string
): GoalTemplate => {
    const coreHeadName = installedClassCoreName(
        declarations,
        application.class,
        `${path}.class`
    );
    if (
        coreHeadName !== application.coreHeadName ||
        application.arguments.length !== application.class.parameterCount
    ) {
        return fail(
            'INVALID_PROVIDER',
            path,
            'Provider class metadata differs from its checked declaration head'
        );
    }
    return {
        class: cloneClass(application.class),
        coreHeadName,
        roles: application.arguments.map(argument => argument.role),
        plicities: application.arguments.map(argument => argument.plicity)
    };
};

interface ValidatedSnapshots {
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly scope: CoreLfInstanceScopeSnapshot;
    readonly registryCanonicalJson: string;
    readonly scopeCanonicalJson: string;
}

const validateSnapshots = (
    registryInput: CoreLfInstanceRegistrySnapshot,
    scopeInput: CoreLfInstanceScopeSnapshot
): ValidatedSnapshots => {
    let phase: 'registry' | 'scope' = 'registry';
    try {
        if (!record(registryInput)) {
            return fail(
                'INVALID_REGISTRY',
                'input.registry',
                'Instance synthesis requires one registry snapshot'
            );
        }
        const registry = createCoreLfInstanceRegistrySnapshot({
            revision: registryInput.registryRevision,
            providers: registryInput.providers
        });
        const suppliedRegistry = serializeCoreLfInstanceRegistrySnapshot(
            registryInput
        );
        const registryCanonicalJson =
            serializeCoreLfInstanceRegistrySnapshot(registry);
        if (suppliedRegistry !== registryCanonicalJson) {
            return fail(
                'INVALID_REGISTRY',
                'input.registry',
                'Instance registry is not its canonical validated snapshot'
            );
        }
        phase = 'scope';
        if (
            !record(scopeInput) ||
            !Array.isArray(scopeInput.localFrames) ||
            !Array.isArray(scopeInput.openedNamedScopes) ||
            !Array.isArray(scopeInput.imports)
        ) {
            return fail(
                'INVALID_SCOPE',
                'input.scope',
                'Instance synthesis requires one complete scope snapshot'
            );
        }
        const scope = createCoreLfInstanceScopeSnapshot({
            revision: scopeInput.scopeRevision,
            registry,
            moduleId: scopeInput.moduleId,
            contextDepth: scopeInput.contextDepth,
            localFrames: scopeInput.localFrames.map(frame => ({
                frameId: frame.frameId,
                kind: frame.kind,
                providers: frame.providers
            })),
            openedNamedScopes: scopeInput.openedNamedScopes,
            imports: scopeInput.imports.map(importEntry => ({
                moduleId: importEntry.moduleId,
                moduleRevision: importEntry.moduleRevision,
                interfaceRevision: importEntry.interfaceRevision,
                interfaceSha256: importEntry.interfaceSha256,
                providers: importEntry.providers
            }))
        });
        const suppliedScope = serializeCoreLfInstanceScopeSnapshot(scopeInput);
        const scopeCanonicalJson = serializeCoreLfInstanceScopeSnapshot(scope);
        if (suppliedScope !== scopeCanonicalJson) {
            return fail(
                'INVALID_SCOPE',
                'input.scope',
                'Instance scope is not its canonical validated snapshot'
            );
        }
        return {
            registry,
            scope,
            registryCanonicalJson,
            scopeCanonicalJson
        };
    } catch (error: unknown) {
        if (error instanceof CoreLfInstanceSynthesisError) throw error;
        const code = phase === 'registry'
            ? 'INVALID_REGISTRY'
            : 'INVALID_SCOPE';
        return fail(
            code,
            code === 'INVALID_REGISTRY' ? 'input.registry' : 'input.scope',
            `Invalid instance ${code === 'INVALID_REGISTRY'
                ? 'registry'
                : 'scope'} snapshot`,
            error instanceof Error ? error : undefined
        );
    }
};

const activatedProviders = (
    declarations: CoreLfMixedDeclarationBaseContext,
    context: CoreContext,
    registry: CoreLfInstanceRegistrySnapshot,
    scope: CoreLfInstanceScopeSnapshot,
    comparisonStepLimit: number,
    runtimeProgram: CoreLfCatalogRuntime | undefined
): ReadonlyMap<string, CoreLfInstanceProviderDeclaration> => {
    const byId = new Map(
        registry.providers.map(provider => [
            symbolKey(provider.providerId),
            provider
        ])
    );
    const activated = new Map<string, CoreLfInstanceProviderDeclaration>();
    scope.candidates.forEach((candidate, index) => {
        const key = symbolKey(candidate.providerId);
        const provider = byId.get(key);
        if (provider === undefined) {
            fail(
                'INVALID_SCOPE',
                `input.scope.candidates[${index}]`,
                `Scope candidate '${displaySymbol(candidate.providerId)}' ` +
                    'is absent from the validated registry'
            );
        }
        if (
            activated.has(key) ||
            candidate.priority !== provider.priority
        ) {
            fail(
                'INVALID_SCOPE',
                `input.scope.candidates[${index}]`,
                'Scope candidate identity or priority is inconsistent'
            );
        }
        if (
            provider.source.kind === 'local-bound'
                ? provider.ambientDepth !== context.depth
                : provider.ambientDepth !== 0
        ) {
            fail(
                'INVALID_PROVIDER',
                `input.registry.providers.${displaySymbol(provider.providerId)}`,
                'Activated provider has the wrong ambient Core depth'
            );
        }
        try {
            const checker = createCoreLfChecker(
                declarations.environment,
                comparisonStepLimit,
                runtimeProgram
            );
            checker.check(context, provider.term, provider.type);
            templateFromApplication(
                declarations,
                provider.result,
                `providers.${displaySymbol(provider.providerId)}.result`
            );
            provider.telescope.forEach(binder => {
                if (binder.kind === 'instance-premise') {
                    templateFromApplication(
                        declarations,
                        binder.target,
                        `providers.${displaySymbol(provider.providerId)}.` +
                            `telescope[${binder.ordinal}].target`
                    );
                }
            });
        } catch (error: unknown) {
            if (error instanceof CoreLfInstanceSynthesisError) throw error;
            fail(
                'INVALID_PROVIDER',
                `input.registry.providers.${displaySymbol(provider.providerId)}`,
                `Activated provider '${displaySymbol(provider.providerId)}' ` +
                    'does not recheck in the exact synthesis context',
                error instanceof Error ? error : undefined
            );
        }
        activated.set(key, provider);
    });
    return activated;
};

const candidateTrace = (
    candidate: CoreLfInstanceScopeCandidate,
    outcome: CoreLfInstanceCandidateTraceOutcome,
    reason: string
): MutableCandidateTrace => ({
    providerId: cloneSymbol(candidate.providerId),
    rank: candidate.rank,
    priority: candidate.priority,
    outcome,
    reason,
    ordinaryArguments: [],
    premises: []
});

const unresolvedPriority = (
    statuses: readonly CandidateResolution[]
): 'limit-exceeded' | 'ambiguous' | 'stuck' | undefined => {
    if (statuses.some(status => status.status === 'limit-exceeded')) {
        return 'limit-exceeded';
    }
    if (statuses.some(status => status.status === 'ambiguous')) {
        return 'ambiguous';
    }
    if (statuses.some(status => status.status === 'stuck')) return 'stuck';
    return undefined;
};

class CoreLfInstanceResolver {
    private readonly providerById:
        ReadonlyMap<string, CoreLfInstanceProviderDeclaration>;
    private readonly table = new Map<string, TableEntry>();
    private readonly goalTraces: MutableGoalTrace[] = [];
    private nextGoalOrdinal = 0;
    private fuelUsed = 0;
    private candidateAttempts = 0;
    private maxDepthReached = 0;

    constructor(
        private readonly declarations: CoreLfMixedDeclarationBaseContext,
        private readonly context: CoreContext,
        private readonly registry: CoreLfInstanceRegistrySnapshot,
        private readonly scope: CoreLfInstanceScopeSnapshot,
        private readonly limits: CoreLfInstanceSynthesisLimits,
        private readonly registryCanonicalJson: string,
        private readonly scopeCanonicalJson: string,
        private readonly runtimeProgram: CoreLfCatalogRuntime | undefined,
        private readonly runtimeFingerprint:
            CoreLfInstanceSynthesisRuntimeFingerprintMaterial
    ) {
        this.providerById = activatedProviders(
            declarations,
            context,
            registry,
            scope,
            limits.comparisonStepLimit,
            runtimeProgram
        );
    }

    private prepareGoal(
        template: GoalTemplate,
        type: KernelExpression
    ): GoalPreparation {
        const directArguments = expressionArguments(
            type,
            template,
            'instanceGoal'
        );
        const originalTrace = targetTrace(
            template,
            type,
            type,
            directArguments,
            this.context.depth
        );
        if (containsMeta(type)) {
            const goalKey = `${displaySymbol(template.class.classId)}::` +
                serializeCoreExpressionAtDepth(type, this.context.depth);
            return {
                status: 'stuck',
                reason: 'goal-contains-unresolved-metavariable',
                targetTrace: originalTrace,
                goalKey,
                tableKey: this.tableKey(template.class, goalKey)
            };
        }
        const normalization = coreLfCombinedNormalize(
            this.declarations.environment,
            type,
            this.limits.comparisonStepLimit,
            undefined,
            this.runtimeProgram
        );
        if (normalization.status !== 'normal') {
            const partial = normalization.expression;
            const goalKey = `${displaySymbol(template.class.classId)}::` +
                serializeCoreExpressionAtDepth(partial, this.context.depth);
            return {
                status: normalization.status === 'step-limit-exceeded'
                    ? 'limit-exceeded'
                    : 'stuck',
                reason: normalization.status === 'step-limit-exceeded'
                    ? 'goal-normalization-step-limit'
                    : 'goal-normalization-plicity-stuck',
                targetTrace: targetTrace(
                    template,
                    type,
                    partial,
                    directArguments,
                    this.context.depth
                ),
                goalKey,
                tableKey: this.tableKey(template.class, goalKey)
            };
        }
        const normalizedArguments = expressionArguments(
            normalization.expression,
            template,
            'normalizedInstanceGoal'
        );
        const goalKey = `${displaySymbol(template.class.classId)}::` +
            serializeCoreExpressionAtDepth(
                normalization.expression,
                this.context.depth
            );
        return {
            template,
            type,
            normalizedType: normalization.expression,
            arguments: normalizedArguments,
            targetTrace: targetTrace(
                template,
                type,
                normalization.expression,
                normalizedArguments,
                this.context.depth
            ),
            goalKey,
            tableKey: this.tableKey(template.class, goalKey)
        };
    }

    private tableKey(
        reference: CoreLfClassReference,
        goalKey: string
    ): string {
        return `${symbolKey(reference.classId)}\u0000` +
            `${reference.parameterCount}\u0000${goalKey}\u0000` +
            `${this.registryCanonicalJson}\u0000${this.scopeCanonicalJson}` +
            `\u0000${JSON.stringify(this.runtimeFingerprint)}`;
    }

    private newGoalTrace(
        preparation: GoalPreparation,
        depth: number
    ): MutableGoalTrace {
        const trace: MutableGoalTrace = {
            goalId: `g${this.nextGoalOrdinal++}`,
            key: preparation.goalKey,
            depth,
            target: preparation.targetTrace,
            outcome: 'stuck',
            candidates: []
        };
        this.goalTraces.push(trace);
        return trace;
    }

    private skippedCandidates(
        goal: PreparedGoal,
        fromIndex: number,
        reason: string
    ): MutableCandidateTrace[] {
        return this.headCandidates(goal)
            .slice(fromIndex)
            .map(candidate => candidateTrace(candidate, 'skipped', reason));
    }

    private headCandidates(
        goal: PreparedGoal
    ): readonly CoreLfInstanceScopeCandidate[] {
        return this.scope.candidates.filter(candidate => {
            const provider = this.providerById.get(
                symbolKey(candidate.providerId)
            );
            return provider !== undefined &&
                sameClass(provider.result.class, goal.template.class) &&
                provider.result.coreHeadName === goal.template.coreHeadName;
        });
    }

    private providerResultDependsOnPremise(
        provider: CoreLfInstanceProviderDeclaration
    ): boolean {
        const telescopeLength = provider.telescope.length;
        const premiseIndices = new Set(
            provider.telescope
                .filter(binder => binder.kind === 'instance-premise')
                .map(binder => telescopeLength - binder.ordinal - 1)
        );
        return kernelAmbientDependencies(
            provider.result.type,
            provider.ambientDepth + telescopeLength
        ).some(dependency => premiseIndices.has(dependency.index));
    }

    private spendFuel(trace: MutableCandidateTrace): boolean {
        if (this.fuelUsed >= this.limits.maxFuel) {
            trace.outcome = 'limit-exceeded';
            trace.reason = 'candidate-fuel-exhausted';
            return false;
        }
        this.fuelUsed++;
        this.candidateAttempts++;
        return true;
    }

    private attemptCandidate(
        goal: PreparedGoal,
        candidate: CoreLfInstanceScopeCandidate,
        depth: number
    ): CandidateResolution {
        const trace = candidateTrace(candidate, 'rejected', 'not-attempted');
        if (!this.spendFuel(trace)) {
            return { status: 'limit-exceeded', trace };
        }
        const provider = this.providerById.get(symbolKey(candidate.providerId));
        if (provider === undefined) {
            return fail(
                'INTERNAL_INVARIANT',
                `scope.candidates.${displaySymbol(candidate.providerId)}`,
                'Validated scope candidate lost its provider declaration'
            );
        }
        if (this.providerResultDependsOnPremise(provider)) {
            trace.outcome = 'stuck';
            trace.reason = 'provider-result-depends-on-instance-premise';
            return { status: 'stuck', trace };
        }

        const checker = createCoreLfChecker(
            this.declarations.environment,
            this.limits.comparisonStepLimit,
            this.runtimeProgram
        );
        const session = checker.lfSession;
        let currentType = provider.type;
        const metas: {
            readonly binder: CoreLfInstanceProviderDeclaration['telescope'][number];
            readonly meta: KernelMetaVariable;
        }[] = [];
        const arguments_: {
            readonly plicity: Plicity;
            readonly value: KernelExpression;
        }[] = [];
        for (const binder of provider.telescope) {
            if (currentType.tag !== 'pi') {
                return fail(
                    'INVALID_PROVIDER',
                    `providers.${displaySymbol(provider.providerId)}.type`,
                    'Provider telescope ended before its checked Pi type'
                );
            }
            const meta = session.freshMeta(
                this.context,
                currentType.binder.type,
                provenance(
                    'derived',
                    `instance synthesis ${displaySymbol(provider.providerId)} ` +
                        `binder ${binder.ordinal}`
                )
            );
            metas.push({ binder, meta });
            arguments_.push({
                plicity: currentType.binder.mode.plicity,
                value: meta
            });
            currentType = session.zonk(kernelInstantiate(
                currentType.body,
                meta
            ));
        }
        const application = arguments_.length === 0
            ? provider.term
            : kernelCall(
                provider.term,
                arguments_,
                provenance(
                    'derived',
                    `instance candidate ${displaySymbol(provider.providerId)}`
                )
            );
        try {
            checker.checkRefinement(this.context, application, goal.type);
        } catch (error: unknown) {
            if (error instanceof CoreCheckerError) {
                if (error.code === 'CONVERSION_STEP_LIMIT') {
                    trace.outcome = 'limit-exceeded';
                    trace.reason = 'candidate-result-comparison-step-limit';
                    return { status: 'limit-exceeded', trace };
                }
                if (
                    error.code === 'UNRESOLVED_CONSTRAINTS' ||
                    error.code === 'UNRESOLVED_METAVARIABLE'
                ) {
                    trace.outcome = 'stuck';
                    trace.reason = 'candidate-result-unification-stuck';
                    return { status: 'stuck', trace };
                }
                if (
                    error.code === 'TYPE_MISMATCH' ||
                    error.code === 'PLICITY_MISMATCH' ||
                    error.code === 'BINDER_MODE_MISMATCH' ||
                    error.code === 'CONSTRAINT_REJECTED'
                ) {
                    trace.outcome = 'rejected';
                    trace.reason = 'candidate-result-mismatch';
                    return { status: 'rejected', trace };
                }
            }
            return fail(
                'INVALID_PROVIDER',
                `providers.${displaySymbol(provider.providerId)}`,
                'Provider candidate could not be matched through the checked ' +
                    'refinement boundary',
                error instanceof Error ? error : undefined
            );
        }

        for (const entry of metas) {
            const value = session.zonk(entry.meta);
            if (entry.binder.kind === 'ordinary') {
                if (containsMeta(value)) {
                    trace.outcome = 'stuck';
                    trace.reason = 'ordinary-parameter-not-goal-determined';
                    return { status: 'stuck', trace };
                }
                trace.ordinaryArguments.push({
                    binderOrdinal: entry.binder.ordinal,
                    binderName: entry.binder.binderName,
                    value: serializeCoreExpressionAtDepth(
                        value,
                        this.context.depth
                    )
                });
            } else if (value.tag !== 'meta') {
                trace.outcome = 'stuck';
                trace.reason = 'result-match-assigned-instance-premise';
                return { status: 'stuck', trace };
            }
        }

        let resultSize = 1;
        for (const entry of metas) {
            if (entry.binder.kind !== 'instance-premise') continue;
            const metaEntry = session.metavariable(entry.meta);
            const premiseType = session.zonk(metaEntry.type);
            const premiseTemplate = templateFromApplication(
                this.declarations,
                entry.binder.target,
                `providers.${displaySymbol(provider.providerId)}.` +
                    `telescope[${entry.binder.ordinal}].target`
            );
            if (containsMeta(premiseType)) {
                trace.premises.push({
                    binderOrdinal: entry.binder.ordinal,
                    binderName: entry.binder.binderName,
                    class: cloneClass(entry.binder.target.class),
                    target: serializeCoreExpressionAtDepth(
                        premiseType,
                        this.context.depth
                    ),
                    disposition: 'not-ready',
                    outcome: 'stuck'
                });
                trace.outcome = 'stuck';
                trace.reason = 'instance-premise-not-ground';
                return { status: 'stuck', trace };
            }
            let edge: ResolutionEdge;
            try {
                const premiseChecker = createCoreLfChecker(
                    this.declarations.environment,
                    this.limits.comparisonStepLimit,
                    this.runtimeProgram
                );
                premiseChecker.check(
                    this.context,
                    premiseType,
                    kernelUniverse(provenance(
                        'derived',
                        'instance premise must inhabit TYPE'
                    ))
                );
                edge = this.resolveGoal(
                    premiseTemplate,
                    premiseType,
                    depth + 1
                );
            } catch (error: unknown) {
                if (error instanceof CoreLfInstanceSynthesisError) throw error;
                return fail(
                    'INVALID_PROVIDER',
                    `providers.${displaySymbol(provider.providerId)}.` +
                        `telescope[${entry.binder.ordinal}]`,
                    'Instantiated instance premise is not a checked class type',
                    error instanceof Error ? error : undefined
                );
            }
            trace.premises.push({
                binderOrdinal: entry.binder.ordinal,
                binderName: entry.binder.binderName,
                class: cloneClass(entry.binder.target.class),
                target: serializeCoreExpressionAtDepth(
                    premiseType,
                    this.context.depth
                ),
                disposition: edge.disposition,
                outcome: edge.resolution.status,
                goalId: edge.resolution.goalId
            });
            if (edge.resolution.status !== 'solved') {
                if (edge.resolution.status === 'limit-exceeded') {
                    trace.outcome = 'limit-exceeded';
                    trace.reason = 'instance-premise-limit-exceeded';
                    return { status: 'limit-exceeded', trace };
                }
                if (edge.resolution.status === 'ambiguous') {
                    trace.outcome = 'ambiguous-success';
                    trace.reason = 'instance-premise-ambiguous';
                    return { status: 'ambiguous', trace };
                }
                if (edge.resolution.status === 'stuck') {
                    trace.outcome = 'stuck';
                    trace.reason = 'instance-premise-stuck';
                    return { status: 'stuck', trace };
                }
                trace.outcome = 'rejected';
                trace.reason = edge.resolution.cycle
                    ? 'instance-premise-cycle'
                    : 'instance-premise-missing';
                return { status: 'rejected', trace };
            }
            try {
                checker.check(
                    this.context,
                    edge.resolution.term,
                    premiseType
                );
                session.solve(entry.meta, edge.resolution.term);
            } catch (error: unknown) {
                return fail(
                    'INTERNAL_INVARIANT',
                    `providers.${displaySymbol(provider.providerId)}.` +
                        `telescope[${entry.binder.ordinal}]`,
                    'Recursively checked premise could not fill its exact meta',
                    error instanceof Error ? error : undefined
                );
            }
            resultSize += edge.resolution.size;
            if (resultSize > this.limits.maxResultSize) {
                trace.outcome = 'limit-exceeded';
                trace.reason = 'candidate-result-size-limit';
                return { status: 'limit-exceeded', trace };
            }
        }

        const term = session.zonk(application);
        if (containsMeta(term)) {
            trace.outcome = 'stuck';
            trace.reason = 'candidate-retains-unresolved-metavariable';
            return { status: 'stuck', trace };
        }
        let checkedTerm: KernelExpression;
        try {
            checkedTerm = checker.check(
                this.context,
                term,
                goal.type
            ).term;
        } catch (error: unknown) {
            if (
                error instanceof CoreCheckerError &&
                error.code === 'CONVERSION_STEP_LIMIT'
            ) {
                trace.outcome = 'limit-exceeded';
                trace.reason = 'candidate-final-check-step-limit';
                return { status: 'limit-exceeded', trace };
            }
            return fail(
                'INVALID_PROVIDER',
                `providers.${displaySymbol(provider.providerId)}`,
                'Assembled explicit provider application failed final checking',
                error instanceof Error ? error : undefined
            );
        }
        trace.outcome = 'success';
        trace.reason = 'checked-explicit-evidence';
        trace.term = serializeCoreExpressionAtDepth(
            checkedTerm,
            this.context.depth
        );
        trace.resultSize = resultSize;
        return {
            status: 'success',
            trace,
            term: checkedTerm,
            provider,
            size: resultSize
        };
    }

    private equivalentClasses(
        successes: readonly CandidateSuccess[]
    ): {
        readonly classes: readonly CandidateSuccess[][];
        readonly limitTrace?: MutableCandidateTrace;
    } {
        const classes: CandidateSuccess[][] = [];
        for (const success of successes) {
            let equivalentClass: CandidateSuccess[] | undefined;
            for (const existing of classes) {
                const comparison = coreLfDefinitionalCompare(
                    this.declarations.environment,
                    success.term,
                    existing[0].term,
                    this.limits.comparisonStepLimit,
                    undefined,
                    this.runtimeProgram
                );
                if (comparison.status === 'step-limit-exceeded') {
                    success.trace.outcome = 'limit-exceeded';
                    success.trace.reason =
                        'success-equivalence-comparison-step-limit';
                    return { classes, limitTrace: success.trace };
                }
                if (comparison.status === 'equal') {
                    equivalentClass = existing;
                    break;
                }
            }
            if (equivalentClass === undefined) {
                classes.push([success]);
            } else {
                equivalentClass.push(success);
            }
        }
        return { classes };
    }

    private resolvePreparedGoal(
        goal: PreparedGoal,
        trace: MutableGoalTrace,
        depth: number
    ): InternalResolution {
        const candidates = this.headCandidates(goal);
        if (candidates.length === 0) {
            trace.outcome = 'missing';
            return { status: 'missing', goalId: trace.goalId };
        }
        let index = 0;
        while (index < candidates.length) {
            const first = candidates[index];
            let end = index + 1;
            while (
                end < candidates.length &&
                candidates[end].rank === first.rank &&
                candidates[end].priority === first.priority
            ) {
                end++;
            }
            const group = candidates.slice(index, end);
            const results = group.map(candidate =>
                this.attemptCandidate(goal, candidate, depth)
            );
            trace.candidates.push(...results.map(result => result.trace));
            const blocker = unresolvedPriority(results);
            if (blocker !== undefined) {
                trace.outcome = blocker;
                trace.decisionRank = first.rank;
                trace.decisionPriority = first.priority;
                trace.candidates.push(...this.skippedCandidates(
                    goal,
                    end,
                    `${blocker}-blocks-lower-precedence`
                ));
                return {
                    status: blocker,
                    goalId: trace.goalId
                };
            }
            const successes = results.filter(
                (result): result is CandidateSuccess =>
                    result.status === 'success'
            );
            if (successes.length > 0) {
                const equivalence = this.equivalentClasses(successes);
                if (equivalence.limitTrace !== undefined) {
                    trace.outcome = 'limit-exceeded';
                    trace.decisionRank = first.rank;
                    trace.decisionPriority = first.priority;
                    trace.candidates.push(...this.skippedCandidates(
                        goal,
                        end,
                        'equivalence-limit-blocks-lower-precedence'
                    ));
                    return {
                        status: 'limit-exceeded',
                        goalId: trace.goalId
                    };
                }
                equivalence.classes.forEach((evidenceClass, classIndex) => {
                    evidenceClass.forEach((success, memberIndex) => {
                        success.trace.equivalenceClass = classIndex;
                        success.trace.outcome = memberIndex === 0
                            ? 'success'
                            : 'equivalent-success';
                        success.trace.reason = memberIndex === 0
                            ? 'checked-evidence-class-representative'
                            : 'definitionally-equal-success';
                    });
                });
                trace.decisionRank = first.rank;
                trace.decisionPriority = first.priority;
                if (equivalence.classes.length > 1) {
                    successes.forEach(success => {
                        success.trace.outcome = 'ambiguous-success';
                        success.trace.reason =
                            'distinct-definitional-evidence-class';
                    });
                    trace.outcome = 'ambiguous';
                    trace.candidates.push(...this.skippedCandidates(
                        goal,
                        end,
                        'ambiguity-blocks-lower-precedence'
                    ));
                    return { status: 'ambiguous', goalId: trace.goalId };
                }
                const evidenceClass = equivalence.classes[0];
                const selected = evidenceClass[0];
                trace.outcome = 'solved';
                trace.selectedProvider = cloneSymbol(
                    selected.provider.providerId
                );
                trace.equivalentProviders = evidenceClass.map(success =>
                    cloneSymbol(success.provider.providerId)
                );
                trace.resultSize = selected.size;
                trace.candidates.push(...this.skippedCandidates(
                    goal,
                    end,
                    'higher-precedence-evidence-solved'
                ));
                return {
                    status: 'solved',
                    selected: cloneSymbol(selected.provider.providerId),
                    term: selected.term,
                    size: selected.size,
                    goalId: trace.goalId
                };
            }
            index = end;
        }
        trace.outcome = 'missing';
        return { status: 'missing', goalId: trace.goalId };
    }

    resolveGoal(
        template: GoalTemplate,
        type: KernelExpression,
        depth: number
    ): ResolutionEdge {
        this.maxDepthReached = Math.max(this.maxDepthReached, depth);
        const preparation = this.prepareGoal(template, type);
        const existing = this.table.get(preparation.tableKey);
        if (existing?.state === 'visiting') {
            return {
                disposition: 'cycle',
                resolution: {
                    status: 'missing',
                    goalId: existing.goalId,
                    cycle: true
                }
            };
        }
        if (existing?.state === 'done' && existing.resolution !== undefined) {
            return {
                disposition: 'table-hit',
                resolution: existing.resolution
            };
        }

        const trace = this.newGoalTrace(preparation, depth);
        if (depth > this.limits.maxDepth) {
            trace.outcome = 'limit-exceeded';
            return {
                disposition: 'expanded',
                resolution: {
                    status: 'limit-exceeded',
                    goalId: trace.goalId
                }
            };
        }
        if (this.table.size >= this.limits.maxTableEntries) {
            trace.outcome = 'limit-exceeded';
            return {
                disposition: 'expanded',
                resolution: {
                    status: 'limit-exceeded',
                    goalId: trace.goalId
                }
            };
        }
        if ('status' in preparation) {
            trace.outcome = preparation.status;
            const resolution: InternalUnsolved = {
                status: preparation.status,
                goalId: trace.goalId
            };
            this.table.set(preparation.tableKey, {
                goalId: trace.goalId,
                state: 'done',
                resolution
            });
            return { disposition: 'expanded', resolution };
        }

        const entry: TableEntry = {
            goalId: trace.goalId,
            state: 'visiting'
        };
        this.table.set(preparation.tableKey, entry);
        const resolution = this.resolvePreparedGoal(
            preparation,
            trace,
            depth
        );
        entry.state = 'done';
        entry.resolution = resolution;
        return { disposition: 'expanded', resolution };
    }

    createReport(root: InternalResolution): CoreLfInstanceSynthesisReport {
        const rootTrace = this.goalTraces.find(
            trace => trace.goalId === root.goalId
        );
        if (rootTrace === undefined) {
            return fail(
                'INTERNAL_INVARIANT',
                'report.rootGoalId',
                'Root synthesis resolution lost its goal trace'
            );
        }
        return freezeData({
            revision: CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
            limits: this.limits,
            usage: {
                fuelUsed: this.fuelUsed,
                candidateAttempts: this.candidateAttempts,
                tableEntries: this.table.size,
                maxDepthReached: this.maxDepthReached
            },
            registryRevision: this.registry.registryRevision,
            scopeRevision: this.scope.scopeRevision,
            scopeFingerprintMaterial: {
                registryCanonicalJson: this.registryCanonicalJson,
                scopeCanonicalJson: this.scopeCanonicalJson
            },
            runtimeFingerprintMaterial: this.runtimeFingerprint,
            rootGoalId: root.goalId,
            target: rootTrace.target,
            outcome: root.status,
            goals: this.goalTraces
        });
    }
}

const rootTemplate = (
    declarations: CoreLfMixedDeclarationBaseContext,
    layoutInput: CoreLfClassInheritanceLayout
): GoalTemplate => {
    let layout: CoreLfClassInheritanceLayout;
    try {
        layout = validateCoreLfClassInheritanceLayout(layoutInput);
    } catch (error: unknown) {
        return fail(
            'INVALID_TARGET',
            'input.targetClass',
            'Synthesis target class must be one completed inheritance layout',
            error instanceof Error ? error : undefined
        );
    }
    const reference: CoreLfClassReference = {
        classId: cloneSymbol(layout.classId),
        parameterCount: layout.schema.parameters.length
    };
    return {
        class: reference,
        coreHeadName: installedClassCoreName(
            declarations,
            reference,
            'input.targetClass'
        ),
        roles: layout.schema.parameters.map(parameter => parameter.role),
        plicities: layout.schema.parameters.map(
            parameter => parameter.parameter.modes.carrier.plicity
        )
    };
};

/** Resolve one ground class goal to explicit checked Core evidence. */
export function synthesizeCoreLfInstance(
    input: CoreLfInstanceSynthesisInput
): CoreLfInstanceSynthesisOutcome {
    if (!record(input)) {
        return fail(
            'INVALID_INPUT',
            'input',
            'Instance synthesis input must be one object'
        );
    }
    if (
        !record(input.declarations) ||
        typeof input.declarations.declaration !== 'function' ||
        input.declarations.environment === undefined
    ) {
        return fail(
            'INVALID_INPUT',
            'input.declarations',
            'Instance synthesis requires one checked declaration base'
        );
    }
    if (
        !(input.context instanceof CoreContext) ||
        input.context.environment !==
            input.declarations.environment.coreEnvironment
    ) {
        return fail(
            'INVALID_CONTEXT',
            'input.context',
            'Instance synthesis context belongs to another declaration base'
        );
    }
    const limits = synthesisLimits(input.limits);
    const runtimeFingerprint = runtimeFingerprintMaterial(
        input.runtimeProgram
    );
    const snapshots = validateSnapshots(input.registry, input.scope);
    if (snapshots.scope.contextDepth !== input.context.depth) {
        return fail(
            'INVALID_CONTEXT',
            'input.scope.contextDepth',
            'Instance scope depth differs from the exact Core context depth'
        );
    }
    const template = rootTemplate(input.declarations, input.targetClass);
    let target: KernelExpression;
    try {
        const checker = createCoreLfChecker(
            input.declarations.environment,
            limits.comparisonStepLimit,
            input.runtimeProgram
        );
        target = checker.check(
            input.context,
            input.target,
            kernelUniverse(provenance(
                'derived',
                'instance synthesis target must inhabit TYPE'
            ))
        ).term;
        if (containsMeta(target)) {
            return fail(
                'INVALID_TARGET',
                'input.target',
                'Instance synthesis requires one meta-free root target'
            );
        }
        expressionArguments(target, template, 'input.target');
    } catch (error: unknown) {
        if (error instanceof CoreLfInstanceSynthesisError) throw error;
        return fail(
            'INVALID_TARGET',
            'input.target',
            'Instance synthesis target is not one checked meta-free class type',
            error instanceof Error ? error : undefined
        );
    }

    const resolver = new CoreLfInstanceResolver(
        input.declarations,
        input.context,
        snapshots.registry,
        snapshots.scope,
        limits,
        snapshots.registryCanonicalJson,
        snapshots.scopeCanonicalJson,
        input.runtimeProgram,
        runtimeFingerprint
    );
    const edge = resolver.resolveGoal(template, target, 0);
    const rootGoal = edge.resolution;
    const goalTrace = resolver.createReport(rootGoal);
    if (rootGoal.status !== 'solved') {
        return freezeData({ status: rootGoal.status, report: goalTrace });
    }
    return freezeData({
        status: 'solved',
        selected: rootGoal.selected,
        term: rootGoal.term,
        type: target,
        resultSize: rootGoal.size,
        report: goalTrace
    });
}

/** Canonical browser-safe JSON for one immutable synthesis report. */
export const serializeCoreLfInstanceSynthesisReport = (
    report: CoreLfInstanceSynthesisReport
): string => {
    try {
        return serializeCoreLfWorkspaceCanonicalJson(
            report,
            'instanceSynthesisReport'
        );
    } catch (error: unknown) {
        return fail(
            'NON_PORTABLE_DATA',
            'report',
            'Instance-synthesis report is not canonical portable data',
            error instanceof Error ? error : undefined
        );
    }
};
