/**
 * Bounded output-parameter discovery over exact checked instance synthesis.
 *
 * This management layer uses explicit role-pattern holes to discover one
 * meta-free class target. It delegates all proof search and final evidence
 * checking to `synthesizeCoreLfInstance`; no hole or class node reaches Core.
 */

import { CoreCheckerError, isCoreKind } from './checker';
import { CoreContext } from './context';
import { serializeCoreExpressionAtDepth } from './core_serialization';
import {
    CoreLfClassInheritanceLayout,
    validateCoreLfClassInheritanceLayout
} from './lf_class_inheritance';
import {
    CoreLfClassParameterRole,
    CoreLfClassReference,
    validateCoreLfClassParameterRoleDependencies
} from './lf_class_schema';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    CoreLfChecker,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfCatalogRuntime,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
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
    CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
    CoreLfInstanceSynthesisLimits,
    CoreLfInstanceSynthesisLimitsInput,
    CoreLfInstanceSynthesisReport,
    CoreLfInstanceSynthesisSolved,
    CoreLfInstanceSynthesisStatus,
    synthesizeCoreLfInstance
} from './lf_instance_synthesis';
import { CoreLfMixedDeclarationBaseContext } from './lf_transfer_mixed';
import { CoreLfQualifiedSymbol } from './lf_transfer';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import {
    KernelCallArgumentInput,
    KernelExpression,
    KernelMetaVariable,
    Plicity,
    kernelAmbientDependencies,
    kernelCall,
    kernelFree,
    kernelInstantiate,
    kernelUniverse,
    provenance
} from './kernel';

export const CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE = Object.freeze({
    revision: 'emdash-lf-instance-role-synthesis-v1' as const,
    targetReadiness:
        'ground-input-and-semi-output-with-explicit-output-holes' as const,
    evidenceBoundary: 'delegated-exact-ground-synthesis' as const,
    providerChoice:
        'rank-then-priority-then-definitional-equivalence' as const,
    expectedOutcomes: CORE_LF_INSTANCE_SYNTHESIS_PROFILE.expectedOutcomes,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type CoreLfInstanceRoleSynthesisStatus =
    typeof CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE.expectedOutcomes[number];

export type CoreLfInstanceRoleSynthesisErrorCode =
    | 'INVALID_INPUT'
    | 'INVALID_CONTEXT'
    | 'INVALID_TARGET_PATTERN'
    | 'INVALID_CLASS_ROLE_DEPENDENCY'
    | 'INVALID_LIMITS'
    | 'INVALID_REGISTRY'
    | 'INVALID_SCOPE'
    | 'INVALID_PROVIDER'
    | 'NON_PORTABLE_DATA'
    | 'INTERNAL_INVARIANT';

export class CoreLfInstanceRoleSynthesisError extends Error {
    constructor(
        public readonly code: CoreLfInstanceRoleSynthesisErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfInstanceRoleSynthesisError';
    }
}

export type CoreLfInstanceRoleTargetArgumentInput =
    | {
        readonly kind: 'known';
        readonly value: KernelExpression;
    }
    | {
        readonly kind: 'infer-output';
    };

export interface CoreLfInstanceRoleSynthesisInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly context: CoreContext;
    readonly runtimeProgram?: CoreLfCatalogRuntime;
    readonly targetClass: CoreLfClassInheritanceLayout;
    readonly targetArguments:
        readonly CoreLfInstanceRoleTargetArgumentInput[];
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly scope: CoreLfInstanceScopeSnapshot;
    readonly limits?: CoreLfInstanceSynthesisLimitsInput;
}

export interface CoreLfInstanceRoleTargetArgumentTrace {
    readonly ordinal: number;
    readonly role: CoreLfClassParameterRole;
    readonly plicity: Plicity;
    readonly kind: 'known' | 'infer-output';
    readonly value?: string;
}

export interface CoreLfInstanceRoleInferredOutput {
    readonly ordinal: number;
    readonly value: KernelExpression;
}

export interface CoreLfInstanceRoleInferredOutputTrace {
    readonly ordinal: number;
    readonly value: string;
}

export type CoreLfInstanceRoleCandidateOutcome =
    | 'rejected'
    | 'stuck'
    | 'limit-exceeded'
    | 'inferred-target'
    | 'duplicate-target'
    | 'skipped';

export interface CoreLfInstanceRoleCandidateTrace {
    readonly providerId: CoreLfQualifiedSymbol;
    readonly rank: number;
    readonly priority: number;
    readonly outcome: CoreLfInstanceRoleCandidateOutcome;
    readonly reason: string;
    readonly targetKey?: string;
    readonly inferredTarget?: string;
    readonly inferredOutputs?:
        readonly CoreLfInstanceRoleInferredOutputTrace[];
}

export interface CoreLfInstanceRoleDelegatedSearchTrace {
    readonly targetKey: string;
    readonly target: string;
    readonly inferredOutputs:
        readonly CoreLfInstanceRoleInferredOutputTrace[];
    readonly outcome: CoreLfInstanceSynthesisStatus;
    readonly report: CoreLfInstanceSynthesisReport;
}

export interface CoreLfInstanceRoleSynthesisUsage {
    readonly fuelUsed: number;
    readonly seedCandidateAttempts: number;
    readonly delegatedCandidateAttempts: number;
    readonly inferredTargets: number;
    readonly delegatedSearches: number;
    readonly delegatedTableEntries: number;
    readonly maxDepthReached: number;
}

export interface CoreLfInstanceRoleSynthesisReport {
    readonly revision:
        typeof CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE.revision;
    readonly status: CoreLfInstanceRoleSynthesisStatus;
    readonly reason: string;
    readonly limits: CoreLfInstanceSynthesisLimits;
    readonly usage: CoreLfInstanceRoleSynthesisUsage;
    readonly registryRevision: string;
    readonly scopeRevision: string;
    readonly registryCanonicalJson: string;
    readonly scopeCanonicalJson: string;
    readonly targetClass: CoreLfClassReference;
    readonly coreHeadName: string;
    readonly arguments: readonly CoreLfInstanceRoleTargetArgumentTrace[];
    readonly decisionRank?: number;
    readonly decisionPriority?: number;
    readonly selectedProvider?: CoreLfQualifiedSymbol;
    readonly selectedTarget?: string;
    readonly inferredOutputs?:
        readonly CoreLfInstanceRoleInferredOutputTrace[];
    readonly candidates: readonly CoreLfInstanceRoleCandidateTrace[];
    readonly searches: readonly CoreLfInstanceRoleDelegatedSearchTrace[];
}

interface CoreLfInstanceRoleSynthesisOutcomeBase {
    readonly status: CoreLfInstanceRoleSynthesisStatus;
    readonly report: CoreLfInstanceRoleSynthesisReport;
}

export interface CoreLfInstanceRoleSynthesisSolved
extends CoreLfInstanceRoleSynthesisOutcomeBase {
    readonly status: 'solved';
    readonly selected: CoreLfQualifiedSymbol;
    readonly term: KernelExpression;
    readonly type: KernelExpression;
    readonly resultSize: number;
    readonly inferredOutputs: readonly CoreLfInstanceRoleInferredOutput[];
    readonly synthesis: CoreLfInstanceSynthesisReport;
}

export interface CoreLfInstanceRoleSynthesisUnsolved
extends CoreLfInstanceRoleSynthesisOutcomeBase {
    readonly status: Exclude<
        CoreLfInstanceRoleSynthesisStatus,
        'solved'
    >;
}

export type CoreLfInstanceRoleSynthesisOutcome =
    | CoreLfInstanceRoleSynthesisSolved
    | CoreLfInstanceRoleSynthesisUnsolved;

interface TargetTemplate {
    readonly class: CoreLfClassReference;
    readonly coreHeadName: string;
    readonly roles: readonly CoreLfClassParameterRole[];
    readonly plicities: readonly Plicity[];
}

interface ValidatedSnapshots {
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly scope: CoreLfInstanceScopeSnapshot;
    readonly registryCanonicalJson: string;
    readonly scopeCanonicalJson: string;
}

interface PatternTarget {
    readonly target: KernelExpression;
    readonly outputMetas: readonly {
        readonly ordinal: number;
        readonly meta: KernelMetaVariable;
    }[];
}

interface SeedInference {
    readonly status: 'inferred';
    readonly trace: MutableCandidateTrace;
    readonly target: KernelExpression;
    readonly targetKey: string;
    readonly inferredOutputs: readonly CoreLfInstanceRoleInferredOutput[];
}

interface SeedUnsolved {
    readonly status: 'rejected' | 'stuck' | 'limit-exceeded';
    readonly trace: MutableCandidateTrace;
}

type SeedResult = SeedInference | SeedUnsolved;

interface MutableCandidateTrace {
    providerId: CoreLfQualifiedSymbol;
    rank: number;
    priority: number;
    outcome: CoreLfInstanceRoleCandidateOutcome;
    reason: string;
    targetKey?: string;
    inferredTarget?: string;
    inferredOutputs?: CoreLfInstanceRoleInferredOutputTrace[];
}

interface DelegatedSuccess {
    readonly target: KernelExpression;
    readonly targetKey: string;
    readonly inferredOutputs: readonly CoreLfInstanceRoleInferredOutput[];
    readonly outcome: CoreLfInstanceSynthesisSolved;
}

const fail = (
    code: CoreLfInstanceRoleSynthesisErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfInstanceRoleSynthesisError(
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

const checkedLimit = (value: unknown, path: string): number => {
    if (!Number.isSafeInteger(value) || (value as number) < 0) {
        return fail(
            'INVALID_LIMITS',
            path,
            'Role-synthesis limits must be nonnegative safe integers'
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
            'Role-synthesis limits must be an object when supplied'
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
            input?.comparisonStepLimit ??
                CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
            'input.limits.comparisonStepLimit'
        )
    });
};

const validateRuntime = (
    runtimeProgram: CoreLfCatalogRuntime | undefined
): void => {
    if (runtimeProgram === undefined) return;
    if (
        !record(runtimeProgram) ||
        typeof runtimeProgram.revision !== 'string' ||
        runtimeProgram.revision.length === 0 ||
        !Array.isArray(runtimeProgram.ruleIds) ||
        runtimeProgram.ruleIds.some(ruleId =>
            typeof ruleId !== 'string' || ruleId.length === 0
        ) ||
        new Set(runtimeProgram.ruleIds).size !==
            runtimeProgram.ruleIds.length ||
        typeof runtimeProgram.rewriteHead !== 'function'
    ) {
        return fail(
            'INVALID_INPUT',
            'input.runtimeProgram',
            'Role synthesis requires one reviewed catalog runtime'
        );
    }
};

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
                'Role synthesis requires one registry snapshot'
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
        if (!record(scopeInput)) {
            return fail(
                'INVALID_SCOPE',
                'input.scope',
                'Role synthesis requires one scope snapshot'
            );
        }
        const scope = createCoreLfInstanceScopeSnapshot({
            revision: scopeInput.scopeRevision,
            registry,
            moduleId: scopeInput.moduleId,
            contextDepth: scopeInput.contextDepth,
            localFrames: scopeInput.localFrames,
            openedNamedScopes: scopeInput.openedNamedScopes,
            imports: scopeInput.imports
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
        if (error instanceof CoreLfInstanceRoleSynthesisError) throw error;
        const code = phase === 'registry'
            ? 'INVALID_REGISTRY'
            : 'INVALID_SCOPE';
        return fail(
            code,
            code === 'INVALID_REGISTRY' ? 'input.registry' : 'input.scope',
            `Invalid instance ${phase} snapshot`,
            error instanceof Error ? error : undefined
        );
    }
};

const targetTemplate = (
    declarations: CoreLfMixedDeclarationBaseContext,
    layoutInput: CoreLfClassInheritanceLayout
): TargetTemplate => {
    let layout: CoreLfClassInheritanceLayout;
    try {
        layout = validateCoreLfClassInheritanceLayout(layoutInput);
        validateCoreLfClassParameterRoleDependencies(
            layout.schema,
            'input.targetClass.schema'
        );
    } catch (error: unknown) {
        return fail(
            record(error) &&
                error.code === 'INVALID_PARAMETER_ROLE_DEPENDENCY'
                ? 'INVALID_CLASS_ROLE_DEPENDENCY'
                : 'INVALID_TARGET_PATTERN',
            'input.targetClass',
            'Role synthesis requires one dependency-safe completed class layout',
            error instanceof Error ? error : undefined
        );
    }
    const reference: CoreLfClassReference = {
        classId: cloneSymbol(layout.classId),
        parameterCount: layout.schema.parameters.length
    };
    const declaration = declarations.declaration(reference.classId);
    if (
        declaration === undefined ||
        declaration.link.kind !== 'free-declaration' ||
        !declaration.status.startsWith('installed-') ||
        !sameSymbol(declaration.symbol, reference.classId) ||
        !sameSymbol(declaration.link.symbol, reference.classId)
    ) {
        return fail(
            'INVALID_TARGET_PATTERN',
            'input.targetClass',
            `Class '${displaySymbol(reference.classId)}' is not installed`
        );
    }
    return {
        class: reference,
        coreHeadName: declaration.link.coreName,
        roles: layout.schema.parameters.map(parameter => parameter.role),
        plicities: layout.schema.parameters.map(
            parameter => parameter.parameter.modes.carrier.plicity
        )
    };
};

const validatePattern = (
    input: readonly CoreLfInstanceRoleTargetArgumentInput[],
    template: TargetTemplate
): readonly CoreLfInstanceRoleTargetArgumentInput[] => {
    if (
        !Array.isArray(input) ||
        input.length !== template.class.parameterCount
    ) {
        return fail(
            'INVALID_TARGET_PATTERN',
            'input.targetArguments',
            `Expected ${template.class.parameterCount} ordered arguments`
        );
    }
    let holes = 0;
    const pattern = input.map((argument, ordinal) => {
        const path = `input.targetArguments[${ordinal}]`;
        if (!record(argument)) {
            return fail(
                'INVALID_TARGET_PATTERN',
                path,
                'Role target argument must be one explicit pattern entry'
            );
        }
        if (argument.kind === 'infer-output') {
            if (template.roles[ordinal] !== 'output') {
                return fail(
                    'INVALID_TARGET_PATTERN',
                    path,
                    'Only an output class parameter may be inferred in 10A'
                );
            }
            holes++;
            return { kind: 'infer-output' as const };
        }
        const value = argument.value as unknown as KernelExpression;
        if (
            argument.kind !== 'known' ||
            !record(argument.value) ||
            containsMeta(value)
        ) {
            return fail(
                'INVALID_TARGET_PATTERN',
                path,
                'Known role target arguments must be meta-free Core expressions'
            );
        }
        return {
            kind: 'known' as const,
            value: cloneData(value)
        };
    });
    if (holes === 0) {
        return fail(
            'INVALID_TARGET_PATTERN',
            'input.targetArguments',
            'Role synthesis requires at least one infer-output argument'
        );
    }
    return pattern;
};

const buildPatternTarget = (
    checker: CoreLfChecker,
    context: CoreContext,
    template: TargetTemplate,
    pattern: readonly CoreLfInstanceRoleTargetArgumentInput[],
    source: string
): PatternTarget => {
    const nodeProvenance = provenance('derived', source);
    const callee = kernelFree(template.coreHeadName, nodeProvenance);
    const inferred = checker.infer(context, callee);
    if (isCoreKind(inferred.type)) {
        return fail(
            'INVALID_TARGET_PATTERN',
            'input.targetClass',
            'Installed class head inferred checker KIND'
        );
    }
    let currentType = inferred.type;
    const arguments_: KernelCallArgumentInput[] = [];
    const outputMetas: Array<{
        readonly ordinal: number;
        readonly meta: KernelMetaVariable;
    }> = [];
    pattern.forEach((argument, ordinal) => {
        currentType = checker.lfSession.zonk(currentType);
        if (
            currentType.tag !== 'pi' ||
            currentType.binder.mode.plicity !== template.plicities[ordinal]
        ) {
            return fail(
                'INVALID_TARGET_PATTERN',
                `input.targetArguments[${ordinal}]`,
                'Class carrier telescope differs from its role metadata'
            );
        }
        let value: KernelExpression;
        if (argument.kind === 'known') {
            try {
                value = checker.checkRefinement(
                    context,
                    argument.value,
                    currentType.binder.type
                ).term;
            } catch (error: unknown) {
                return fail(
                    'INVALID_TARGET_PATTERN',
                    `input.targetArguments[${ordinal}].value`,
                    'Known role argument does not check at its class parameter',
                    error instanceof Error ? error : undefined
                );
            }
        } else {
            const meta = checker.lfSession.freshMeta(
                context,
                currentType.binder.type,
                provenance('derived', `${source} output ${ordinal}`)
            );
            value = meta;
            outputMetas.push({ ordinal, meta });
        }
        arguments_.push({
            plicity: currentType.binder.mode.plicity,
            value,
            provenance: nodeProvenance
        });
        currentType = checker.lfSession.zonk(kernelInstantiate(
            currentType.body,
            value
        ));
    });
    return {
        target: arguments_.length === 0
            ? callee
            : kernelCall(callee, arguments_, nodeProvenance),
        outputMetas
    };
};

const providerResultDependsOnPremise = (
    provider: CoreLfInstanceProviderDeclaration
): boolean => {
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
};

const candidateTrace = (
    candidate: CoreLfInstanceScopeCandidate
): MutableCandidateTrace => ({
    providerId: cloneSymbol(candidate.providerId),
    rank: candidate.rank,
    priority: candidate.priority,
    outcome: 'rejected',
    reason: 'not-attempted'
});

const inferSeedTarget = (
    declarations: CoreLfMixedDeclarationBaseContext,
    context: CoreContext,
    runtimeProgram: CoreLfCatalogRuntime | undefined,
    comparisonStepLimit: number,
    template: TargetTemplate,
    pattern: readonly CoreLfInstanceRoleTargetArgumentInput[],
    provider: CoreLfInstanceProviderDeclaration,
    candidate: CoreLfInstanceScopeCandidate
): SeedResult => {
    const trace = candidateTrace(candidate);
    if (providerResultDependsOnPremise(provider)) {
        trace.outcome = 'stuck';
        trace.reason = 'provider-result-depends-on-instance-premise';
        return { status: 'stuck', trace };
    }
    const checker = createCoreLfChecker(
        declarations.environment,
        comparisonStepLimit,
        runtimeProgram
    );
    try {
        checker.check(context, provider.term, provider.type);
    } catch (error: unknown) {
        return fail(
            'INVALID_PROVIDER',
            `providers.${displaySymbol(provider.providerId)}`,
            'Role seed provider does not recheck in the exact context',
            error instanceof Error ? error : undefined
        );
    }
    let currentType = provider.type;
    const metas: Array<{
        readonly binder: CoreLfInstanceProviderDeclaration['telescope'][number];
        readonly meta: KernelMetaVariable;
    }> = [];
    const arguments_: KernelCallArgumentInput[] = [];
    for (const binder of provider.telescope) {
        if (currentType.tag !== 'pi') {
            return fail(
                'INVALID_PROVIDER',
                `providers.${displaySymbol(provider.providerId)}.type`,
                'Provider telescope ended before its checked Pi type'
            );
        }
        const meta = checker.lfSession.freshMeta(
            context,
            currentType.binder.type,
            provenance(
                'derived',
                `role seed ${displaySymbol(provider.providerId)} ` +
                    `binder ${binder.ordinal}`
            )
        );
        metas.push({ binder, meta });
        arguments_.push({
            plicity: currentType.binder.mode.plicity,
            value: meta,
            provenance: meta.provenance
        });
        currentType = checker.lfSession.zonk(kernelInstantiate(
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
                `role seed candidate ${displaySymbol(provider.providerId)}`
            )
        );
    const built = buildPatternTarget(
        checker,
        context,
        template,
        pattern,
        `role seed target ${displaySymbol(provider.providerId)}`
    );
    try {
        checker.checkRefinement(context, application, built.target);
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
                trace.reason = 'candidate-output-unification-stuck';
                return { status: 'stuck', trace };
            }
            if (
                error.code === 'TYPE_MISMATCH' ||
                error.code === 'PLICITY_MISMATCH' ||
                error.code === 'BINDER_MODE_MISMATCH' ||
                error.code === 'CONSTRAINT_REJECTED'
            ) {
                trace.outcome = 'rejected';
                trace.reason = 'candidate-known-input-mismatch';
                return { status: 'rejected', trace };
            }
        }
        return fail(
            'INVALID_PROVIDER',
            `providers.${displaySymbol(provider.providerId)}`,
            'Provider could not be matched at the role refinement boundary',
            error instanceof Error ? error : undefined
        );
    }
    for (const entry of metas) {
        const value = checker.lfSession.zonk(entry.meta);
        if (entry.binder.kind === 'ordinary' && containsMeta(value)) {
            trace.outcome = 'stuck';
            trace.reason = 'ordinary-parameter-not-result-determined';
            return { status: 'stuck', trace };
        }
        if (entry.binder.kind === 'instance-premise' && value.tag !== 'meta') {
            trace.outcome = 'stuck';
            trace.reason = 'result-match-assigned-instance-premise';
            return { status: 'stuck', trace };
        }
    }
    const inferredOutputs = built.outputMetas.map(entry => ({
        ordinal: entry.ordinal,
        value: checker.lfSession.zonk(entry.meta)
    }));
    if (inferredOutputs.some(output => containsMeta(output.value))) {
        trace.outcome = 'stuck';
        trace.reason = 'candidate-did-not-determine-every-output';
        return { status: 'stuck', trace };
    }
    const target = checker.lfSession.zonk(built.target);
    if (containsMeta(target)) {
        trace.outcome = 'stuck';
        trace.reason = 'candidate-target-retains-metavariable';
        return { status: 'stuck', trace };
    }
    try {
        checker.check(
            context,
            target,
            kernelUniverse(provenance(
                'derived',
                'role seed target must inhabit TYPE'
            ))
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_PROVIDER',
            `providers.${displaySymbol(provider.providerId)}.result`,
            'Inferred role target is not a checked class type',
            error instanceof Error ? error : undefined
        );
    }
    const targetKey = serializeCoreExpressionAtDepth(target, context.depth);
    trace.outcome = 'inferred-target';
    trace.reason = 'candidate-result-determined-ground-output';
    trace.targetKey = targetKey;
    trace.inferredTarget = targetKey;
    trace.inferredOutputs = inferredOutputs.map(output => ({
        ordinal: output.ordinal,
        value: serializeCoreExpressionAtDepth(output.value, context.depth)
    }));
    return {
        status: 'inferred',
        trace,
        target,
        targetKey,
        inferredOutputs
    };
};

const comparisonClass = (
    declarations: CoreLfMixedDeclarationBaseContext,
    runtimeProgram: CoreLfCatalogRuntime | undefined,
    comparisonStepLimit: number,
    successes: readonly DelegatedSuccess[]
): {
    readonly classes: readonly DelegatedSuccess[][];
    readonly limit: boolean;
} => {
    const classes: DelegatedSuccess[][] = [];
    for (const success of successes) {
        let found: DelegatedSuccess[] | undefined;
        for (const existing of classes) {
            const typeComparison = coreLfDefinitionalCompare(
                declarations.environment,
                success.outcome.type,
                existing[0].outcome.type,
                comparisonStepLimit,
                undefined,
                runtimeProgram
            );
            if (typeComparison.status === 'step-limit-exceeded') {
                return { classes, limit: true };
            }
            if (typeComparison.status !== 'equal') continue;
            const termComparison = coreLfDefinitionalCompare(
                declarations.environment,
                success.outcome.term,
                existing[0].outcome.term,
                comparisonStepLimit,
                undefined,
                runtimeProgram
            );
            if (termComparison.status === 'step-limit-exceeded') {
                return { classes, limit: true };
            }
            if (termComparison.status === 'equal') {
                found = existing;
                break;
            }
        }
        if (found === undefined) classes.push([success]);
        else found.push(success);
    }
    return { classes, limit: false };
};

const unresolvedPriority = (
    statuses: readonly CoreLfInstanceRoleSynthesisStatus[]
): Exclude<CoreLfInstanceRoleSynthesisStatus, 'solved' | 'missing'> | undefined => {
    if (statuses.includes('limit-exceeded')) return 'limit-exceeded';
    if (statuses.includes('ambiguous')) return 'ambiguous';
    if (statuses.includes('stuck')) return 'stuck';
    return undefined;
};

/**
 * Infer output arguments, then resolve the selected ground class target to
 * explicit checked Core evidence.
 */
export function synthesizeCoreLfInstanceByRoles(
    input: CoreLfInstanceRoleSynthesisInput
): CoreLfInstanceRoleSynthesisOutcome {
    if (!record(input)) {
        return fail(
            'INVALID_INPUT',
            'input',
            'Role-synthesis input must be one object'
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
            'Role synthesis requires one checked declaration base'
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
            'Role-synthesis context belongs to another declaration base'
        );
    }
    const limits = synthesisLimits(input.limits);
    validateRuntime(input.runtimeProgram);
    const snapshots = validateSnapshots(input.registry, input.scope);
    if (snapshots.scope.contextDepth !== input.context.depth) {
        return fail(
            'INVALID_CONTEXT',
            'input.scope.contextDepth',
            'Instance scope depth differs from the exact Core context depth'
        );
    }
    const template = targetTemplate(input.declarations, input.targetClass);
    const pattern = validatePattern(input.targetArguments, template);
    buildPatternTarget(
        createCoreLfChecker(
            input.declarations.environment,
            limits.comparisonStepLimit,
            input.runtimeProgram
        ),
        input.context,
        template,
        pattern,
        'role target validation'
    );

    const providerById = new Map(
        snapshots.registry.providers.map(provider => [
            symbolKey(provider.providerId),
            provider
        ])
    );
    const candidates = snapshots.scope.candidates.filter(candidate => {
        const provider = providerById.get(symbolKey(candidate.providerId));
        return provider !== undefined &&
            sameClass(provider.result.class, template.class) &&
            provider.result.coreHeadName === template.coreHeadName;
    });
    const traces: MutableCandidateTrace[] = [];
    const searches: CoreLfInstanceRoleDelegatedSearchTrace[] = [];
    let fuelUsed = 0;
    let seedCandidateAttempts = 0;
    let delegatedCandidateAttempts = 0;
    let delegatedTableEntries = 0;
    let maxDepthReached = 0;
    let inferredTargetCount = 0;
    let decisionRank: number | undefined;
    let decisionPriority: number | undefined;

    const argumentTraces: CoreLfInstanceRoleTargetArgumentTrace[] =
        pattern.map((argument, ordinal) => ({
            ordinal,
            role: template.roles[ordinal],
            plicity: template.plicities[ordinal],
            kind: argument.kind,
            ...(argument.kind === 'known'
                ? {
                    value: serializeCoreExpressionAtDepth(
                        argument.value,
                        input.context.depth
                    )
                }
                : {})
        }));

    const report = (
        status: CoreLfInstanceRoleSynthesisStatus,
        reason: string,
        selected?: DelegatedSuccess
    ): CoreLfInstanceRoleSynthesisReport => freezeData({
        revision: CORE_LF_INSTANCE_ROLE_SYNTHESIS_PROFILE.revision,
        status,
        reason,
        limits,
        usage: {
            fuelUsed,
            seedCandidateAttempts,
            delegatedCandidateAttempts,
            inferredTargets: inferredTargetCount,
            delegatedSearches: searches.length,
            delegatedTableEntries,
            maxDepthReached
        },
        registryRevision: snapshots.registry.registryRevision,
        scopeRevision: snapshots.scope.scopeRevision,
        registryCanonicalJson: snapshots.registryCanonicalJson,
        scopeCanonicalJson: snapshots.scopeCanonicalJson,
        targetClass: cloneClass(template.class),
        coreHeadName: template.coreHeadName,
        arguments: argumentTraces,
        ...(decisionRank === undefined ? {} : { decisionRank }),
        ...(decisionPriority === undefined ? {} : { decisionPriority }),
        ...(selected === undefined
            ? {}
            : {
                selectedProvider: cloneSymbol(selected.outcome.selected),
                selectedTarget: serializeCoreExpressionAtDepth(
                    selected.outcome.type,
                    input.context.depth
                ),
                inferredOutputs: selected.inferredOutputs.map(output => ({
                    ordinal: output.ordinal,
                    value: serializeCoreExpressionAtDepth(
                        output.value,
                        input.context.depth
                    )
                }))
            }),
        candidates: candidates.map(candidate => {
            const attempted = traces.find(trace =>
                sameSymbol(trace.providerId, candidate.providerId)
            );
            if (attempted !== undefined) return attempted;
            return {
                ...candidateTrace(candidate),
                outcome: 'skipped' as const,
                reason: `role-search-ended-${reason}`
            };
        }),
        searches
    });

    if (candidates.length === 0) {
        return freezeData({
            status: 'missing',
            report: report('missing', 'no-visible-provider-for-class-head')
        });
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
        const seeds: SeedResult[] = [];
        for (const candidate of group) {
            if (fuelUsed >= limits.maxFuel) {
                const trace = candidateTrace(candidate);
                trace.outcome = 'limit-exceeded';
                trace.reason = 'role-synthesis-fuel-exhausted';
                seeds.push({ status: 'limit-exceeded', trace });
                traces.push(trace);
                continue;
            }
            fuelUsed++;
            seedCandidateAttempts++;
            const provider = providerById.get(symbolKey(candidate.providerId));
            if (provider === undefined) {
                return fail(
                    'INTERNAL_INVARIANT',
                    `scope.candidates.${displaySymbol(candidate.providerId)}`,
                    'Validated candidate lost its provider declaration'
                );
            }
            if (
                provider.source.kind === 'local-bound'
                    ? provider.ambientDepth !== input.context.depth
                    : provider.ambientDepth !== 0
            ) {
                return fail(
                    'INVALID_PROVIDER',
                    `providers.${displaySymbol(provider.providerId)}`,
                    'Role seed provider has the wrong ambient Core depth'
                );
            }
            const seed = inferSeedTarget(
                input.declarations,
                input.context,
                input.runtimeProgram,
                limits.comparisonStepLimit,
                template,
                pattern,
                provider,
                candidate
            );
            seeds.push(seed);
            traces.push(seed.trace);
        }
        const seedBlocker = unresolvedPriority(seeds.map(seed => {
            if (seed.status === 'inferred') return 'solved';
            if (seed.status === 'rejected') return 'missing';
            return seed.status;
        }));
        if (seedBlocker !== undefined) {
            decisionRank = first.rank;
            decisionPriority = first.priority;
            return freezeData({
                status: seedBlocker,
                report: report(
                    seedBlocker,
                    `role-seed-${seedBlocker}-blocks-lower-precedence`
                )
            });
        }
        const uniqueTargets = new Map<string, SeedInference>();
        for (const seed of seeds) {
            if (seed.status !== 'inferred') continue;
            const existing = uniqueTargets.get(seed.targetKey);
            if (existing !== undefined) {
                seed.trace.outcome = 'duplicate-target';
                seed.trace.reason = 'same-canonical-ground-target';
                continue;
            }
            if (inferredTargetCount >= limits.maxTableEntries) {
                seed.trace.outcome = 'limit-exceeded';
                seed.trace.reason = 'inferred-target-table-limit';
                decisionRank = first.rank;
                decisionPriority = first.priority;
                return freezeData({
                    status: 'limit-exceeded',
                    report: report(
                        'limit-exceeded',
                        'inferred-target-table-limit'
                    )
                });
            }
            uniqueTargets.set(seed.targetKey, seed);
            inferredTargetCount++;
        }

        const successes: DelegatedSuccess[] = [];
        const delegatedStatuses: CoreLfInstanceRoleSynthesisStatus[] = [];
        for (const seed of uniqueTargets.values()) {
            const remainingFuel = Math.max(0, limits.maxFuel - fuelUsed);
            const remainingTableEntries = Math.max(
                0,
                limits.maxTableEntries -
                    inferredTargetCount -
                    delegatedTableEntries
            );
            const outcome = synthesizeCoreLfInstance({
                declarations: input.declarations,
                context: input.context,
                runtimeProgram: input.runtimeProgram,
                targetClass: input.targetClass,
                target: seed.target,
                registry: snapshots.registry,
                scope: snapshots.scope,
                limits: {
                    ...limits,
                    maxFuel: remainingFuel,
                    maxTableEntries: remainingTableEntries
                }
            });
            fuelUsed += outcome.report.usage.fuelUsed;
            delegatedCandidateAttempts +=
                outcome.report.usage.candidateAttempts;
            delegatedTableEntries += outcome.report.usage.tableEntries;
            maxDepthReached = Math.max(
                maxDepthReached,
                outcome.report.usage.maxDepthReached
            );
            delegatedStatuses.push(outcome.status);
            searches.push({
                targetKey: seed.targetKey,
                target: serializeCoreExpressionAtDepth(
                    seed.target,
                    input.context.depth
                ),
                inferredOutputs: seed.inferredOutputs.map(output => ({
                    ordinal: output.ordinal,
                    value: serializeCoreExpressionAtDepth(
                        output.value,
                        input.context.depth
                    )
                })),
                outcome: outcome.status,
                report: outcome.report
            });
            if (outcome.status === 'solved') {
                successes.push({
                    target: seed.target,
                    targetKey: seed.targetKey,
                    inferredOutputs: seed.inferredOutputs,
                    outcome
                });
            }
        }
        const delegatedBlocker = unresolvedPriority(delegatedStatuses);
        if (delegatedBlocker !== undefined) {
            decisionRank = first.rank;
            decisionPriority = first.priority;
            return freezeData({
                status: delegatedBlocker,
                report: report(
                    delegatedBlocker,
                    `delegated-${delegatedBlocker}-blocks-lower-precedence`
                )
            });
        }
        if (successes.length > 0) {
            decisionRank = first.rank;
            decisionPriority = first.priority;
            const comparison = comparisonClass(
                input.declarations,
                input.runtimeProgram,
                limits.comparisonStepLimit,
                successes
            );
            if (comparison.limit) {
                return freezeData({
                    status: 'limit-exceeded',
                    report: report(
                        'limit-exceeded',
                        'output-equivalence-comparison-step-limit'
                    )
                });
            }
            if (comparison.classes.length !== 1) {
                return freezeData({
                    status: 'ambiguous',
                    report: report(
                        'ambiguous',
                        'distinct-output-or-evidence-equivalence-class'
                    )
                });
            }
            const selected = comparison.classes[0][0];
            return freezeData({
                status: 'solved',
                selected: cloneSymbol(selected.outcome.selected),
                term: selected.outcome.term,
                type: selected.outcome.type,
                resultSize: selected.outcome.resultSize,
                inferredOutputs: selected.inferredOutputs,
                synthesis: selected.outcome.report,
                report: report(
                    'solved',
                    'explicit-meta-free-output-target-and-evidence-checked',
                    selected
                )
            });
        }
        index = end;
    }
    return freezeData({
        status: 'missing',
        report: report('missing', 'no-role-seed-produced-checked-evidence')
    });
}

/** Canonical browser-safe JSON for one immutable role-synthesis report. */
export const serializeCoreLfInstanceRoleSynthesisReport = (
    report: CoreLfInstanceRoleSynthesisReport
): string => {
    try {
        return serializeCoreLfWorkspaceCanonicalJson(
            report,
            'instanceRoleSynthesisReport'
        );
    } catch (error: unknown) {
        return fail(
            'NON_PORTABLE_DATA',
            'report',
            'Instance role-synthesis report is not canonical portable data',
            error instanceof Error ? error : undefined
        );
    }
};
