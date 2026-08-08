/**
 * Browser-safe exact same-module LF fragment chains for AI-authored work.
 *
 * This first fragment profile composes one pinned source module only. Source
 * references name exact provider revision tuples; compilation delegates to
 * the existing declaration, mixed-phase, runtime, proof, and visibility
 * engines. Cross-module provider graphs remain a separate later profile.
 */

import {
    CORE_EXPLICIT_SERIALIZATION_REVISION,
    serializeCoreExpression
} from './core_serialization';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferPolicyOverlay,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclaration,
    CoreLfCompiledDeclarationModule,
    CoreLfTransferDeclarationLink,
    CoreLfTransferDeclarationLinkage,
    compileCoreLfDeclarations,
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfCompiledMixedModule,
    CoreLfMixedDeclarationBaseContext,
    CoreLfMixedDeclarationContext,
    CoreLfMixedDeclarationLinkage,
    CoreLfMixedPhasePlan,
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import {
    CoreLfCompiledProofProgram,
    CoreLfComposedProofProgram,
    composeCoreLfProofPrograms
} from './lf_transfer_proof';
import {
    CoreLfCompiledRuntimeFragment,
    CoreLfRuntimeFragmentDependency,
    composeCoreLfRuntimeDependencies
} from './lf_transfer_runtime';
import {
    CoreLfCompiledModuleInterface,
    createCoreLfCompiledModuleInterface
} from './lf_transfer_visibility';
import {
    CoreLfDeclarationWorkspaceInterfaceSnapshot,
    createCoreLfDeclarationWorkspaceInterfaceSnapshot,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE = Object.freeze({
    revision: 'emdash-lf-same-module-fragment-workspace-v1' as const,
    fragmentSourceSnapshotRevision:
        'emdash-lf-same-module-fragment-source-v1' as const,
    workspaceSourceSnapshotRevision:
        'emdash-lf-same-module-fragment-workspace-source-v1' as const,
    workspaceSnapshotRevision:
        'emdash-lf-same-module-fragment-snapshot-v1' as const,
    contentProfile:
        'declaration-or-noninductive-mixed-fragments' as const,
    providerIdentityProfile:
        'module-fragment-module-policy-linkage-revisions' as const,
    runtimeLineageProfile: 'explicit-latest-local-provider' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    executesIncrementally: false as const,
    supportsDependencyModules: false as const,
    supportsInductives: false as const,
    acceptsCompilerCallbacks: false as const
});

/**
 * Internal-chain profile used only as a checked component of the 1B2B module
 * graph. Unlike the public 1B2A profile it admits explicit dependency-module
 * externals, but it performs no module acquisition or provider selection.
 */
export const CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE = Object.freeze({
    revision: 'emdash-lf-dependency-module-fragment-chain-v1' as const,
    workspaceSourceSnapshotRevision:
        'emdash-lf-dependency-module-fragment-chain-source-v1' as const,
    workspaceSnapshotRevision:
        'emdash-lf-dependency-module-fragment-chain-snapshot-v1' as const,
    supportsDependencyModules: true as const,
    acceptsCompilerCallbacks: false as const
});

export const serializeCoreLfSameModuleFragmentWorkspaceProfile = (): string =>
    `${JSON.stringify(
        CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE,
        null,
        2
    )}\n`;

export type CoreLfSameModuleFragmentWorkspaceErrorCode =
    | 'INVALID_WORKSPACE'
    | 'INVALID_FRAGMENT'
    | 'DUPLICATE_FRAGMENT'
    | 'SOURCE_PIN_DRIFT'
    | 'OVERLAPPING_SOURCE_ORDER'
    | 'UNSUPPORTED_FRAGMENT'
    | 'MISSING_PROVIDER'
    | 'DUPLICATE_PROVIDER'
    | 'INVALID_PROVIDER'
    | 'PROVIDER_DRIFT'
    | 'INVALID_RUNTIME_PROVIDER';

export class CoreLfSameModuleFragmentWorkspaceError extends Error {
    constructor(
        public readonly code:
            CoreLfSameModuleFragmentWorkspaceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfSameModuleFragmentWorkspaceError';
    }
}

const fail = (
    code: CoreLfSameModuleFragmentWorkspaceErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfSameModuleFragmentWorkspaceError(code, path, message);
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

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const WORKSPACE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

export interface CoreLfWorkspaceFragmentIdentity {
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly moduleRevision: string;
    readonly policyRevision: string;
    readonly linkageRevision: string;
}

const fragmentIdentity = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    linkage: {
        readonly revision: string;
        readonly moduleRevision: string;
        readonly moduleId: string;
        readonly fragmentId: string;
    }
): CoreLfWorkspaceFragmentIdentity => deepFreeze({
    moduleId: module.moduleId,
    fragmentId: module.fragmentId,
    moduleRevision: module.revision,
    policyRevision: policy.revision,
    linkageRevision: linkage.revision
});

const identityKey = (
    identity: CoreLfWorkspaceFragmentIdentity
): string => [
    identity.moduleId,
    identity.fragmentId,
    identity.moduleRevision,
    identity.policyRevision,
    identity.linkageRevision
].join('\u0000');

const cloneIdentity = (
    identity: CoreLfWorkspaceFragmentIdentity
): CoreLfWorkspaceFragmentIdentity => deepFreeze({ ...identity });

const sameIdentity = (
    left: CoreLfWorkspaceFragmentIdentity,
    right: CoreLfWorkspaceFragmentIdentity
): boolean => identityKey(left) === identityKey(right);

export interface CoreLfWorkspaceExternalProvider {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly provider: CoreLfWorkspaceFragmentIdentity;
}

interface CoreLfSameModuleFragmentSourceBase {
    readonly identity: CoreLfWorkspaceFragmentIdentity;
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly externalProviders:
        readonly CoreLfWorkspaceExternalProvider[];
    readonly runtimeProvider?: CoreLfWorkspaceFragmentIdentity;
    readonly sourceOrders: readonly number[];
    readonly firstSourceOrder: number;
    readonly lastSourceOrder: number;
}

export interface CoreLfSameModuleDeclarationFragmentSource
extends CoreLfSameModuleFragmentSourceBase {
    readonly kind: 'declaration';
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

export interface CoreLfSameModuleMixedFragmentSource
extends CoreLfSameModuleFragmentSourceBase {
    readonly kind: 'mixed';
    readonly linkage: CoreLfMixedDeclarationLinkage;
    /** Deterministic derived plan; source snapshots retain the source triple. */
    readonly mixedPlan: CoreLfMixedPhasePlan;
}

export type CoreLfSameModuleFragmentSource =
    | CoreLfSameModuleDeclarationFragmentSource
    | CoreLfSameModuleMixedFragmentSource;

interface CoreLfSameModuleFragmentInputBase {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly externalProviders?:
        readonly CoreLfWorkspaceExternalProvider[];
    readonly runtimeProvider?: CoreLfWorkspaceFragmentIdentity;
}

export interface CoreLfSameModuleDeclarationFragmentInput
extends CoreLfSameModuleFragmentInputBase {
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

export interface CoreLfSameModuleMixedFragmentInput
extends CoreLfSameModuleFragmentInputBase {
    readonly linkage: CoreLfMixedDeclarationLinkage;
}

const sourceOrders = (module: CoreLfModuleSpec): readonly number[] =>
    Object.freeze([
        ...module.declarations.map(item => item.order),
        ...module.inductives.map(item => item.order),
        ...module.runtimeRules.map(item => item.order),
        ...module.proofRules.map(item => item.order)
    ].sort((left, right) => left - right));

const assertCompanionTargets = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    linkage: {
        readonly moduleRevision: string;
        readonly moduleId: string;
        readonly fragmentId: string;
    }
): void => {
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        fail(
            'INVALID_FRAGMENT',
            'fragment.policy',
            'Fragment policy targets a foreign module revision'
        );
    }
    if (
        linkage.moduleRevision !== module.revision ||
        linkage.moduleId !== module.moduleId ||
        linkage.fragmentId !== module.fragmentId
    ) {
        fail(
            'INVALID_FRAGMENT',
            'fragment.linkage',
            'Fragment linkage targets a foreign module revision'
        );
    }
};

const canonicalExternalProviders = (
    module: CoreLfModuleSpec,
    providers: readonly CoreLfWorkspaceExternalProvider[],
    supportsDependencyModules: boolean
): readonly CoreLfWorkspaceExternalProvider[] => {
    if (
        !supportsDependencyModules &&
        (
            module.dependencies.length > 0 ||
            module.externalSymbols.some(external =>
                external.availability === 'dependency-module'
            )
        )
    ) {
        return fail(
            'UNSUPPORTED_FRAGMENT',
            'fragment.module.dependencies',
            'The same-module fragment profile excludes dependency modules'
        );
    }
    const expected = module.externalSymbols.filter(external =>
        external.availability === 'earlier-fragment'
    );
    const bySymbol = new Map<string, CoreLfWorkspaceExternalProvider>();
    providers.forEach((provider, index) => {
        const key = symbolKey(provider.symbol);
        if (bySymbol.has(key)) {
            fail(
                'DUPLICATE_PROVIDER',
                `fragment.externalProviders[${index}]`,
                `External provider for '${displaySymbol(provider.symbol)}' ` +
                    'is duplicated'
            );
        }
        bySymbol.set(key, provider);
    });
    const canonical = expected.map((external, index) => {
        const provider = bySymbol.get(symbolKey(external.symbol));
        if (provider === undefined) {
            return fail(
                'MISSING_PROVIDER',
                `fragment.module.externalSymbols[${index}]`,
                `Earlier-fragment external ` +
                    `'${displaySymbol(external.symbol)}' has no exact provider`
            );
        }
        bySymbol.delete(symbolKey(external.symbol));
        return deepFreeze({
            symbol: { ...external.symbol },
            provider: cloneIdentity(provider.provider)
        });
    });
    if (bySymbol.size > 0) {
        const extra = [...bySymbol.values()][0];
        return fail(
            'INVALID_PROVIDER',
            'fragment.externalProviders',
            `Provider for '${displaySymbol(extra.symbol)}' does not target ` +
                'an earlier-fragment external'
        );
    }
    return Object.freeze(canonical);
};

const commonSource = (
    input: CoreLfSameModuleFragmentInputBase,
    policy: CoreLfTransferPolicyOverlay,
    linkage: CoreLfTransferDeclarationLinkage |
        CoreLfMixedDeclarationLinkage,
    supportsDependencyModules: boolean
) => {
    const orders = sourceOrders(input.module);
    if (orders.length === 0) {
        return fail(
            'INVALID_FRAGMENT',
            'fragment.module',
            'A fragment source must contain at least one command'
        );
    }
    return {
        identity: fragmentIdentity(input.module, policy, linkage),
        module: input.module,
        policy,
        linkage,
        externalProviders: canonicalExternalProviders(
            input.module,
            input.externalProviders ?? [],
            supportsDependencyModules
        ),
        ...(input.runtimeProvider === undefined
            ? {}
            : { runtimeProvider: cloneIdentity(input.runtimeProvider) }),
        sourceOrders: orders,
        firstSourceOrder: orders[0],
        lastSourceOrder: orders[orders.length - 1]
    };
};

const assertDependencyProfileLinkage = (
    module: CoreLfModuleSpec,
    linkage: CoreLfTransferDeclarationLinkage |
        CoreLfMixedDeclarationLinkage
): void => {
    module.externalSymbols.forEach((external, index) => {
        if (external.availability !== 'existing-core') return;
        const link = linkage.entries.find(entry =>
            symbolKey(entry.symbol) === symbolKey(external.symbol)
        );
        if (link === undefined || link.kind !== 'core-owner') {
            fail(
                'UNSUPPORTED_FRAGMENT',
                `fragment.module.externalSymbols[${index}]`,
                'Dependency fragment chains reserve existing-core for ' +
                    'intrinsic Core-owner linkage'
            );
        }
    });
};

const defineDeclarationFragment = (
    input: CoreLfSameModuleDeclarationFragmentInput,
    supportsDependencyModules: boolean
): CoreLfSameModuleDeclarationFragmentSource => {
    const { module } = input;
    assertCompanionTargets(module, input.policy, input.linkage);
    if (
        module.declarations.length === 0 ||
        module.inductives.length > 0 ||
        module.runtimeRules.length > 0 ||
        module.proofRules.length > 0
    ) {
        return fail(
            'UNSUPPORTED_FRAGMENT',
            'fragment.module',
            'Declaration fragment must contain declarations only'
        );
    }
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: input.policy.revision,
        moduleRevision: module.revision,
        entries: input.policy.entries
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: input.linkage.revision,
        moduleRevision: module.revision,
        entries: input.linkage.entries
    });
    if (supportsDependencyModules) {
        assertDependencyProfileLinkage(module, linkage);
    }
    return deepFreeze({
        kind: 'declaration' as const,
        ...commonSource(
            input,
            policy,
            linkage,
            supportsDependencyModules
        ),
        linkage
    });
};

/** Define one nonempty declaration-only source fragment. */
export function defineCoreLfSameModuleDeclarationFragment(
    input: CoreLfSameModuleDeclarationFragmentInput
): CoreLfSameModuleDeclarationFragmentSource {
    return defineDeclarationFragment(input, false);
}

/** Define one declaration fragment for an exact 1B2B module graph. */
export function defineCoreLfDependencyModuleDeclarationFragment(
    input: CoreLfSameModuleDeclarationFragmentInput
): CoreLfSameModuleDeclarationFragmentSource {
    return defineDeclarationFragment(input, true);
}

const defineMixedFragment = (
    input: CoreLfSameModuleMixedFragmentInput,
    supportsDependencyModules: boolean
): CoreLfSameModuleMixedFragmentSource => {
    const { module } = input;
    assertCompanionTargets(module, input.policy, input.linkage);
    const kinds = [
        module.declarations.length > 0,
        module.runtimeRules.length > 0,
        module.proofRules.length > 0
    ].filter(Boolean).length;
    if (module.inductives.length > 0 || kinds < 2) {
        return fail(
            'UNSUPPORTED_FRAGMENT',
            'fragment.module',
            'Mixed fragment requires at least two declaration/runtime/proof ' +
                'kinds and no inductives'
        );
    }
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: input.policy.revision,
        moduleRevision: module.revision,
        entries: input.policy.entries
    });
    const mixedPlan = planCoreLfMixedPhases(module, policy);
    const linkage = createCoreLfMixedDeclarationLinkage(mixedPlan, {
        revision: input.linkage.revision,
        moduleRevision: module.revision,
        entries: input.linkage.entries
    });
    if (supportsDependencyModules) {
        assertDependencyProfileLinkage(module, linkage);
    }
    return deepFreeze({
        kind: 'mixed' as const,
        ...commonSource(
            input,
            policy,
            linkage,
            supportsDependencyModules
        ),
        linkage,
        mixedPlan
    });
};

/** Define one non-inductive mixed declaration/runtime/proof fragment. */
export function defineCoreLfSameModuleMixedFragment(
    input: CoreLfSameModuleMixedFragmentInput
): CoreLfSameModuleMixedFragmentSource {
    return defineMixedFragment(input, false);
}

/** Define one mixed fragment for an exact 1B2B module graph. */
export function defineCoreLfDependencyModuleMixedFragment(
    input: CoreLfSameModuleMixedFragmentInput
): CoreLfSameModuleMixedFragmentSource {
    return defineMixedFragment(input, true);
}

export interface CoreLfSameModuleFragmentWorkspaceInput {
    readonly revision: string;
    readonly fragments: readonly CoreLfSameModuleFragmentSource[];
}

export interface CoreLfSameModuleFragmentWorkspacePlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision;
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly fragments: readonly CoreLfSameModuleFragmentSource[];
    readonly order: readonly CoreLfWorkspaceFragmentIdentity[];
}

export interface CoreLfDependencyModuleFragmentChainPlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision;
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly fragments: readonly CoreLfSameModuleFragmentSource[];
    readonly order: readonly CoreLfWorkspaceFragmentIdentity[];
}

export type CoreLfFragmentChainPlan =
    | CoreLfSameModuleFragmentWorkspacePlan
    | CoreLfDependencyModuleFragmentChainPlan;

const redefineSource = (
    source: CoreLfSameModuleFragmentSource,
    supportsDependencyModules: boolean
): CoreLfSameModuleFragmentSource => source.kind === 'declaration'
    ? defineDeclarationFragment(source, supportsDependencyModules)
    : defineMixedFragment(source, supportsDependencyModules);

interface CoreLfFragmentChainProfileOptions {
    readonly profileRevision:
        CoreLfFragmentChainPlan['profileRevision'];
    readonly supportsDependencyModules: boolean;
    readonly minimumFragments: number;
}

const createFragmentChain = (
    input: CoreLfSameModuleFragmentWorkspaceInput,
    profile: CoreLfFragmentChainProfileOptions
): CoreLfFragmentChainPlan => {
    if (!WORKSPACE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_WORKSPACE',
            'revision',
            `Invalid fragment workspace revision '${input.revision}'`
        );
    }
    if (input.fragments.length < profile.minimumFragments) {
        return fail(
            'INVALID_WORKSPACE',
            'fragments',
            profile.minimumFragments === 1
                ? 'A module fragment chain requires at least one source fragment'
                : 'A fragment chain requires at least two source fragments'
        );
    }
    const fragments = input.fragments
        .map(source => redefineSource(
            source,
            profile.supportsDependencyModules
        ))
        .sort((left, right) =>
            left.firstSourceOrder - right.firstSourceOrder ||
            compareText(left.identity.fragmentId, right.identity.fragmentId)
        );
    const first = fragments[0];
    const identities = new Set<string>();
    const fragmentIds = new Set<string>();
    let previous: CoreLfSameModuleFragmentSource | undefined;
    let latestRuntimeSource: CoreLfSameModuleFragmentSource | undefined;

    fragments.forEach((source, index) => {
        const path = `fragments[${index}]`;
        const key = identityKey(source.identity);
        if (identities.has(key) || fragmentIds.has(source.module.fragmentId)) {
            fail(
                'DUPLICATE_FRAGMENT',
                path,
                `Fragment '${source.module.fragmentId}' is duplicated`
            );
        }
        identities.add(key);
        fragmentIds.add(source.module.fragmentId);
        if (
            source.module.moduleId !== first.module.moduleId ||
            source.module.authorityPath !== first.module.authorityPath ||
            source.module.sourceSha256 !== first.module.sourceSha256 ||
            !sameData(
                source.module.canonicalExport,
                first.module.canonicalExport
            ) ||
            !sameData(
                source.module.dependencies,
                first.module.dependencies
            )
        ) {
            fail(
                'SOURCE_PIN_DRIFT',
                `${path}.module`,
                'All fragments must share one module, authority, source hash, ' +
                    'dependency view, and canonical export view'
            );
        }
        if (
            previous !== undefined &&
            source.firstSourceOrder <= previous.lastSourceOrder
        ) {
            fail(
                'OVERLAPPING_SOURCE_ORDER',
                `${path}.sourceOrders`,
                `Fragment '${source.module.fragmentId}' overlaps source order ` +
                    `of '${previous.module.fragmentId}'`
            );
        }
        previous = source;

        if (latestRuntimeSource === undefined) {
            if (source.runtimeProvider !== undefined) {
                fail(
                    'INVALID_RUNTIME_PROVIDER',
                    `${path}.runtimeProvider`,
                    'No earlier source fragment provides a runtime'
                );
            }
        } else if (
            source.runtimeProvider === undefined ||
            !sameIdentity(
                source.runtimeProvider,
                latestRuntimeSource.identity
            )
        ) {
            fail(
                'INVALID_RUNTIME_PROVIDER',
                `${path}.runtimeProvider`,
                `Fragment '${source.module.fragmentId}' must name latest ` +
                    `runtime provider ` +
                    `'${latestRuntimeSource.module.fragmentId}'`
            );
        }
        if (source.module.runtimeRules.length > 0) {
            latestRuntimeSource = source;
        }
    });

    const byIdentity = new Map(fragments.map(source => [
        identityKey(source.identity),
        source
    ] as const));
    fragments.forEach((source, sourceIndex) => {
        source.externalProviders.forEach((external, providerIndex) => {
            const provider = byIdentity.get(identityKey(external.provider));
            const path = `fragments[${sourceIndex}].externalProviders[` +
                `${providerIndex}].provider`;
            if (provider === undefined) {
                fail(
                    'INVALID_PROVIDER',
                    path,
                    `External '${displaySymbol(external.symbol)}' names an ` +
                        'unknown or stale provider identity'
                );
            }
            if (provider.lastSourceOrder >= source.firstSourceOrder) {
                fail(
                    'INVALID_PROVIDER',
                    path,
                    `Provider '${provider.module.fragmentId}' is not earlier ` +
                        `than '${source.module.fragmentId}'`
                );
            }
        });
    });

    return deepFreeze({
        revision: input.revision,
        profileRevision: profile.profileRevision,
        moduleId: first.module.moduleId,
        authorityPath: first.module.authorityPath,
        sourceSha256: first.module.sourceSha256,
        fragments,
        order: fragments.map(source => cloneIdentity(source.identity))
    });
};

/** Validate and canonically order one exact pinned same-module chain. */
export function createCoreLfSameModuleFragmentWorkspace(
    input: CoreLfSameModuleFragmentWorkspaceInput
): CoreLfSameModuleFragmentWorkspacePlan {
    return createFragmentChain(input, {
        profileRevision:
            CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision,
        supportsDependencyModules: false,
        minimumFragments: 2
    }) as CoreLfSameModuleFragmentWorkspacePlan;
}

/** Validate one dependency-aware source chain used inside a 1B2B graph. */
export function createCoreLfDependencyModuleFragmentChain(
    input: CoreLfSameModuleFragmentWorkspaceInput
): CoreLfDependencyModuleFragmentChainPlan {
    return createFragmentChain(input, {
        profileRevision:
            CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision,
        supportsDependencyModules: true,
        minimumFragments: 1
    }) as CoreLfDependencyModuleFragmentChainPlan;
}

const sameDeclarationLink = (
    left: CoreLfTransferDeclarationLink,
    right: CoreLfTransferDeclarationLink
): boolean => {
    if (
        left.symbol.moduleId !== right.symbol.moduleId ||
        left.symbol.name !== right.symbol.name ||
        left.kind !== right.kind
    ) {
        return false;
    }
    if (left.kind === 'core-owner' && right.kind === 'core-owner') {
        return left.owner === right.owner;
    }
    if (
        left.kind === 'free-declaration' &&
        right.kind === 'free-declaration'
    ) {
        return left.coreName === right.coreName &&
            left.backendName === right.backendName;
    }
    return false;
};

const localDeclaration = (
    modules: readonly CoreLfCompiledDeclarationModule[],
    symbol: CoreLfQualifiedSymbol
): CoreLfCompiledDeclaration | undefined => {
    for (const module of modules) {
        const declaration = module.declaration(symbol);
        if (declaration !== undefined) return declaration;
    }
    return undefined;
};

export interface CoreLfCompiledSameModuleFragment {
    readonly source: CoreLfSameModuleFragmentSource;
    readonly sourceSnapshot: CoreLfSameModuleFragmentSourceSnapshot;
    readonly sourceText: string;
    readonly declarationModules:
        readonly CoreLfCompiledDeclarationModule[];
    readonly runtime?: CoreLfCompiledRuntimeFragment;
    readonly proofPrograms: readonly CoreLfCompiledProofProgram[];
    readonly mixed?: CoreLfCompiledMixedModule;
}

export class CoreLfCompiledSameModuleFragmentWorkspace<
    TPlan extends CoreLfFragmentChainPlan =
        CoreLfSameModuleFragmentWorkspacePlan
> {
    readonly revision: string;
    readonly fragments: readonly CoreLfCompiledSameModuleFragment[];
    readonly declarationModules:
        readonly CoreLfCompiledDeclarationModule[];
    readonly moduleInterface?: CoreLfCompiledModuleInterface;

    constructor(
        public readonly plan: TPlan,
        fragments: readonly CoreLfCompiledSameModuleFragment[],
        public readonly declarations: CoreLfMixedDeclarationContext,
        public readonly latestRuntime?: CoreLfCompiledRuntimeFragment,
        public readonly proofProgram?: CoreLfComposedProofProgram
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.fragments = Object.freeze([...fragments]);
        this.declarationModules = Object.freeze(
            fragments.flatMap(fragment => fragment.declarationModules)
        );
        this.moduleInterface = this.declarationModules.length === 0
            ? undefined
            : createCoreLfCompiledModuleInterface(this.declarationModules);
        Object.freeze(this);
    }

    fragment(
        identity: CoreLfWorkspaceFragmentIdentity
    ): CoreLfCompiledSameModuleFragment | undefined {
        const key = identityKey(identity);
        return this.fragments.find(fragment =>
            identityKey(fragment.source.identity) === key
        );
    }
}

const assertExternalProvidersCompiled = (
    source: CoreLfSameModuleFragmentSource,
    compiledByIdentity:
        ReadonlyMap<string, CoreLfCompiledSameModuleFragment>
): void => source.externalProviders.forEach((external, index) => {
    const provider = compiledByIdentity.get(identityKey(external.provider));
    if (provider === undefined) {
        fail(
            'INVALID_PROVIDER',
            `fragment.externalProviders[${index}].provider`,
            `Provider for '${displaySymbol(external.symbol)}' is not compiled`
        );
    }
    const declaration = localDeclaration(
        provider.declarationModules,
        external.symbol
    );
    if (declaration === undefined || declaration.status === 'excluded') {
        fail(
            'INVALID_PROVIDER',
            `fragment.externalProviders[${index}]`,
            `Fragment '${provider.source.module.fragmentId}' does not locally ` +
                `provide '${displaySymbol(external.symbol)}'`
        );
    }
    const link = source.linkage.entries.find(entry =>
        symbolKey(entry.symbol) === symbolKey(external.symbol)
    );
    if (link === undefined || !sameDeclarationLink(link, declaration.link)) {
        fail(
            'PROVIDER_DRIFT',
            `fragment.externalProviders[${index}]`,
            `Provider and consumer linkage for ` +
                `'${displaySymbol(external.symbol)}' differ`
        );
    }
});

export interface CoreLfDependencyModuleFragmentChainCompileOptions {
    readonly initialDeclarations?: CoreLfMixedDeclarationBaseContext;
    readonly dependencyInterfaces?:
        readonly CoreLfCompiledModuleInterface[];
    readonly runtimeDependencies?:
        readonly CoreLfRuntimeFragmentDependency[];
}

interface CoreLfFragmentChainCompileProfile<
    TPlan extends CoreLfFragmentChainPlan
> {
    readonly profileRevision: TPlan['profileRevision'];
    readonly reconstruct: (
        input: CoreLfSameModuleFragmentWorkspaceInput
    ) => TPlan;
}

const compileFragmentChain = <TPlan extends CoreLfFragmentChainPlan>(
    inputPlan: TPlan,
    profile: CoreLfFragmentChainCompileProfile<TPlan>,
    options: CoreLfDependencyModuleFragmentChainCompileOptions = {}
): CoreLfCompiledSameModuleFragmentWorkspace<TPlan> => {
    if (
        inputPlan.profileRevision !== profile.profileRevision
    ) {
        return fail(
            'INVALID_WORKSPACE',
            'plan.profileRevision',
            'Fragment workspace plan targets an unsupported profile'
        );
    }
    const plan = profile.reconstruct({
        revision: inputPlan.revision,
        fragments: inputPlan.fragments
    });
    if (
        serializeCoreLfWorkspaceCanonicalJson(
            inputPlan,
            'inputFragmentChainPlan'
        ) !== serializeCoreLfWorkspaceCanonicalJson(
            plan,
            'reconstructedFragmentChainPlan'
        )
    ) {
        return fail(
            'INVALID_WORKSPACE',
            'plan',
            'Fragment workspace plan is not in canonical reconstructed form'
        );
    }
    let declarations = new CoreLfMixedDeclarationContext(
        options.initialDeclarations
    );
    let latestRuntime: CoreLfCompiledRuntimeFragment | undefined;
    const externalRuntimeDependencies =
        options.runtimeDependencies ?? [];
    const externalRuntime = composeCoreLfRuntimeDependencies(
        externalRuntimeDependencies
    );
    const proofPrograms: CoreLfCompiledProofProgram[] = [];
    const compiledByIdentity = new Map<
        string,
        CoreLfCompiledSameModuleFragment
    >();
    const fragments: CoreLfCompiledSameModuleFragment[] = [];

    plan.fragments.forEach((source, index) => {
        assertExternalProvidersCompiled(source, compiledByIdentity);
        let runtimeProvider: CoreLfCompiledRuntimeFragment | undefined;
        if (source.runtimeProvider !== undefined) {
            const provider = compiledByIdentity.get(
                identityKey(source.runtimeProvider)
            );
            runtimeProvider = provider?.runtime;
            if (runtimeProvider === undefined) {
                fail(
                    'INVALID_RUNTIME_PROVIDER',
                    `fragments[${index}].runtimeProvider`,
                    'Named source fragment did not locally compile a runtime'
                );
            }
            if (runtimeProvider !== latestRuntime) {
                fail(
                    'INVALID_RUNTIME_PROVIDER',
                    `fragments[${index}].runtimeProvider`,
                    'Named runtime artifact is not the latest exact closure'
                );
            }
        }

        let declarationModules: readonly CoreLfCompiledDeclarationModule[];
        let runtime: CoreLfCompiledRuntimeFragment | undefined;
        let localProofPrograms: readonly CoreLfCompiledProofProgram[];
        let mixed: CoreLfCompiledMixedModule | undefined;
        if (source.kind === 'declaration') {
            const compiled = compileCoreLfDeclarations(
                source.module,
                source.policy,
                source.linkage,
                {
                    initialEnvironment: declarations.environment,
                    dependencyInterfaces:
                        options.dependencyInterfaces,
                    runtimeProgram:
                        runtimeProvider?.runtime ?? externalRuntime
                }
            );
            declarations = declarations.extend(compiled);
            declarationModules = Object.freeze([compiled]);
            localProofPrograms = Object.freeze([]);
        } else {
            mixed = compileCoreLfMixedPhases(
                source.mixedPlan,
                source.linkage,
                {
                    initialDeclarations: declarations,
                    dependencyInterfaces:
                        options.dependencyInterfaces,
                    runtimeDependencies: [
                        ...externalRuntimeDependencies,
                        ...(runtimeProvider === undefined
                            ? []
                            : [{
                                relation: 'earlier-fragment' as const,
                                fragment: runtimeProvider
                            }])
                    ]
                }
            );
            declarations = mixed.declarations;
            declarationModules = Object.freeze(mixed.phases.flatMap(phase =>
                phase.kind === 'declaration' ||
                phase.kind === 'inductive-signature'
                    ? [phase.declarations]
                    : []
            ));
            runtime = mixed.latestRuntime;
            localProofPrograms = mixed.proofPrograms;
        }
        if (runtime !== undefined) latestRuntime = runtime;
        proofPrograms.push(...localProofPrograms);

        const partial = {
            source,
            sourceSnapshot:
                createCoreLfSameModuleFragmentSourceSnapshot(source),
            sourceText: '',
            declarationModules,
            runtime,
            proofPrograms: Object.freeze([...localProofPrograms]),
            mixed
        };
        const result: CoreLfCompiledSameModuleFragment = Object.freeze({
            ...partial,
            sourceText: serializeCoreLfSameModuleFragmentSource(
                partial.sourceSnapshot
            )
        });
        compiledByIdentity.set(identityKey(source.identity), result);
        fragments.push(result);
    });

    const proofProgram = proofPrograms.length === 0
        ? undefined
        : composeCoreLfProofPrograms(
            proofPrograms,
            declarations,
            {
                executionRuntimeProgram:
                    latestRuntime?.runtime ?? externalRuntime
            }
        );
    return new CoreLfCompiledSameModuleFragmentWorkspace(
        plan,
        fragments,
        declarations,
        latestRuntime,
        proofProgram
    );
};

/** Compile the qualified dependency-free 1B2A chain. */
export function compileCoreLfSameModuleFragmentWorkspace(
    inputPlan: CoreLfSameModuleFragmentWorkspacePlan
): CoreLfCompiledSameModuleFragmentWorkspace {
    return compileFragmentChain(inputPlan, {
        profileRevision:
            CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision,
        reconstruct: createCoreLfSameModuleFragmentWorkspace
    });
}

/** Compile one dependency-aware chain under exact graph-supplied artifacts. */
export function compileCoreLfDependencyModuleFragmentChain(
    inputPlan: CoreLfDependencyModuleFragmentChainPlan,
    options: CoreLfDependencyModuleFragmentChainCompileOptions
): CoreLfCompiledSameModuleFragmentWorkspace<
    CoreLfDependencyModuleFragmentChainPlan
> {
    return compileFragmentChain(
        inputPlan,
        {
            profileRevision:
                CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision,
            reconstruct: createCoreLfDependencyModuleFragmentChain
        },
        options
    );
}

export interface CoreLfSameModuleFragmentSourceSnapshot {
    readonly revision:
        typeof CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
            .fragmentSourceSnapshotRevision;
    readonly kind: CoreLfSameModuleFragmentSource['kind'];
    readonly identity: CoreLfWorkspaceFragmentIdentity;
    readonly sourceOrders: readonly number[];
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage:
        CoreLfTransferDeclarationLinkage | CoreLfMixedDeclarationLinkage;
    readonly externalProviders:
        readonly CoreLfWorkspaceExternalProvider[];
    readonly runtimeProvider?: CoreLfWorkspaceFragmentIdentity;
}

export const createCoreLfSameModuleFragmentSourceSnapshot = (
    source: CoreLfSameModuleFragmentSource
): CoreLfSameModuleFragmentSourceSnapshot => deepFreeze({
    revision:
        CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
            .fragmentSourceSnapshotRevision,
    kind: source.kind,
    identity: source.identity,
    sourceOrders: [...source.sourceOrders],
    module: source.module,
    policy: source.policy,
    linkage: source.linkage,
    externalProviders: source.externalProviders,
    ...(source.runtimeProvider === undefined
        ? {}
        : { runtimeProvider: source.runtimeProvider })
});

export const serializeCoreLfSameModuleFragmentSource = (
    snapshot: CoreLfSameModuleFragmentSourceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'sameModuleFragmentSource'
);

export interface CoreLfSameModuleFragmentWorkspaceSourceSnapshot {
    readonly revision:
        typeof CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
            .workspaceSourceSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly order: readonly CoreLfWorkspaceFragmentIdentity[];
    readonly fragments: readonly CoreLfSameModuleFragmentSourceSnapshot[];
}

export const createCoreLfSameModuleFragmentWorkspaceSourceSnapshot = (
    plan: CoreLfSameModuleFragmentWorkspacePlan
): CoreLfSameModuleFragmentWorkspaceSourceSnapshot => deepFreeze({
    revision:
        CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
            .workspaceSourceSnapshotRevision,
    profileRevision:
        CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision,
    workspaceRevision: plan.revision,
    moduleId: plan.moduleId,
    authorityPath: plan.authorityPath,
    sourceSha256: plan.sourceSha256,
    order: plan.order,
    fragments: plan.fragments.map(
        createCoreLfSameModuleFragmentSourceSnapshot
    )
});

export const serializeCoreLfSameModuleFragmentWorkspaceSourceSnapshot = (
    snapshot: CoreLfSameModuleFragmentWorkspaceSourceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'sameModuleFragmentWorkspaceSourceSnapshot'
);

export type CoreLfDependencyModuleFragmentChainSourceSnapshot = Omit<
    CoreLfSameModuleFragmentWorkspaceSourceSnapshot,
    'revision' | 'profileRevision'
> & {
    readonly revision:
        typeof CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE
            .workspaceSourceSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision;
};

export const createCoreLfDependencyModuleFragmentChainSourceSnapshot = (
    plan: CoreLfDependencyModuleFragmentChainPlan
): CoreLfDependencyModuleFragmentChainSourceSnapshot => deepFreeze({
    revision:
        CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE
            .workspaceSourceSnapshotRevision,
    profileRevision:
        CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision,
    workspaceRevision: plan.revision,
    moduleId: plan.moduleId,
    authorityPath: plan.authorityPath,
    sourceSha256: plan.sourceSha256,
    order: plan.order,
    fragments: plan.fragments.map(
        createCoreLfSameModuleFragmentSourceSnapshot
    )
});

export const serializeCoreLfDependencyModuleFragmentChainSourceSnapshot = (
    snapshot: CoreLfDependencyModuleFragmentChainSourceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'dependencyModuleFragmentChainSourceSnapshot'
);

export interface CoreLfSameModuleRuntimeSnapshot {
    readonly identity: string;
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly revision: string;
    readonly ruleIds: readonly string[];
    readonly dependencies: readonly {
        readonly relation: 'dependency-module' | 'earlier-fragment';
        readonly compiledIdentity: string;
    }[];
}

export interface CoreLfSameModuleProofSnapshot {
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly revision: string;
    readonly ruleIds: readonly string[];
    readonly runtimeRevision?: string;
}

export interface CoreLfSameModuleInterfaceSnapshot {
    readonly explicitCoreRevision:
        typeof CORE_EXPLICIT_SERIALIZATION_REVISION;
    readonly moduleId: string;
    readonly providerRevisions: readonly string[];
    readonly fragmentIds: readonly string[];
    readonly entries: readonly {
        readonly symbol: CoreLfQualifiedSymbol;
        readonly visibility: 'public' | 'protected' | 'private';
        readonly link: CoreLfTransferDeclarationLink;
        readonly status: CoreLfCompiledDeclaration['status'];
        readonly type: string;
    }[];
}

export interface CoreLfSameModuleCompiledFragmentSnapshot {
    readonly source: CoreLfSameModuleFragmentSourceSnapshot;
    readonly declarationInterfaces:
        readonly CoreLfDeclarationWorkspaceInterfaceSnapshot[];
    readonly runtime?: CoreLfSameModuleRuntimeSnapshot;
    readonly proofPrograms: readonly CoreLfSameModuleProofSnapshot[];
}

export interface CoreLfSameModuleFragmentWorkspaceSnapshot {
    readonly revision:
        typeof CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
            .workspaceSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly order: readonly CoreLfWorkspaceFragmentIdentity[];
    readonly fragments: readonly CoreLfSameModuleCompiledFragmentSnapshot[];
    readonly moduleInterface?: CoreLfSameModuleInterfaceSnapshot;
    readonly finalRuntime?: CoreLfSameModuleRuntimeSnapshot;
    readonly proofProgram?: {
        readonly revision: string;
        readonly ruleIds: readonly string[];
        readonly comparisonStepLimit: number;
        readonly runtimeRevision?: string;
    };
}

const runtimeSnapshot = (
    runtime: CoreLfCompiledRuntimeFragment
): CoreLfSameModuleRuntimeSnapshot => deepFreeze({
    identity: runtime.identity,
    moduleId: runtime.module.moduleId,
    fragmentId: runtime.module.fragmentId,
    revision: runtime.localProgram.revision,
    ruleIds: [...runtime.runtime.ruleIds],
    dependencies: runtime.dependencies.map(dependency => ({
        relation: dependency.relation,
        compiledIdentity: dependency.fragment.identity
    }))
});

const proofSnapshot = (
    proof: CoreLfCompiledProofProgram
): CoreLfSameModuleProofSnapshot => deepFreeze({
    moduleId: proof.module.moduleId,
    fragmentId: proof.module.fragmentId,
    revision: proof.revision,
    ruleIds: [...proof.ruleIds],
    ...(proof.runtimeProgram === undefined
        ? {}
        : { runtimeRevision: proof.runtimeProgram.revision })
});

const interfaceSnapshot = (
    moduleInterface: CoreLfCompiledModuleInterface
): CoreLfSameModuleInterfaceSnapshot => deepFreeze({
    explicitCoreRevision: CORE_EXPLICIT_SERIALIZATION_REVISION,
    moduleId: moduleInterface.moduleId,
    providerRevisions: [...moduleInterface.providerRevisions],
    fragmentIds: [...moduleInterface.fragmentIds],
    entries: moduleInterface.entries.map(entry => ({
        symbol: { ...entry.symbol },
        visibility: entry.visibility,
        link: entry.link,
        status: entry.status,
        type: serializeCoreExpression(entry.type)
    }))
});

export const createCoreLfSameModuleFragmentWorkspaceSnapshot = (
    compiled: CoreLfCompiledSameModuleFragmentWorkspace
): CoreLfSameModuleFragmentWorkspaceSnapshot => deepFreeze({
    revision:
        CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
            .workspaceSnapshotRevision,
    profileRevision:
        CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE.revision,
    workspaceRevision: compiled.plan.revision,
    moduleId: compiled.plan.moduleId,
    authorityPath: compiled.plan.authorityPath,
    sourceSha256: compiled.plan.sourceSha256,
    order: compiled.plan.order,
    fragments: compiled.fragments.map(fragment => ({
        source: fragment.sourceSnapshot,
        declarationInterfaces: fragment.declarationModules.map(
            createCoreLfDeclarationWorkspaceInterfaceSnapshot
        ),
        ...(fragment.runtime === undefined
            ? {}
            : { runtime: runtimeSnapshot(fragment.runtime) }),
        proofPrograms: fragment.proofPrograms.map(proofSnapshot)
    })),
    ...(compiled.moduleInterface === undefined
        ? {}
        : { moduleInterface: interfaceSnapshot(compiled.moduleInterface) }),
    ...(compiled.latestRuntime === undefined
        ? {}
        : { finalRuntime: runtimeSnapshot(compiled.latestRuntime) }),
    ...(compiled.proofProgram === undefined
        ? {}
        : {
            proofProgram: {
                revision: compiled.proofProgram.revision,
                ruleIds: [...compiled.proofProgram.ruleIds],
                comparisonStepLimit:
                    compiled.proofProgram.comparisonStepLimit,
                ...(compiled.proofProgram.runtimeProgram === undefined
                    ? {}
                    : {
                        runtimeRevision:
                            compiled.proofProgram.runtimeProgram.revision
                    })
            }
        })
});

export const serializeCoreLfSameModuleFragmentWorkspaceSnapshot = (
    snapshot: CoreLfSameModuleFragmentWorkspaceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'sameModuleFragmentWorkspaceSnapshot'
);

export type CoreLfDependencyModuleFragmentChainSnapshot = Omit<
    CoreLfSameModuleFragmentWorkspaceSnapshot,
    'revision' | 'profileRevision'
> & {
    readonly revision:
        typeof CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE
            .workspaceSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision;
};

export const createCoreLfDependencyModuleFragmentChainSnapshot = (
    compiled: CoreLfCompiledSameModuleFragmentWorkspace<
        CoreLfDependencyModuleFragmentChainPlan
    >
): CoreLfDependencyModuleFragmentChainSnapshot => deepFreeze({
    revision:
        CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE
            .workspaceSnapshotRevision,
    profileRevision:
        CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision,
    workspaceRevision: compiled.plan.revision,
    moduleId: compiled.plan.moduleId,
    authorityPath: compiled.plan.authorityPath,
    sourceSha256: compiled.plan.sourceSha256,
    order: compiled.plan.order,
    fragments: compiled.fragments.map(fragment => ({
        source: fragment.sourceSnapshot,
        declarationInterfaces: fragment.declarationModules.map(
            createCoreLfDeclarationWorkspaceInterfaceSnapshot
        ),
        ...(fragment.runtime === undefined
            ? {}
            : { runtime: runtimeSnapshot(fragment.runtime) }),
        proofPrograms: fragment.proofPrograms.map(proofSnapshot)
    })),
    ...(compiled.moduleInterface === undefined
        ? {}
        : { moduleInterface: interfaceSnapshot(compiled.moduleInterface) }),
    ...(compiled.latestRuntime === undefined
        ? {}
        : { finalRuntime: runtimeSnapshot(compiled.latestRuntime) }),
    ...(compiled.proofProgram === undefined
        ? {}
        : {
            proofProgram: {
                revision: compiled.proofProgram.revision,
                ruleIds: [...compiled.proofProgram.ruleIds],
                comparisonStepLimit:
                    compiled.proofProgram.comparisonStepLimit,
                ...(compiled.proofProgram.runtimeProgram === undefined
                    ? {}
                    : {
                        runtimeRevision:
                            compiled.proofProgram.runtimeProgram.revision
                    })
            }
        })
});

export const serializeCoreLfDependencyModuleFragmentChainSnapshot = (
    snapshot: CoreLfDependencyModuleFragmentChainSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'dependencyModuleFragmentChainSnapshot'
);
