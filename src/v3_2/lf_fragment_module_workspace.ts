/**
 * Browser-safe exact cross-module fragment graphs for AI-authored LF work.
 *
 * Source nodes persist complete module/fragment identities. Compilation uses
 * only the existing declaration-interface, mixed-phase, runtime-composition,
 * and proof-program engines. Filesystem acquisition, hashing, caching, and
 * incremental execution remain outer concerns.
 */

import {
    CoreLfCanonicalExportEvidence
} from './lf_transfer';
import {
    CoreLfMixedDeclarationContext
} from './lf_transfer_mixed';
import {
    CoreLfCompiledRuntimeFragment,
    CoreLfRuntimeFragmentDependency
} from './lf_transfer_runtime';
import {
    CoreLfCompiledModuleInterface
} from './lf_transfer_visibility';
import {
    CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE,
    CoreLfCompiledSameModuleFragmentWorkspace,
    CoreLfDependencyModuleFragmentChainPlan,
    CoreLfDependencyModuleFragmentChainSnapshot,
    CoreLfDependencyModuleFragmentChainSourceSnapshot,
    CoreLfWorkspaceFragmentIdentity,
    compileCoreLfDependencyModuleFragmentChain,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfDependencyModuleFragmentChainSnapshot,
    createCoreLfDependencyModuleFragmentChainSourceSnapshot
} from './lf_fragment_workspace';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE = Object.freeze({
    revision: 'emdash-lf-fragment-module-workspace-v1' as const,
    sourceSnapshotRevision:
        'emdash-lf-fragment-module-workspace-source-v1' as const,
    compiledSnapshotRevision:
        'emdash-lf-fragment-module-workspace-snapshot-v1' as const,
    moduleIdentityProfile:
        'source-export-dependencies-chain-and-fragment-identities' as const,
    moduleOrderProfile: 'stable-topological-module-id' as const,
    dependencyInterfaceProfile:
        'exact-multi-provider-compiled-interface' as const,
    dependencyRuntimeProfile:
        'exact-final-local-runtime-fragment' as const,
    existingCoreProfile: 'intrinsic-core-owner-only' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    executesIncrementally: false as const,
    acceptsCompilerCallbacks: false as const
});

export const serializeCoreLfFragmentModuleWorkspaceProfile = (): string =>
    `${JSON.stringify(CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE, null, 2)}\n`;

export type CoreLfFragmentModuleWorkspaceErrorCode =
    | 'INVALID_WORKSPACE'
    | 'INVALID_MODULE_CHAIN'
    | 'DUPLICATE_MODULE'
    | 'MISSING_DEPENDENCY'
    | 'CYCLIC_DEPENDENCY'
    | 'MISSING_DEPENDENCY_PROVIDER'
    | 'INVALID_DEPENDENCY_PROVIDER'
    | 'MISSING_RUNTIME_PROVIDER'
    | 'INVALID_RUNTIME_PROVIDER';

export class CoreLfFragmentModuleWorkspaceError extends Error {
    constructor(
        public readonly code: CoreLfFragmentModuleWorkspaceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfFragmentModuleWorkspaceError';
    }
}

const fail = (
    code: CoreLfFragmentModuleWorkspaceErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfFragmentModuleWorkspaceError(code, path, message);
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

const WORKSPACE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

export interface CoreLfFragmentModuleIdentity {
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport?: CoreLfCanonicalExportEvidence;
    readonly dependencies: readonly string[];
    readonly chainRevision: string;
    readonly chainProfileRevision:
        typeof CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision;
    readonly fragments: readonly CoreLfWorkspaceFragmentIdentity[];
}

export interface CoreLfFragmentModuleRuntimeProvider {
    readonly moduleId: string;
    readonly fragment: CoreLfWorkspaceFragmentIdentity;
}

export interface CoreLfFragmentModuleWorkspaceModuleInput {
    readonly chain: CoreLfDependencyModuleFragmentChainPlan;
    readonly dependencyProviders?: readonly CoreLfFragmentModuleIdentity[];
    readonly runtimeProviders?:
        readonly CoreLfFragmentModuleRuntimeProvider[];
}

export interface CoreLfFragmentModuleWorkspaceModule {
    readonly identity: CoreLfFragmentModuleIdentity;
    readonly chain: CoreLfDependencyModuleFragmentChainPlan;
    readonly dependencyProviders: readonly CoreLfFragmentModuleIdentity[];
    readonly runtimeProviders:
        readonly CoreLfFragmentModuleRuntimeProvider[];
}

export interface CoreLfFragmentModuleWorkspaceInput {
    readonly revision: string;
    readonly modules: readonly CoreLfFragmentModuleWorkspaceModuleInput[];
}

export interface CoreLfFragmentModuleWorkspacePlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly modules: readonly CoreLfFragmentModuleWorkspaceModule[];
    readonly order: readonly string[];
}

const canonicalExport = (
    value: CoreLfCanonicalExportEvidence | undefined
): CoreLfCanonicalExportEvidence | undefined => value === undefined
    ? undefined
    : deepFreeze({ ...value });

const cloneFragmentIdentity = (
    identity: CoreLfWorkspaceFragmentIdentity
): CoreLfWorkspaceFragmentIdentity => deepFreeze({ ...identity });

const moduleIdentity = (
    chain: CoreLfDependencyModuleFragmentChainPlan
): CoreLfFragmentModuleIdentity => {
    const first = chain.fragments[0].module;
    return deepFreeze({
        moduleId: chain.moduleId,
        authorityPath: chain.authorityPath,
        sourceSha256: chain.sourceSha256,
        ...(first.canonicalExport === undefined
            ? {}
            : { canonicalExport: canonicalExport(first.canonicalExport) }),
        dependencies: [...first.dependencies],
        chainRevision: chain.revision,
        chainProfileRevision: chain.profileRevision,
        fragments: chain.order.map(cloneFragmentIdentity)
    });
};

/** Derive the complete portable identity referenced by graph dependency edges. */
export const createCoreLfFragmentModuleIdentity = (
    chain: CoreLfDependencyModuleFragmentChainPlan
): CoreLfFragmentModuleIdentity => moduleIdentity(
    reconstructChain(chain, 'chain')
);

const identityText = (identity: CoreLfFragmentModuleIdentity): string =>
    serializeCoreLfWorkspaceCanonicalJson(
        identity,
        'fragmentModuleIdentity'
    );

const sameModuleIdentity = (
    left: CoreLfFragmentModuleIdentity,
    right: CoreLfFragmentModuleIdentity
): boolean => identityText(left) === identityText(right);

const sameFragmentIdentity = (
    left: CoreLfWorkspaceFragmentIdentity,
    right: CoreLfWorkspaceFragmentIdentity
): boolean => serializeCoreLfWorkspaceCanonicalJson(
    left,
    'leftFragmentIdentity'
) === serializeCoreLfWorkspaceCanonicalJson(
    right,
    'rightFragmentIdentity'
);

const reconstructChain = (
    input: CoreLfDependencyModuleFragmentChainPlan,
    path: string
): CoreLfDependencyModuleFragmentChainPlan => {
    if (
        input.profileRevision !==
            CORE_LF_DEPENDENCY_MODULE_FRAGMENT_CHAIN_PROFILE.revision
    ) {
        return fail(
            'INVALID_MODULE_CHAIN',
            `${path}.profileRevision`,
            'Module chain targets an unsupported dependency profile'
        );
    }
    const chain = createCoreLfDependencyModuleFragmentChain({
        revision: input.revision,
        fragments: input.fragments
    });
    if (
        serializeCoreLfWorkspaceCanonicalJson(
            input,
            'inputDependencyModuleFragmentChain'
        ) !== serializeCoreLfWorkspaceCanonicalJson(
            chain,
            'reconstructedDependencyModuleFragmentChain'
        )
    ) {
        return fail(
            'INVALID_MODULE_CHAIN',
            path,
            'Module chain is not in canonical reconstructed form'
        );
    }
    return chain;
};

const latestLocalRuntimeIdentity = (
    source: CoreLfFragmentModuleWorkspaceModule
): CoreLfWorkspaceFragmentIdentity | undefined => {
    for (let index = source.chain.fragments.length - 1; index >= 0; index--) {
        const fragment = source.chain.fragments[index];
        if (fragment.module.runtimeRules.length > 0) {
            return fragment.identity;
        }
    }
    return undefined;
};

const dependencyCycle = (
    byId: ReadonlyMap<string, CoreLfFragmentModuleWorkspaceModule>
): readonly string[] | undefined => {
    const state = new Map<string, 'visiting' | 'complete'>();
    const stack: string[] = [];

    const visit = (moduleId: string): readonly string[] | undefined => {
        const existing = state.get(moduleId);
        if (existing === 'complete') return undefined;
        if (existing === 'visiting') {
            const start = stack.indexOf(moduleId);
            return Object.freeze([...stack.slice(start), moduleId]);
        }
        state.set(moduleId, 'visiting');
        stack.push(moduleId);
        const source = byId.get(moduleId);
        if (source === undefined) {
            return fail(
                'MISSING_DEPENDENCY',
                'modules',
                `Workspace has no module '${moduleId}'`
            );
        }
        for (const dependency of [...source.identity.dependencies]
            .sort(compareText)) {
            const cycle = visit(dependency);
            if (cycle !== undefined) return cycle;
        }
        stack.pop();
        state.set(moduleId, 'complete');
        return undefined;
    };

    for (const moduleId of [...byId.keys()].sort(compareText)) {
        const cycle = visit(moduleId);
        if (cycle !== undefined) return cycle;
    }
    return undefined;
};

const topologicalOrder = (
    byId: ReadonlyMap<string, CoreLfFragmentModuleWorkspaceModule>
): readonly string[] => {
    const cycle = dependencyCycle(byId);
    if (cycle !== undefined) {
        return fail(
            'CYCLIC_DEPENDENCY',
            'modules',
            `Workspace dependency cycle: ${cycle.join(' -> ')}`
        );
    }
    const inDegree = new Map<string, number>();
    const dependents = new Map<string, Set<string>>();
    byId.forEach(source => {
        inDegree.set(
            source.identity.moduleId,
            source.identity.dependencies.length
        );
        source.identity.dependencies.forEach(dependency => {
            const consumers = dependents.get(dependency) ?? new Set<string>();
            consumers.add(source.identity.moduleId);
            dependents.set(dependency, consumers);
        });
    });
    const ready = [...inDegree.entries()]
        .filter(([, degree]) => degree === 0)
        .map(([moduleId]) => moduleId)
        .sort(compareText);
    const order: string[] = [];
    while (ready.length > 0) {
        const moduleId = ready.shift();
        if (moduleId === undefined) break;
        order.push(moduleId);
        [...(dependents.get(moduleId) ?? [])]
            .sort(compareText)
            .forEach(consumer => {
                const degree = (inDegree.get(consumer) ?? 0) - 1;
                inDegree.set(consumer, degree);
                if (degree === 0) {
                    ready.push(consumer);
                    ready.sort(compareText);
                }
            });
    }
    if (order.length !== byId.size) {
        return fail(
            'CYCLIC_DEPENDENCY',
            'modules',
            'Workspace dependency graph cannot be ordered'
        );
    }
    return Object.freeze(order);
};

const canonicalProviderMap = (
    providers: readonly CoreLfFragmentModuleIdentity[],
    path: string
): Map<string, CoreLfFragmentModuleIdentity> => {
    const byId = new Map<string, CoreLfFragmentModuleIdentity>();
    providers.forEach((provider, index) => {
        if (byId.has(provider.moduleId)) {
            fail(
                'INVALID_DEPENDENCY_PROVIDER',
                `${path}[${index}]`,
                `Dependency provider '${provider.moduleId}' is duplicated`
            );
        }
        byId.set(provider.moduleId, provider);
    });
    return byId;
};

const canonicalRuntimeProviderMap = (
    providers: readonly CoreLfFragmentModuleRuntimeProvider[],
    path: string
): Map<string, CoreLfFragmentModuleRuntimeProvider> => {
    const byId = new Map<string, CoreLfFragmentModuleRuntimeProvider>();
    providers.forEach((provider, index) => {
        if (byId.has(provider.moduleId)) {
            fail(
                'INVALID_RUNTIME_PROVIDER',
                `${path}[${index}]`,
                `Runtime provider '${provider.moduleId}' is duplicated`
            );
        }
        byId.set(provider.moduleId, provider);
    });
    return byId;
};

/** Validate and canonically order one exact local cross-module graph. */
export function createCoreLfFragmentModuleWorkspace(
    input: CoreLfFragmentModuleWorkspaceInput
): CoreLfFragmentModuleWorkspacePlan {
    if (!WORKSPACE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_WORKSPACE',
            'revision',
            `Invalid fragment-module workspace revision '${input.revision}'`
        );
    }
    if (input.modules.length < 2) {
        return fail(
            'INVALID_WORKSPACE',
            'modules',
            'A cross-module fragment workspace requires at least two modules'
        );
    }

    const inputs = input.modules.map((source, index) => {
        const chain = reconstructChain(source.chain, `modules[${index}].chain`);
        return {
            chain,
            identity: moduleIdentity(chain),
            dependencyProviders: source.dependencyProviders ?? [],
            runtimeProviders: source.runtimeProviders ?? []
        };
    });
    const byId = new Map<string, CoreLfFragmentModuleWorkspaceModule>();
    inputs.forEach((source, index) => {
        if (byId.has(source.identity.moduleId)) {
            fail(
                'DUPLICATE_MODULE',
                `modules[${index}].chain.moduleId`,
                `Module '${source.identity.moduleId}' is duplicated`
            );
        }
        byId.set(source.identity.moduleId, deepFreeze({
            identity: source.identity,
            chain: source.chain,
            dependencyProviders: [],
            runtimeProviders: []
        }));
    });

    inputs.forEach((source, index) => {
        source.identity.dependencies.forEach((dependency, dependencyIndex) => {
            if (byId.has(dependency)) return;
            fail(
                'MISSING_DEPENDENCY',
                `modules[${index}].chain.dependencies[${dependencyIndex}]`,
                `Module '${source.identity.moduleId}' requires missing ` +
                    `module '${dependency}'`
            );
        });
    });

    const completeById = new Map<string, CoreLfFragmentModuleWorkspaceModule>();
    inputs.forEach((source, index) => {
        const providerById = canonicalProviderMap(
            source.dependencyProviders,
            `modules[${index}].dependencyProviders`
        );
        const runtimeById = canonicalRuntimeProviderMap(
            source.runtimeProviders,
            `modules[${index}].runtimeProviders`
        );
        const dependencyProviders = source.identity.dependencies.map(
            (dependency, dependencyIndex) => {
                const actual = byId.get(dependency);
                if (actual === undefined) {
                    return fail(
                        'MISSING_DEPENDENCY',
                        `modules[${index}].dependencyProviders[` +
                            `${dependencyIndex}]`,
                        `Dependency '${dependency}' disappeared`
                    );
                }
                const supplied = providerById.get(dependency);
                if (supplied === undefined) {
                    return fail(
                        'MISSING_DEPENDENCY_PROVIDER',
                        `modules[${index}].dependencyProviders`,
                        `Dependency '${dependency}' has no exact source ` +
                            'provider identity'
                    );
                }
                providerById.delete(dependency);
                if (!sameModuleIdentity(supplied, actual.identity)) {
                    return fail(
                        'INVALID_DEPENDENCY_PROVIDER',
                        `modules[${index}].dependencyProviders[` +
                            `${dependencyIndex}]`,
                        `Dependency '${dependency}' provider identity drifted`
                    );
                }
                return actual.identity;
            }
        );
        if (providerById.size > 0) {
            const extra = [...providerById.keys()][0];
            fail(
                'INVALID_DEPENDENCY_PROVIDER',
                `modules[${index}].dependencyProviders`,
                `Provider '${extra}' is not a direct source dependency`
            );
        }

        const runtimeProviders = source.identity.dependencies.flatMap(
            (dependency, dependencyIndex) => {
                const dependencySource = byId.get(dependency);
                if (dependencySource === undefined) {
                    return fail(
                        'MISSING_DEPENDENCY',
                        `modules[${index}].runtimeProviders[` +
                            `${dependencyIndex}]`,
                        `Dependency '${dependency}' disappeared`
                    );
                }
                const expected = latestLocalRuntimeIdentity(dependencySource);
                const supplied = runtimeById.get(dependency);
                if (expected === undefined) {
                    if (supplied !== undefined) {
                        return fail(
                            'INVALID_RUNTIME_PROVIDER',
                            `modules[${index}].runtimeProviders[` +
                                `${dependencyIndex}]`,
                            `Dependency '${dependency}' has no local runtime`
                        );
                    }
                    return [];
                }
                if (supplied === undefined) {
                    return fail(
                        'MISSING_RUNTIME_PROVIDER',
                        `modules[${index}].runtimeProviders`,
                        `Dependency '${dependency}' has no exact runtime ` +
                            'provider identity'
                    );
                }
                runtimeById.delete(dependency);
                if (!sameFragmentIdentity(supplied.fragment, expected)) {
                    return fail(
                        'INVALID_RUNTIME_PROVIDER',
                        `modules[${index}].runtimeProviders[` +
                            `${dependencyIndex}]`,
                        `Dependency '${dependency}' runtime provider is not ` +
                            'its latest local runtime fragment'
                    );
                }
                return [deepFreeze({
                    moduleId: dependency,
                    fragment: cloneFragmentIdentity(expected)
                })];
            }
        );
        if (runtimeById.size > 0) {
            const extra = [...runtimeById.keys()][0];
            fail(
                'INVALID_RUNTIME_PROVIDER',
                `modules[${index}].runtimeProviders`,
                `Runtime provider '${extra}' is not required by this module`
            );
        }
        completeById.set(source.identity.moduleId, deepFreeze({
            identity: source.identity,
            chain: source.chain,
            dependencyProviders,
            runtimeProviders
        }));
    });

    const order = topologicalOrder(completeById);
    const modules = order.map(moduleId => {
        const source = completeById.get(moduleId);
        if (source === undefined) {
            return fail(
                'INVALID_WORKSPACE',
                'modules',
                `Planned module '${moduleId}' disappeared`
            );
        }
        return source;
    });
    return deepFreeze({
        revision: input.revision,
        profileRevision: CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
        modules,
        order
    });
}

export interface CoreLfCompiledFragmentModuleWorkspaceModule {
    readonly source: CoreLfFragmentModuleWorkspaceModule;
    readonly dependencyInterfaces:
        readonly CoreLfCompiledModuleInterface[];
    readonly runtimeDependencies:
        readonly CoreLfRuntimeFragmentDependency[];
    readonly compiled: CoreLfCompiledSameModuleFragmentWorkspace<
        CoreLfDependencyModuleFragmentChainPlan
    >;
}

export class CoreLfCompiledFragmentModuleWorkspace {
    readonly revision: string;
    readonly modules:
        readonly CoreLfCompiledFragmentModuleWorkspaceModule[];

    constructor(
        public readonly plan: CoreLfFragmentModuleWorkspacePlan,
        modules: readonly CoreLfCompiledFragmentModuleWorkspaceModule[],
        public readonly declarations: CoreLfMixedDeclarationContext
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.modules = Object.freeze([...modules]);
        Object.freeze(this);
    }

    module(
        moduleId: string
    ): CoreLfCompiledFragmentModuleWorkspaceModule | undefined {
        return this.modules.find(source =>
            source.source.identity.moduleId === moduleId
        );
    }
}

/** Reconstruct and compile every exact provider in stable topological order. */
export function compileCoreLfFragmentModuleWorkspace(
    inputPlan: CoreLfFragmentModuleWorkspacePlan
): CoreLfCompiledFragmentModuleWorkspace {
    if (
        inputPlan.profileRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision
    ) {
        return fail(
            'INVALID_WORKSPACE',
            'plan.profileRevision',
            'Fragment-module workspace targets an unsupported profile'
        );
    }
    const plan = createCoreLfFragmentModuleWorkspace({
        revision: inputPlan.revision,
        modules: inputPlan.modules
    });
    if (
        serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
            createCoreLfFragmentModuleWorkspaceSourceSnapshot(inputPlan)
        ) !== serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
            createCoreLfFragmentModuleWorkspaceSourceSnapshot(plan)
        )
    ) {
        return fail(
            'INVALID_WORKSPACE',
            'plan',
            'Fragment-module workspace is not canonically reconstructed'
        );
    }

    let declarations = new CoreLfMixedDeclarationContext();
    const compiledById = new Map<
        string,
        CoreLfCompiledFragmentModuleWorkspaceModule
    >();
    const modules: CoreLfCompiledFragmentModuleWorkspaceModule[] = [];

    plan.modules.forEach((source, moduleIndex) => {
        const dependencyModules = source.dependencyProviders.map(
            (provider, dependencyIndex) => {
                const compiled = compiledById.get(provider.moduleId);
                if (compiled === undefined) {
                    return fail(
                        'INVALID_DEPENDENCY_PROVIDER',
                        `modules[${moduleIndex}].dependencyProviders[` +
                            `${dependencyIndex}]`,
                        `Dependency '${provider.moduleId}' is not compiled`
                    );
                }
                if (!sameModuleIdentity(provider, compiled.source.identity)) {
                    return fail(
                        'INVALID_DEPENDENCY_PROVIDER',
                        `modules[${moduleIndex}].dependencyProviders[` +
                            `${dependencyIndex}]`,
                        `Compiled dependency '${provider.moduleId}' drifted`
                    );
                }
                return compiled;
            }
        );
        const dependencyInterfaces = dependencyModules.flatMap(compiled =>
            compiled.compiled.moduleInterface === undefined
                ? []
                : [compiled.compiled.moduleInterface]
        );
        const runtimeDependencies = source.runtimeProviders.map(
            (provider, runtimeIndex) => {
                const compiled = compiledById.get(provider.moduleId);
                const fragment = compiled?.compiled.fragment(provider.fragment);
                if (fragment?.runtime === undefined) {
                    return fail(
                        'INVALID_RUNTIME_PROVIDER',
                        `modules[${moduleIndex}].runtimeProviders[` +
                            `${runtimeIndex}]`,
                        `Runtime provider '${provider.moduleId}' did not ` +
                            'locally compile the named fragment'
                    );
                }
                return deepFreeze({
                    relation: 'dependency-module' as const,
                    fragment: fragment.runtime
                });
            }
        );
        const compiled = compileCoreLfDependencyModuleFragmentChain(
            source.chain,
            {
                initialDeclarations: declarations,
                dependencyInterfaces,
                runtimeDependencies
            }
        );
        declarations = compiled.declarations;
        const result = deepFreeze({
            source,
            dependencyInterfaces,
            runtimeDependencies,
            compiled
        });
        compiledById.set(source.identity.moduleId, result);
        modules.push(result);
    });

    return new CoreLfCompiledFragmentModuleWorkspace(
        plan,
        modules,
        declarations
    );
}

export interface CoreLfFragmentModuleWorkspaceSourceSnapshotModule {
    readonly identity: CoreLfFragmentModuleIdentity;
    readonly dependencyProviders: readonly CoreLfFragmentModuleIdentity[];
    readonly runtimeProviders:
        readonly CoreLfFragmentModuleRuntimeProvider[];
    readonly chain: CoreLfDependencyModuleFragmentChainSourceSnapshot;
}

export interface CoreLfFragmentModuleWorkspaceSourceSnapshot {
    readonly revision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
            .sourceSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly order: readonly string[];
    readonly modules:
        readonly CoreLfFragmentModuleWorkspaceSourceSnapshotModule[];
}

export const createCoreLfFragmentModuleWorkspaceSourceSnapshot = (
    plan: CoreLfFragmentModuleWorkspacePlan
): CoreLfFragmentModuleWorkspaceSourceSnapshot => deepFreeze({
    revision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.sourceSnapshotRevision,
    profileRevision: CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
    workspaceRevision: plan.revision,
    order: [...plan.order],
    modules: plan.modules.map(source => ({
        identity: source.identity,
        dependencyProviders: source.dependencyProviders,
        runtimeProviders: source.runtimeProviders,
        chain: createCoreLfDependencyModuleFragmentChainSourceSnapshot(
            source.chain
        )
    }))
});

export const serializeCoreLfFragmentModuleWorkspaceSourceSnapshot = (
    snapshot: CoreLfFragmentModuleWorkspaceSourceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'fragmentModuleWorkspaceSourceSnapshot'
);

export interface CoreLfFragmentModuleWorkspaceCompiledSnapshotModule {
    readonly source: CoreLfFragmentModuleWorkspaceSourceSnapshotModule;
    readonly dependencyInterfaceModuleIds: readonly string[];
    readonly runtimeDependencies: readonly {
        readonly relation: 'dependency-module';
        readonly compiledIdentity: string;
    }[];
    readonly chain: CoreLfDependencyModuleFragmentChainSnapshot;
}

export interface CoreLfFragmentModuleWorkspaceSnapshot {
    readonly revision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
            .compiledSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly order: readonly string[];
    readonly modules:
        readonly CoreLfFragmentModuleWorkspaceCompiledSnapshotModule[];
}

export const createCoreLfFragmentModuleWorkspaceSnapshot = (
    compiled: CoreLfCompiledFragmentModuleWorkspace
): CoreLfFragmentModuleWorkspaceSnapshot => {
    const sourceSnapshot =
        createCoreLfFragmentModuleWorkspaceSourceSnapshot(compiled.plan);
    return deepFreeze({
        revision:
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
                .compiledSnapshotRevision,
        profileRevision: CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
        workspaceRevision: compiled.plan.revision,
        order: [...compiled.plan.order],
        modules: compiled.modules.map((module, index) => ({
            source: sourceSnapshot.modules[index],
            dependencyInterfaceModuleIds:
                module.dependencyInterfaces.map(value => value.moduleId),
            runtimeDependencies: module.runtimeDependencies.map(value => ({
                relation: 'dependency-module' as const,
                compiledIdentity: value.fragment.identity
            })),
            chain: createCoreLfDependencyModuleFragmentChainSnapshot(
                module.compiled
            )
        }))
    });
};

export const serializeCoreLfFragmentModuleWorkspaceSnapshot = (
    snapshot: CoreLfFragmentModuleWorkspaceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'fragmentModuleWorkspaceSnapshot'
);
