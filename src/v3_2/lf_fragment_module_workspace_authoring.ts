/**
 * Direct-TypeScript authoring facade for exact fragment-module workspaces.
 *
 * A caller which already owns the complete closed module-chain set should not
 * have to repeat each dependency's full portable identity and latest local
 * runtime-fragment identity. This owner derives only those graph edges, then
 * lowers through the existing exact workspace factory. Explicit provider
 * claims remain the low-level authority for serialized or remote source.
 */

import {
    CoreLfDependencyModuleFragmentChainPlan,
    CoreLfWorkspaceFragmentIdentity
} from './lf_fragment_workspace';
import {
    CoreLfFragmentModuleIdentity,
    CoreLfFragmentModuleWorkspacePlan,
    createCoreLfFragmentModuleIdentity,
    createCoreLfFragmentModuleWorkspace
} from './lf_fragment_module_workspace';

export const CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE =
    Object.freeze({
        revision:
            'emdash-lf-fragment-module-workspace-authoring-v1' as const,
        lowering: 'exact-fragment-module-workspace-plan' as const,
        sourcePolicy: 'closed-complete-module-chain-set' as const,
        dependencyProviderPolicy:
            'derive-exact-declared-direct-module-identities' as const,
        runtimeProviderPolicy:
            'derive-latest-local-runtime-fragment-per-direct-dependency' as const,
        explicitRemoteProviderClaimsPreserved: true as const,
        promotesTransitiveDependencies: false as const,
        acceptsModuleIdentityInput: false as const,
        acceptsRuntimeInput: false as const,
        acceptsCompilerCallbacks: false as const,
        computesCryptographicHashes: false as const,
        performsIo: false as const,
        nodeBuiltinDependency: false as const,
        productionLambdapiDependency: false as const
    });

export const serializeCoreLfFragmentModuleWorkspaceAuthoringProfile =
    (): string => `${JSON.stringify(
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE,
        null,
        2
    )}\n`;

export interface CoreLfFragmentModuleWorkspaceAuthoringInput {
    readonly revision: string;
    readonly modules:
        readonly CoreLfDependencyModuleFragmentChainPlan[];
}

interface AuthoredModuleChain {
    readonly chain: CoreLfDependencyModuleFragmentChainPlan;
    readonly identity: CoreLfFragmentModuleIdentity;
}

const latestLocalRuntimeIdentity = (
    chain: CoreLfDependencyModuleFragmentChainPlan
): CoreLfWorkspaceFragmentIdentity | undefined => {
    for (let index = chain.fragments.length - 1; index >= 0; index--) {
        const fragment = chain.fragments[index];
        if (fragment.module.runtimeRules.length > 0) {
            return fragment.identity;
        }
    }
    return undefined;
};

/**
 * Derive exact direct-provider edges from complete chains and erase to the
 * unchanged low-level workspace plan. Missing, duplicate, cyclic, malformed,
 * or otherwise impossible graphs retain the existing owner's typed errors.
 */
export function createCoreLfAuthoredFragmentModuleWorkspace(
    input: CoreLfFragmentModuleWorkspaceAuthoringInput
): CoreLfFragmentModuleWorkspacePlan {
    const sources: readonly AuthoredModuleChain[] = input.modules.map(chain => ({
        chain,
        identity: createCoreLfFragmentModuleIdentity(chain)
    }));
    const byId = new Map(sources.map(source => [
        source.identity.moduleId,
        source
    ]));

    return createCoreLfFragmentModuleWorkspace({
        revision: input.revision,
        modules: sources.map(source => ({
            chain: source.chain,
            dependencyProviders: source.identity.dependencies.flatMap(
                dependency => {
                    const provider = byId.get(dependency);
                    return provider === undefined ? [] : [provider.identity];
                }
            ),
            runtimeProviders: source.identity.dependencies.flatMap(
                dependency => {
                    const provider = byId.get(dependency);
                    if (provider === undefined) return [];
                    const fragment = latestLocalRuntimeIdentity(provider.chain);
                    return fragment === undefined
                        ? []
                        : [{ moduleId: dependency, fragment }];
                }
            )
        }))
    });
}
