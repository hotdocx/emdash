/** Shared mechanism-only fixture for exact runtime-backed proof tests. */

import {
    CoreLfCompiledFragmentModuleWorkspace,
    CoreLfFragmentWorkspaceProofDocumentInput,
    CoreLfModuleSpec,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    binderMode,
    compileCoreLfFragmentModuleWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfFragmentModuleIdentity,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    defineCoreLfDependencyModuleDeclarationFragment,
    defineCoreLfDependencyModuleMixedFragment,
    kernelCall,
    kernelFree,
    planCoreLfMixedPhases,
    provenance
} from '../../src/v3_2';

type Symbol = ReturnType<typeof coreLfQualifiedSymbol>;

export const runtimeProofUnrelatedModuleId =
    'fixture.a_runtime_proof_unrelated';
export const runtimeProofProviderModuleId =
    'fixture.runtime_proof_provider';
export const runtimeProofConsumerModuleId =
    'fixture.runtime_proof_consumer';

const providerPath = 'tests/fixtures/runtime_proof_provider.lp';
const consumerPath = 'tests/fixtures/runtime_proof_consumer.lp';
const unrelatedPath = 'tests/fixtures/runtime_proof_unrelated.lp';
const providerSha = `sha256:${'1'.repeat(64)}`;
const consumerSha = `sha256:${'2'.repeat(64)}`;
const unrelatedSha = `sha256:${'3'.repeat(64)}`;

const code = coreLfQualifiedSymbol(runtimeProofProviderModuleId, 'Code');
const decode = coreLfQualifiedSymbol(runtimeProofProviderModuleId, 'El');
const base = coreLfQualifiedSymbol(
    runtimeProofProviderModuleId,
    'base_code'
);
const normalize = coreLfQualifiedSymbol(
    runtimeProofProviderModuleId,
    'normalize'
);
const marker = coreLfQualifiedSymbol(
    runtimeProofProviderModuleId,
    'runtime_marker'
);
const value = coreLfQualifiedSymbol(runtimeProofConsumerModuleId, 'value');
const secret = coreLfQualifiedSymbol(
    runtimeProofUnrelatedModuleId,
    'secret'
);
const mode = binderMode('explicit', 'functorial');

export const runtimeProofSymbols = Object.freeze({
    code,
    decode,
    base,
    normalize,
    marker,
    value,
    secret
});

const source = (authorityPath: string, sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const global = (symbol: Symbol) => ({
    tag: 'global' as const,
    symbol
});

const call = (
    symbol: Symbol,
    argument: CoreLfTransferExpression
): CoreLfTransferExpression => ({
    tag: 'call',
    callee: global(symbol),
    arguments: [{ plicity: 'explicit', value: argument }]
});

export const runtimeProofCoreName = (symbol: Symbol): string =>
    `${symbol.moduleId.replace(/\./gu, '_')}_${symbol.name}`;

const declaration = (
    order: number,
    symbol: Symbol,
    type: CoreLfTransferExpression,
    authorityPath: string
) => ({
    order,
    symbol,
    type,
    body: coreLfTransferAbsentBody(),
    modifiers: {
        visibility: 'public' as const,
        rigidity: 'ordinary' as const,
        sourceOpacity: 'opaque' as const
    },
    provenance: source(authorityPath, `symbol ${symbol.name};`)
});

const links = (symbols: readonly Symbol[]) => symbols.map((symbol, order) => ({
    order,
    symbol,
    kind: 'free-declaration' as const,
    coreName: runtimeProofCoreName(symbol),
    backendName: symbol.name
}));

const policyFor = (
    module: CoreLfModuleSpec,
    revision: string
): CoreLfTransferPolicyOverlay => {
    const entries = [
        ...module.declarations.map(entry => ({
            sourceOrder: entry.order,
            target: {
                kind: 'declaration' as const,
                symbol: entry.symbol
            },
            policy: 'opaque-signature' as const
        })),
        ...module.runtimeRules.map(entry => ({
            sourceOrder: entry.order,
            target: {
                kind: 'runtime-rule' as const,
                id: entry.id
            },
            policy: 'runtime-rewrite' as const
        }))
    ].sort((left, right) => left.sourceOrder - right.sourceOrder);
    return createCoreLfTransferPolicyOverlay(module, {
        revision,
        moduleRevision: module.revision,
        entries: entries.map((entry, order) => ({
            order,
            target: entry.target,
            policy: entry.policy,
            evidence: 'standalone runtime-proof fixture'
        }))
    });
};

const providerFixture = (withRuntime: boolean) => {
    const baseModule = createCoreLfModuleSpec({
        revision: 'runtime-proof-provider-base-1',
        moduleId: runtimeProofProviderModuleId,
        fragmentId: 'provider-base',
        authorityPath: providerPath,
        sourceSha256: providerSha,
        dependencies: [],
        externalSymbols: [],
        declarations: [
            declaration(0, code, { tag: 'type' }, providerPath),
            {
                order: 1,
                symbol: decode,
                type: {
                    tag: 'pi' as const,
                    binder: {
                        hint: 'code',
                        mode,
                        type: global(code)
                    },
                    body: { tag: 'type' as const }
                },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'opaque' as const
                },
                provenance: source(providerPath, 'symbol El;')
            },
            {
                order: 2,
                symbol: normalize,
                type: {
                    tag: 'pi' as const,
                    binder: {
                        hint: 'code',
                        mode,
                        type: global(code)
                    },
                    body: global(code)
                },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'opaque' as const
                },
                provenance: source(providerPath, 'symbol normalize;')
            },
            declaration(3, base, global(code), providerPath)
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const baseFragment = defineCoreLfDependencyModuleDeclarationFragment({
        module: baseModule,
        policy: policyFor(baseModule, 'runtime-proof-provider-base-policy-1'),
        linkage: createCoreLfTransferDeclarationLinkage(baseModule, {
            revision: 'runtime-proof-provider-base-linkage-1',
            moduleRevision: baseModule.revision,
            entries: links([code, decode, normalize, base])
        })
    });
    if (!withRuntime) {
        return {
            chain: createCoreLfDependencyModuleFragmentChain({
                revision: 'runtime-proof-provider-no-runtime-chain-1',
                fragments: [baseFragment]
            }),
            runtimeFragment: undefined
        };
    }

    const builder = new CoreLfTransferScopedBuilder();
    const captured = builder.capture('A');
    const mixedModule = createCoreLfModuleSpec({
        revision: 'runtime-proof-provider-mixed-1',
        moduleId: runtimeProofProviderModuleId,
        fragmentId: 'provider-mixed',
        authorityPath: providerPath,
        sourceSha256: providerSha,
        dependencies: [],
        externalSymbols: [code, normalize].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [
            declaration(4, marker, { tag: 'type' }, providerPath)
        ],
        inductives: [],
        runtimeRules: [{
            order: 5,
            id: 'fixture.runtime_proof.normalize',
            groupId: 'fixture.runtime_proof.normalize',
            clauseOrder: 0,
            sourceOwner: normalize,
            variables: [{ name: 'A', type: global(code) }],
            left: builder.pattern(builder.call(
                builder.global(normalize),
                [{ plicity: 'explicit', value: captured }]
            )),
            right: builder.template(captured),
            provenance: source(
                providerPath,
                'rule normalize $A ↪ $A;'
            )
        }],
        proofRules: []
    });
    const mixedPolicy = policyFor(
        mixedModule,
        'runtime-proof-provider-mixed-policy-1'
    );
    const mixedPlan = planCoreLfMixedPhases(mixedModule, mixedPolicy);
    const mixedFragment = defineCoreLfDependencyModuleMixedFragment({
        module: mixedModule,
        policy: mixedPolicy,
        linkage: createCoreLfMixedDeclarationLinkage(mixedPlan, {
            revision: 'runtime-proof-provider-mixed-linkage-1',
            moduleRevision: mixedModule.revision,
            entries: links([code, normalize, marker])
        }),
        externalProviders: [code, normalize].map(symbol => ({
            symbol,
            provider: baseFragment.identity
        }))
    });
    return {
        chain: createCoreLfDependencyModuleFragmentChain({
            revision: 'runtime-proof-provider-chain-1',
            fragments: [baseFragment, mixedFragment]
        }),
        runtimeFragment: mixedFragment.identity
    };
};

const consumerFixture = () => {
    const module = createCoreLfModuleSpec({
        revision: 'runtime-proof-consumer-1',
        moduleId: runtimeProofConsumerModuleId,
        fragmentId: 'consumer-base',
        authorityPath: consumerPath,
        sourceSha256: consumerSha,
        dependencies: [runtimeProofProviderModuleId],
        externalSymbols: [decode, normalize, base].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [declaration(
            0,
            value,
            call(decode, call(normalize, global(base))),
            consumerPath
        )],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const fragment = defineCoreLfDependencyModuleDeclarationFragment({
        module,
        policy: policyFor(module, 'runtime-proof-consumer-policy-1'),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'runtime-proof-consumer-linkage-1',
            moduleRevision: module.revision,
            entries: links([decode, normalize, base, value])
        })
    });
    return createCoreLfDependencyModuleFragmentChain({
        revision: 'runtime-proof-consumer-chain-1',
        fragments: [fragment]
    });
};

const unrelatedFixture = () => {
    const module = createCoreLfModuleSpec({
        revision: 'runtime-proof-unrelated-1',
        moduleId: runtimeProofUnrelatedModuleId,
        fragmentId: 'unrelated-base',
        authorityPath: unrelatedPath,
        sourceSha256: unrelatedSha,
        dependencies: [],
        externalSymbols: [],
        declarations: [declaration(0, secret, { tag: 'type' }, unrelatedPath)],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const fragment = defineCoreLfDependencyModuleDeclarationFragment({
        module,
        policy: policyFor(module, 'runtime-proof-unrelated-policy-1'),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'runtime-proof-unrelated-linkage-1',
            moduleRevision: module.revision,
            entries: links([secret])
        })
    });
    return createCoreLfDependencyModuleFragmentChain({
        revision: 'runtime-proof-unrelated-chain-1',
        fragments: [fragment]
    });
};

export interface RuntimeProofWorkspaceFixtureOptions {
    readonly runtime?: boolean;
    readonly reverse?: boolean;
}

export const createRuntimeProofWorkspaceFixture = (
    options: RuntimeProofWorkspaceFixtureOptions = {}
): CoreLfCompiledFragmentModuleWorkspace => {
    const provider = providerFixture(options.runtime ?? true);
    const consumer = consumerFixture();
    const unrelated = unrelatedFixture();
    const providerIdentity = createCoreLfFragmentModuleIdentity(provider.chain);
    const consumerInput = {
        chain: consumer,
        dependencyProviders: [providerIdentity],
        runtimeProviders: provider.runtimeFragment === undefined
            ? []
            : [{
                moduleId: runtimeProofProviderModuleId,
                fragment: provider.runtimeFragment
            }]
    };
    const modules = [
        consumerInput,
        { chain: provider.chain },
        { chain: unrelated }
    ];
    const plan = createCoreLfFragmentModuleWorkspace({
        revision: 'runtime-proof-workspace-1',
        modules: options.reverse ? [...modules].reverse() : modules
    });
    return compileCoreLfFragmentModuleWorkspace(plan);
};

export const createRuntimeProofDocumentInput = (
    workspace: CoreLfCompiledFragmentModuleWorkspace,
    open = false
): CoreLfFragmentWorkspaceProofDocumentInput => {
    const nodeSource = provenance('surface', 'runtime-proof source');
    const target = kernelCall(
        kernelFree(runtimeProofCoreName(decode), nodeSource),
        [{
            plicity: 'explicit',
            value: kernelFree(runtimeProofCoreName(base), nodeSource)
        }],
        nodeSource
    );
    return {
        moduleId: runtimeProofConsumerModuleId,
        declarationId: open
            ? 'open_runtime_proof'
            : 'complete_runtime_proof',
        type: target,
        plan: open
            ? coreProofPlanHole('runtime_body', { provenance: nodeSource })
            : coreProofPlanExact(
                kernelFree(runtimeProofCoreName(value), nodeSource)
            ),
        provenance: nodeSource,
        fingerprint: createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
            workspace,
            runtimeProofConsumerModuleId,
            'tests/fixtures/runtime_proof.surface.ts',
            {
                sourceSha256: `sha256:${'4'.repeat(64)}`,
                profileSha256: `sha256:${'5'.repeat(64)}`,
                interfaceSha256ByModuleId: {
                    [runtimeProofProviderModuleId]:
                        `sha256:${'6'.repeat(64)}`,
                    [runtimeProofConsumerModuleId]:
                        `sha256:${'7'.repeat(64)}`
                }
            }
        )
    };
};
