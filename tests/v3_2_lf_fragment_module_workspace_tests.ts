/** Focused AI-WORKSPACE-1B2B exact cross-module fragment-graph tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE,
    CoreLfFragmentModuleIdentity,
    CoreLfFragmentModuleWorkspaceError,
    CoreLfMixedDeclarationLinkage,
    CoreLfModuleSpec,
    CoreLfModuleVisibilityError,
    CoreLfSameModuleFragmentWorkspaceError,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    KernelExpression,
    binderMode,
    compileCoreLfFragmentModuleWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfFragmentModuleIdentity,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSnapshot,
    createCoreLfFragmentModuleWorkspaceSourceSnapshot,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    defineCoreLfDependencyModuleDeclarationFragment,
    defineCoreLfDependencyModuleMixedFragment,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    planCoreLfMixedPhases,
    provenance,
    serializeCoreLfFragmentModuleWorkspaceSnapshot,
    serializeCoreLfFragmentModuleWorkspaceSourceSnapshot
} from '../src/v3_2';

type Symbol = ReturnType<typeof coreLfQualifiedSymbol>;

const providerModuleId = 'fixture.fragment_graph_provider';
const consumerModuleId = 'fixture.fragment_graph_consumer';
const unrelatedModuleId = 'fixture.fragment_graph_aaa_unrelated';
const siblingModuleId = 'fixture.fragment_graph_sibling';
const topModuleId = 'fixture.fragment_graph_top';
const providerAuthority = 'tests/fixtures/fragment_graph_provider.lp';
const consumerAuthority = 'tests/fixtures/fragment_graph_consumer.lp';
const unrelatedAuthority = 'tests/fixtures/fragment_graph_unrelated.lp';
const providerSha = `sha256:${'c'.repeat(64)}`;
const consumerSha = `sha256:${'d'.repeat(64)}`;
const unrelatedSha = `sha256:${'e'.repeat(64)}`;

const carrier = coreLfQualifiedSymbol(providerModuleId, 'Carrier');
const token = coreLfQualifiedSymbol(providerModuleId, 'token');
const normalize = coreLfQualifiedSymbol(providerModuleId, 'normalize');
const providerLeft = coreLfQualifiedSymbol(providerModuleId, 'left_head');
const providerRight = coreLfQualifiedSymbol(providerModuleId, 'right_head');
const published = coreLfQualifiedSymbol(providerModuleId, 'published');
const consume = coreLfQualifiedSymbol(consumerModuleId, 'consume');
const consumerLeft = coreLfQualifiedSymbol(consumerModuleId, 'left_head');
const unrelatedSecret = coreLfQualifiedSymbol(unrelatedModuleId, 'secret');
const siblingHead = coreLfQualifiedSymbol(siblingModuleId, 'sibling');
const topHead = coreLfQualifiedSymbol(topModuleId, 'top');

const mode = binderMode('explicit', 'functorial');

const coreName = (symbol: Symbol): string =>
    `${symbol.moduleId.replace(/\./gu, '_')}_${symbol.name}`;

const source = (authorityPath: string, sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const global = (symbol: Symbol): CoreLfTransferExpression => ({
    tag: 'global',
    symbol
});

const unaryType = (base: Symbol): CoreLfTransferExpression => ({
    tag: 'pi',
    binder: {
        hint: 'value',
        mode,
        type: global(base)
    },
    body: global(base)
});

const modifiers = (visibility: 'public' | 'protected' | 'private') => ({
    visibility,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
});

const declaration = (
    order: number,
    symbol: Symbol,
    type: CoreLfTransferExpression,
    authorityPath: string,
    visibility: 'public' | 'protected' | 'private' = 'public'
) => ({
    order,
    symbol,
    type,
    body: coreLfTransferAbsentBody(),
    modifiers: modifiers(visibility),
    provenance: source(authorityPath, `symbol ${symbol.name};`)
});

const links = (symbols: readonly Symbol[]) => symbols.map((symbol, order) => ({
    order,
    symbol,
    kind: 'free-declaration' as const,
    coreName: coreName(symbol),
    backendName: symbol.name
}));

const policyFor = (
    module: CoreLfModuleSpec,
    revision: string
): CoreLfTransferPolicyOverlay => {
    const entries = [
        ...module.declarations.map(value => ({
            sourceOrder: value.order,
            target: {
                kind: 'declaration' as const,
                symbol: value.symbol
            },
            policy: 'opaque-signature' as const
        })),
        ...module.runtimeRules.map(value => ({
            sourceOrder: value.order,
            target: {
                kind: 'runtime-rule' as const,
                id: value.id
            },
            policy: 'runtime-rewrite' as const
        })),
        ...module.proofRules.map(value => ({
            sourceOrder: value.order,
            target: {
                kind: 'proof-rule' as const,
                id: value.id
            },
            policy: 'proof-unification' as const
        }))
    ].sort((left, right) => left.sourceOrder - right.sourceOrder);
    return createCoreLfTransferPolicyOverlay(module, {
        revision,
        moduleRevision: module.revision,
        entries: entries.map((entry, order) => ({
            order,
            target: entry.target,
            policy: entry.policy,
            evidence: 'fragment-module workspace fixture'
        }))
    });
};

const call = (
    builder: CoreLfTransferScopedBuilder,
    symbol: Symbol,
    value: ReturnType<CoreLfTransferScopedBuilder['capture']>
) => builder.call(
    builder.global(symbol),
    [{ plicity: 'explicit', value }]
);

const proofRule = (
    order: number,
    id: string,
    base: Symbol,
    left: Symbol,
    right: Symbol,
    authorityPath: string
) => {
    const pattern = new CoreLfTransferScopedBuilder();
    const template = new CoreLfTransferScopedBuilder();
    return {
        order,
        id,
        sourceOwner: left,
        variables: ['x', 'y'].map(name => ({
            name,
            role: 'matched' as const,
            type: global(base)
        })),
        problem: {
            left: pattern.pattern(call(
                pattern,
                left,
                pattern.capture('x')
            )),
            right: pattern.pattern(call(
                pattern,
                right,
                pattern.capture('y')
            ))
        },
        generatedConstraints: [{
            left: template.template(template.capture('x')),
            right: template.template(template.capture('y'))
        }],
        provenance: source(authorityPath, `unif_rule ${id};`)
    };
};

interface FixtureOptions {
    readonly privateCarrier?: boolean;
    readonly reverseProviderFragments?: boolean;
    readonly reverseConsumerFragments?: boolean;
    readonly includeUnrelated?: boolean;
}

const providerFixture = (options: FixtureOptions = {}) => {
    const baseModule = createCoreLfModuleSpec({
        revision: 'fragment-graph-provider-base-1',
        moduleId: providerModuleId,
        fragmentId: 'provider-base',
        authorityPath: providerAuthority,
        sourceSha256: providerSha,
        dependencies: [],
        externalSymbols: [],
        declarations: [
            declaration(
                0,
                carrier,
                { tag: 'type' },
                providerAuthority,
                options.privateCarrier ? 'private' : 'public'
            ),
            declaration(1, token, global(carrier), providerAuthority),
            declaration(2, normalize, unaryType(carrier), providerAuthority),
            declaration(3, providerLeft, unaryType(carrier), providerAuthority),
            declaration(4, providerRight, unaryType(carrier), providerAuthority)
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const base = defineCoreLfDependencyModuleDeclarationFragment({
        module: baseModule,
        policy: policyFor(baseModule, 'fragment-graph-provider-base-policy-1'),
        linkage: createCoreLfTransferDeclarationLinkage(baseModule, {
            revision: 'fragment-graph-provider-base-linkage-1',
            moduleRevision: baseModule.revision,
            entries: links([
                carrier,
                token,
                normalize,
                providerLeft,
                providerRight
            ])
        })
    });

    const runtime = new CoreLfTransferScopedBuilder();
    const value = runtime.capture('value');
    const mixedModule = createCoreLfModuleSpec({
        revision: 'fragment-graph-provider-mixed-1',
        moduleId: providerModuleId,
        fragmentId: 'provider-mixed',
        authorityPath: providerAuthority,
        sourceSha256: providerSha,
        dependencies: [],
        externalSymbols: [
            carrier,
            normalize,
            providerLeft,
            providerRight
        ].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [
            declaration(5, published, global(carrier), providerAuthority)
        ],
        inductives: [],
        runtimeRules: [{
            order: 6,
            id: 'fixture.fragment_graph.normalize',
            groupId: 'fixture.fragment_graph.normalize',
            clauseOrder: 0,
            sourceOwner: normalize,
            variables: [{ name: 'value', type: global(carrier) }],
            left: runtime.pattern(call(runtime, normalize, value)),
            right: runtime.template(value),
            provenance: source(
                providerAuthority,
                'rule normalize $value ↪ $value;'
            )
        }],
        proofRules: [proofRule(
            7,
            'fixture.fragment_graph.provider_heads',
            carrier,
            providerLeft,
            providerRight,
            providerAuthority
        )]
    });
    const mixedPolicy = policyFor(
        mixedModule,
        'fragment-graph-provider-mixed-policy-1'
    );
    const mixedPlan = planCoreLfMixedPhases(mixedModule, mixedPolicy);
    const mixed = defineCoreLfDependencyModuleMixedFragment({
        module: mixedModule,
        policy: mixedPolicy,
        linkage: createCoreLfMixedDeclarationLinkage(mixedPlan, {
            revision: 'fragment-graph-provider-mixed-linkage-1',
            moduleRevision: mixedModule.revision,
            entries: links([
                carrier,
                normalize,
                providerLeft,
                providerRight,
                published
            ])
        }),
        externalProviders: mixedModule.externalSymbols.map(external => ({
            symbol: external.symbol,
            provider: base.identity
        }))
    });
    const chain = createCoreLfDependencyModuleFragmentChain({
        revision: 'fragment-graph-provider-chain-1',
        fragments: options.reverseProviderFragments
            ? [mixed, base]
            : [base, mixed]
    });
    return { base, mixed, chain };
};

const consumerFixture = (
    options: FixtureOptions = {}
) => {
    const baseModule = createCoreLfModuleSpec({
        revision: 'fragment-graph-consumer-base-1',
        moduleId: consumerModuleId,
        fragmentId: 'consumer-base',
        authorityPath: consumerAuthority,
        sourceSha256: consumerSha,
        dependencies: [providerModuleId],
        externalSymbols: [{
            symbol: carrier,
            availability: 'dependency-module'
        }],
        declarations: [
            declaration(0, consume, unaryType(carrier), consumerAuthority),
            declaration(
                1,
                consumerLeft,
                unaryType(carrier),
                consumerAuthority
            )
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const base = defineCoreLfDependencyModuleDeclarationFragment({
        module: baseModule,
        policy: policyFor(baseModule, 'fragment-graph-consumer-base-policy-1'),
        linkage: createCoreLfTransferDeclarationLinkage(baseModule, {
            revision: 'fragment-graph-consumer-base-linkage-1',
            moduleRevision: baseModule.revision,
            entries: links([carrier, consume, consumerLeft])
        })
    });

    const runtime = new CoreLfTransferScopedBuilder();
    const value = runtime.capture('value');
    const nested = call(runtime, normalize, value);
    const mixedModule = createCoreLfModuleSpec({
        revision: 'fragment-graph-consumer-mixed-1',
        moduleId: consumerModuleId,
        fragmentId: 'consumer-mixed',
        authorityPath: consumerAuthority,
        sourceSha256: consumerSha,
        dependencies: [providerModuleId],
        externalSymbols: [
            ...[
                carrier,
                normalize,
                providerRight
            ].map(symbol => ({
                symbol,
                availability: 'dependency-module' as const
            })),
            ...[
                consume,
                consumerLeft
            ].map(symbol => ({
                symbol,
                availability: 'earlier-fragment' as const
            }))
        ],
        declarations: [],
        inductives: [],
        runtimeRules: [{
            order: 2,
            id: 'fixture.fragment_graph.consume',
            groupId: 'fixture.fragment_graph.consume',
            clauseOrder: 0,
            sourceOwner: consume,
            variables: [{ name: 'value', type: global(carrier) }],
            left: runtime.pattern(call(runtime, consume, value)),
            right: runtime.template(call(runtime, normalize, nested)),
            provenance: source(
                consumerAuthority,
                'rule consume $value ↪ normalize (normalize $value);'
            )
        }],
        proofRules: [proofRule(
            3,
            'fixture.fragment_graph.consumer_heads',
            carrier,
            consumerLeft,
            providerRight,
            consumerAuthority
        )]
    });
    const mixedPolicy = policyFor(
        mixedModule,
        'fragment-graph-consumer-mixed-policy-1'
    );
    const mixedPlan = planCoreLfMixedPhases(mixedModule, mixedPolicy);
    const mixed = defineCoreLfDependencyModuleMixedFragment({
        module: mixedModule,
        policy: mixedPolicy,
        linkage: createCoreLfMixedDeclarationLinkage(mixedPlan, {
            revision: 'fragment-graph-consumer-mixed-linkage-1',
            moduleRevision: mixedModule.revision,
            entries: links([
                carrier,
                normalize,
                providerRight,
                consume,
                consumerLeft
            ])
        }),
        externalProviders: [consume, consumerLeft].map(symbol => ({
            symbol,
            provider: base.identity
        }))
    });
    const chain = createCoreLfDependencyModuleFragmentChain({
        revision: 'fragment-graph-consumer-chain-1',
        fragments: options.reverseConsumerFragments
            ? [mixed, base]
            : [base, mixed]
    });
    return { base, mixed, chain };
};

const unrelatedFixture = () => {
    const module = createCoreLfModuleSpec({
        revision: 'fragment-graph-unrelated-1',
        moduleId: unrelatedModuleId,
        fragmentId: 'unrelated-base',
        authorityPath: unrelatedAuthority,
        sourceSha256: unrelatedSha,
        dependencies: [],
        externalSymbols: [],
        declarations: [declaration(
            0,
            unrelatedSecret,
            { tag: 'type' },
            unrelatedAuthority
        )],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const fragment = defineCoreLfDependencyModuleDeclarationFragment({
        module,
        policy: policyFor(module, 'fragment-graph-unrelated-policy-1'),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'fragment-graph-unrelated-linkage-1',
            moduleRevision: module.revision,
            entries: links([unrelatedSecret])
        })
    });
    return createCoreLfDependencyModuleFragmentChain({
        revision: 'fragment-graph-unrelated-chain-1',
        fragments: [fragment]
    });
};

const siblingFixture = () => {
    const authorityPath = 'tests/fixtures/fragment_graph_sibling.lp';
    const runtime = new CoreLfTransferScopedBuilder();
    const value = runtime.capture('value');
    const module = createCoreLfModuleSpec({
        revision: 'fragment-graph-sibling-1',
        moduleId: siblingModuleId,
        fragmentId: 'sibling-mixed',
        authorityPath,
        sourceSha256: `sha256:${'f'.repeat(64)}`,
        dependencies: [providerModuleId],
        externalSymbols: [carrier, normalize].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [
            declaration(0, siblingHead, unaryType(carrier), authorityPath)
        ],
        inductives: [],
        runtimeRules: [{
            order: 1,
            id: 'fixture.fragment_graph.sibling',
            groupId: 'fixture.fragment_graph.sibling',
            clauseOrder: 0,
            sourceOwner: siblingHead,
            variables: [{ name: 'value', type: global(carrier) }],
            left: runtime.pattern(call(runtime, siblingHead, value)),
            right: runtime.template(call(runtime, normalize, value)),
            provenance: source(
                authorityPath,
                'rule sibling $value ↪ normalize $value;'
            )
        }],
        proofRules: []
    });
    const policy = policyFor(module, 'fragment-graph-sibling-policy-1');
    const plan = planCoreLfMixedPhases(module, policy);
    const fragment = defineCoreLfDependencyModuleMixedFragment({
        module,
        policy,
        linkage: createCoreLfMixedDeclarationLinkage(plan, {
            revision: 'fragment-graph-sibling-linkage-1',
            moduleRevision: module.revision,
            entries: links([carrier, normalize, siblingHead])
        })
    });
    return {
        fragment,
        chain: createCoreLfDependencyModuleFragmentChain({
            revision: 'fragment-graph-sibling-chain-1',
            fragments: [fragment]
        })
    };
};

const topFixture = () => {
    const authorityPath = 'tests/fixtures/fragment_graph_top.lp';
    const runtime = new CoreLfTransferScopedBuilder();
    const value = runtime.capture('value');
    const siblingValue = call(runtime, siblingHead, value);
    const module = createCoreLfModuleSpec({
        revision: 'fragment-graph-top-1',
        moduleId: topModuleId,
        fragmentId: 'top-mixed',
        authorityPath,
        sourceSha256: `sha256:${'9'.repeat(64)}`,
        dependencies: [
            providerModuleId,
            consumerModuleId,
            siblingModuleId
        ],
        externalSymbols: [
            carrier,
            normalize,
            consume,
            siblingHead
        ].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [
            declaration(0, topHead, unaryType(carrier), authorityPath)
        ],
        inductives: [],
        runtimeRules: [{
            order: 1,
            id: 'fixture.fragment_graph.top',
            groupId: 'fixture.fragment_graph.top',
            clauseOrder: 0,
            sourceOwner: topHead,
            variables: [{ name: 'value', type: global(carrier) }],
            left: runtime.pattern(call(runtime, topHead, value)),
            right: runtime.template(call(
                runtime,
                consume,
                siblingValue
            )),
            provenance: source(
                authorityPath,
                'rule top $value ↪ consume (sibling $value);'
            )
        }],
        proofRules: []
    });
    const policy = policyFor(module, 'fragment-graph-top-policy-1');
    const plan = planCoreLfMixedPhases(module, policy);
    const fragment = defineCoreLfDependencyModuleMixedFragment({
        module,
        policy,
        linkage: createCoreLfMixedDeclarationLinkage(plan, {
            revision: 'fragment-graph-top-linkage-1',
            moduleRevision: module.revision,
            entries: links([
                carrier,
                normalize,
                consume,
                siblingHead,
                topHead
            ])
        })
    });
    return {
        fragment,
        chain: createCoreLfDependencyModuleFragmentChain({
            revision: 'fragment-graph-top-chain-1',
            fragments: [fragment]
        })
    };
};

const fixture = (options: FixtureOptions = {}) => {
    const provider = providerFixture(options);
    const consumer = consumerFixture(options);
    const providerIdentity = createCoreLfFragmentModuleIdentity(provider.chain);
    const modules = [
        {
            chain: consumer.chain,
            dependencyProviders: [providerIdentity],
            runtimeProviders: [{
                moduleId: providerModuleId,
                fragment: provider.mixed.identity
            }]
        },
        { chain: provider.chain },
        ...(options.includeUnrelated
            ? [{ chain: unrelatedFixture() }]
            : [])
    ];
    return { provider, consumer, providerIdentity, modules };
};

const planFixture = (options: FixtureOptions = {}) => {
    const value = fixture(options);
    return {
        ...value,
        plan: createCoreLfFragmentModuleWorkspace({
            revision: 'fragment-module-workspace-fixture-1',
            modules: value.modules
        })
    };
};

const expectWorkspaceError = (
    action: () => unknown,
    code: CoreLfFragmentModuleWorkspaceError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfFragmentModuleWorkspaceError &&
            error.code === code &&
            error.path.length > 0
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('AI-WORKSPACE-1B2B exact cross-module fragment graph', () => {
    it('compiles multi-provider interfaces, imported runtime, and local proof', () => {
        const { plan } = planFixture();
        const compiled = compileCoreLfFragmentModuleWorkspace(plan);
        assert.deepEqual(compiled.plan.order, [
            providerModuleId,
            consumerModuleId
        ]);
        const provider = compiled.module(providerModuleId);
        const consumer = compiled.module(consumerModuleId);
        assert.notEqual(provider, undefined);
        assert.notEqual(consumer, undefined);
        if (provider === undefined || consumer === undefined) return;
        assert.equal(provider.compiled.moduleInterface?.providers.length, 2);
        assert.deepEqual(
            provider.compiled.moduleInterface?.entries.map(entry =>
                entry.symbol.name
            ),
            [
                'Carrier',
                'token',
                'normalize',
                'left_head',
                'right_head',
                'published'
            ]
        );
        assert.deepEqual(
            consumer.dependencyInterfaces.map(value => value.moduleId),
            [providerModuleId]
        );
        assert.deepEqual(
            consumer.runtimeDependencies.map(value => [
                value.relation,
                value.fragment.module.fragmentId
            ]),
            [['dependency-module', 'provider-mixed-mixed-1-runtime']]
        );
        assert.deepEqual(consumer.compiled.latestRuntime?.runtime.ruleIds, [
            'fixture.fragment_graph.normalize',
            'fixture.fragment_graph.consume'
        ]);

        const nodeSource = provenance(
            'derived',
            'AI-WORKSPACE-1B2B execution witness'
        );
        const tokenTerm = kernelFree(coreName(token), nodeSource);
        const consumeTerm = kernelCall(
            kernelFree(coreName(consume), nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const runtime = consumer.compiled.latestRuntime?.runtime;
        assert.notEqual(runtime, undefined);
        if (runtime === undefined) return;
        const ruleIds: string[] = [];
        let reduced: KernelExpression = consumeTerm;
        for (let step = 0; step < 8; step += 1) {
            const rewrite = runtime.rewriteHead(reduced);
            if (rewrite.status === 'irreducible') break;
            ruleIds.push(rewrite.ruleId);
            reduced = rewrite.after;
        }
        assert.equal(kernelExpressionEquals(reduced, tokenTerm), true);
        assert.deepEqual(ruleIds, [
            'fixture.fragment_graph.consume',
            'fixture.fragment_graph.normalize',
            'fixture.fragment_graph.normalize'
        ]);

        const leftTerm = kernelCall(
            kernelFree(coreName(consumerLeft), nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const rightTerm = kernelCall(
            kernelFree(coreName(providerRight), nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const proof = consumer.compiled.proofProgram?.compare(
            leftTerm,
            rightTerm,
            { stepLimit: 8 }
        );
        assert.equal(proof?.status, 'solved', JSON.stringify(proof));
        assertDeepFrozen(compiled.plan);
    });

    it('is byte-stable across module and fragment input permutations', () => {
        const first = planFixture();
        const second = planFixture({
            reverseProviderFragments: true,
            reverseConsumerFragments: true
        });
        const reversedModules = createCoreLfFragmentModuleWorkspace({
            revision: second.plan.revision,
            modules: [...second.modules].reverse()
        });
        assert.equal(
            serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
                createCoreLfFragmentModuleWorkspaceSourceSnapshot(first.plan)
            ),
            serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
                createCoreLfFragmentModuleWorkspaceSourceSnapshot(
                    reversedModules
                )
            )
        );
        const firstText = serializeCoreLfFragmentModuleWorkspaceSnapshot(
            createCoreLfFragmentModuleWorkspaceSnapshot(
                compileCoreLfFragmentModuleWorkspace(first.plan)
            )
        );
        const secondText = serializeCoreLfFragmentModuleWorkspaceSnapshot(
            createCoreLfFragmentModuleWorkspaceSnapshot(
                compileCoreLfFragmentModuleWorkspace(reversedModules)
            )
        );
        assert.equal(firstText, secondText);
        assert.equal(/environment|session|callback|objectIdentity/u.test(
            firstText
        ), false);
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.nodeBuiltinDependency,
            false
        );
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
                .computesCryptographicHashes,
            false
        );
    });

    it('deduplicates an exact imported runtime diamond in source order', () => {
        const value = fixture();
        const consumerInput = value.modules[0];
        const consumerIdentity = createCoreLfFragmentModuleIdentity(
            value.consumer.chain
        );
        const sibling = siblingFixture();
        const siblingIdentity = createCoreLfFragmentModuleIdentity(
            sibling.chain
        );
        const top = topFixture();
        const plan = createCoreLfFragmentModuleWorkspace({
            revision: 'fragment-module-runtime-diamond-1',
            modules: [
                {
                    chain: top.chain,
                    dependencyProviders: [
                        siblingIdentity,
                        value.providerIdentity,
                        consumerIdentity
                    ],
                    runtimeProviders: [
                        {
                            moduleId: siblingModuleId,
                            fragment: sibling.fragment.identity
                        },
                        {
                            moduleId: consumerModuleId,
                            fragment: value.consumer.mixed.identity
                        },
                        {
                            moduleId: providerModuleId,
                            fragment: value.provider.mixed.identity
                        }
                    ]
                },
                {
                    chain: sibling.chain,
                    dependencyProviders: [value.providerIdentity],
                    runtimeProviders: [{
                        moduleId: providerModuleId,
                        fragment: value.provider.mixed.identity
                    }]
                },
                consumerInput,
                { chain: value.provider.chain }
            ]
        });
        const topSource = plan.modules.find(source =>
            source.identity.moduleId === topModuleId
        );
        assert.deepEqual(
            topSource?.dependencyProviders.map(source => source.moduleId),
            [providerModuleId, consumerModuleId, siblingModuleId]
        );
        assert.deepEqual(
            topSource?.runtimeProviders.map(source => source.moduleId),
            [providerModuleId, consumerModuleId, siblingModuleId]
        );

        const compiled = compileCoreLfFragmentModuleWorkspace(plan);
        const topRuntime = compiled.module(topModuleId)
            ?.compiled.latestRuntime?.runtime;
        assert.deepEqual(topRuntime?.ruleIds, [
            'fixture.fragment_graph.normalize',
            'fixture.fragment_graph.consume',
            'fixture.fragment_graph.sibling',
            'fixture.fragment_graph.top'
        ]);
        assert.equal(
            topRuntime?.fragments.filter(fragment =>
                fragment.module.moduleId === providerModuleId
            ).length,
            1
        );

        const nodeSource = provenance(
            'derived',
            'AI-WORKSPACE-1B2B runtime diamond witness'
        );
        const tokenTerm = kernelFree(coreName(token), nodeSource);
        let reduced: KernelExpression = kernelCall(
            kernelFree(coreName(topHead), nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        for (let step = 0; step < 12; step += 1) {
            const rewrite = topRuntime?.rewriteHead(reduced);
            if (rewrite === undefined || rewrite.status === 'irreducible') {
                break;
            }
            reduced = rewrite.after;
        }
        assert.equal(kernelExpressionEquals(reduced, tokenTerm), true);
    });

    it('requires exact direct dependency source identities', () => {
        const value = fixture();
        const consumer = value.modules[0];
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'missing-dependency-provider-1',
                modules: [
                    { chain: consumer.chain },
                    { chain: value.provider.chain }
                ]
            }),
            'MISSING_DEPENDENCY_PROVIDER'
        );
        const stale: CoreLfFragmentModuleIdentity = {
            ...value.providerIdentity,
            chainRevision: 'stale-provider-chain-1'
        };
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'stale-dependency-provider-1',
                modules: [
                    {
                        ...consumer,
                        dependencyProviders: [stale]
                    },
                    { chain: value.provider.chain }
                ]
            }),
            'INVALID_DEPENDENCY_PROVIDER'
        );
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'extra-dependency-provider-1',
                modules: [
                    { chain: value.provider.chain },
                    {
                        chain: value.consumer.chain,
                        dependencyProviders: [
                            value.providerIdentity,
                            {
                                ...value.providerIdentity,
                                moduleId: unrelatedModuleId
                            }
                        ],
                        runtimeProviders: consumer.runtimeProviders
                    }
                ]
            }),
            'INVALID_DEPENDENCY_PROVIDER'
        );
    });

    it('requires each dependency exact latest local runtime provider', () => {
        const value = fixture();
        const consumer = value.modules[0];
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'missing-runtime-provider-1',
                modules: [
                    {
                        chain: consumer.chain,
                        dependencyProviders: consumer.dependencyProviders
                    },
                    { chain: value.provider.chain }
                ]
            }),
            'MISSING_RUNTIME_PROVIDER'
        );
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'stale-runtime-provider-1',
                modules: [
                    {
                        ...consumer,
                        runtimeProviders: [{
                            moduleId: providerModuleId,
                            fragment: value.provider.base.identity
                        }]
                    },
                    { chain: value.provider.chain }
                ]
            }),
            'INVALID_RUNTIME_PROVIDER'
        );
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'extra-runtime-provider-1',
                modules: [
                    {
                        chain: value.provider.chain,
                        runtimeProviders: [{
                            moduleId: providerModuleId,
                            fragment: value.provider.mixed.identity
                        }]
                    },
                    consumer
                ]
            }),
            'INVALID_RUNTIME_PROVIDER'
        );
    });

    it('keeps unrelated earlier modules outside exact dependency artifacts', () => {
        const { plan } = planFixture({ includeUnrelated: true });
        const compiled = compileCoreLfFragmentModuleWorkspace(plan);
        assert.deepEqual(compiled.plan.order, [
            unrelatedModuleId,
            providerModuleId,
            consumerModuleId
        ]);
        assert.deepEqual(
            compiled.module(consumerModuleId)?.dependencyInterfaces.map(
                value => value.moduleId
            ),
            [providerModuleId]
        );

        const module = createCoreLfModuleSpec({
            revision: 'fragment-graph-contaminated-1',
            moduleId: consumerModuleId,
            fragmentId: 'contaminated',
            authorityPath: consumerAuthority,
            sourceSha256: consumerSha,
            dependencies: [providerModuleId],
            externalSymbols: [{
                symbol: unrelatedSecret,
                availability: 'existing-core'
            }],
            declarations: [declaration(
                20,
                coreLfQualifiedSymbol(consumerModuleId, 'bad'),
                global(unrelatedSecret),
                consumerAuthority
            )],
            inductives: [],
            runtimeRules: [],
            proofRules: []
        });
        const policy = policyFor(module, 'fragment-graph-contaminated-policy-1');
        assert.throws(
            () => defineCoreLfDependencyModuleDeclarationFragment({
                module,
                policy,
                linkage: createCoreLfTransferDeclarationLinkage(module, {
                    revision: 'fragment-graph-contaminated-linkage-1',
                    moduleRevision: module.revision,
                    entries: links([
                        unrelatedSecret,
                        coreLfQualifiedSymbol(consumerModuleId, 'bad')
                    ])
                })
            }),
            error =>
                error instanceof CoreLfSameModuleFragmentWorkspaceError &&
                error.code === 'UNSUPPORTED_FRAGMENT'
        );
    });

    it('preserves dependency visibility through the multi-provider interface', () => {
        const { plan } = planFixture({ privateCarrier: true });
        assert.throws(
            () => compileCoreLfFragmentModuleWorkspace(plan),
            error =>
                error instanceof CoreLfModuleVisibilityError &&
                error.code === 'INACCESSIBLE_EXTERNAL_SYMBOL'
        );
    });

    it('rejects missing, duplicate, cyclic, and fabricated module graphs', () => {
        const value = fixture();
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'missing-module-1',
                modules: [value.modules[0], { chain: unrelatedFixture() }]
            }),
            'MISSING_DEPENDENCY'
        );
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'duplicate-module-1',
                modules: [
                    { chain: value.provider.chain },
                    { chain: value.provider.chain }
                ]
            }),
            'DUPLICATE_MODULE'
        );

        const simpleChain = (moduleId: string, dependency: string) => {
            const symbol = coreLfQualifiedSymbol(moduleId, 'Unit');
            const module = createCoreLfModuleSpec({
                revision: `${moduleId.replace(/\./gu, '-')}-1`,
                moduleId,
                fragmentId: 'base',
                authorityPath: `tests/fixtures/${moduleId}.lp`,
                sourceSha256: `sha256:${moduleId.endsWith('a')
                    ? '1'.repeat(64)
                    : '2'.repeat(64)}`,
                dependencies: [dependency],
                externalSymbols: [],
                declarations: [declaration(
                    0,
                    symbol,
                    { tag: 'type' },
                    `tests/fixtures/${moduleId}.lp`
                )],
                inductives: [],
                runtimeRules: [],
                proofRules: []
            });
            const fragment =
                defineCoreLfDependencyModuleDeclarationFragment({
                    module,
                    policy: policyFor(module, `${module.revision}-policy`),
                    linkage: createCoreLfTransferDeclarationLinkage(module, {
                        revision: `${module.revision}-linkage`,
                        moduleRevision: module.revision,
                        entries: links([symbol])
                    })
                });
            return createCoreLfDependencyModuleFragmentChain({
                revision: `${module.revision}-chain`,
                fragments: [fragment]
            });
        };
        const a = simpleChain('fixture.fragment_cycle_a', 'fixture.fragment_cycle_b');
        const b = simpleChain('fixture.fragment_cycle_b', 'fixture.fragment_cycle_a');
        const aIdentity = createCoreLfFragmentModuleIdentity(a);
        const bIdentity = createCoreLfFragmentModuleIdentity(b);
        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: 'cyclic-module-1',
                modules: [
                    { chain: a, dependencyProviders: [bIdentity] },
                    { chain: b, dependencyProviders: [aIdentity] }
                ]
            }),
            'CYCLIC_DEPENDENCY'
        );

        const { plan } = planFixture();
        expectWorkspaceError(
            () => compileCoreLfFragmentModuleWorkspace({
                ...plan,
                order: [...plan.order].reverse()
            }),
            'INVALID_WORKSPACE'
        );
    });
});
