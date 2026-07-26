/**
 * Focused SCALE-MODULE-VISIBILITY-1 and SCALE-TACTIC-THEOREM-1 tests.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfDeclarationCompilerError,
    CoreLfMixedDeclarationContext,
    CoreLfModuleSpec,
    CoreLfModuleVisibilityError,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    binderMode,
    compileCoreLfDeclarations,
    compileCoreLfRuntimeProgram,
    coreLfDefinitionalCompare,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    coreLfTransferTacticBody,
    createCoreLfCompiledModuleInterface,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    kernelFree,
    provenance
} from '../src/v3_2';

const providerModuleId = 'fixture.visibility_provider';
const consumerModuleId = 'fixture.visibility_consumer';
const providerPath = 'tests/fixtures/visibility_provider.lp';
const consumerPath = 'tests/fixtures/visibility_consumer.lp';

const base = coreLfQualifiedSymbol(providerModuleId, 'Base');
const protectedHelper =
    coreLfQualifiedSymbol(providerModuleId, 'protected_helper');
const privateHelper =
    coreLfQualifiedSymbol(providerModuleId, 'private_helper');
const publicWrapper =
    coreLfQualifiedSymbol(providerModuleId, 'public_wrapper');
const publicTactic =
    coreLfQualifiedSymbol(providerModuleId, 'public_tactic');
const consumerUse =
    coreLfQualifiedSymbol(consumerModuleId, 'consumer_use');
const consumerTacticAlias =
    coreLfQualifiedSymbol(consumerModuleId, 'consumer_tactic_alias');
const ruleHead =
    coreLfQualifiedSymbol(consumerModuleId, 'rule_head');

const mode = binderMode('explicit', 'functorial');

const source = (
    authorityPath: string,
    sourceFragment: string
) => ({ authorityPath, sourceFragment });

const global = (symbol: typeof base) => ({
    tag: 'global' as const,
    symbol
});

const unaryType = () => ({
    tag: 'pi' as const,
    binder: {
        hint: 'value',
        mode,
        type: global(base)
    },
    body: global(base)
});

const identityBody = () => ({
    tag: 'lambda' as const,
    binder: {
        hint: 'value',
        mode,
        type: global(base)
    },
    body: {
        tag: 'bound' as const,
        index: 0
    }
});

const wrapperBody = () => ({
    tag: 'lambda' as const,
    binder: {
        hint: 'value',
        mode,
        type: global(base)
    },
    body: {
        tag: 'call' as const,
        callee: global(protectedHelper),
        arguments: [{
            plicity: 'explicit' as const,
            value: {
                tag: 'bound' as const,
                index: 0
            }
        }]
    }
});

interface ProviderFixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

const providerFixture = (): ProviderFixture => {
    const module = createCoreLfModuleSpec({
        revision: 'visibility-provider-1',
        moduleId: providerModuleId,
        fragmentId: 'protected-public-closure',
        authorityPath: providerPath,
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        canonicalExport: {
            exporterVersion: 'fixture-exporter-1',
            sha256:
                'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb'
        },
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: base,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: source(providerPath, 'symbol Base : TYPE;')
            },
            {
                order: 1,
                symbol: protectedHelper,
                type: unaryType(),
                body: coreLfTransferExplicitBody(identityBody()),
                modifiers: {
                    visibility: 'protected',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    providerPath,
                    'protected symbol protected_helper ' +
                        '(value : Base) : Base ≔ value;'
                )
            },
            {
                order: 2,
                symbol: privateHelper,
                type: unaryType(),
                body: coreLfTransferExplicitBody(identityBody()),
                modifiers: {
                    visibility: 'private',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    providerPath,
                    'private symbol private_helper ' +
                        '(value : Base) : Base ≔ value;'
                )
            },
            {
                order: 3,
                symbol: publicWrapper,
                type: unaryType(),
                body: coreLfTransferExplicitBody(wrapperBody()),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    providerPath,
                    'symbol public_wrapper (value : Base) : Base ' +
                        '≔ protected_helper value;'
                )
            },
            {
                order: 4,
                symbol: publicTactic,
                type: global(base),
                body: coreLfTransferTacticBody(
                    'begin\n  exact provider_witness;\nend'
                ),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    providerPath,
                    'symbol public_tactic : Base ≔ begin ... end;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policies = [
        'opaque-signature',
        'checked-transparent-definition',
        'checked-transparent-definition',
        'checked-transparent-definition',
        'theorem-body'
    ] as const;
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'visibility-provider-policy-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: policies[order],
            evidence: 'generic module visibility fixture'
        }))
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'visibility-provider-linkage-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            symbol: declaration.symbol,
            kind: 'free-declaration' as const,
            coreName: `visibility_${declaration.symbol.name}`,
            backendName: declaration.symbol.name
        }))
    });
    return { module, policy, linkage };
};

const consumerFixture = (
    providerLinkage: CoreLfTransferDeclarationLinkage
): ProviderFixture => {
    const module = createCoreLfModuleSpec({
        revision: 'visibility-consumer-1',
        moduleId: consumerModuleId,
        fragmentId: 'public-consumer',
        authorityPath: consumerPath,
        sourceSha256:
            'sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc',
        dependencies: [providerModuleId],
        externalSymbols: [
            base,
            publicWrapper,
            publicTactic
        ].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [
            {
                order: 0,
                symbol: consumerUse,
                type: unaryType(),
                body: coreLfTransferExplicitBody({
                    tag: 'lambda',
                    binder: {
                        hint: 'value',
                        mode,
                        type: global(base)
                    },
                    body: {
                        tag: 'call',
                        callee: global(publicWrapper),
                        arguments: [{
                            plicity: 'explicit',
                            value: {
                                tag: 'bound',
                                index: 0
                            }
                        }]
                    }
                }),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    consumerPath,
                    'symbol consumer_use (value : Base) : Base ' +
                        '≔ public_wrapper value;'
                )
            },
            {
                order: 1,
                symbol: consumerTacticAlias,
                type: global(base),
                body: coreLfTransferExplicitBody(global(publicTactic)),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    consumerPath,
                    'symbol consumer_tactic_alias : Base ≔ public_tactic;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'visibility-consumer-policy-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: order === 0
                ? 'checked-transparent-definition' as const
                : 'theorem-body' as const,
            evidence: 'public dependency consumer'
        }))
    });
    const providerLinks = new Map(
        providerLinkage.entries.map(link => [
            `${link.symbol.moduleId}\u0000${link.symbol.name}`,
            link
        ])
    );
    const externalLinks = module.externalSymbols.map(
        ({ symbol }, order) => {
            const link = providerLinks.get(
                `${symbol.moduleId}\u0000${symbol.name}`
            );
            assert.notEqual(link, undefined);
            if (link === undefined) {
                throw new Error('Missing provider fixture link');
            }
            return { ...link, order };
        }
    );
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'visibility-consumer-linkage-1',
        moduleRevision: module.revision,
        entries: [
            ...externalLinks,
            {
                order: externalLinks.length,
                symbol: consumerUse,
                kind: 'free-declaration',
                coreName: 'visibility_consumer_use',
                backendName: 'consumer_use'
            },
            {
                order: externalLinks.length + 1,
                symbol: consumerTacticAlias,
                kind: 'free-declaration',
                coreName: 'visibility_consumer_tactic_alias',
                backendName: 'consumer_tactic_alias'
            }
        ]
    });
    return { module, policy, linkage };
};

const expectVisibilityError = (
    action: () => unknown,
    code: CoreLfModuleVisibilityError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfModuleVisibilityError &&
            error.code === code
    );
};

describe('SCALE-MODULE-VISIBILITY-1 compiled module interface', () => {
    it('keeps protected computation internal and exposes public terms', () => {
        const providerSource = providerFixture();
        const provider = compileCoreLfDeclarations(
            providerSource.module,
            providerSource.policy,
            providerSource.linkage
        );
        const dependency =
            createCoreLfCompiledModuleInterface(provider);
        const consumerSource =
            consumerFixture(providerSource.linkage);
        const consumer = compileCoreLfDeclarations(
            consumerSource.module,
            consumerSource.policy,
            consumerSource.linkage,
            {
                initialEnvironment: provider.environment,
                dependencyInterfaces: [dependency]
            }
        );

        assert.deepEqual(
            dependency.entries.map(entry => [
                entry.symbol.name,
                entry.visibility
            ]),
            [
                ['Base', 'public'],
                ['protected_helper', 'protected'],
                ['private_helper', 'private'],
                ['public_wrapper', 'public'],
                ['public_tactic', 'public']
            ]
        );
        const tactic = provider.declaration(publicTactic);
        assert.equal(tactic?.status, 'installed-theorem');
        assert.equal(tactic?.body, undefined);
        assert.equal(
            provider.environment.lookup('visibility_public_tactic')
                ?.transparency,
            'opaque'
        );
        assert.equal(
            provider.environment.lookup('visibility_public_tactic')
                ?.body,
            undefined
        );
        assert.equal(
            provider.module.declarations[4].body.kind,
            'checked-tactic-source'
        );

        const nodeProvenance = provenance(
            'derived',
            'visibility public reduction'
        );
        const value = kernelFree('visibility_value', nodeProvenance);
        const result = coreLfDefinitionalCompare(
            consumer.environment,
            consumer.application(
                consumerUse,
                [value],
                nodeProvenance
            ),
            value,
            16
        );
        assert.equal(result.status, 'equal');
        assert.ok(
            result.trace.filter(step =>
                step.reduction.kind === 'delta'
            ).length >= 3
        );
        assert.equal(Object.isFrozen(dependency), true);
        assert.equal(Object.isFrozen(dependency.entries), true);
    });

    it('requires an exact compiled interface for free dependencies', () => {
        const providerSource = providerFixture();
        const provider = compileCoreLfDeclarations(
            providerSource.module,
            providerSource.policy,
            providerSource.linkage
        );
        const consumerSource =
            consumerFixture(providerSource.linkage);

        expectVisibilityError(
            () => compileCoreLfDeclarations(
                consumerSource.module,
                consumerSource.policy,
                consumerSource.linkage,
                { initialEnvironment: provider.environment }
            ),
            'MISSING_MODULE_INTERFACE'
        );

        const driftedEntries =
            consumerSource.linkage.entries.map((entry, index) =>
                index === 1 && entry.kind === 'free-declaration'
                    ? {
                        ...entry,
                        coreName: 'visibility_wrong_public_wrapper'
                    }
                    : entry
            );
        const drifted = createCoreLfTransferDeclarationLinkage(
            consumerSource.module,
            {
                revision: 'visibility-consumer-linkage-drift-1',
                moduleRevision: consumerSource.module.revision,
                entries: driftedEntries
            }
        );
        expectVisibilityError(
            () => compileCoreLfDeclarations(
                consumerSource.module,
                consumerSource.policy,
                drifted,
                {
                    initialEnvironment: provider.environment,
                    dependencyInterfaces: [
                        createCoreLfCompiledModuleInterface(provider)
                    ]
                }
            ),
            'DEPENDENCY_LINK_MISMATCH'
        );
    });

    it('rejects protected and private declarations in general terms', () => {
        const providerSource = providerFixture();
        const provider = compileCoreLfDeclarations(
            providerSource.module,
            providerSource.policy,
            providerSource.linkage
        );
        const dependency =
            createCoreLfCompiledModuleInterface(provider);

        for (const inaccessible of [protectedHelper, privateHelper]) {
            const local = coreLfQualifiedSymbol(
                consumerModuleId,
                `use_${inaccessible.name}`
            );
            const module = createCoreLfModuleSpec({
                revision: `visibility-${inaccessible.name}-consumer-1`,
                moduleId: consumerModuleId,
                fragmentId: `consume-${inaccessible.name}`,
                authorityPath: consumerPath,
                sourceSha256:
                    'sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd',
                dependencies: [providerModuleId],
                externalSymbols: [base, inaccessible].map(symbol => ({
                    symbol,
                    availability: 'dependency-module' as const
                })),
                declarations: [{
                    order: 0,
                    symbol: local,
                    type: unaryType(),
                    body: coreLfTransferExplicitBody({
                        tag: 'lambda',
                        binder: {
                            hint: 'value',
                            mode,
                            type: global(base)
                        },
                        body: {
                            tag: 'call',
                            callee: global(inaccessible),
                            arguments: [{
                                plicity: 'explicit',
                                value: {
                                    tag: 'bound',
                                    index: 0
                                }
                            }]
                        }
                    }),
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'transparent'
                    },
                    provenance: source(
                        consumerPath,
                        `symbol ${local.name} ...;`
                    )
                }],
                inductives: [],
                runtimeRules: [],
                proofRules: []
            });
            const policy = createCoreLfTransferPolicyOverlay(module, {
                revision: `${module.revision}-policy`,
                moduleRevision: module.revision,
                entries: [{
                    order: 0,
                    target: {
                        kind: 'declaration',
                        symbol: local
                    },
                    policy: 'checked-transparent-definition',
                    evidence: 'negative visibility fixture'
                }]
            });
            const providerLinks = new Map(
                providerSource.linkage.entries.map(link => [
                    link.symbol.name,
                    link
                ])
            );
            const links = [base, inaccessible].map((symbol, order) => {
                const link = providerLinks.get(symbol.name);
                assert.notEqual(link, undefined);
                if (link === undefined) {
                    throw new Error('Missing provider link');
                }
                return { ...link, order };
            });
            const linkage = createCoreLfTransferDeclarationLinkage(
                module,
                {
                    revision: `${module.revision}-linkage`,
                    moduleRevision: module.revision,
                    entries: [
                        ...links,
                        {
                            order: links.length,
                            symbol: local,
                            kind: 'free-declaration',
                            coreName: `visibility_${local.name}`,
                            backendName: local.name
                        }
                    ]
                }
            );

            expectVisibilityError(
                () => compileCoreLfDeclarations(
                    module,
                    policy,
                    linkage,
                    {
                        initialEnvironment: provider.environment,
                        dependencyInterfaces: [dependency]
                    }
                ),
                'INACCESSIBLE_EXTERNAL_SYMBOL'
            );
        }
    });

    it('permits protected dependencies only inside runtime patterns', () => {
        const providerSource = providerFixture();
        const provider = compileCoreLfDeclarations(
            providerSource.module,
            providerSource.policy,
            providerSource.linkage
        );
        const dependency =
            createCoreLfCompiledModuleInterface(provider);

        const headModule = createCoreLfModuleSpec({
            revision: 'visibility-runtime-head-1',
            moduleId: consumerModuleId,
            fragmentId: 'runtime-head',
            authorityPath: consumerPath,
            sourceSha256:
                'sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee',
            dependencies: [providerModuleId],
            externalSymbols: [{
                symbol: base,
                availability: 'dependency-module'
            }],
            declarations: [{
                order: 0,
                symbol: ruleHead,
                type: unaryType(),
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: source(
                    consumerPath,
                    'symbol rule_head (value : Base) : Base;'
                )
            }],
            inductives: [],
            runtimeRules: [],
            proofRules: []
        });
        const headPolicy = createCoreLfTransferPolicyOverlay(
            headModule,
            {
                revision: 'visibility-runtime-head-policy-1',
                moduleRevision: headModule.revision,
                entries: [{
                    order: 0,
                    target: {
                        kind: 'declaration',
                        symbol: ruleHead
                    },
                    policy: 'opaque-signature',
                    evidence: 'local runtime owner'
                }]
            }
        );
        const baseLink = providerSource.linkage.entries[0];
        const headLinkage = createCoreLfTransferDeclarationLinkage(
            headModule,
            {
                revision: 'visibility-runtime-head-linkage-1',
                moduleRevision: headModule.revision,
                entries: [
                    { ...baseLink, order: 0 },
                    {
                        order: 1,
                        symbol: ruleHead,
                        kind: 'free-declaration',
                        coreName: 'visibility_rule_head',
                        backendName: 'rule_head'
                    }
                ]
            }
        );
        const head = compileCoreLfDeclarations(
            headModule,
            headPolicy,
            headLinkage,
            {
                initialEnvironment: provider.environment,
                dependencyInterfaces: [dependency]
            }
        );
        const context = new CoreLfMixedDeclarationContext()
            .extend(provider)
            .extend(head);
        const pattern = new CoreLfTransferScopedBuilder();
        const value = pattern.capture('value');
        const protectedCall = pattern.call(
            pattern.global(protectedHelper),
            [{ plicity: 'explicit', value }]
        );
        const left = pattern.pattern(pattern.call(
            pattern.global(ruleHead),
            [{ plicity: 'explicit', value: protectedCall }]
        ));
        const template = new CoreLfTransferScopedBuilder();
        const right = template.template(template.capture('value'));

        const runtimeModule = (protectedOnRight: boolean) =>
            createCoreLfModuleSpec({
                revision: protectedOnRight
                    ? 'visibility-runtime-bad-1'
                    : 'visibility-runtime-good-1',
                moduleId: consumerModuleId,
                fragmentId: protectedOnRight
                    ? 'runtime-bad'
                    : 'runtime-good',
                authorityPath: consumerPath,
                sourceSha256:
                    'sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff',
                dependencies: [providerModuleId],
                externalSymbols: [
                    {
                        symbol: base,
                        availability: 'dependency-module' as const
                    },
                    {
                        symbol: protectedHelper,
                        availability: 'dependency-module' as const
                    },
                    {
                        symbol: ruleHead,
                        availability: 'earlier-fragment' as const
                    }
                ],
                declarations: [],
                inductives: [],
                runtimeRules: [{
                    order: 0,
                    id: protectedOnRight
                        ? 'visibility.protected.bad'
                        : 'visibility.protected.good',
                    groupId: protectedOnRight
                        ? 'visibility.protected.bad'
                        : 'visibility.protected.good',
                    clauseOrder: 0,
                    sourceOwner: ruleHead,
                    variables: [{
                        name: 'value',
                        type: global(base)
                    }],
                    left,
                    right: protectedOnRight
                        ? {
                            tag: 'call',
                            callee: global(protectedHelper),
                            arguments: [{
                                plicity: 'explicit',
                                value: {
                                    tag: 'capture',
                                    name: 'value'
                                }
                            }]
                        }
                        : right,
                    provenance: source(
                        consumerPath,
                        'rule rule_head (protected_helper $value) ↪ $value;'
                    )
                }],
                proofRules: []
            });

        const goodModule = runtimeModule(false);
        const goodPolicy = createCoreLfTransferPolicyOverlay(
            goodModule,
            {
                revision: 'visibility-runtime-good-policy-1',
                moduleRevision: goodModule.revision,
                entries: [{
                    order: 0,
                    target: {
                        kind: 'runtime-rule',
                        id: 'visibility.protected.good'
                    },
                    policy: 'runtime-rewrite',
                    evidence: 'protected nested runtime pattern'
                }]
            }
        );
        const good = compileCoreLfRuntimeProgram(
            goodModule,
            goodPolicy,
            context,
            { dependencyInterfaces: [dependency] }
        );
        assert.deepEqual(good.ruleIds, ['visibility.protected.good']);

        const badModule = runtimeModule(true);
        const badPolicy = createCoreLfTransferPolicyOverlay(
            badModule,
            {
                revision: 'visibility-runtime-bad-policy-1',
                moduleRevision: badModule.revision,
                entries: [{
                    order: 0,
                    target: {
                        kind: 'runtime-rule',
                        id: 'visibility.protected.bad'
                    },
                    policy: 'runtime-rewrite',
                    evidence: 'negative protected RHS fixture'
                }]
            }
        );
        expectVisibilityError(
            () => compileCoreLfRuntimeProgram(
                badModule,
                badPolicy,
                context,
                { dependencyInterfaces: [dependency] }
            ),
            'INACCESSIBLE_EXTERNAL_SYMBOL'
        );
    });

    it('leaves ordinary compiler failures distinct from visibility errors', () => {
        const providerSource = providerFixture();
        const provider = compileCoreLfDeclarations(
            providerSource.module,
            providerSource.policy,
            providerSource.linkage
        );
        const consumerSource =
            consumerFixture(providerSource.linkage);
        const badPolicy = createCoreLfTransferPolicyOverlay(
            consumerSource.module,
            {
                revision: 'visibility-bad-policy-1',
                moduleRevision: consumerSource.module.revision,
                entries: consumerSource.policy.entries.map(
                    (entry, order) => order === 0
                        ? { ...entry, policy: 'opaque-signature' }
                        : entry
                )
            }
        );
        assert.throws(
            () => compileCoreLfDeclarations(
                consumerSource.module,
                badPolicy,
                consumerSource.linkage,
                {
                    initialEnvironment: provider.environment,
                    dependencyInterfaces: [
                        createCoreLfCompiledModuleInterface(provider)
                    ]
                }
            ),
            error =>
                error instanceof CoreLfDeclarationCompilerError &&
                error.code === 'INCOMPATIBLE_POLICY'
        );
    });
});
