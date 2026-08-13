/** Focused DECLARATION-AUTHORING-24 erasing-facade tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE,
    CoreLfDeclarationCompilerError,
    CoreLfDeclarationFragmentAuthoringDeclaration,
    CoreLfDeclarationFragmentAuthoringInput,
    CoreLfSameModuleFragmentWorkspaceError,
    CoreLfTransferError,
    CoreLfTransferExpression,
    CoreLfTransferScopedBuilder,
    binderMode,
    compileCoreLfAuthoredModuleTheoremDevelopment,
    compileCoreLfDependencyModuleFragmentChain,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    coreProofPlanExact,
    createCoreLfAuthoredDependencyModuleDeclarationFragment,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfFragmentModuleIdentity,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    defineCoreLfDependencyModuleDeclarationFragment,
    defineCoreLfDependencyModuleMixedFragment,
    kernelFree,
    planCoreLfMixedPhases,
    provenance,
    serializeCoreLfDeclarationFragmentAuthoringProfile
} from '../src/v3_2';

type Symbol = ReturnType<typeof coreLfQualifiedSymbol>;

const providerModuleId = 'fixture.declaration_authoring_provider';
const consumerModuleId = 'fixture.declaration_authoring_consumer';
const providerPath = 'tests/fixtures/declaration_authoring_provider.lp';
const consumerPath = 'tests/fixtures/declaration_authoring_consumer.lp';
const providerSha = `sha256:${'1'.repeat(64)}`;
const consumerSha = `sha256:${'2'.repeat(64)}`;
const mode = binderMode('explicit', 'functorial');

const code = coreLfQualifiedSymbol(providerModuleId, 'Code');
const decode = coreLfQualifiedSymbol(providerModuleId, 'El');
const normalize = coreLfQualifiedSymbol(providerModuleId, 'normalize');
const base = coreLfQualifiedSymbol(providerModuleId, 'base');
const baseAlias = coreLfQualifiedSymbol(providerModuleId, 'base_alias');
const witness = coreLfQualifiedSymbol(providerModuleId, 'witness');
const providerTheorem = coreLfQualifiedSymbol(
    providerModuleId,
    'provider_theorem'
);
const marker = coreLfQualifiedSymbol(providerModuleId, 'runtime_marker');
const later = coreLfQualifiedSymbol(providerModuleId, 'later');
const consumerTheorem = coreLfQualifiedSymbol(
    consumerModuleId,
    'consumer_theorem'
);

const global = (symbol: Symbol): CoreLfTransferExpression => ({
    tag: 'global',
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

const unaryType = (
    domain: Symbol,
    body: CoreLfTransferExpression
): CoreLfTransferExpression => ({
    tag: 'pi',
    binder: {
        hint: 'value',
        mode,
        type: global(domain)
    },
    body
});

const theoremType = (): CoreLfTransferExpression =>
    call(decode, call(normalize, global(base)));

const source = (authorityPath: string, sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const coreName = (symbol: Symbol): string =>
    `${symbol.moduleId.replace(/\./gu, '_')}_${symbol.name}`;

const absentDeclaration = (
    symbol: Symbol,
    type: CoreLfTransferExpression,
    authorityPath: string,
    visibility: 'public' | 'protected' | 'private' = 'public'
): CoreLfDeclarationFragmentAuthoringDeclaration => ({
    symbol,
    type,
    body: coreLfTransferAbsentBody(),
    modifiers: {
        visibility,
        rigidity: 'ordinary',
        sourceOpacity: 'opaque'
    },
    provenance: source(authorityPath, `symbol ${symbol.name};`),
    trust: {
        policy: 'opaque-signature',
        evidence: 'focused direct-TypeScript declaration authoring fixture'
    },
    linkage: {
        kind: 'free-declaration',
        coreName: coreName(symbol),
        backendName: symbol.name
    }
});

const transparentDeclaration = (
    symbol: Symbol,
    type: CoreLfTransferExpression,
    body: CoreLfTransferExpression,
    authorityPath: string
): CoreLfDeclarationFragmentAuthoringDeclaration => ({
    symbol,
    type,
    body: coreLfTransferExplicitBody(body),
    modifiers: {
        visibility: 'public',
        rigidity: 'ordinary',
        sourceOpacity: 'transparent'
    },
    provenance: source(authorityPath, `definition ${symbol.name};`),
    trust: {
        policy: 'checked-transparent-definition',
        evidence: 'focused direct-TypeScript declaration authoring fixture'
    },
    linkage: {
        kind: 'free-declaration',
        coreName: coreName(symbol),
        backendName: symbol.name
    }
});

const providerDeclarations = (
): readonly CoreLfDeclarationFragmentAuthoringDeclaration[] => [
    absentDeclaration(code, { tag: 'type' }, providerPath),
    absentDeclaration(
        decode,
        unaryType(code, { tag: 'type' }),
        providerPath
    ),
    absentDeclaration(normalize, unaryType(code, global(code)), providerPath),
    absentDeclaration(base, global(code), providerPath),
    transparentDeclaration(baseAlias, global(code), global(base), providerPath),
    absentDeclaration(witness, call(decode, global(base)), providerPath),
    absentDeclaration(providerTheorem, theoremType(), providerPath)
];

const providerInput = (): CoreLfDeclarationFragmentAuthoringInput => ({
    moduleRevision: 'declaration-authoring-provider-base-1',
    moduleId: providerModuleId,
    fragmentId: 'provider-base',
    authorityPath: providerPath,
    sourceSha256: providerSha,
    dependencies: [],
    firstSourceOrder: 0,
    externals: [],
    declarations: providerDeclarations()
});

const explicitFragment = (
    input: CoreLfDeclarationFragmentAuthoringInput
) => {
    const module = createCoreLfModuleSpec({
        revision: input.moduleRevision,
        moduleId: input.moduleId,
        fragmentId: input.fragmentId,
        authorityPath: input.authorityPath,
        sourceSha256: input.sourceSha256,
        dependencies: input.dependencies,
        externalSymbols: input.externals.map(external => ({
            symbol: external.symbol,
            availability: external.availability
        })),
        declarations: input.declarations.map((declaration, index) => ({
            order: input.firstSourceOrder + index,
            symbol: declaration.symbol,
            type: declaration.type,
            body: declaration.body,
            modifiers: declaration.modifiers,
            provenance: declaration.provenance
        })),
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: `${input.moduleRevision}.policy`,
        moduleRevision: input.moduleRevision,
        entries: input.declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: declaration.trust.policy,
            evidence: declaration.trust.evidence
        }))
    });
    const linked = [
        ...input.externals.map(external => ({
            symbol: external.symbol,
            linkage: external.linkage
        })),
        ...input.declarations.map(declaration => ({
            symbol: declaration.symbol,
            linkage: declaration.linkage
        }))
    ];
    return defineCoreLfDependencyModuleDeclarationFragment({
        module,
        policy,
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: `${input.moduleRevision}.linkage`,
            moduleRevision: input.moduleRevision,
            entries: linked.map((entry, order) => ({
                order,
                symbol: entry.symbol,
                ...entry.linkage
            }))
        }),
        externalProviders: input.externals.flatMap(external =>
            external.availability === 'earlier-fragment'
                ? [{
                    symbol: external.symbol,
                    provider: external.provider
                }]
                : []
        )
    });
};

const assertDeepFrozen = (value: unknown, path = 'value'): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true, `${path} is not frozen`);
    Object.entries(value as Record<string, unknown>).forEach(([key, entry]) =>
        assertDeepFrozen(entry, `${path}.${key}`)
    );
};

const providerRuntimeFragment = (
    providerBase: ReturnType<
        typeof createCoreLfAuthoredDependencyModuleDeclarationFragment
    >
) => {
    const builder = new CoreLfTransferScopedBuilder();
    const captured = builder.capture('code');
    const module = createCoreLfModuleSpec({
        revision: 'declaration-authoring-provider-runtime-1',
        moduleId: providerModuleId,
        fragmentId: 'provider-runtime',
        authorityPath: providerPath,
        sourceSha256: providerSha,
        dependencies: [],
        externalSymbols: [code, normalize].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [{
            order: 7,
            symbol: marker,
            type: { tag: 'type' },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'private',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque'
            },
            provenance: source(providerPath, 'symbol runtime_marker;')
        }],
        inductives: [],
        runtimeRules: [{
            order: 8,
            id: 'fixture.declaration_authoring.normalize',
            groupId: 'fixture.declaration_authoring.normalize',
            clauseOrder: 0,
            sourceOwner: normalize,
            variables: [{ name: 'code', type: global(code) }],
            left: builder.pattern(builder.call(
                builder.global(normalize),
                [{ plicity: 'explicit', value: captured }]
            )),
            right: builder.template(captured),
            provenance: source(providerPath, 'rule normalize $code ↪ $code;')
        }],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'declaration-authoring-provider-runtime-policy-1',
        moduleRevision: module.revision,
        entries: [{
            order: 0,
            target: { kind: 'declaration', symbol: marker },
            policy: 'opaque-signature',
            evidence: 'explicit runtime fixture marker'
        }, {
            order: 1,
            target: {
                kind: 'runtime-rule',
                id: 'fixture.declaration_authoring.normalize'
            },
            policy: 'runtime-rewrite',
            evidence: 'explicit checked runtime fixture'
        }]
    });
    const plan = planCoreLfMixedPhases(module, policy);
    return defineCoreLfDependencyModuleMixedFragment({
        module,
        policy,
        linkage: createCoreLfMixedDeclarationLinkage(plan, {
            revision: 'declaration-authoring-provider-runtime-linkage-1',
            moduleRevision: module.revision,
            entries: [code, normalize, marker].map((symbol, order) => ({
                order,
                symbol,
                kind: 'free-declaration' as const,
                coreName: coreName(symbol),
                backendName: symbol.name
            }))
        }),
        externalProviders: [code, normalize].map(symbol => ({
            symbol,
            provider: providerBase.identity
        }))
    });
};

const theoremWorkspace = () => {
    const providerBase =
        createCoreLfAuthoredDependencyModuleDeclarationFragment(
            providerInput()
        );
    const runtime = providerRuntimeFragment(providerBase);
    const provider = createCoreLfDependencyModuleFragmentChain({
        revision: 'declaration-authoring-provider-chain-1',
        fragments: [providerBase, runtime]
    });
    const consumer = createCoreLfAuthoredDependencyModuleDeclarationFragment({
        moduleRevision: 'declaration-authoring-consumer-base-1',
        moduleId: consumerModuleId,
        fragmentId: 'consumer-base',
        authorityPath: consumerPath,
        sourceSha256: consumerSha,
        dependencies: [providerModuleId],
        firstSourceOrder: 0,
        externals: [decode, normalize, base, providerTheorem].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const,
            linkage: {
                kind: 'free-declaration' as const,
                coreName: coreName(symbol),
                backendName: symbol.name
            }
        })),
        declarations: [absentDeclaration(
            consumerTheorem,
            theoremType(),
            consumerPath
        )]
    });
    const consumerChain = createCoreLfDependencyModuleFragmentChain({
        revision: 'declaration-authoring-consumer-chain-1',
        fragments: [consumer]
    });
    const providerIdentity = createCoreLfFragmentModuleIdentity(provider);
    return createCoreLfFragmentModuleWorkspace({
        revision: 'declaration-authoring-workspace-1',
        modules: [{
            chain: consumerChain,
            dependencyProviders: [providerIdentity],
            runtimeProviders: [{
                moduleId: providerModuleId,
                fragment: runtime.identity
            }]
        }, { chain: provider }]
    });
};

describe('DECLARATION-AUTHORING-24 direct TypeScript lowering', () => {
    it('erases to the exact explicit fragment and freezes caller data', () => {
        const input = providerInput();
        const authored =
            createCoreLfAuthoredDependencyModuleDeclarationFragment(input);

        assert.deepEqual(authored, explicitFragment(input));
        assert.deepEqual(
            authored.module.declarations.map(entry => entry.order),
            [0, 1, 2, 3, 4, 5, 6]
        );
        assert.equal(authored.policy.revision, `${input.moduleRevision}.policy`);
        assert.equal(
            authored.linkage.revision,
            `${input.moduleRevision}.linkage`
        );
        assert.equal(
            authored.module.declarations[4].body.kind,
            'explicit-term'
        );
        assertDeepFrozen(authored);

        const mutable = input.declarations[0].provenance as {
            sourceFragment: string;
        };
        mutable.sourceFragment = 'mutated after lowering';
        assert.equal(
            authored.module.declarations[0].provenance.sourceFragment,
            'symbol Code;'
        );
        assert.deepEqual(
            authored,
            createCoreLfAuthoredDependencyModuleDeclarationFragment(
                providerInput()
            )
        );
    });

    it('leaves explicit trust/body compatibility to the existing compiler',
        () => {
            const input = providerInput();
            const declarations = [...input.declarations];
            declarations[0] = {
                ...declarations[0],
                trust: {
                    policy: 'checked-transparent-definition',
                    evidence: 'deliberately incompatible focused negative'
                }
            };
            const fragment =
                createCoreLfAuthoredDependencyModuleDeclarationFragment({
                    ...input,
                    moduleRevision: 'declaration-authoring-bad-trust-1',
                    declarations
                });
            const chain = createCoreLfDependencyModuleFragmentChain({
                revision: 'declaration-authoring-bad-trust-chain-1',
                fragments: [fragment]
            });

            assert.throws(
                () => compileCoreLfDependencyModuleFragmentChain(chain, {}),
                error => error instanceof CoreLfDeclarationCompilerError &&
                    error.code === 'INCOMPATIBLE_POLICY'
            );
        }
    );

    it('delegates malformed metadata, evidence, order, symbol, and linkage',
        () => {
            const input = providerInput();
            const expectTransferError = (
                changed: CoreLfDeclarationFragmentAuthoringInput,
                code: CoreLfTransferError['code']
            ): void => {
                assert.throws(
                    () =>
                        createCoreLfAuthoredDependencyModuleDeclarationFragment(
                            changed
                        ),
                    error => error instanceof CoreLfTransferError &&
                        error.code === code && error.path.length > 0
                );
            };

            expectTransferError(
                { ...input, moduleId: 'not a module id' },
                'INVALID_IDENTIFIER'
            );
            expectTransferError(
                { ...input, firstSourceOrder: -1 },
                'INVALID_ORDER'
            );
            expectTransferError(
                {
                    ...input,
                    declarations: [
                        input.declarations[0],
                        input.declarations[0]
                    ]
                },
                'DUPLICATE_IDENTITY'
            );
            expectTransferError(
                {
                    ...input,
                    declarations: [{
                        ...input.declarations[0],
                        trust: {
                            ...input.declarations[0].trust,
                            evidence: '   '
                        }
                    }]
                },
                'INVALID_POLICY'
            );
            assert.throws(
                () =>
                    createCoreLfAuthoredDependencyModuleDeclarationFragment({
                        ...input,
                        declarations: [{
                            ...input.declarations[0],
                            linkage: {
                                kind: 'free-declaration',
                                coreName: 'not a Core name',
                                backendName: 'Code'
                            }
                        }]
                    }),
                error => error instanceof CoreLfDeclarationCompilerError &&
                    error.code === 'INVALID_LINKAGE'
            );
        }
    );

    it('retains exact earlier-fragment provider ownership', () => {
        const baseFragment =
            createCoreLfAuthoredDependencyModuleDeclarationFragment(
                providerInput()
            );
        const laterInput: CoreLfDeclarationFragmentAuthoringInput = {
            moduleRevision: 'declaration-authoring-provider-later-1',
            moduleId: providerModuleId,
            fragmentId: 'provider-later',
            authorityPath: providerPath,
            sourceSha256: providerSha,
            dependencies: [],
            firstSourceOrder: 7,
            externals: [{
                symbol: code,
                availability: 'earlier-fragment',
                provider: baseFragment.identity,
                linkage: {
                    kind: 'free-declaration',
                    coreName: coreName(code),
                    backendName: code.name
                }
            }],
            declarations: [absentDeclaration(
                later,
                global(code),
                providerPath
            )]
        };
        const laterFragment =
            createCoreLfAuthoredDependencyModuleDeclarationFragment(laterInput);
        const chain = createCoreLfDependencyModuleFragmentChain({
            revision: 'declaration-authoring-provider-later-chain-1',
            fragments: [baseFragment, laterFragment]
        });

        assert.equal(
            compileCoreLfDependencyModuleFragmentChain(chain, {})
                .moduleInterface?.declaration(later)?.symbol.name,
            later.name
        );
        const wrongProvider = {
            ...baseFragment.identity,
            fragmentId: 'not-the-base-fragment'
        };
        const invalid =
            createCoreLfAuthoredDependencyModuleDeclarationFragment({
                ...laterInput,
                moduleRevision: 'declaration-authoring-bad-provider-1',
                externals: [{
                    ...laterInput.externals[0],
                    availability: 'earlier-fragment',
                    provider: wrongProvider
                }]
            });
        assert.throws(
            () => createCoreLfDependencyModuleFragmentChain({
                revision: 'declaration-authoring-bad-provider-chain-1',
                fragments: [baseFragment, invalid]
            }),
            error => error instanceof CoreLfSameModuleFragmentWorkspaceError &&
                error.code === 'INVALID_PROVIDER'
        );
    });

    it('composes with runtime-backed cross-module theorem authoring', () => {
        const workspace = theoremWorkspace();
        const nodeSource = provenance(
            'surface',
            'declaration-authoring theorem proof'
        );
        const compiled = compileCoreLfAuthoredModuleTheoremDevelopment({
            revision: 'declaration-authoring-theorems-1',
            workspace,
            theorems: [{
                proofId: 'prove_provider_theorem',
                theorem: providerTheorem,
                plan: coreProofPlanExact(kernelFree(
                    coreName(witness),
                    nodeSource
                )),
                provenance: nodeSource,
                sourceId: `${providerPath}#provider_theorem`,
                fingerprintHashes: {
                    sourceSha256: `sha256:${'3'.repeat(64)}`,
                    profileSha256: `sha256:${'4'.repeat(64)}`,
                    interfaceSha256ByModuleId: {
                        [providerModuleId]: `sha256:${'5'.repeat(64)}`
                    }
                }
            }, {
                proofId: 'prove_consumer_theorem',
                theorem: consumerTheorem,
                plan: coreProofPlanExact(kernelFree(
                    coreName(providerTheorem),
                    nodeSource
                )),
                provenance: nodeSource,
                sourceId: `${consumerPath}#consumer_theorem`,
                fingerprintHashes: {
                    sourceSha256: `sha256:${'6'.repeat(64)}`,
                    profileSha256: `sha256:${'7'.repeat(64)}`,
                    interfaceSha256ByModuleId: {
                        [providerModuleId]: `sha256:${'8'.repeat(64)}`,
                        [consumerModuleId]: `sha256:${'9'.repeat(64)}`
                    }
                }
            }]
        });

        assert.equal(compiled.artifact.status, 'complete');
        assert.deepEqual(
            compiled.artifact.theoremOrder.map(entry => entry.declarationId),
            ['prove_provider_theorem', 'prove_consumer_theorem']
        );
        assert.equal(compiled.artifact.openGoalCount, 0);
        assertDeepFrozen(compiled.artifact);
    });

    it('publishes an honest browser-safe non-semantic profile', () => {
        assert.equal(
            CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE.revision,
            'emdash-lf-declaration-fragment-authoring-v1'
        );
        assert.equal(
            CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE.infersTrust,
            false
        );
        assert.equal(
            CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE
                .generatesRuntimeRules,
            false
        );
        assert.equal(
            CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE.performsIo,
            false
        );
        assert.equal(
            JSON.parse(serializeCoreLfDeclarationFragmentAuthoringProfile())
                .revision,
            CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE.revision
        );
        assertDeepFrozen(CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE);
    });
});
