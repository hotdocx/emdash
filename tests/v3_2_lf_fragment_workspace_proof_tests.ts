/** Focused PRACTICAL-CLASS-PROOF-18 runtime-closure proof tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE,
    CoreCheckerError,
    CoreContextError,
    CoreLfCompiledFragmentModuleWorkspace,
    CoreLfFragmentWorkspaceProofError,
    CoreLfModuleSpec,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    binderMode,
    compileCoreLfFragmentModuleWorkspace,
    compileCoreLfFragmentWorkspaceProofDocument,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfFragmentModuleIdentity,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentWorkspaceProofFingerprint,
    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    createCoreProofChecker,
    defineCoreLfDependencyModuleDeclarationFragment,
    defineCoreLfDependencyModuleMixedFragment,
    kernelCall,
    kernelFree,
    planCoreLfMixedPhases,
    provenance,
    serializeCoreLfFragmentWorkspaceProofArtifact
} from '../src/v3_2';

type Symbol = ReturnType<typeof coreLfQualifiedSymbol>;

const unrelatedModuleId = 'fixture.a_runtime_proof_unrelated';
const providerModuleId = 'fixture.runtime_proof_provider';
const consumerModuleId = 'fixture.runtime_proof_consumer';
const providerPath = 'tests/fixtures/runtime_proof_provider.lp';
const consumerPath = 'tests/fixtures/runtime_proof_consumer.lp';
const unrelatedPath = 'tests/fixtures/runtime_proof_unrelated.lp';
const providerSha = `sha256:${'1'.repeat(64)}`;
const consumerSha = `sha256:${'2'.repeat(64)}`;
const unrelatedSha = `sha256:${'3'.repeat(64)}`;

const code = coreLfQualifiedSymbol(providerModuleId, 'Code');
const decode = coreLfQualifiedSymbol(providerModuleId, 'El');
const base = coreLfQualifiedSymbol(providerModuleId, 'base_code');
const normalize = coreLfQualifiedSymbol(providerModuleId, 'normalize');
const marker = coreLfQualifiedSymbol(providerModuleId, 'runtime_marker');
const value = coreLfQualifiedSymbol(consumerModuleId, 'value');
const secret = coreLfQualifiedSymbol(unrelatedModuleId, 'secret');
const mode = binderMode('explicit', 'functorial');

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

const coreName = (symbol: Symbol): string =>
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
    coreName: coreName(symbol),
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
        moduleId: providerModuleId,
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
        moduleId: providerModuleId,
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
        moduleId: consumerModuleId,
        fragmentId: 'consumer-base',
        authorityPath: consumerPath,
        sourceSha256: consumerSha,
        dependencies: [providerModuleId],
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
        moduleId: unrelatedModuleId,
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

const workspaceFixture = (
    options: { readonly runtime?: boolean; readonly reverse?: boolean } = {}
) => {
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
                moduleId: providerModuleId,
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

const proofInput = (
    workspace: CoreLfCompiledFragmentModuleWorkspace,
    open = false
) => {
    const nodeSource = provenance('surface', 'runtime-proof source');
    const target = kernelCall(
        kernelFree(coreName(decode), nodeSource),
        [{
            plicity: 'explicit',
            value: kernelFree(coreName(base), nodeSource)
        }],
        nodeSource
    );
    return {
        moduleId: consumerModuleId,
        declarationId: open ? 'open_runtime_proof' : 'complete_runtime_proof',
        type: target,
        plan: open
            ? coreProofPlanHole('runtime_body', { provenance: nodeSource })
            : coreProofPlanExact(kernelFree(coreName(value), nodeSource)),
        provenance: nodeSource,
        fingerprint: createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
            workspace,
            consumerModuleId,
            'tests/fixtures/runtime_proof.surface.ts',
            {
                sourceSha256: `sha256:${'4'.repeat(64)}`,
                profileSha256: `sha256:${'5'.repeat(64)}`,
                interfaceSha256ByModuleId: {
                    [providerModuleId]: `sha256:${'6'.repeat(64)}`,
                    [consumerModuleId]: `sha256:${'7'.repeat(64)}`
                }
            }
        )
    };
};

const expectProofError = (
    action: () => unknown,
    code: CoreLfFragmentWorkspaceProofError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfFragmentWorkspaceProofError &&
            error.code === code &&
            error.path.length > 0
    );
};

const assertDeepFrozen = (value_: unknown): void => {
    if (value_ === null || typeof value_ !== 'object') return;
    assert.equal(Object.isFrozen(value_), true);
    Object.values(value_ as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('PRACTICAL-CLASS-PROOF-18 exact runtime proof attachment', () => {
    it('rechecks complete and named-open plans with the derived runtime', () => {
        const workspace = workspaceFixture();
        assert.deepEqual(workspace.plan.order, [
            unrelatedModuleId,
            providerModuleId,
            consumerModuleId
        ]);
        const completeInput = proofInput(workspace);
        assert.equal(completeInput.plan.tag, 'exact');
        if (completeInput.plan.tag !== 'exact') return;
        const solution = completeInput.plan.solution;
        const root = workspace.module(consumerModuleId);
        assert.notEqual(root, undefined);
        if (root === undefined) return;
        const plain = createCoreProofChecker(
            root.compiled.declarations.environment
        );
        assert.throws(
            () => plain.check(
                plain.rootContext,
                solution,
                completeInput.type
            ),
            error => error instanceof CoreCheckerError &&
                error.code === 'TYPE_MISMATCH'
        );
        const complete = compileCoreLfFragmentWorkspaceProofDocument(
            workspace,
            completeInput
        );
        const open = compileCoreLfFragmentWorkspaceProofDocument(
            workspace,
            proofInput(workspace, true)
        );
        assert.equal(complete.artifact.state.status, 'complete');
        assert.notEqual(complete.checkedTerm, undefined);
        assert.equal(open.artifact.state.status, 'incomplete');
        assert.deepEqual(
            open.artifact.state.goals.map(goal => goal.id),
            ['runtime_body']
        );
        assert.deepEqual(complete.artifact.closure.order, [
            providerModuleId,
            consumerModuleId
        ]);
        assert.equal(
            complete.artifact.closure.order.includes(unrelatedModuleId),
            false
        );
        assert.deepEqual(complete.artifact.runtime.ruleIds, [
            'fixture.runtime_proof.normalize'
        ]);
        assert.equal(
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.acceptsRuntimeInput,
            false
        );
        assertDeepFrozen(complete.artifact);
    });

    it('is byte-stable across workspace input permutations', () => {
        const firstWorkspace = workspaceFixture();
        const secondWorkspace = workspaceFixture({ reverse: true });
        const first = compileCoreLfFragmentWorkspaceProofDocument(
            firstWorkspace,
            proofInput(firstWorkspace)
        ).artifact;
        const second = compileCoreLfFragmentWorkspaceProofDocument(
            secondWorkspace,
            proofInput(secondWorkspace)
        ).artifact;
        assert.equal(
            serializeCoreLfFragmentWorkspaceProofArtifact(first),
            serializeCoreLfFragmentWorkspaceProofArtifact(second)
        );
    });

    it('requires exactly the closure modules in the fingerprint', () => {
        const workspace = workspaceFixture();
        const input = proofInput(workspace);
        expectProofError(
            () => compileCoreLfFragmentWorkspaceProofDocument(workspace, {
                ...input,
                fingerprint: createCoreLfFragmentWorkspaceProofFingerprint({
                    source: input.fingerprint.source,
                    profileSha256: input.fingerprint.profile.sha256,
                    dependencies: input.fingerprint.dependencies.slice(1),
                    runtime: input.fingerprint.runtime
                })
            }),
            'FINGERPRINT_CLOSURE_MISMATCH'
        );
    });

    it('rejects runtime omission and runtime fingerprint drift', () => {
        const withoutRuntime = workspaceFixture({ runtime: false });
        const nodeSource = provenance('surface', 'missing runtime proof');
        expectProofError(
            () => compileCoreLfFragmentWorkspaceProofDocument(
                withoutRuntime,
                {
                    moduleId: consumerModuleId,
                    declarationId: 'missing_runtime',
                    type: kernelFree(coreName(base), nodeSource),
                    plan: coreProofPlanHole('body', {
                        provenance: nodeSource
                    }),
                    provenance: nodeSource,
                    fingerprint:
                        createCoreLfFragmentWorkspaceProofFingerprint({
                            source: {
                                id: 'missing-runtime.surface.ts',
                                sha256: `sha256:${'8'.repeat(64)}`
                            },
                            profileSha256: `sha256:${'9'.repeat(64)}`,
                            dependencies: [
                                providerModuleId,
                                consumerModuleId
                            ].map(moduleId => ({
                                moduleId,
                                interfaceSha256:
                                    `sha256:${'a'.repeat(64)}`
                            })),
                            runtime: {
                                revision: 'absent-runtime',
                                ruleIds: ['absent.rule']
                            }
                        })
                }
            ),
            'MISSING_RUNTIME'
        );

        const workspace = workspaceFixture();
        const input = proofInput(workspace);
        expectProofError(
            () => compileCoreLfFragmentWorkspaceProofDocument(workspace, {
                ...input,
                fingerprint: createCoreLfFragmentWorkspaceProofFingerprint({
                    source: input.fingerprint.source,
                    profileSha256: input.fingerprint.profile.sha256,
                    dependencies: input.fingerprint.dependencies,
                    runtime: {
                        revision: `${input.fingerprint.runtime.revision}+drift`,
                        ruleIds: input.fingerprint.runtime.ruleIds
                    }
                })
            }),
            'RUNTIME_FINGERPRINT_MISMATCH'
        );
    });

    it('excludes declarations from an unrelated earlier module', () => {
        const workspace = workspaceFixture();
        const input = proofInput(workspace, true);
        assert.throws(
            () => compileCoreLfFragmentWorkspaceProofDocument(workspace, {
                ...input,
                declarationId: 'unrelated_target',
                type: kernelFree(
                    coreName(secret),
                    provenance('surface', 'unrelated target')
                )
            }),
            error => error instanceof CoreContextError &&
                error.code === 'UNBOUND_FREE_REFERENCE'
        );
    });

    it('rejects compiled closure drift', () => {
        const workspace = workspaceFixture();
        const modules = workspace.modules.map(module =>
            module.source.identity.moduleId === consumerModuleId
                ? Object.freeze({
                    ...module,
                    dependencyInterfaces: []
                })
                : module
        );
        const drifted = new CoreLfCompiledFragmentModuleWorkspace(
            workspace.plan,
            modules,
            workspace.declarations
        );
        expectProofError(
            () => compileCoreLfFragmentWorkspaceProofDocument(
                drifted,
                proofInput(workspace)
            ),
            'CLOSURE_DRIFT'
        );
    });

    it('serializes no process-local proof or runtime authority', () => {
        const workspace = workspaceFixture();
        const text = serializeCoreLfFragmentWorkspaceProofArtifact(
            compileCoreLfFragmentWorkspaceProofDocument(
                workspace,
                proofInput(workspace)
            ).artifact
        );
        assert.doesNotMatch(
            text,
            /session|environment|callback|rewriteHead|objectIdentity|\?m\d/u
        );
        assert.equal(text.endsWith('\n'), true);
    });
});
