/** Focused MODULE-WORKSPACE-AUTHORING-25 source-expansion tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE,
    CoreLfFragmentModuleWorkspaceError,
    compileCoreLfAuthoredModuleTheoremDevelopment,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanExact,
    createCoreLfAuthoredDependencyModuleDeclarationFragment,
    createCoreLfAuthoredFragmentModuleWorkspace,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSourceSnapshot,
    kernelFree,
    provenance,
    serializeCoreLfFragmentModuleWorkspaceAuthoringProfile,
    serializeCoreLfFragmentModuleWorkspaceSourceSnapshot
} from '../src/v3_2';
import {
    createRuntimeProofWorkspaceFixture,
    runtimeProofConsumerModuleId,
    runtimeProofCoreName,
    runtimeProofProviderModuleId,
    runtimeProofSymbols,
    runtimeProofUnrelatedModuleId
} from './support/v3_2_runtime_proof_fixture';

const assertDeepFrozen = (value: unknown, path = 'value'): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true, `${path} is not frozen`);
    Object.entries(value as Record<string, unknown>).forEach(([key, entry]) =>
        assertDeepFrozen(entry, `${path}.${key}`)
    );
};

const expectWorkspaceError = (
    action: () => unknown,
    code: CoreLfFragmentModuleWorkspaceError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfFragmentModuleWorkspaceError &&
            error.code === code && error.path.length > 0
    );
};

const sourceSnapshotText = (
    plan: ReturnType<typeof createCoreLfAuthoredFragmentModuleWorkspace>
): string => serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
    createCoreLfFragmentModuleWorkspaceSourceSnapshot(plan)
);

const theoremSource = provenance(
    'surface',
    'authored fragment-module workspace theorem source'
);

const theoremEntries = () => [{
    proofId: 'z_prove_provider_public',
    theorem: runtimeProofSymbols.providerPublicTheorem,
    plan: coreProofPlanExact(kernelFree(
        runtimeProofCoreName(runtimeProofSymbols.providerValue),
        theoremSource
    )),
    provenance: theoremSource,
    sourceId: 'tests/fixtures/workspace-authoring-provider.surface.ts',
    fingerprintHashes: {
        sourceSha256: `sha256:${'8'.repeat(64)}`,
        profileSha256: `sha256:${'9'.repeat(64)}`,
        interfaceSha256ByModuleId: {
            [runtimeProofProviderModuleId]: `sha256:${'a'.repeat(64)}`
        }
    }
}, {
    proofId: 'a_prove_consumer_second',
    theorem: runtimeProofSymbols.second,
    plan: coreProofPlanExact(kernelFree(
        runtimeProofCoreName(runtimeProofSymbols.providerPublicTheorem),
        theoremSource
    )),
    provenance: theoremSource,
    sourceId: 'tests/fixtures/workspace-authoring-consumer.surface.ts',
    fingerprintHashes: {
        sourceSha256: `sha256:${'4'.repeat(64)}`,
        profileSha256: `sha256:${'5'.repeat(64)}`,
        interfaceSha256ByModuleId: {
            [runtimeProofProviderModuleId]: `sha256:${'6'.repeat(64)}`,
            [runtimeProofConsumerModuleId]: `sha256:${'7'.repeat(64)}`
        }
    }
}];

const cyclicChain = (moduleId: string, dependency: string) => {
    const symbol = coreLfQualifiedSymbol(moduleId, 'Carrier');
    const authorityPath = `tests/fixtures/${moduleId}.surface.ts`;
    const fragment =
        createCoreLfAuthoredDependencyModuleDeclarationFragment({
            moduleRevision: `${moduleId}.module.1`,
            moduleId,
            fragmentId: 'declarations',
            authorityPath,
            sourceSha256: `sha256:${moduleId.endsWith('a')
                ? 'b'.repeat(64)
                : 'c'.repeat(64)}`,
            dependencies: [dependency],
            firstSourceOrder: 0,
            externals: [],
            declarations: [{
                symbol,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: {
                    authorityPath,
                    sourceFragment: 'symbol Carrier : TYPE;'
                },
                trust: {
                    policy: 'opaque-signature',
                    evidence: 'standalone cyclic workspace fixture'
                },
                linkage: {
                    kind: 'free-declaration',
                    coreName: `${moduleId.replace(/\./gu, '_')}_Carrier`,
                    backendName: 'Carrier'
                }
            }]
        });
    return createCoreLfDependencyModuleFragmentChain({
        revision: `${moduleId}.chain.1`,
        fragments: [fragment]
    });
};

describe('MODULE-WORKSPACE-AUTHORING-25 direct TypeScript lowering', () => {
    it('erases chain-only input to the exact explicit canonical workspace',
        () => {
            const reference = createRuntimeProofWorkspaceFixture();
            const chains = reference.plan.modules.map(source => source.chain);
            const authored = createCoreLfAuthoredFragmentModuleWorkspace({
                revision: reference.plan.revision,
                modules: chains
            });
            const reversed = createCoreLfAuthoredFragmentModuleWorkspace({
                revision: reference.plan.revision,
                modules: [...chains].reverse()
            });

            assert.deepEqual(authored, reference.plan);
            assert.deepEqual(reversed, reference.plan);
            assert.equal(
                sourceSnapshotText(authored),
                sourceSnapshotText(reference.plan)
            );
            assert.equal(
                sourceSnapshotText(reversed),
                sourceSnapshotText(reference.plan)
            );
            chains.reverse();
            assert.deepEqual(authored, reference.plan);
            assertDeepFrozen(authored);
        }
    );

    it('powers a runtime-backed cross-module theorem development', () => {
        const reference = createRuntimeProofWorkspaceFixture();
        const workspace = createCoreLfAuthoredFragmentModuleWorkspace({
            revision: reference.plan.revision,
            modules: reference.plan.modules.map(source => source.chain)
        });
        const compiled = compileCoreLfAuthoredModuleTheoremDevelopment({
            revision: 'module-workspace-authoring-theorems-1',
            workspace,
            theorems: theoremEntries()
        });

        assert.equal(compiled.artifact.status, 'complete');
        assert.equal(compiled.artifact.openGoalCount, 0);
        assert.deepEqual(
            compiled.artifact.bindings.map(binding => binding.theorem),
            [
                runtimeProofSymbols.second,
                runtimeProofSymbols.providerPublicTheorem
            ]
        );
    });

    it('derives only direct providers and their latest local runtime', () => {
        const reference = createRuntimeProofWorkspaceFixture({
            providerDependsOnUnrelated: true
        });
        const authored = createCoreLfAuthoredFragmentModuleWorkspace({
            revision: reference.plan.revision,
            modules: reference.plan.modules.map(source => source.chain)
        });
        const provider = authored.modules.find(source =>
            source.identity.moduleId === runtimeProofProviderModuleId
        );
        const consumer = authored.modules.find(source =>
            source.identity.moduleId === runtimeProofConsumerModuleId
        );
        assert.ok(provider);
        assert.ok(consumer);

        assert.deepEqual(
            provider.dependencyProviders.map(source => source.moduleId),
            [runtimeProofUnrelatedModuleId]
        );
        assert.deepEqual(provider.runtimeProviders, []);
        assert.deepEqual(
            consumer.dependencyProviders.map(source => source.moduleId),
            [runtimeProofProviderModuleId]
        );
        assert.deepEqual(
            consumer.runtimeProviders,
            reference.plan.modules.find(source =>
                source.identity.moduleId === runtimeProofConsumerModuleId
            )?.runtimeProviders
        );
        assert.equal(
            consumer.dependencyProviders.some(source =>
                source.moduleId === runtimeProofUnrelatedModuleId
            ),
            false
        );
    });

    it('delegates missing, duplicate, and cyclic graphs to existing errors',
        () => {
            const reference = createRuntimeProofWorkspaceFixture();
            const chains = reference.plan.modules.map(source => source.chain);
            const provider = chains.find(chain =>
                chain.moduleId === runtimeProofProviderModuleId
            );
            assert.ok(provider);

            expectWorkspaceError(
                () => createCoreLfAuthoredFragmentModuleWorkspace({
                    revision: reference.plan.revision,
                    modules: chains.filter(chain =>
                        chain.moduleId !== runtimeProofProviderModuleId
                    )
                }),
                'MISSING_DEPENDENCY'
            );
            expectWorkspaceError(
                () => createCoreLfAuthoredFragmentModuleWorkspace({
                    revision: reference.plan.revision,
                    modules: [...chains, provider]
                }),
                'DUPLICATE_MODULE'
            );
            const left = cyclicChain(
                'fixture.workspace_cycle_a',
                'fixture.workspace_cycle_b'
            );
            const right = cyclicChain(
                'fixture.workspace_cycle_b',
                'fixture.workspace_cycle_a'
            );
            expectWorkspaceError(
                () => createCoreLfAuthoredFragmentModuleWorkspace({
                    revision: 'module-workspace-authoring-cycle-1',
                    modules: [left, right]
                }),
                'CYCLIC_DEPENDENCY'
            );
        }
    );

    it('leaves explicit provider drift validation on the low-level API', () => {
        const reference = createRuntimeProofWorkspaceFixture();
        const inputs = reference.plan.modules.map(source => ({
            chain: source.chain,
            dependencyProviders: source.dependencyProviders,
            runtimeProviders: source.runtimeProviders
        }));
        const consumer = inputs.find(source =>
            source.chain.moduleId === runtimeProofConsumerModuleId
        );
        assert.ok(consumer);
        const provider = consumer.dependencyProviders[0];
        assert.ok(provider);
        consumer.dependencyProviders = [{
            ...provider,
            sourceSha256: `sha256:${'f'.repeat(64)}`
        }];

        expectWorkspaceError(
            () => createCoreLfFragmentModuleWorkspace({
                revision: reference.plan.revision,
                modules: inputs
            }),
            'INVALID_DEPENDENCY_PROVIDER'
        );
    });

    it('publishes an inert browser-safe source-expansion profile', () => {
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE.revision,
            'emdash-lf-fragment-module-workspace-authoring-v1'
        );
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE
                .explicitRemoteProviderClaimsPreserved,
            true
        );
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE
                .promotesTransitiveDependencies,
            false
        );
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE
                .acceptsRuntimeInput,
            false
        );
        assert.equal(
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE.performsIo,
            false
        );
        assert.equal(
            serializeCoreLfFragmentModuleWorkspaceAuthoringProfile(),
            serializeCoreLfFragmentModuleWorkspaceAuthoringProfile()
        );
        assertDeepFrozen(CORE_LF_FRAGMENT_MODULE_WORKSPACE_AUTHORING_PROFILE);
    });
});
