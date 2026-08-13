/** Focused THEOREM-AUTHORING-22 source-expansion tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE,
    CoreLfDeclaredTheoremDevelopmentError,
    CoreLfFragmentProofDevelopmentError,
    CoreLfFragmentWorkspaceProofError,
    CoreLfModuleTheoremAuthoringEntry,
    CoreLfModuleTheoremAuthoringError,
    CoreLfQualifiedSymbol,
    CoreProofPlan,
    compileCoreLfAuthoredModuleTheoremDevelopment,
    compileCoreLfModuleTheoremDevelopment,
    coreLfQualifiedSymbol,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreLfAuthoredModuleTheoremDevelopment,
    createCoreLfFragmentProofDevelopment,
    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace,
    createCoreLfModuleTheoremDevelopment,
    kernelFree,
    provenance,
    serializeCoreLfModuleTheoremAuthoringProfile,
    serializeCoreLfModuleTheoremDevelopmentArtifact
} from '../src/v3_2';
import {
    createRuntimeProofWorkspaceFixture,
    runtimeProofConsumerModuleId,
    runtimeProofCoreName,
    runtimeProofProviderModuleId,
    runtimeProofSymbols
} from './support/v3_2_runtime_proof_fixture';

type Workspace = ReturnType<typeof createRuntimeProofWorkspaceFixture>;

const nodeSource = provenance('surface', 'module theorem authoring source');
const revision = 'module-theorem-authoring-development-1';

const assertDeepFrozen = (value: unknown, path = 'value'): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true, `${path} is not frozen`);
    Object.entries(value as Record<string, unknown>).forEach(([key, entry]) =>
        assertDeepFrozen(entry, `${path}.${key}`)
    );
};

const providerEntry = (
    plan: CoreProofPlan = coreProofPlanExact(kernelFree(
        runtimeProofCoreName(runtimeProofSymbols.providerValue),
        nodeSource
    ))
): CoreLfModuleTheoremAuthoringEntry => ({
    proofId: 'z_prove_provider_public',
    theorem: runtimeProofSymbols.providerPublicTheorem,
    plan,
    provenance: nodeSource,
    sourceId: 'tests/fixtures/authored-module-theorem-provider.surface.ts',
    fingerprintHashes: {
        sourceSha256: `sha256:${'8'.repeat(64)}`,
        profileSha256: `sha256:${'9'.repeat(64)}`,
        interfaceSha256ByModuleId: {
            [runtimeProofProviderModuleId]: `sha256:${'a'.repeat(64)}`
        }
    }
});

const consumerEntry = (
    solution: CoreLfQualifiedSymbol =
        runtimeProofSymbols.providerPublicTheorem
): CoreLfModuleTheoremAuthoringEntry => ({
    proofId: 'a_prove_consumer_second',
    theorem: runtimeProofSymbols.second,
    plan: coreProofPlanExact(kernelFree(
        runtimeProofCoreName(solution),
        nodeSource
    )),
    provenance: nodeSource,
    sourceId: 'tests/fixtures/authored-module-theorem-consumer.surface.ts',
    fingerprintHashes: {
        sourceSha256: `sha256:${'4'.repeat(64)}`,
        profileSha256: `sha256:${'5'.repeat(64)}`,
        interfaceSha256ByModuleId: {
            [runtimeProofProviderModuleId]: `sha256:${'6'.repeat(64)}`,
            [runtimeProofConsumerModuleId]: `sha256:${'7'.repeat(64)}`
        }
    }
});

const entries = (reverse = false) => {
    const result = [providerEntry(), consumerEntry()];
    return reverse ? result.reverse() : result;
};

const authoredInput = (
    workspace: Workspace,
    theorems: readonly CoreLfModuleTheoremAuthoringEntry[] = entries()
) => ({
    revision,
    workspace: workspace.plan,
    theorems
});

const localType = (
    workspace: Workspace,
    theorem: CoreLfQualifiedSymbol
) => {
    const declaration = workspace.module(theorem.moduleId)
        ?.compiled.moduleInterface?.declaration(theorem);
    assert.ok(declaration);
    return declaration.type;
};

const explicitPlan = (
    workspace: Workspace,
    theorems: readonly CoreLfModuleTheoremAuthoringEntry[]
) => createCoreLfModuleTheoremDevelopment({
    revision,
    development: createCoreLfFragmentProofDevelopment({
        revision,
        workspace: workspace.plan,
        proofs: theorems.map(entry => ({
            moduleId: entry.theorem.moduleId,
            declarationId: entry.proofId,
            type: localType(workspace, entry.theorem),
            plan: entry.plan,
            provenance: entry.provenance,
            fingerprint:
                createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
                    workspace,
                    entry.theorem.moduleId,
                    entry.sourceId,
                    entry.fingerprintHashes
                )
        }))
    }),
    bindings: theorems.map(entry => ({
        proof: {
            moduleId: entry.theorem.moduleId,
            declarationId: entry.proofId
        },
        theorem: entry.theorem
    }))
});

const expectAuthoringError = (
    action: () => unknown,
    code: CoreLfModuleTheoremAuthoringError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfModuleTheoremAuthoringError &&
            error.code === code && error.path.length > 0
    );
};

describe('THEOREM-AUTHORING-22 direct TypeScript lowering', () => {
    it('derives exact proof documents and erases to the explicit row-21 plan',
        () => {
            const workspace = createRuntimeProofWorkspaceFixture();
            const sourceEntries = entries();
            const authored = createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, sourceEntries)
            );
            const explicit = explicitPlan(workspace, sourceEntries);

            assert.deepEqual(authored, explicit);
            assert.deepEqual(
                authored.development.proofs.map(proof => ({
                    moduleId: proof.moduleId,
                    declarationId: proof.declarationId,
                    type: proof.type,
                    runtime: proof.fingerprint.runtime
                })),
                explicit.development.proofs.map(proof => ({
                    moduleId: proof.moduleId,
                    declarationId: proof.declarationId,
                    type: proof.type,
                    runtime: proof.fingerprint.runtime
                }))
            );
            assertDeepFrozen(authored);
        }
    );

    it('compiles to byte-identical row-21 evidence across source permutations',
        () => {
            const workspace = createRuntimeProofWorkspaceFixture();
            const reverseWorkspace = createRuntimeProofWorkspaceFixture({
                reverse: true
            });
            const authored = compileCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace)
            );
            const explicit = compileCoreLfModuleTheoremDevelopment(
                explicitPlan(workspace, entries())
            );
            const reversed =
                compileCoreLfAuthoredModuleTheoremDevelopment(
                    authoredInput(reverseWorkspace, entries(true))
                );
            const text = serializeCoreLfModuleTheoremDevelopmentArtifact(
                authored.artifact
            );

            assert.equal(authored.artifact.status, 'complete');
            assert.equal(
                text,
                serializeCoreLfModuleTheoremDevelopmentArtifact(
                    explicit.artifact
                )
            );
            assert.equal(
                text,
                serializeCoreLfModuleTheoremDevelopmentArtifact(
                    reversed.artifact
                )
            );
            assert.deepEqual(
                authored.artifact.theoremOrder.map(proof =>
                    proof.declarationId
                ),
                ['z_prove_provider_public', 'a_prove_consumer_second']
            );
            assertDeepFrozen(authored.artifact);
        }
    );

    it('retains ordinary open theorem state through unchanged row-21 checking',
        () => {
            const workspace = createRuntimeProofWorkspaceFixture();
            const open = providerEntry(coreProofPlanHole('provider_body', {
                provenance: nodeSource
            }));
            const compiled =
                compileCoreLfAuthoredModuleTheoremDevelopment(
                    authoredInput(workspace, [open])
                );

            assert.equal(compiled.artifact.status, 'incomplete');
            assert.equal(compiled.artifact.openGoalCount, 1);
            assert.equal(compiled.artifact.bindings[0].status, 'incomplete');
        }
    );

    it('delegates proof-source visibility to the exact row-21 compiler', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        assert.throws(
            () => compileCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [
                    providerEntry(),
                    consumerEntry(runtimeProofSymbols.providerPrivateTheorem)
                ])
            ),
            error => error instanceof CoreLfDeclaredTheoremDevelopmentError &&
                error.code === 'INACCESSIBLE_PROOF_REFERENCE'
        );
    });

    it('rejects unknown theorem modules and nonlocal declarations', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        expectAuthoringError(
            () => createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [{
                    ...providerEntry(),
                    theorem: coreLfQualifiedSymbol(
                        'fixture.missing_theorem_module',
                        'theorem'
                    )
                }])
            ),
            'UNKNOWN_THEOREM_MODULE'
        );
        expectAuthoringError(
            () => createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [{
                    ...providerEntry(),
                    theorem: coreLfQualifiedSymbol(
                        runtimeProofProviderModuleId,
                        'missing_theorem'
                    )
                }])
            ),
            'UNKNOWN_LOCAL_THEOREM_DECLARATION'
        );
        expectAuthoringError(
            () => createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [{
                    ...providerEntry(),
                    theorem: {
                        moduleId: 'invalid module',
                        name: 'theorem'
                    }
                }])
            ),
            'INVALID_THEOREM_SYMBOL'
        );
    });

    it('preserves downstream duplicate and fingerprint diagnostics', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        assert.throws(
            () => createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [
                    providerEntry(),
                    {
                        ...providerEntry(),
                        theorem: runtimeProofSymbols.providerPrivateTheorem
                    }
                ])
            ),
            error => error instanceof CoreLfFragmentProofDevelopmentError &&
                error.code === 'DUPLICATE_PROOF'
        );
        assert.throws(
            () => createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [
                    providerEntry(),
                    { ...providerEntry(), proofId: 'another_provider_proof' }
                ])
            ),
            error => error instanceof CoreLfDeclaredTheoremDevelopmentError &&
                error.code === 'DUPLICATE_THEOREM_BINDING'
        );
        assert.throws(
            () => createCoreLfAuthoredModuleTheoremDevelopment(
                authoredInput(workspace, [{
                    ...providerEntry(),
                    fingerprintHashes: {
                        ...providerEntry().fingerprintHashes,
                        sourceSha256: 'not-a-sha256'
                    }
                }])
            ),
            error => error instanceof CoreLfFragmentWorkspaceProofError &&
                error.code === 'INVALID_FINGERPRINT'
        );
    });

    it('publishes an inert browser-safe authoring profile', () => {
        assert.equal(
            CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE.revision,
            'emdash-lf-module-theorem-authoring-v1'
        );
        assert.equal(
            CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE
                .addsProofCheckingSemantics,
            false
        );
        assert.equal(
            CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE
                .workspaceCompilationDuringLowering,
            true
        );
        assert.equal(
            CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE
                .computesCryptographicHashes,
            false
        );
        assert.equal(CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE.performsIo, false);
        assert.equal(
            serializeCoreLfModuleTheoremAuthoringProfile(),
            serializeCoreLfModuleTheoremAuthoringProfile()
        );
        assertDeepFrozen(CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE);
    });
});
