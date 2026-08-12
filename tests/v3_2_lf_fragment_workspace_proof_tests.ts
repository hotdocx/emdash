/** Focused PRACTICAL-CLASS-PROOF-18 runtime-closure proof tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE,
    CoreCheckerError,
    CoreContextError,
    CoreLfCompiledFragmentModuleWorkspace,
    CoreLfFragmentWorkspaceProofError,
    compileCoreLfFragmentWorkspaceProofDocument,
    coreProofPlanHole,
    createCoreLfFragmentWorkspaceProofFingerprint,
    createCoreProofChecker,
    kernelFree,
    provenance,
    serializeCoreLfFragmentWorkspaceProofArtifact
} from '../src/v3_2';
import {
    createRuntimeProofDocumentInput,
    createRuntimeProofWorkspaceFixture,
    runtimeProofConsumerModuleId,
    runtimeProofCoreName,
    runtimeProofProviderModuleId,
    runtimeProofSymbols,
    runtimeProofUnrelatedModuleId
} from './support/v3_2_runtime_proof_fixture';

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

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('PRACTICAL-CLASS-PROOF-18 exact runtime proof attachment', () => {
    it('rechecks complete and named-open plans with the derived runtime', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        assert.deepEqual(workspace.plan.order, [
            runtimeProofUnrelatedModuleId,
            runtimeProofProviderModuleId,
            runtimeProofConsumerModuleId
        ]);
        const completeInput = createRuntimeProofDocumentInput(workspace);
        assert.equal(completeInput.plan.tag, 'exact');
        if (completeInput.plan.tag !== 'exact') return;
        const solution = completeInput.plan.solution;
        const root = workspace.module(runtimeProofConsumerModuleId);
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
            createRuntimeProofDocumentInput(workspace, true)
        );
        assert.equal(complete.artifact.state.status, 'complete');
        assert.notEqual(complete.checkedTerm, undefined);
        assert.equal(open.artifact.state.status, 'incomplete');
        assert.deepEqual(
            open.artifact.state.goals.map(goal => goal.id),
            ['runtime_body']
        );
        assert.deepEqual(complete.artifact.closure.order, [
            runtimeProofProviderModuleId,
            runtimeProofConsumerModuleId
        ]);
        assert.equal(
            complete.artifact.closure.order.includes(
                runtimeProofUnrelatedModuleId
            ),
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
        const firstWorkspace = createRuntimeProofWorkspaceFixture();
        const secondWorkspace = createRuntimeProofWorkspaceFixture({
            reverse: true
        });
        const first = compileCoreLfFragmentWorkspaceProofDocument(
            firstWorkspace,
            createRuntimeProofDocumentInput(firstWorkspace)
        ).artifact;
        const second = compileCoreLfFragmentWorkspaceProofDocument(
            secondWorkspace,
            createRuntimeProofDocumentInput(secondWorkspace)
        ).artifact;
        assert.equal(
            serializeCoreLfFragmentWorkspaceProofArtifact(first),
            serializeCoreLfFragmentWorkspaceProofArtifact(second)
        );
    });

    it('requires exactly the closure modules in the fingerprint', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const input = createRuntimeProofDocumentInput(workspace);
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
        const withoutRuntime = createRuntimeProofWorkspaceFixture({
            runtime: false
        });
        const nodeSource = provenance('surface', 'missing runtime proof');
        expectProofError(
            () => compileCoreLfFragmentWorkspaceProofDocument(
                withoutRuntime,
                {
                    moduleId: runtimeProofConsumerModuleId,
                    declarationId: 'missing_runtime',
                    type: kernelFree(
                        runtimeProofCoreName(runtimeProofSymbols.base),
                        nodeSource
                    ),
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
                                runtimeProofProviderModuleId,
                                runtimeProofConsumerModuleId
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

        const workspace = createRuntimeProofWorkspaceFixture();
        const input = createRuntimeProofDocumentInput(workspace);
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
        const workspace = createRuntimeProofWorkspaceFixture();
        const input = createRuntimeProofDocumentInput(workspace, true);
        assert.throws(
            () => compileCoreLfFragmentWorkspaceProofDocument(workspace, {
                ...input,
                declarationId: 'unrelated_target',
                type: kernelFree(
                    runtimeProofCoreName(runtimeProofSymbols.secret),
                    provenance('surface', 'unrelated target')
                )
            }),
            error => error instanceof CoreContextError &&
                error.code === 'UNBOUND_FREE_REFERENCE'
        );
    });

    it('rejects compiled closure drift', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const modules = workspace.modules.map(module =>
            module.source.identity.moduleId === runtimeProofConsumerModuleId
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
                createRuntimeProofDocumentInput(workspace)
            ),
            'CLOSURE_DRIFT'
        );
    });

    it('serializes no process-local proof or runtime authority', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const text = serializeCoreLfFragmentWorkspaceProofArtifact(
            compileCoreLfFragmentWorkspaceProofDocument(
                workspace,
                createRuntimeProofDocumentInput(workspace)
            ).artifact
        );
        assert.doesNotMatch(
            text,
            /session|environment|callback|rewriteHead|objectIdentity|\?m\d/u
        );
        assert.equal(text.endsWith('\n'), true);
    });
});
