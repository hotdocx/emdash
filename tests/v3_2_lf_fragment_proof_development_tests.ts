/** Focused RUNTIME-DEV-CATALOG-19 multi-proof catalog tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE,
    CoreLfFragmentProofDevelopmentError,
    CoreLfFragmentWorkspaceProofError,
    compileCoreLfFragmentProofDevelopment,
    createCoreLfFragmentProofDevelopment,
    createCoreLfFragmentWorkspaceProofFingerprint,
    serializeCoreLfFragmentProofDevelopmentArtifact
} from '../src/v3_2';
import {
    createRuntimeProofDocumentInput,
    createRuntimeProofWorkspaceFixture,
    runtimeProofConsumerModuleId,
    runtimeProofProviderModuleId,
    runtimeProofUnrelatedModuleId
} from './support/v3_2_runtime_proof_fixture';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectDevelopmentError = (
    action: () => unknown,
    code: CoreLfFragmentProofDevelopmentError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfFragmentProofDevelopmentError &&
            error.code === code &&
            error.path.length > 0
    );
};

const developmentPlan = (
    reverseWorkspace = false,
    reverseProofs = false
) => {
    const workspace = createRuntimeProofWorkspaceFixture({
        reverse: reverseWorkspace
    });
    const proofs = [
        createRuntimeProofDocumentInput(workspace, true),
        createRuntimeProofDocumentInput(workspace)
    ];
    if (reverseProofs) proofs.reverse();
    return createCoreLfFragmentProofDevelopment({
        revision: 'runtime-proof-development-1',
        workspace: workspace.plan,
        proofs
    });
};

describe('RUNTIME-DEV-CATALOG-19 fragment proof development', () => {
    it('catalogs complete and open runtime proofs in canonical order', () => {
        const plan = developmentPlan();
        assert.deepEqual(
            plan.proofs.map(proof => proof.declarationId),
            ['complete_runtime_proof', 'open_runtime_proof']
        );

        const development = compileCoreLfFragmentProofDevelopment(plan);
        assert.equal(development.artifact.status, 'incomplete');
        assert.equal(development.artifact.openGoalCount, 1);
        assert.deepEqual(development.goals.map(entry => ({
            moduleId: entry.moduleId,
            declarationId: entry.declarationId,
            goalId: entry.goal.id
        })), [{
            moduleId: runtimeProofConsumerModuleId,
            declarationId: 'open_runtime_proof',
            goalId: 'runtime_body'
        }]);
        assert.equal(
            development.proof(
                runtimeProofConsumerModuleId,
                'complete_runtime_proof'
            )?.artifact.state.status,
            'complete'
        );
        assert.equal(
            development.proof(runtimeProofConsumerModuleId, 'absent'),
            undefined
        );
        assert.deepEqual(
            development.artifact.workspace.order,
            [
                runtimeProofUnrelatedModuleId,
                runtimeProofProviderModuleId,
                runtimeProofConsumerModuleId
            ]
        );
        development.artifact.proofs.forEach(proof => {
            assert.deepEqual(proof.closure.order, [
                runtimeProofProviderModuleId,
                runtimeProofConsumerModuleId
            ]);
            assert.equal(
                proof.closure.order.includes(runtimeProofUnrelatedModuleId),
                false
            );
            assert.deepEqual(proof.runtime.ruleIds, [
                'fixture.runtime_proof.normalize'
            ]);
        });
        assert.equal(
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE
                .theoremDependencyPolicy,
            'independent-proof-leaves'
        );
        assert.equal(
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.acceptsRuntimeInput,
            false
        );
        assertDeepFrozen(development.artifact);
        assert.equal(Object.isFrozen(development.proofs), true);
        assert.equal(Object.isFrozen(development.goals), true);
    });

    it('serializes byte-identically across source permutations', () => {
        const first = compileCoreLfFragmentProofDevelopment(
            developmentPlan(false, false)
        );
        const second = compileCoreLfFragmentProofDevelopment(
            developmentPlan(true, true)
        );
        const firstText = serializeCoreLfFragmentProofDevelopmentArtifact(
            first.artifact
        );
        assert.equal(
            firstText,
            serializeCoreLfFragmentProofDevelopmentArtifact(second.artifact)
        );
        assert.equal(firstText.endsWith('\n'), true);
        assert.doesNotMatch(
            firstText,
            /session|environment|callback|rewriteHead|checkedTerm|\?m\d/u
        );
    });

    it('rejects malformed, empty, duplicate, and ownerless catalogs', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const complete = createRuntimeProofDocumentInput(workspace);
        expectDevelopmentError(
            () => createCoreLfFragmentProofDevelopment({
                revision: 'bad revision',
                workspace: workspace.plan,
                proofs: [complete]
            }),
            'INVALID_DEVELOPMENT'
        );
        expectDevelopmentError(
            () => createCoreLfFragmentProofDevelopment({
                revision: 'empty-runtime-development-1',
                workspace: workspace.plan,
                proofs: []
            }),
            'INVALID_DEVELOPMENT'
        );
        expectDevelopmentError(
            () => createCoreLfFragmentProofDevelopment({
                revision: 'duplicate-runtime-development-1',
                workspace: workspace.plan,
                proofs: [complete, complete]
            }),
            'DUPLICATE_PROOF'
        );
        expectDevelopmentError(
            () => createCoreLfFragmentProofDevelopment({
                revision: 'ownerless-runtime-development-1',
                workspace: workspace.plan,
                proofs: [{
                    ...complete,
                    moduleId: 'fixture.runtime_proof_missing'
                }]
            }),
            'UNKNOWN_PROOF_MODULE'
        );
        expectDevelopmentError(
            () => createCoreLfFragmentProofDevelopment({
                revision: 'invalid-id-runtime-development-1',
                workspace: workspace.plan,
                proofs: [{
                    ...complete,
                    declarationId: 'not portable'
                }]
            }),
            'INVALID_PROOF_ID'
        );
    });

    it('delegates stale runtime rejection to the exact proof owner', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const input = createRuntimeProofDocumentInput(workspace);
        const stale = {
            ...input,
            fingerprint: createCoreLfFragmentWorkspaceProofFingerprint({
                source: input.fingerprint.source,
                profileSha256: input.fingerprint.profile.sha256,
                dependencies: input.fingerprint.dependencies,
                runtime: {
                    revision: `${input.fingerprint.runtime.revision}+stale`,
                    ruleIds: input.fingerprint.runtime.ruleIds
                }
            })
        };
        const plan = createCoreLfFragmentProofDevelopment({
            revision: 'stale-runtime-development-1',
            workspace: workspace.plan,
            proofs: [stale]
        });
        assert.throws(
            () => compileCoreLfFragmentProofDevelopment(plan),
            error => error instanceof CoreLfFragmentWorkspaceProofError &&
                error.code === 'RUNTIME_FINGERPRINT_MISMATCH'
        );
    });
});
