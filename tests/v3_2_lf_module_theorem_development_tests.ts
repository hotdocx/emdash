/** Focused MODULE-THEOREM-DAG-21 multi-module visibility tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreContextError,
    CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE,
    CoreLfDeclaredTheoremDevelopmentError,
    CoreLfFragmentWorkspaceProofDocumentInput,
    binderMode,
    compileCoreLfFragmentProofDevelopment,
    compileCoreLfModuleTheoremDevelopment,
    coreProofPlanApply,
    coreProofPlanExact,
    coreProofPlanHave,
    coreProofPlanHole,
    createCoreLfDeclaredTheoremDevelopment,
    createCoreLfFragmentProofDevelopment,
    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace,
    createCoreLfModuleTheoremDevelopment,
    kernelBinder,
    kernelBound,
    kernelFree,
    provenance,
    serializeCoreLfModuleTheoremDevelopmentArtifact
} from '../src/v3_2';
import {
    createRuntimeProofDocumentInput,
    createRuntimeProofWorkspaceFixture,
    runtimeProofConsumerModuleId,
    runtimeProofCoreName,
    runtimeProofProviderModuleId,
    runtimeProofSymbols
} from './support/v3_2_runtime_proof_fixture';

type Workspace = ReturnType<typeof createRuntimeProofWorkspaceFixture>;
type Symbol = typeof runtimeProofSymbols[keyof typeof runtimeProofSymbols];

const nodeSource = provenance('surface', 'module-theorem test source');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectTheoremError = (
    action: () => unknown,
    code: CoreLfDeclaredTheoremDevelopmentError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfDeclaredTheoremDevelopmentError &&
            error.code === code &&
            error.path.length > 0
    );
};

const providerProof = (
    workspace: Workspace,
    open = false
): CoreLfFragmentWorkspaceProofDocumentInput => {
    const base = createRuntimeProofDocumentInput(workspace);
    return {
        ...base,
        moduleId: runtimeProofProviderModuleId,
        declarationId: 'z_prove_provider_public',
        plan: open
            ? coreProofPlanHole('provider_body', {
                provenance: nodeSource,
                expectation: { target: base.type }
            })
            : coreProofPlanExact(kernelFree(
                runtimeProofCoreName(runtimeProofSymbols.providerValue),
                nodeSource
            )),
        provenance: nodeSource,
        fingerprint:
            createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
                workspace,
                runtimeProofProviderModuleId,
                'tests/fixtures/module-theorem-provider.surface.ts',
                {
                    sourceSha256: `sha256:${'8'.repeat(64)}`,
                    profileSha256: `sha256:${'9'.repeat(64)}`,
                    interfaceSha256ByModuleId: {
                        [runtimeProofProviderModuleId]:
                            `sha256:${'a'.repeat(64)}`
                    }
                }
            )
    };
};

const consumerProof = (
    workspace: Workspace,
    solution: Symbol = runtimeProofSymbols.providerPublicTheorem
): CoreLfFragmentWorkspaceProofDocumentInput => {
    const base = createRuntimeProofDocumentInput(workspace);
    return {
        ...base,
        declarationId: 'a_prove_consumer_second',
        plan: coreProofPlanExact(kernelFree(
            runtimeProofCoreName(solution),
            nodeSource
        )),
        provenance: nodeSource
    };
};

const consumerTypeProof = (
    workspace: Workspace,
    solutionName: string
): CoreLfFragmentWorkspaceProofDocumentInput => {
    const base = createRuntimeProofDocumentInput(workspace);
    return {
        ...base,
        declarationId: 'b_prove_consumer_type_goal',
        type: kernelFree(
            runtimeProofCoreName(runtimeProofSymbols.providerTransitiveAlias),
            nodeSource
        ),
        plan: coreProofPlanExact(kernelFree(solutionName, nodeSource)),
        provenance: nodeSource
    };
};

const development = (
    workspace: Workspace,
    provider: CoreLfFragmentWorkspaceProofDocumentInput,
    consumer: CoreLfFragmentWorkspaceProofDocumentInput,
    reverse = false
) => createCoreLfFragmentProofDevelopment({
    revision: 'module-theorem-fragment-development-1',
    workspace: workspace.plan,
    proofs: reverse ? [consumer, provider] : [provider, consumer]
});

const bindings = (reverse = false) => {
    const entries = [{
        proof: {
            moduleId: runtimeProofProviderModuleId,
            declarationId: 'z_prove_provider_public'
        },
        theorem: runtimeProofSymbols.providerPublicTheorem
    }, {
        proof: {
            moduleId: runtimeProofConsumerModuleId,
            declarationId: 'a_prove_consumer_second'
        },
        theorem: runtimeProofSymbols.second
    }];
    return reverse ? entries.reverse() : entries;
};

const modulePlan = (
    workspace = createRuntimeProofWorkspaceFixture(),
    reverse = false
) => createCoreLfModuleTheoremDevelopment({
    revision: 'module-theorem-development-1',
    development: development(
        workspace,
        providerProof(workspace),
        consumerProof(workspace),
        reverse
    ),
    bindings: bindings(reverse)
});

describe('MODULE-THEOREM-DAG-21 closed workspace theorem developments', () => {
    it('certifies a direct-public provider theorem used by a consumer', () => {
        const compiled = compileCoreLfModuleTheoremDevelopment(modulePlan());
        assert.equal(compiled.artifact.status, 'complete');
        assert.deepEqual(
            compiled.artifact.bindings.map(entry => [
                entry.proof.moduleId,
                entry.proof.declarationId
            ]),
            [
                [
                    runtimeProofConsumerModuleId,
                    'a_prove_consumer_second'
                ],
                [
                    runtimeProofProviderModuleId,
                    'z_prove_provider_public'
                ]
            ]
        );
        const consumer = compiled.binding(
            runtimeProofConsumerModuleId,
            'a_prove_consumer_second'
        );
        assert.deepEqual(consumer?.theoremDependencies, [{
            moduleId: runtimeProofProviderModuleId,
            declarationId: 'z_prove_provider_public'
        }]);
        assert.deepEqual(consumer?.sourceFreeReferences, [
            runtimeProofCoreName(runtimeProofSymbols.decode),
            runtimeProofCoreName(runtimeProofSymbols.base),
            runtimeProofCoreName(runtimeProofSymbols.providerPublicTheorem)
        ].sort());
        assert.deepEqual(
            compiled.artifact.theoremOrder.map(entry => entry.declarationId),
            ['z_prove_provider_public', 'a_prove_consumer_second']
        );
        assert.equal(
            CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.referencePolicy,
            'root-local-plus-direct-public-imports'
        );
        assert.equal(
            CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE
                .supportsDetachedTheoremImports,
            false
        );
        assertDeepFrozen(compiled.artifact);
    });

    it('is byte-stable across workspace, proof, and binding permutations', () => {
        const first = compileCoreLfModuleTheoremDevelopment(modulePlan());
        const second = compileCoreLfModuleTheoremDevelopment(modulePlan(
            createRuntimeProofWorkspaceFixture({ reverse: true }),
            true
        ));
        const text = serializeCoreLfModuleTheoremDevelopmentArtifact(
            first.artifact
        );
        assert.equal(
            text,
            serializeCoreLfModuleTheoremDevelopmentArtifact(second.artifact)
        );
        assert.doesNotMatch(
            text,
            /checker|environment|callback|catalogRuntime|checkedTerm|\?m\d/u
        );
    });

    it('keeps the completed same-module profile closed to multiple roots', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const multi = development(
            workspace,
            providerProof(workspace),
            consumerProof(workspace)
        );
        expectTheoremError(
            () => createCoreLfDeclaredTheoremDevelopment({
                revision: 'same-module-still-closed-1',
                development: multi,
                bindings: bindings()
            }),
            'MULTIPLE_THEOREM_MODULES'
        );
    });

    it('rejects direct private and protected provider references', () => {
        for (const inaccessible of [
            runtimeProofSymbols.providerPrivateTheorem,
            runtimeProofSymbols.providerProtectedTheorem
        ]) {
            const workspace = createRuntimeProofWorkspaceFixture();
            const provider = providerProof(workspace);
            const consumer = consumerProof(workspace, inaccessible);
            const fragment = development(workspace, provider, consumer);

            // This records the exact pre-existing checker boundary: the full
            // closure can check the raw free reference before source preflight.
            assert.equal(
                compileCoreLfFragmentProofDevelopment(fragment)
                    .artifact.status,
                'complete'
            );
            const plan = createCoreLfModuleTheoremDevelopment({
                revision: `inaccessible-${inaccessible.name}-1`,
                development: fragment,
                bindings: bindings()
            });
            expectTheoremError(
                () => compileCoreLfModuleTheoremDevelopment(plan),
                'INACCESSIBLE_PROOF_REFERENCE'
            );
        }
    });

    it('preflights inaccessible references nested inside contextual have', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const provider = providerProof(workspace);
        const base = consumerProof(
            workspace,
            runtimeProofSymbols.providerPrivateTheorem
        );
        const consumer = {
            ...base,
            plan: coreProofPlanHave(
                kernelBinder(
                    'hidden',
                    base.type,
                    binderMode('explicit', 'functorial'),
                    nodeSource
                ),
                coreProofPlanExact(kernelFree(
                    runtimeProofCoreName(
                        runtimeProofSymbols.providerPrivateTheorem
                    ),
                    nodeSource
                )),
                coreProofPlanExact(kernelBound(0, nodeSource)),
                { provenance: nodeSource }
            )
        };
        const plan = createCoreLfModuleTheoremDevelopment({
            revision: 'nested-private-reference-1',
            development: development(workspace, provider, consumer),
            bindings: bindings()
        });
        expectTheoremError(
            () => compileCoreLfModuleTheoremDevelopment(plan),
            'INACCESSIBLE_PROOF_REFERENCE'
        );
    });

    it('preflights inaccessible references nested inside apply premises', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const provider = providerProof(workspace);
        const base = consumerProof(workspace);
        const consumer = {
            ...base,
            plan: coreProofPlanApply(
                kernelFree(
                    runtimeProofCoreName(runtimeProofSymbols.localPass),
                    nodeSource
                ),
                [coreProofPlanExact(kernelFree(
                    runtimeProofCoreName(
                        runtimeProofSymbols.providerPrivateTheorem
                    ),
                    nodeSource
                ))],
                { provenance: nodeSource }
            )
        };
        const fragment = development(workspace, provider, consumer);
        assert.equal(
            compileCoreLfFragmentProofDevelopment(fragment).artifact.status,
            'complete'
        );
        const plan = createCoreLfModuleTheoremDevelopment({
            revision: 'apply-private-reference-1',
            development: fragment,
            bindings: bindings()
        });
        expectTheoremError(
            () => compileCoreLfModuleTheoremDevelopment(plan),
            'INACCESSIBLE_PROOF_REFERENCE'
        );
    });

    it('permits root-private assumptions while retaining them explicitly', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const consumer = consumerProof(
            workspace,
            runtimeProofSymbols.localPrivate
        );
        const fragment = createCoreLfFragmentProofDevelopment({
            revision: 'local-private-fragment-development-1',
            workspace: workspace.plan,
            proofs: [consumer]
        });
        const compiled = compileCoreLfModuleTheoremDevelopment(
            createCoreLfModuleTheoremDevelopment({
                revision: 'local-private-theorem-development-1',
                development: fragment,
                bindings: [bindings()[1]]
            })
        );
        const result = compiled.binding(
            runtimeProofConsumerModuleId,
            'a_prove_consumer_second'
        );
        const localName = runtimeProofCoreName(
            runtimeProofSymbols.localPrivate
        );
        assert.equal(result?.sourceFreeReferences.includes(localName), true);
        assert.equal(result?.workspaceDependencies.includes(localName), true);
    });

    it('rejects a merely transitive declaration accepted by raw closure checking',
        () => {
            const workspace = createRuntimeProofWorkspaceFixture({
                providerDependsOnUnrelated: true
            });
            const proof = consumerTypeProof(
                workspace,
                runtimeProofCoreName(runtimeProofSymbols.secret)
            );
            const fragment = createCoreLfFragmentProofDevelopment({
                revision: 'transitive-reference-fragment-development-1',
                workspace: workspace.plan,
                proofs: [proof]
            });
            assert.equal(
                compileCoreLfFragmentProofDevelopment(fragment)
                    .artifact.status,
                'complete'
            );
            const plan = createCoreLfModuleTheoremDevelopment({
                revision: 'transitive-reference-theorem-development-1',
                development: fragment,
                bindings: [{
                    proof: {
                        moduleId: runtimeProofConsumerModuleId,
                        declarationId: proof.declarationId
                    },
                    theorem: runtimeProofSymbols.consumerTypeGoal
                }]
            });
            expectTheoremError(
                () => compileCoreLfModuleTheoremDevelopment(plan),
                'INACCESSIBLE_PROOF_REFERENCE'
            );
        });

    it('rejects unrelated and unknown names before theorem evidence', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        for (const solutionName of [
            runtimeProofCoreName(runtimeProofSymbols.secret),
            'fixture_unknown_direct_reference'
        ]) {
            const proof = {
                ...consumerProof(workspace),
                plan: coreProofPlanExact(kernelFree(
                    solutionName,
                    nodeSource
                ))
            };
            const fragment = createCoreLfFragmentProofDevelopment({
                revision: `absent-reference-${solutionName}-1`,
                workspace: workspace.plan,
                proofs: [proof]
            });
            const plan = createCoreLfModuleTheoremDevelopment({
                revision: `absent-reference-theorem-${solutionName}-1`,
                development: fragment,
                bindings: [{
                    proof: {
                        moduleId: runtimeProofConsumerModuleId,
                        declarationId: proof.declarationId
                    },
                    theorem: runtimeProofSymbols.second
                }]
            });
            assert.throws(
                () => compileCoreLfModuleTheoremDevelopment(plan),
                error => error instanceof CoreContextError &&
                    error.code === 'UNBOUND_FREE_REFERENCE'
            );
        }
    });

    it('retains an accessible open theorem and its target expectation', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const provider = providerProof(workspace, true);
        const fragment = createCoreLfFragmentProofDevelopment({
            revision: 'open-module-theorem-fragment-development-1',
            workspace: workspace.plan,
            proofs: [provider]
        });
        const compiled = compileCoreLfModuleTheoremDevelopment(
            createCoreLfModuleTheoremDevelopment({
                revision: 'open-module-theorem-development-1',
                development: fragment,
                bindings: [bindings()[0]]
            })
        );
        assert.equal(compiled.artifact.status, 'incomplete');
        assert.equal(compiled.artifact.openGoalCount, 1);
        assert.deepEqual(
            compiled.development.goals.map(entry => entry.goal.id),
            ['provider_body']
        );
        assert.deepEqual(
            compiled.artifact.bindings[0].sourceFreeReferences,
            [
                runtimeProofCoreName(runtimeProofSymbols.decode),
                runtimeProofCoreName(runtimeProofSymbols.base)
            ].sort()
        );
    });

    it('rejects a completed consumer of an open provider theorem', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const plan = createCoreLfModuleTheoremDevelopment({
            revision: 'open-provider-theorem-1',
            development: development(
                workspace,
                providerProof(workspace, true),
                consumerProof(workspace)
            ),
            bindings: bindings()
        });
        expectTheoremError(
            () => compileCoreLfModuleTheoremDevelopment(plan),
            'OPEN_THEOREM_DEPENDENCY'
        );
    });
});
