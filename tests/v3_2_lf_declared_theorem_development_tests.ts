/** Focused DECLARED-THEOREM-DAG-20 theorem binding and dependency tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE,
    CoreLfDeclaredTheoremDevelopmentError,
    CoreLfFragmentWorkspaceProofDocumentInput,
    compileCoreLfDeclaredTheoremDevelopment,
    coreLfQualifiedSymbol,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreLfDeclaredTheoremDevelopment,
    createCoreLfFragmentProofDevelopment,
    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace,
    kernelFree,
    provenance,
    serializeCoreLfDeclaredTheoremDevelopmentArtifact
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

const nodeSource = provenance('surface', 'declared-theorem test source');

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

const proof = (
    workspace: Workspace,
    declarationId: string,
    solution: Symbol,
    open = false
): CoreLfFragmentWorkspaceProofDocumentInput => {
    const base = createRuntimeProofDocumentInput(workspace, open);
    return {
        ...base,
        declarationId,
        plan: open
            ? coreProofPlanHole(`${declarationId}_body`, {
                provenance: nodeSource
            })
            : coreProofPlanExact(kernelFree(
                runtimeProofCoreName(solution),
                nodeSource
            )),
        provenance: nodeSource
    };
};

const fragmentDevelopment = (
    workspace: Workspace,
    proofs: readonly CoreLfFragmentWorkspaceProofDocumentInput[]
) => createCoreLfFragmentProofDevelopment({
    revision: 'declared-theorem-fragment-development-1',
    workspace: workspace.plan,
    proofs
});

const binding = (
    declarationId: string,
    theorem: Symbol
) => ({
    proof: {
        moduleId: runtimeProofConsumerModuleId,
        declarationId
    },
    theorem
});

const theoremPlan = (
    workspace = createRuntimeProofWorkspaceFixture(),
    reverse = false
) => {
    const first = proof(
        workspace,
        'z_prove_first',
        runtimeProofSymbols.value
    );
    const second = proof(
        workspace,
        'a_prove_second',
        runtimeProofSymbols.first
    );
    const proofs = reverse ? [second, first] : [first, second];
    const bindings = [
        binding('z_prove_first', runtimeProofSymbols.first),
        binding('a_prove_second', runtimeProofSymbols.second)
    ];
    if (reverse) bindings.reverse();
    return createCoreLfDeclaredTheoremDevelopment({
        revision: 'declared-theorem-development-1',
        development: fragmentDevelopment(workspace, proofs),
        bindings
    });
};

const providerProof = (
    workspace: Workspace
): CoreLfFragmentWorkspaceProofDocumentInput => ({
    moduleId: runtimeProofProviderModuleId,
    declarationId: 'prove_provider_base',
    type: kernelFree(
        runtimeProofCoreName(runtimeProofSymbols.code),
        nodeSource
    ),
    plan: coreProofPlanExact(kernelFree(
        runtimeProofCoreName(runtimeProofSymbols.base),
        nodeSource
    )),
    provenance: nodeSource,
    fingerprint: createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
        workspace,
        runtimeProofProviderModuleId,
        'tests/fixtures/declared-theorem-provider.surface.ts',
        {
            sourceSha256: `sha256:${'8'.repeat(64)}`,
            profileSha256: `sha256:${'9'.repeat(64)}`,
            interfaceSha256ByModuleId: {
                [runtimeProofProviderModuleId]:
                    `sha256:${'a'.repeat(64)}`
            }
        }
    )
});

describe('DECLARED-THEOREM-DAG-20 theorem developments', () => {
    it('certifies a runtime-dependent theorem chain and portable DAG', () => {
        const compiled = compileCoreLfDeclaredTheoremDevelopment(
            theoremPlan()
        );
        assert.equal(compiled.artifact.status, 'complete');
        assert.equal(compiled.artifact.openGoalCount, 0);
        assert.deepEqual(
            compiled.artifact.bindings.map(entry => entry.proof.declarationId),
            ['a_prove_second', 'z_prove_first']
        );

        const first = compiled.binding(
            runtimeProofConsumerModuleId,
            'z_prove_first'
        );
        const second = compiled.binding(
            runtimeProofConsumerModuleId,
            'a_prove_second'
        );
        assert.deepEqual(first?.theoremDependencies, []);
        assert.deepEqual(first?.workspaceDependencies, [
            runtimeProofCoreName(runtimeProofSymbols.value)
        ]);
        assert.deepEqual(second?.directFreeReferences, [
            runtimeProofCoreName(runtimeProofSymbols.first)
        ]);
        assert.deepEqual(second?.theoremDependencies, [{
            moduleId: runtimeProofConsumerModuleId,
            declarationId: 'z_prove_first'
        }]);
        assert.deepEqual(second?.workspaceDependencies, []);
        assert.deepEqual(
            compiled.artifact.theoremOrder.map(entry => entry.declarationId),
            ['z_prove_first', 'a_prove_second']
        );
        assert.equal(
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE
                .supportsCrossModuleTheoremBindings,
            false
        );
        assert.equal(
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.acceptsRuntimeInput,
            false
        );
        assertDeepFrozen(compiled.artifact);
    });

    it('is byte-stable across workspace, proof, and binding permutations', () => {
        const first = compileCoreLfDeclaredTheoremDevelopment(theoremPlan());
        const second = compileCoreLfDeclaredTheoremDevelopment(theoremPlan(
            createRuntimeProofWorkspaceFixture({ reverse: true }),
            true
        ));
        const text = serializeCoreLfDeclaredTheoremDevelopmentArtifact(
            first.artifact
        );
        assert.equal(
            text,
            serializeCoreLfDeclaredTheoremDevelopmentArtifact(second.artifact)
        );
        assert.equal(text.endsWith('\n'), true);
        assert.doesNotMatch(
            text,
            /checker|environment|callback|catalogRuntime|checkedTerm|\?m\d/u
        );
    });

    it('retains an unconsumed open theorem as explicit incomplete state', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const first = proof(
            workspace,
            'prove_first',
            runtimeProofSymbols.value,
            true
        );
        const compiled = compileCoreLfDeclaredTheoremDevelopment(
            createCoreLfDeclaredTheoremDevelopment({
                revision: 'open-declared-theorem-1',
                development: fragmentDevelopment(workspace, [first]),
                bindings: [binding(
                    'prove_first',
                    runtimeProofSymbols.first
                )]
            })
        );
        assert.equal(compiled.artifact.status, 'incomplete');
        assert.equal(compiled.artifact.openGoalCount, 1);
        assert.equal(compiled.artifact.bindings[0].status, 'incomplete');
        assert.deepEqual(
            compiled.artifact.bindings[0].theoremDependencies,
            []
        );
        assert.deepEqual(
            compiled.artifact.theoremOrder.map(entry => entry.declarationId),
            ['prove_first']
        );
        assert.deepEqual(
            compiled.development.goals.map(entry => entry.goal.id),
            ['prove_first_body']
        );
    });

    it('rejects malformed, incomplete, duplicate, and cross-root bindings', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const first = proof(
            workspace,
            'prove_first',
            runtimeProofSymbols.value
        );
        const second = proof(
            workspace,
            'prove_second',
            runtimeProofSymbols.first
        );
        const development = fragmentDevelopment(workspace, [first, second]);
        const bindings = [
            binding('prove_first', runtimeProofSymbols.first),
            binding('prove_second', runtimeProofSymbols.second)
        ];

        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'bad revision',
            development,
            bindings
        }), 'INVALID_DEVELOPMENT');
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'invalid-symbol-1',
            development,
            bindings: [{
                ...bindings[0],
                theorem: {
                    moduleId: runtimeProofConsumerModuleId,
                    name: 'not portable'
                }
            }, bindings[1]]
        }), 'INVALID_BINDING');
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'missing-binding-1',
            development,
            bindings: [bindings[0]]
        }), 'MISSING_BINDING');
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'unknown-proof-1',
            development,
            bindings: [bindings[0], {
                ...bindings[1],
                proof: {
                    ...bindings[1].proof,
                    declarationId: 'absent'
                }
            }]
        }), 'UNKNOWN_PROOF');
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'duplicate-proof-binding-1',
            development,
            bindings: [bindings[0], bindings[0], bindings[1]]
        }), 'DUPLICATE_PROOF_BINDING');
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'duplicate-theorem-binding-1',
            development,
            bindings: [bindings[0], {
                ...bindings[1],
                theorem: runtimeProofSymbols.first
            }]
        }), 'DUPLICATE_THEOREM_BINDING');
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'module-mismatch-1',
            development,
            bindings: [{
                ...bindings[0],
                theorem: runtimeProofSymbols.base
            }, bindings[1]]
        }), 'THEOREM_MODULE_MISMATCH');

        const provider = providerProof(workspace);
        const multiRoot = fragmentDevelopment(workspace, [first, provider]);
        expectTheoremError(() => createCoreLfDeclaredTheoremDevelopment({
            revision: 'multiple-theorem-roots-1',
            development: multiRoot,
            bindings: [
                bindings[0],
                {
                    proof: {
                        moduleId: runtimeProofProviderModuleId,
                        declarationId: provider.declarationId
                    },
                    theorem: runtimeProofSymbols.base
                }
            ]
        }), 'MULTIPLE_THEOREM_MODULES');
    });

    it('rejects absent, non-signature, and mismatched theorem targets', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const first = proof(
            workspace,
            'prove_first',
            runtimeProofSymbols.value
        );
        const development = fragmentDevelopment(workspace, [first]);

        const compileBinding = (theorem: Symbol) =>
            compileCoreLfDeclaredTheoremDevelopment(
                createCoreLfDeclaredTheoremDevelopment({
                    revision: 'invalid-theorem-declaration-1',
                    development,
                    bindings: [binding('prove_first', theorem)]
                })
            );
        expectTheoremError(
            () => compileBinding(coreLfQualifiedSymbol(
                runtimeProofConsumerModuleId,
                'absent'
            )),
            'UNKNOWN_THEOREM_DECLARATION'
        );
        expectTheoremError(
            () => compileBinding(runtimeProofSymbols.helperFirst),
            'UNSUPPORTED_THEOREM_DECLARATION'
        );

        const wrongTarget: CoreLfFragmentWorkspaceProofDocumentInput = {
            ...first,
            declarationId: 'prove_code',
            type: kernelFree(
                runtimeProofCoreName(runtimeProofSymbols.code),
                nodeSource
            ),
            plan: coreProofPlanExact(kernelFree(
                runtimeProofCoreName(runtimeProofSymbols.base),
                nodeSource
            ))
        };
        const wrongDevelopment = fragmentDevelopment(workspace, [wrongTarget]);
        expectTheoremError(
            () => compileCoreLfDeclaredTheoremDevelopment(
                createCoreLfDeclaredTheoremDevelopment({
                    revision: 'mismatched-theorem-target-1',
                    development: wrongDevelopment,
                    bindings: [{
                        proof: {
                            moduleId: runtimeProofConsumerModuleId,
                            declarationId: wrongTarget.declarationId
                        },
                        theorem: runtimeProofSymbols.first
                    }]
                })
            ),
            'THEOREM_TARGET_MISMATCH'
        );
    });

    it('rejects direct and helper-hidden self dependencies', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const compile = (solution: Symbol, revision: string) => {
            const first = proof(workspace, 'prove_first', solution);
            return compileCoreLfDeclaredTheoremDevelopment(
                createCoreLfDeclaredTheoremDevelopment({
                    revision,
                    development: fragmentDevelopment(workspace, [first]),
                    bindings: [binding(
                        'prove_first',
                        runtimeProofSymbols.first
                    )]
                })
            );
        };
        expectTheoremError(
            () => compile(runtimeProofSymbols.first, 'direct-self-1'),
            'SELF_THEOREM_DEPENDENCY'
        );
        expectTheoremError(
            () => compile(runtimeProofSymbols.helperFirst, 'hidden-self-1'),
            'SELF_THEOREM_DEPENDENCY'
        );
    });

    it('rejects direct and helper-hidden theorem cycles', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const compileCycle = (secondSolution: Symbol, revision: string) => {
            const first = proof(
                workspace,
                'prove_first',
                runtimeProofSymbols.second
            );
            const second = proof(
                workspace,
                'prove_second',
                secondSolution
            );
            return compileCoreLfDeclaredTheoremDevelopment(
                createCoreLfDeclaredTheoremDevelopment({
                    revision,
                    development: fragmentDevelopment(
                        workspace,
                        [first, second]
                    ),
                    bindings: [
                        binding('prove_first', runtimeProofSymbols.first),
                        binding('prove_second', runtimeProofSymbols.second)
                    ]
                })
            );
        };
        expectTheoremError(
            () => compileCycle(runtimeProofSymbols.first, 'direct-cycle-1'),
            'CYCLIC_THEOREM_DEPENDENCY'
        );
        expectTheoremError(
            () => compileCycle(
                runtimeProofSymbols.helperFirst,
                'hidden-cycle-1'
            ),
            'CYCLIC_THEOREM_DEPENDENCY'
        );
    });

    it('rejects complete proofs that consume open bound theorems', () => {
        const workspace = createRuntimeProofWorkspaceFixture();
        const first = proof(
            workspace,
            'prove_first',
            runtimeProofSymbols.value,
            true
        );
        const second = proof(
            workspace,
            'prove_second',
            runtimeProofSymbols.first
        );
        const plan = createCoreLfDeclaredTheoremDevelopment({
            revision: 'open-theorem-dependency-1',
            development: fragmentDevelopment(workspace, [first, second]),
            bindings: [
                binding('prove_first', runtimeProofSymbols.first),
                binding('prove_second', runtimeProofSymbols.second)
            ]
        });
        expectTheoremError(
            () => compileCoreLfDeclaredTheoremDevelopment(plan),
            'OPEN_THEOREM_DEPENDENCY'
        );
    });
});
