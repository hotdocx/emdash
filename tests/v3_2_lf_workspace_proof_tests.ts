/** Focused AI-WORKSPACE-1B1 exact-closure proof-attachment tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_PROOF_DEVELOPMENT_PROFILE,
    CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
    CORE_LF_WORKSPACE_PROOF_PROFILE,
    CoreContextError,
    CoreLfCompiledDeclarationWorkspace,
    CoreLfModuleSpec,
    CoreLfProofDevelopmentError,
    CoreLfProofDevelopmentSourceError,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    CoreLfWorkspaceProofDocumentInput,
    CoreLfWorkspaceProofError,
    binderMode,
    compileCoreLfDeclarationWorkspace,
    compileCoreLfProofDevelopment,
    compileCoreLfWorkspaceProofDocument,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanExact,
    coreProofPlanHave,
    coreProofPlanHole,
    coreProofPlanIntro,
    coreProofPlanRefine,
    coreProofTemplateBinding,
    coreProofTemplatePlaceholder,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfProofDevelopment,
    createCoreLfProofDevelopmentSourceSnapshot,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    createCoreProofArtifactFingerprint,
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelPi,
    provenance,
    parseCoreLfProofDevelopmentSourceText,
    reconstructCoreLfProofDevelopmentSourceSnapshot,
    serializeCoreLfProofDevelopmentArtifact,
    serializeCoreLfProofDevelopmentSourceSnapshot,
    serializeCoreLfWorkspaceProofArtifact,
    sourceSpan
} from '../src/v3_2';

const unrelatedModuleId = 'fixture.ai_proof_a_unrelated';
const baseModuleId = 'fixture.ai_proof_b_base';
const consumerModuleId = 'fixture.ai_proof_c_consumer';
const unrelatedCoreName = 'ai_workspace_unrelated_type';
const baseCoreName = 'ai_workspace_base_type';
const consumerCoreName = 'ai_workspace_consumer_seed';

const unrelatedSymbol = coreLfQualifiedSymbol(
    unrelatedModuleId,
    'Unrelated'
);
const baseSymbol = coreLfQualifiedSymbol(baseModuleId, 'Base');
const consumerSymbol = coreLfQualifiedSymbol(consumerModuleId, 'seed');

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;
const mode = {
    plicity: 'explicit' as const,
    variation: 'functorial' as const
};
const proofMode = binderMode('explicit', 'functorial');

const proofProvenance = (line: number, detail: string) => provenance(
    'surface',
    detail,
    sourceSpan(
        'tests/fixtures/ai_workspace_proof.ts',
        line,
        1,
        line,
        2
    )
);

interface Fixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

const typeFixture = (
    moduleId: string,
    symbol: typeof baseSymbol,
    coreName: string,
    sourceDigit: string
): Fixture => {
    const authorityPath = `tests/fixtures/${moduleId}.lp`;
    const module = createCoreLfModuleSpec({
        revision: `${moduleId.replace(/\./gu, '-')}-1`,
        moduleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash(sourceDigit),
        dependencies: [],
        externalSymbols: [],
        declarations: [{
            order: 0,
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
                sourceFragment: `symbol ${symbol.name} : TYPE;`
            }
        }],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: `${module.revision}-policy`,
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                target: { kind: 'declaration', symbol },
                policy: 'opaque-signature',
                evidence: 'AI-WORKSPACE-1B1 type fixture'
            }]
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: `${module.revision}-linkage`,
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                symbol,
                kind: 'free-declaration',
                coreName,
                backendName: symbol.name
            }]
        })
    };
};

const consumerFixture = (): Fixture => {
    const authorityPath = 'tests/fixtures/ai_workspace_consumer.lp';
    const module = createCoreLfModuleSpec({
        revision: 'ai-workspace-consumer-1',
        moduleId: consumerModuleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('c'),
        dependencies: [baseModuleId],
        externalSymbols: [{
            symbol: baseSymbol,
            availability: 'dependency-module'
        }],
        declarations: [{
            order: 0,
            symbol: consumerSymbol,
            type: { tag: 'global', symbol: baseSymbol },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque'
            },
            provenance: {
                authorityPath,
                sourceFragment: 'symbol seed : Base;'
            }
        }],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'ai-workspace-consumer-policy-1',
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: consumerSymbol
                },
                policy: 'opaque-signature',
                evidence: 'AI-WORKSPACE-1B1 dependent fixture'
            }]
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'ai-workspace-consumer-linkage-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    symbol: baseSymbol,
                    kind: 'free-declaration',
                    coreName: baseCoreName,
                    backendName: baseSymbol.name
                },
                {
                    order: 1,
                    symbol: consumerSymbol,
                    kind: 'free-declaration',
                    coreName: consumerCoreName,
                    backendName: consumerSymbol.name
                }
            ]
        })
    };
};

const compileWorkspace = (
    order: readonly ('base' | 'consumer' | 'unrelated')[] = [
        'consumer',
        'base',
        'unrelated'
    ]
): CoreLfCompiledDeclarationWorkspace => {
    const fixtures = {
        base: typeFixture(baseModuleId, baseSymbol, baseCoreName, 'b'),
        consumer: consumerFixture(),
        unrelated: typeFixture(
            unrelatedModuleId,
            unrelatedSymbol,
            unrelatedCoreName,
            'a'
        )
    };
    return compileCoreLfDeclarationWorkspace(
        createCoreLfDeclarationWorkspace({
            revision: 'ai-workspace-proof-fixture-1',
            modules: order.map(id => fixtures[id])
        })
    );
};

const fingerprint = (moduleIds: readonly string[]) =>
    createCoreProofArtifactFingerprint({
        source: {
            id: 'proofs/consumer_identity.ts',
            sha256: hash('1')
        },
        profileSha256: hash('2'),
        dependencies: moduleIds.map((moduleId, index) => ({
            moduleId,
            interfaceSha256: hash(String(index + 3))
        }))
    });

const identityTarget = () => kernelPi(
    kernelBinder(
        'value',
        kernelFree(
            baseCoreName,
            proofProvenance(10, 'AI-WORKSPACE-1B1 Base domain')
        ),
        proofMode,
        proofProvenance(10, 'AI-WORKSPACE-1B1 identity binder')
    ),
    kernelFree(
        baseCoreName,
        proofProvenance(10, 'AI-WORKSPACE-1B1 Base codomain')
    ),
    proofProvenance(10, 'AI-WORKSPACE-1B1 identity target')
);

const proofInput = (
    open: boolean,
    moduleIds: readonly string[] = [baseModuleId, consumerModuleId]
): CoreLfWorkspaceProofDocumentInput => ({
    moduleId: consumerModuleId,
    declarationId: open ? 'open_identity' : 'complete_identity',
    type: identityTarget(),
    plan: coreProofPlanIntro(
        open
            ? coreProofPlanHole('body', {
                provenance: proofProvenance(
                    12,
                    'AI-WORKSPACE-1B1 named hole'
                )
            })
            : coreProofPlanExact(kernelBound(
                0,
                proofProvenance(12, 'AI-WORKSPACE-1B1 exact variable')
            )),
        {
            name: 'value',
            provenance: proofProvenance(11, 'AI-WORKSPACE-1B1 intro')
        }
    ),
    provenance: proofProvenance(9, 'AI-WORKSPACE-1B1 proof root'),
    fingerprint: fingerprint(moduleIds)
});

const contextualHaveProofInput = (
    openFact = false
): CoreLfWorkspaceProofDocumentInput => {
    const binder = kernelBinder(
        'fact',
        kernelFree(
            baseCoreName,
            proofProvenance(13, 'PLAN-DECOMPOSE-3C1 source refine type')
        ),
        proofMode,
        proofProvenance(13, 'PLAN-DECOMPOSE-3C1 source refine binding')
    );
    const factProof = openFact
        ? coreProofPlanHole('source_fact', {
            provenance: proofProvenance(
                14,
                'PLAN-DECOMPOSE-3C1 source proof hole'
            ),
            expectation: { contextDepth: 1 }
        })
        : coreProofPlanExact(kernelBound(
            0,
            proofProvenance(14, 'PLAN-DECOMPOSE-3C1 source fact proof')
        ));
    const options = {
        id: 'source_contextual_have',
        provenance: proofProvenance(
            13,
            openFact
                ? 'PLAN-DECOMPOSE-3B1B source have'
                : 'PLAN-DECOMPOSE-3C1 source refine'
        )
    };
    const body = openFact
        ? coreProofPlanHave(
            binder,
            factProof,
            coreProofPlanExact(kernelBound(
                1,
                proofProvenance(
                    15,
                    'PLAN-DECOMPOSE-3B1B source ignores fact'
                )
            )),
            options
        )
        : coreProofPlanRefine(
            coreProofTemplatePlaceholder(
                'fact',
                proofProvenance(
                    15,
                    'PLAN-DECOMPOSE-3C1 source fact use'
                )
            ),
            [coreProofTemplateBinding(binder, factProof)],
            options
        );
    return {
        ...proofInput(false),
        plan: coreProofPlanIntro(body, {
            name: 'value',
            provenance: proofProvenance(
                11,
                'PLAN-DECOMPOSE-3B1B source intro'
            )
        })
    };
};

const expectWorkspaceProofError = (
    action: () => unknown,
    code: CoreLfWorkspaceProofError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfWorkspaceProofError &&
            error.code === code &&
            error.path.length > 0
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('AI-WORKSPACE-1B1 exact-closure proof attachment', () => {
    it('rechecks complete and open proofs in the exact dependency closure', () => {
        const workspace = compileWorkspace();
        assert.deepEqual(workspace.plan.order, [
            unrelatedModuleId,
            baseModuleId,
            consumerModuleId
        ]);
        assert.notEqual(
            workspace.module(consumerModuleId)?.compiled.environment.lookup(
                unrelatedCoreName
            ),
            undefined
        );

        const complete = compileCoreLfWorkspaceProofDocument(
            workspace,
            proofInput(false)
        );
        const open = compileCoreLfWorkspaceProofDocument(
            workspace,
            proofInput(true)
        );

        assert.deepEqual(complete.artifact.closure.order, [
            baseModuleId,
            consumerModuleId
        ]);
        assert.equal(
            complete.artifact.closure.order.includes(unrelatedModuleId),
            false
        );
        assert.equal(
            complete.proofCompilation.artifact.state.status,
            'complete'
        );
        assert.equal(complete.proofCompilation.checkedTerm?.tag, 'lambda');
        assert.equal(
            open.proofCompilation.artifact.state.status,
            'incomplete'
        );
        assert.deepEqual(
            open.proofCompilation.artifact.state.goals.map(goal => goal.id),
            ['body']
        );
        assert.equal(
            complete.closureCompilation
                .module(consumerModuleId)
                ?.compiled.environment.lookup(unrelatedCoreName),
            undefined
        );
        assert.equal(
            CORE_LF_WORKSPACE_PROOF_PROFILE.computesCryptographicHashes,
            false
        );
        assert.equal(
            CORE_LF_WORKSPACE_PROOF_PROFILE.executesIncrementally,
            false
        );
        assertDeepFrozen(complete.artifact);
    });

    it('is byte-stable across workspace input permutations', () => {
        const first = compileCoreLfWorkspaceProofDocument(
            compileWorkspace(),
            proofInput(false)
        ).artifact;
        const second = compileCoreLfWorkspaceProofDocument(
            compileWorkspace(['unrelated', 'consumer', 'base']),
            proofInput(false)
        ).artifact;

        assert.equal(
            serializeCoreLfWorkspaceProofArtifact(first),
            serializeCoreLfWorkspaceProofArtifact(second)
        );
        assert.equal(first.closureText.endsWith('\n'), true);
        const serialized = serializeCoreLfWorkspaceProofArtifact(first);
        assert.doesNotMatch(
            serialized,
            /\?m\d|sessionIdentity|coreEnvironment|checkedTerm|Symbol\(/u
        );
    });

    it('requires exactly every closure module in the fingerprint', () => {
        const workspace = compileWorkspace();
        const invalidTarget = kernelFree(
            unrelatedCoreName,
            proofProvenance(20, 'unrelated target must not execute')
        );
        const missing = {
            ...proofInput(false, [consumerModuleId]),
            type: invalidTarget
        };
        expectWorkspaceProofError(
            () => compileCoreLfWorkspaceProofDocument(workspace, missing),
            'FINGERPRINT_CLOSURE_MISMATCH'
        );
        expectWorkspaceProofError(
            () => compileCoreLfWorkspaceProofDocument(
                workspace,
                proofInput(false, [
                    baseModuleId,
                    consumerModuleId,
                    unrelatedModuleId
                ])
            ),
            'FINGERPRINT_CLOSURE_MISMATCH'
        );
    });

    it('does not expose an unrelated earlier module to proof checking', () => {
        const workspace = compileWorkspace();
        assert.throws(
            () => compileCoreLfWorkspaceProofDocument(workspace, {
                ...proofInput(true),
                declarationId: 'unrelated_target',
                type: kernelFree(
                    unrelatedCoreName,
                    proofProvenance(21, 'unrelated target')
                )
            }),
            error => error instanceof CoreContextError &&
                error.code === 'UNBOUND_FREE_REFERENCE'
        );
    });

    it('rejects reconstructed source or interface drift', () => {
        const workspace = compileWorkspace();
        const interfaceModules = workspace.modules.map(entry =>
            entry.source.module.moduleId === baseModuleId
                ? Object.freeze({
                    ...entry,
                    interfaceText: `${entry.interfaceText}drift\n`
                })
                : entry
        );
        const drifted = new CoreLfCompiledDeclarationWorkspace(
            workspace.plan,
            interfaceModules,
            workspace.environment
        );
        expectWorkspaceProofError(
            () => compileCoreLfWorkspaceProofDocument(
                drifted,
                proofInput(false)
            ),
            'CLOSURE_DRIFT'
        );

        const sourceModules = workspace.modules.map(entry =>
            entry.source.module.moduleId === baseModuleId
                ? Object.freeze({
                    ...entry,
                    sourceText: `${entry.sourceText}drift\n`
                })
                : entry
        );
        const sourceDrifted = new CoreLfCompiledDeclarationWorkspace(
            workspace.plan,
            sourceModules,
            workspace.environment
        );
        expectWorkspaceProofError(
            () => compileCoreLfWorkspaceProofDocument(
                sourceDrifted,
                proofInput(false)
            ),
            'CLOSURE_DRIFT'
        );
    });
});

const baseProofInput = (
    open: boolean
): CoreLfWorkspaceProofDocumentInput => ({
    ...proofInput(open, [baseModuleId]),
    moduleId: baseModuleId,
    declarationId: open ? 'open_base_identity' : 'base_identity'
});

const expectDevelopmentError = (
    action: () => unknown,
    code: CoreLfProofDevelopmentError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfProofDevelopmentError &&
            error.code === code &&
            error.path.length > 0
    );
};

describe('DEV-CATALOG-1 proof development catalog', () => {
    it('checks and catalogs canonically ordered independent proofs', () => {
        const plan = createCoreLfProofDevelopment({
            revision: 'proof-development-fixture-1',
            workspace: compileWorkspace().plan,
            proofs: [proofInput(false), baseProofInput(true)]
        });

        assert.deepEqual(
            plan.proofs.map(proof => [
                proof.moduleId,
                proof.declarationId
            ]),
            [
                [baseModuleId, 'open_base_identity'],
                [consumerModuleId, 'complete_identity']
            ]
        );

        const development = compileCoreLfProofDevelopment(plan);
        assert.equal(development.artifact.status, 'incomplete');
        assert.equal(development.artifact.openGoalCount, 1);
        assert.deepEqual(development.goals.map(entry => ({
            moduleId: entry.moduleId,
            declarationId: entry.declarationId,
            goalId: entry.goal.id
        })), [{
            moduleId: baseModuleId,
            declarationId: 'open_base_identity',
            goalId: 'body'
        }]);
        assert.equal(
            development.proof(
                consumerModuleId,
                'complete_identity'
            )?.proofCompilation.artifact.state.status,
            'complete'
        );
        assert.equal(
            development.proof(baseModuleId, 'absent'),
            undefined
        );
        assert.deepEqual(
            development.proof(
                baseModuleId,
                'open_base_identity'
            )?.artifact.closure.order,
            [baseModuleId]
        );
        assert.deepEqual(
            development.proof(
                consumerModuleId,
                'complete_identity'
            )?.artifact.closure.order,
            [baseModuleId, consumerModuleId]
        );
        assert.equal(
            development.artifact.workspace.order.includes(
                unrelatedModuleId
            ),
            true
        );
        assert.equal(
            development.proofs.some(proof =>
                proof.artifact.closure.order.includes(unrelatedModuleId)
            ),
            false
        );
        assert.equal(
            CORE_LF_PROOF_DEVELOPMENT_PROFILE.nodeBuiltinDependency,
            false
        );
        assert.equal(
            CORE_LF_PROOF_DEVELOPMENT_PROFILE
                .theoremDependencyPolicy,
            'independent-proof-leaves'
        );
        assertDeepFrozen(development.artifact);
        assert.equal(Object.isFrozen(development.proofs), true);
        assert.equal(Object.isFrozen(development.goals), true);
    });

    it('serializes byte-identically across source permutations', () => {
        const compile = (
            workspaceOrder:
                readonly ('base' | 'consumer' | 'unrelated')[],
            reverseProofs: boolean
        ) => {
            const proofs = [proofInput(false), baseProofInput(true)];
            if (reverseProofs) proofs.reverse();
            return compileCoreLfProofDevelopment(
                createCoreLfProofDevelopment({
                    revision: 'proof-development-fixture-1',
                    workspace: compileWorkspace(workspaceOrder).plan,
                    proofs
                })
            );
        };
        const first = compile(
            ['consumer', 'base', 'unrelated'],
            false
        );
        const second = compile(
            ['unrelated', 'consumer', 'base'],
            true
        );

        const firstText = serializeCoreLfProofDevelopmentArtifact(
            first.artifact
        );
        assert.equal(
            firstText,
            serializeCoreLfProofDevelopmentArtifact(second.artifact)
        );
        assert.equal(firstText.endsWith('\n'), true);
        assert.doesNotMatch(
            firstText,
            /\?m\d|sessionIdentity|coreEnvironment|checkedTerm|Symbol\(/u
        );
    });

    it('rejects malformed, duplicate, and ownerless proof catalogs', () => {
        const workspace = compileWorkspace().plan;
        expectDevelopmentError(
            () => createCoreLfProofDevelopment({
                revision: 'bad revision',
                workspace,
                proofs: [proofInput(false)]
            }),
            'INVALID_DEVELOPMENT'
        );
        expectDevelopmentError(
            () => createCoreLfProofDevelopment({
                revision: 'empty-proof-development-1',
                workspace,
                proofs: []
            }),
            'INVALID_DEVELOPMENT'
        );
        expectDevelopmentError(
            () => createCoreLfProofDevelopment({
                revision: 'duplicate-proof-development-1',
                workspace,
                proofs: [proofInput(false), proofInput(false)]
            }),
            'DUPLICATE_PROOF'
        );
        expectDevelopmentError(
            () => createCoreLfProofDevelopment({
                revision: 'ownerless-proof-development-1',
                workspace,
                proofs: [{
                    ...proofInput(false),
                    moduleId: 'fixture.ai_proof_missing'
                }]
            }),
            'UNKNOWN_PROOF_MODULE'
        );
        expectDevelopmentError(
            () => createCoreLfProofDevelopment({
                revision: 'invalid-proof-id-development-1',
                workspace,
                proofs: [{
                    ...proofInput(false),
                    declarationId: 'not portable'
                }]
            }),
            'INVALID_PROOF_ID'
        );
    });
});

const sourcePlan = (
    workspaceOrder:
        readonly ('base' | 'consumer' | 'unrelated')[] = [
            'consumer',
            'base',
            'unrelated'
        ],
    reverseProofs = false
) => {
    const proofs = [proofInput(false), baseProofInput(true)];
    if (reverseProofs) proofs.reverse();
    return createCoreLfProofDevelopment({
        revision: 'proof-development-source-fixture-1',
        workspace: compileWorkspace(workspaceOrder).plan,
        proofs
    });
};

const expectSourceError = (
    action: () => unknown,
    code: CoreLfProofDevelopmentSourceError['code']
): void => {
    assert.throws(
        action,
        error => error instanceof CoreLfProofDevelopmentSourceError &&
            error.code === code &&
            error.path.length > 0
    );
};

describe('DEV-CLI-2A canonical proof-development source', () => {
    it('round-trips canonical data and preserves checked artifacts', () => {
        const plan = sourcePlan();
        const expected = compileCoreLfProofDevelopment(plan);
        const snapshot = createCoreLfProofDevelopmentSourceSnapshot(plan);
        const sourceText =
            serializeCoreLfProofDevelopmentSourceSnapshot(snapshot);
        const reconstructed =
            parseCoreLfProofDevelopmentSourceText(sourceText);
        const actual = compileCoreLfProofDevelopment(reconstructed.plan);

        assert.equal(
            snapshot.revision,
            CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision
        );
        assert.equal(
            CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.hostExecutionTrusted,
            false
        );
        assert.equal(
            CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.nodeBuiltinDependency,
            false
        );
        assert.equal(reconstructed.sourceText, sourceText);
        assert.deepEqual(actual.artifact, expected.artifact);
        assert.deepEqual(
            reconstructed.plan.proofs.map(proof => [
                proof.moduleId,
                proof.declarationId
            ]),
            [
                [baseModuleId, 'open_base_identity'],
                [consumerModuleId, 'complete_identity']
            ]
        );
        assertDeepFrozen(reconstructed.snapshot);
        assertDeepFrozen(reconstructed.plan);
    });

    it('round-trips and checks the contextual have source tag', () => {
        const completePlan = createCoreLfProofDevelopment({
            revision: 'proof-development-have-source-fixture-1',
            workspace: compileWorkspace().plan,
            proofs: [contextualHaveProofInput()]
        });
        const sourceText = serializeCoreLfProofDevelopmentSourceSnapshot(
            createCoreLfProofDevelopmentSourceSnapshot(completePlan)
        );
        const reconstructed =
            parseCoreLfProofDevelopmentSourceText(sourceText);
        const proofPlan = reconstructed.plan.proofs[0].plan;

        assert.doesNotMatch(sourceText, /"tag": "(?:placeholder|refine)"/u);
        assert.equal(proofPlan.tag, 'intro');
        assert.equal(proofPlan.body.tag, 'have');
        if (proofPlan.body.tag !== 'have') {
            throw new Error('Expected reconstructed contextual have plan');
        }
        assert.equal(proofPlan.body.binding.name, 'fact');
        assert.equal(proofPlan.body.binding.mode.variation, 'functorial');
        assert.equal(
            compileCoreLfProofDevelopment(reconstructed.plan)
                .artifact.status,
            'complete'
        );

        const openPlan = createCoreLfProofDevelopment({
            revision: 'proof-development-have-source-fixture-2',
            workspace: compileWorkspace().plan,
            proofs: [contextualHaveProofInput(true)]
        });
        const openSourceText =
            serializeCoreLfProofDevelopmentSourceSnapshot(
                createCoreLfProofDevelopmentSourceSnapshot(openPlan)
            );
        const openCompilation = compileCoreLfProofDevelopment(
            parseCoreLfProofDevelopmentSourceText(openSourceText).plan
        );
        assert.equal(openCompilation.artifact.status, 'incomplete');
        assert.deepEqual(
            openCompilation.goals.map(entry => [
                entry.goal.id,
                entry.goal.reachability,
                entry.goal.occurrenceCount
            ]),
            [['source_fact', 'retained-source-obligation', 0]]
        );
    });

    it('canonicalizes module and proof input permutations byte-identically', () => {
        const first = serializeCoreLfProofDevelopmentSourceSnapshot(
            createCoreLfProofDevelopmentSourceSnapshot(sourcePlan(
                ['consumer', 'base', 'unrelated'],
                false
            ))
        );
        const second = serializeCoreLfProofDevelopmentSourceSnapshot(
            createCoreLfProofDevelopmentSourceSnapshot(sourcePlan(
                ['unrelated', 'consumer', 'base'],
                true
            ))
        );
        assert.equal(first, second);
        assert.equal(first.endsWith('\n'), true);
    });

    it('rejects malformed, noncanonical, and unsupported source data', () => {
        const snapshot = createCoreLfProofDevelopmentSourceSnapshot(
            sourcePlan()
        );
        const sourceText =
            serializeCoreLfProofDevelopmentSourceSnapshot(snapshot);
        const clone = (): any => JSON.parse(sourceText);

        const staleRevision = clone();
        staleRevision.revision =
            'emdash-lf-proof-development-source-v1';
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                staleRevision
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        expectSourceError(
            () => parseCoreLfProofDevelopmentSourceText('{'),
            'INVALID_SOURCE_TEXT'
        );
        expectSourceError(
            () => parseCoreLfProofDevelopmentSourceText(
                `${JSON.stringify(JSON.parse(sourceText), null, 2)}\n`
            ),
            'NONCANONICAL_SOURCE_TEXT'
        );

        const reversed = clone();
        reversed.proofs.reverse();
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(reversed),
            'NONCANONICAL_SOURCE_SNAPSHOT'
        );

        const extra = clone();
        extra.ambientRegistry = 'forbidden';
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(extra),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const accessor = clone();
        let accessorInvoked = false;
        Object.defineProperty(accessor, 'ambientRegistry', {
            enumerable: true,
            get: () => {
                accessorInvoked = true;
                return 'forbidden';
            }
        });
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(accessor),
            'INVALID_SOURCE_SNAPSHOT'
        );
        assert.equal(accessorInvoked, false);

        const sparse = clone();
        delete sparse.proofs[0];
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(sparse),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const unknownPlan = clone();
        unknownPlan.proofs[0].plan.tag = 'run_tactic_callback';
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                unknownPlan
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const missingType = clone();
        delete missingType.proofs[0].type;
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                missingType
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const unknownExpression = clone();
        const unknownExpressionProof = unknownExpression.proofs.find(
            (proof: any) => proof.declarationId === 'complete_identity'
        );
        unknownExpressionProof.plan.body.solution.tag = 'host_callback';
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                unknownExpression
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const danglingBound = clone();
        danglingBound.proofs[0].type = {
            tag: 'bound',
            index: 0,
            provenance: danglingBound.proofs[0].provenance
        };
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                danglingBound
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const withMeta = clone();
        const complete = withMeta.proofs.find(
            (proof: any) => proof.declarationId === 'complete_identity'
        );
        complete.plan.body.solution = {
            tag: 'meta',
            identity: { index: 0 },
            spine: [],
            provenance: complete.plan.body.provenance
        };
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(withMeta),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const directPlan = sourcePlan();
        const directMetaPlan = {
            ...directPlan,
            proofs: directPlan.proofs.map(proof =>
                proof.declarationId === 'complete_identity'
                    ? {
                        ...proof,
                        plan: {
                            tag: 'exact',
                            provenance: proof.provenance,
                            solution: {
                                tag: 'meta',
                                identity: {
                                    session: Symbol('process-local'),
                                    index: 0
                                },
                                spine: [],
                                provenance: proof.provenance
                            }
                        }
                    }
                    : proof
            )
        };
        expectSourceError(
            () => createCoreLfProofDevelopmentSourceSnapshot(
                directMetaPlan as any
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const badProvenance = clone();
        badProvenance.proofs[0].provenance.origin = 'ambient-agent';
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                badProvenance
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );

        const badFingerprint = clone();
        badFingerprint.proofs[0].fingerprint.revision = 'future-inputs';
        expectSourceError(
            () => reconstructCoreLfProofDevelopmentSourceSnapshot(
                badFingerprint
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );
    });
});
