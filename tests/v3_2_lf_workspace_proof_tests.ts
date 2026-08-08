/** Focused AI-WORKSPACE-1B1 exact-closure proof-attachment tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_WORKSPACE_PROOF_PROFILE,
    CoreContextError,
    CoreLfCompiledDeclarationWorkspace,
    CoreLfModuleSpec,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    CoreLfWorkspaceProofDocumentInput,
    CoreLfWorkspaceProofError,
    binderMode,
    compileCoreLfDeclarationWorkspace,
    compileCoreLfWorkspaceProofDocument,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreProofPlanExact,
    coreProofPlanHole,
    coreProofPlanIntro,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    createCoreProofArtifactFingerprint,
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelPi,
    provenance,
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
