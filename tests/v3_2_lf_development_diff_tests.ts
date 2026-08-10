/** Focused REFACTOR-9A/9B two-revision maintenance tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfModuleSpec,
    CoreLfProofDevelopmentSourceSnapshot,
    CORE_LF_PROOF_MAINTENANCE_PROFILE,
    CoreLfProofMaintenanceError,
    CoreLfProofMaintenanceIdentity,
    CoreLfProofRepairProposal,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    CoreLfWorkspaceProofDocumentInput,
    CORE_LF_DEVELOPMENT_DIFF_PROFILE,
    CoreLfDevelopmentDiffError,
    CoreLfDevelopmentSemanticDiffReport,
    binderMode,
    compileCoreLfProofDevelopment,
    compareCoreLfProofDevelopmentSources,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    coreProofPlanExact,
    coreProofPlanHole,
    coreProofPlanIntro,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfProofDevelopment,
    createCoreLfProofDevelopmentSourceSnapshot,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    createCoreProofArtifactFingerprint,
    inspectCoreLfProofMaintenance,
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelPi,
    provenance,
    proposeCoreLfProofRepairs,
    reconstructCoreLfProofDevelopmentSourceSnapshot,
    replayCoreLfProofRepairCandidate,
    serializeCoreLfDevelopmentSemanticDiff,
    serializeCoreLfProofMaintenanceInspection,
    serializeCoreLfProofRepairCandidateReplay,
    serializeCoreLfProofRepairProposal,
    sourceSpan
} from '../src/v3_2';
import './v3_2_proof_agent_benchmark_tests';

const changedModuleId = 'fixture.diff_changed';
const controlModuleId = 'fixture.diff_control';
const changedPath = 'tests/fixtures/diff_changed.lp';
const controlPath = 'tests/fixtures/diff_control.lp';

const q = coreLfQualifiedSymbol(changedModuleId, 'Q');
const r = coreLfQualifiedSymbol(changedModuleId, 'R');
const alias = coreLfQualifiedSymbol(changedModuleId, 'Alias');
const family = coreLfQualifiedSymbol(changedModuleId, 'Family');
const witness = coreLfQualifiedSymbol(changedModuleId, 'witness');
const dependent = coreLfQualifiedSymbol(changedModuleId, 'Dependent');
const gone = coreLfQualifiedSymbol(changedModuleId, 'Gone');
const fresh = coreLfQualifiedSymbol(changedModuleId, 'Fresh');
const control = coreLfQualifiedSymbol(controlModuleId, 'Control');
const controlWitness = coreLfQualifiedSymbol(controlModuleId, 'control_witness');

const qCore = 'diff_q';
const rCore = 'diff_r';
const aliasCore = 'diff_alias';
const familyCore = 'diff_family';
const witnessCore = 'diff_witness';
const dependentCore = 'diff_dependent';
const renameCore = 'diff_rename_candidate';
const controlCore = 'diff_control_type';
const controlWitnessCore = 'diff_control_witness';

const mode = {
    plicity: 'explicit' as const,
    variation: 'functorial' as const
};
const proofMode = binderMode('explicit', 'functorial');

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;
const global = (
    symbol: { readonly moduleId: string; readonly name: string }
) => ({ tag: 'global' as const, symbol });
const transferSource = (
    authorityPath: string,
    sourceFragment: string
) => ({ authorityPath, sourceFragment });

interface Fixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

const changedFixture = (
    version: 'previous' | 'current',
    breakDeclarationCompilation = false,
    revisionSuffix = ''
): Fixture => {
    const renamed = version === 'previous' ? gone : fresh;
    const aliasTarget = version === 'previous' ? q : r;
    const baseRevision = version === 'previous'
        ? 'diff-changed-previous'
        : 'diff-changed-current';
    const revision = `${baseRevision}${revisionSuffix}`;
    const declarations = [
        {
            order: 0,
            symbol: q,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource(changedPath, 'symbol Q : TYPE;')
        },
        {
            order: 1,
            symbol: r,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource(changedPath, 'symbol R : TYPE;')
        },
        {
            order: 2,
            symbol: alias,
            type: { tag: 'type' as const },
            body: coreLfTransferExplicitBody(global(
                breakDeclarationCompilation ? witness : aliasTarget
            )),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'transparent' as const
            },
            provenance: transferSource(
                changedPath,
                `symbol Alias : TYPE ≔ ${aliasTarget.name};`
            )
        },
        {
            order: 3,
            symbol: family,
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'value',
                    mode,
                    type: global(alias)
                },
                body: { tag: 'type' as const }
            },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource(
                changedPath,
                'symbol Family (value : Alias) : TYPE;'
            )
        },
        {
            order: 4,
            symbol: witness,
            type: global(alias),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource(
                changedPath,
                'symbol witness : Alias;'
            )
        },
        {
            order: 5,
            symbol: dependent,
            type: { tag: 'type' as const },
            body: coreLfTransferExplicitBody({
                tag: 'call',
                callee: global(family),
                arguments: [{
                    plicity: 'explicit',
                    value: global(witness)
                }]
            }),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'transparent' as const
            },
            provenance: transferSource(
                changedPath,
                'symbol Dependent : TYPE ≔ Family witness;'
            )
        },
        {
            order: 6,
            symbol: renamed,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public' as const,
                rigidity: 'ordinary' as const,
                sourceOpacity: 'opaque' as const
            },
            provenance: transferSource(
                changedPath,
                `symbol ${renamed.name} : TYPE;`
            )
        }
    ];
    const module = createCoreLfModuleSpec({
        revision,
        moduleId: changedModuleId,
        fragmentId: 'declarations',
        authorityPath: changedPath,
        sourceSha256: hash(version === 'previous' ? 'a' : 'b'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const transparent = new Set([alias.name, dependent.name]);
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: `${revision}-policy`,
        moduleRevision: module.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: transparent.has(declaration.symbol.name)
                ? 'checked-transparent-definition' as const
                : 'opaque-signature' as const,
            evidence: 'REFACTOR-9A standalone fixture'
        }))
    });
    const coreNames = new Map([
        [q.name, qCore],
        [r.name, rCore],
        [alias.name, aliasCore],
        [family.name, familyCore],
        [witness.name, witnessCore],
        [dependent.name, dependentCore],
        [renamed.name, renameCore]
    ]);
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: `${revision}-linkage`,
        moduleRevision: module.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            symbol: declaration.symbol,
            kind: 'free-declaration' as const,
            coreName: coreNames.get(declaration.symbol.name) as string,
            backendName: declaration.symbol.name
        }))
    });
    return { module, policy, linkage };
};

const controlFixture = (): Fixture => {
    const module = createCoreLfModuleSpec({
        revision: 'diff-control-1',
        moduleId: controlModuleId,
        fragmentId: 'declarations',
        authorityPath: controlPath,
        sourceSha256: hash('c'),
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: control,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: transferSource(
                    controlPath,
                    'symbol Control : TYPE;'
                )
            },
            {
                order: 1,
                symbol: controlWitness,
                type: global(control),
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: transferSource(
                    controlPath,
                    'symbol control_witness : Control;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'diff-control-policy-1',
            moduleRevision: module.revision,
            entries: module.declarations.map(declaration => ({
                order: declaration.order,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: 'opaque-signature' as const,
                evidence: 'REFACTOR-9A independent control'
            }))
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'diff-control-linkage-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    symbol: control,
                    kind: 'free-declaration',
                    coreName: controlCore,
                    backendName: control.name
                },
                {
                    order: 1,
                    symbol: controlWitness,
                    kind: 'free-declaration',
                    coreName: controlWitnessCore,
                    backendName: controlWitness.name
                }
            ]
        })
    };
};

const proofProvenance = (
    line: number,
    detail: string
) => provenance(
    'surface',
    detail,
    sourceSpan('tests/fixtures/diff_proofs.ts', line, 1, line, 2)
);

const fingerprint = (
    moduleId: string,
    sourceId: string,
    digit: string
) => createCoreProofArtifactFingerprint({
    source: { id: sourceId, sha256: hash(digit) },
    profileSha256: hash('f'),
    dependencies: [{ moduleId, interfaceSha256: hash('e') }]
});

const exactProof = (
    moduleId: string,
    declarationId: string,
    typeName: string,
    witnessName: string,
    line: number
): CoreLfWorkspaceProofDocumentInput => ({
    moduleId,
    declarationId,
    type: kernelFree(
        typeName,
        proofProvenance(line, `${declarationId} target`)
    ),
    plan: coreProofPlanExact(
        kernelFree(
            witnessName,
            proofProvenance(line, `${declarationId} witness`)
        ),
        { provenance: proofProvenance(line, `${declarationId} exact`) }
    ),
    provenance: proofProvenance(line, declarationId),
    fingerprint: fingerprint(
        moduleId,
        `proofs/${declarationId}.ts`,
        String(line % 10)
    )
});

const impactedProof = (): CoreLfWorkspaceProofDocumentInput => exactProof(
    changedModuleId,
    'aa_uses_witness',
    qCore,
    witnessCore,
    11
);

const controlProof = (): CoreLfWorkspaceProofDocumentInput => ({
    moduleId: controlModuleId,
    declarationId: 'control_identity',
    type: kernelPi(
        kernelBinder(
            'value',
            kernelFree(
                controlCore,
                proofProvenance(20, 'control identity domain')
            ),
            proofMode,
            proofProvenance(20, 'control identity binder')
        ),
        kernelFree(
            controlCore,
            proofProvenance(20, 'control identity codomain')
        ),
        proofProvenance(20, 'control identity type')
    ),
    plan: coreProofPlanIntro(
        coreProofPlanExact(
            kernelBound(0, proofProvenance(21, 'introduced value')),
            { provenance: proofProvenance(21, 'control exact') }
        ),
        {
            name: 'value',
            provenance: proofProvenance(21, 'control intro')
        }
    ),
    provenance: proofProvenance(20, 'control identity'),
    fingerprint: fingerprint(
        controlModuleId,
        'proofs/control_identity.ts',
        '2'
    )
});

const editedProof = (
    version: 'previous' | 'current'
): CoreLfWorkspaceProofDocumentInput => {
    const base = exactProof(
        controlModuleId,
        'edited',
        controlCore,
        controlWitnessCore,
        30
    );
    if (version === 'previous') return base;
    return {
        ...base,
        type: kernelFree(
            controlCore,
            proofProvenance(31, 'edited current target')
        ),
        plan: coreProofPlanHole('edited_goal', {
            provenance: proofProvenance(31, 'edited current hole')
        }),
        provenance: proofProvenance(31, 'edited current source'),
        fingerprint: fingerprint(
            controlModuleId,
            'proofs/edited-current.ts',
            '3'
        )
    };
};

const identityMoveProof = (
    declarationId: 'rename_old' | 'rename_new'
): CoreLfWorkspaceProofDocumentInput => exactProof(
    controlModuleId,
    declarationId,
    controlCore,
    controlWitnessCore,
    40
);

const unresolvedAddedProof = (): CoreLfWorkspaceProofDocumentInput => ({
    moduleId: controlModuleId,
    declarationId: 'zz_unresolved',
    type: kernelFree(
        controlCore,
        proofProvenance(50, 'unresolved proof target')
    ),
    plan: coreProofPlanHole('unresolved_goal', {
        expectation: {
            contextDepth: 0,
            target: kernelFree(
                'diff_missing_reference',
                proofProvenance(50, 'deliberately unresolved expectation')
            )
        },
        provenance: proofProvenance(50, 'unresolved source hole')
    }),
    provenance: proofProvenance(50, 'unresolved added proof'),
    fingerprint: fingerprint(
        controlModuleId,
        'proofs/zz_unresolved.ts',
        '5'
    )
});

const sourceSnapshot = (
    version: 'previous' | 'current',
    reverseModules = false,
    reverseProofs = false,
    breakDeclarationCompilation = false,
    changedRevisionSuffix = ''
) => {
    const modules = [
        changedFixture(
            version,
            breakDeclarationCompilation,
            changedRevisionSuffix
        ),
        controlFixture()
    ];
    const proofs: CoreLfWorkspaceProofDocumentInput[] = version === 'previous'
        ? [
            impactedProof(),
            controlProof(),
            editedProof(version),
            identityMoveProof('rename_old')
        ]
        : [
            impactedProof(),
            controlProof(),
            editedProof(version),
            identityMoveProof('rename_new'),
            unresolvedAddedProof()
        ];
    const workspace = createCoreLfDeclarationWorkspace({
        revision: `diff-workspace-${version}`,
        modules: reverseModules ? [...modules].reverse() : modules
    });
    return createCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopment({
            revision: `diff-development-${version}`,
            workspace,
            proofs: reverseProofs ? [...proofs].reverse() : proofs
        })
    );
};

const reportFixture = (): CoreLfDevelopmentSemanticDiffReport =>
    compareCoreLfProofDevelopmentSources(
        sourceSnapshot('previous'),
        sourceSnapshot('current')
    );

const qualified = (
    moduleId: string,
    name: string
) => ({ moduleId, name });

const findDeclaration = (
    report: CoreLfDevelopmentSemanticDiffReport,
    name: string
) => report.declarations.find(declaration =>
    declaration.symbol.moduleId === changedModuleId &&
    declaration.symbol.name === name
);

const findProof = (
    report: CoreLfDevelopmentSemanticDiffReport,
    declarationId: string
) => report.proofs.find(proof =>
    proof.proof.declarationId === declarationId
);

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectDiffError = (
    action: () => unknown,
    code: CoreLfDevelopmentDiffError['code']
): void => assert.throws(
    action,
    error => error instanceof CoreLfDevelopmentDiffError &&
        error.code === code &&
        error.path.length > 0
);

const proofIdentity = (
    moduleId: string,
    declarationId: string
): CoreLfProofMaintenanceIdentity => ({ moduleId, declarationId });

const replaceSourceProof = (
    source: CoreLfProofDevelopmentSourceSnapshot,
    declarationId: string,
    update: (
        proof: CoreLfWorkspaceProofDocumentInput
    ) => CoreLfWorkspaceProofDocumentInput
): CoreLfProofDevelopmentSourceSnapshot => {
    const reconstructed = reconstructCoreLfProofDevelopmentSourceSnapshot(
        source
    );
    return createCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopment({
            revision: reconstructed.plan.revision,
            workspace: reconstructed.plan.workspace,
            proofs: reconstructed.plan.proofs.map(proof =>
                proof.declarationId === declarationId
                    ? update(proof)
                    : proof
            )
        })
    );
};

const reviseSourceDevelopment = (
    source: CoreLfProofDevelopmentSourceSnapshot,
    revision: string
): CoreLfProofDevelopmentSourceSnapshot => {
    const reconstructed = reconstructCoreLfProofDevelopmentSourceSnapshot(
        source
    );
    return createCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopment({
            revision,
            workspace: reconstructed.plan.workspace,
            proofs: reconstructed.plan.proofs
        })
    );
};

const expectMaintenanceError = (
    action: () => unknown,
    code: CoreLfProofMaintenanceError['code']
): void => assert.throws(
    action,
    error => error instanceof CoreLfProofMaintenanceError &&
        error.code === code &&
        error.path.length > 0
);

describe('REFACTOR-9A semantic development diff', () => {
    it('reports exact declaration changes and structural impact', () => {
        const report = reportFixture();
        assert.equal(report.repairPolicy, 'repair-not-proposed');
        assert.equal(report.compilesProofs, false);
        assert.equal(report.executesIncrementally, false);
        assert.deepEqual(report.moduleInvalidation.changedModuleIds, [
            changedModuleId
        ]);
        assert.deepEqual(report.moduleInvalidation.reusableModuleIds, [
            controlModuleId
        ]);

        assert.equal(findDeclaration(report, 'Alias')?.state, 'changed');
        assert.deepEqual(
            findDeclaration(report, 'Alias')?.changedFields,
            ['body']
        );
        assert.equal(findDeclaration(report, 'Gone')?.state, 'removed');
        assert.equal(findDeclaration(report, 'Fresh')?.state, 'added');
        assert.equal(findDeclaration(report, 'witness')?.state, 'reusable');
        assert.equal(findDeclaration(report, 'Dependent')?.state, 'reusable');

        const aliasImpact = report.declarationImpacts.find(impact =>
            impact.source.moduleId === changedModuleId &&
            impact.source.name === 'Alias'
        );
        assert.deepEqual(aliasImpact?.directDependents, [
            qualified(changedModuleId, 'Family'),
            qualified(changedModuleId, 'witness')
        ]);
        assert.deepEqual(aliasImpact?.transitiveDependents, [
            qualified(changedModuleId, 'Dependent')
        ]);
        assert.equal(
            report.declarationDependencies.union.edges.some(edge =>
                edge.dependent.name === 'Dependent' &&
                edge.dependency.name === 'witness'
            ),
            true
        );
        assert.equal(report.counts.addedDeclarations, 1);
        assert.equal(report.counts.removedDeclarations, 1);
        assert.equal(report.counts.changedDeclarations, 1);
    });

    it('keeps proof source diff, impact, and validity separate', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        assert.doesNotThrow(() => compileCoreLfProofDevelopment(
            reconstructCoreLfProofDevelopmentSourceSnapshot(previous).plan
        ));
        assert.throws(() => compileCoreLfProofDevelopment(
            reconstructCoreLfProofDevelopmentSourceSnapshot(current).plan
        ));

        const report = compareCoreLfProofDevelopmentSources(
            previous,
            current
        );
        const impacted = findProof(report, 'aa_uses_witness');
        assert.equal(impacted?.state, 'recheck-required');
        assert.deepEqual(impacted?.changedFields, []);
        assert.equal(
            impacted?.reasons.some(reason =>
                reason.kind === 'module-not-reusable' &&
                reason.moduleId === changedModuleId &&
                reason.state === 'changed'
            ),
            true
        );
        assert.equal(
            impacted?.reasons.some(reason =>
                reason.kind === 'declaration-impacted' &&
                reason.declaration.name === 'Alias' &&
                reason.relationship === 'transitive' &&
                reason.directDependency.name === 'witness'
            ),
            true
        );
        assert.equal(findProof(report, 'control_identity')?.state, 'reusable');
        assert.deepEqual(findProof(report, 'edited')?.changedFields, [
            'type',
            'plan',
            'provenance',
            'fingerprint'
        ]);
        assert.equal(findProof(report, 'edited')?.state, 'source-changed');
        assert.equal(findProof(report, 'rename_old')?.state, 'removed');
        assert.equal(findProof(report, 'rename_new')?.state, 'added');
    });

    it('records unresolved source evidence without guessing a declaration', () => {
        const report = reportFixture();
        const unresolved = findProof(report, 'zz_unresolved');
        assert.equal(unresolved?.state, 'added');
        const reference = unresolved?.current?.dependencies.resolutions.find(
            resolution => resolution.kind === 'free-reference' &&
                resolution.name === 'diff_missing_reference'
        );
        assert.equal(reference?.status, 'unresolved');
        assert.deepEqual(reference?.candidates, []);
        assert.deepEqual(
            unresolved?.current?.dependencies.declarationDependencies,
            [qualified(controlModuleId, 'Control')]
        );
    });

    it('is canonical under source permutation and deeply immutable', () => {
        const first = reportFixture();
        const second = compareCoreLfProofDevelopmentSources(
            sourceSnapshot('previous', true, true),
            sourceSnapshot('current', true, true)
        );
        assert.equal(
            serializeCoreLfDevelopmentSemanticDiff(first),
            serializeCoreLfDevelopmentSemanticDiff(second)
        );
        assert.equal(
            serializeCoreLfDevelopmentSemanticDiff(first).endsWith('\n'),
            true
        );
        assertDeepFrozen(first);
        assert.equal(
            CORE_LF_DEVELOPMENT_DIFF_PROFILE.nodeBuiltinDependency,
            false
        );
        assert.equal(
            CORE_LF_DEVELOPMENT_DIFF_PROFILE.productionLambdapiDependency,
            false
        );
        assert.equal(first.visitBudget.expressionNodesVisited > 0, true);
    });

    it('rejects unsafe budgets and malformed cyclic canonical source', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        expectDiffError(
            () => compareCoreLfProofDevelopmentSources(
                previous,
                current,
                { expressionVisitLimit: 0 }
            ),
            'INVALID_EXPRESSION_VISIT_LIMIT'
        );
        expectDiffError(
            () => compareCoreLfProofDevelopmentSources(
                previous,
                current,
                { expressionVisitLimit: 1 }
            ),
            'EXPRESSION_VISIT_LIMIT_EXCEEDED'
        );

        const malformed = JSON.parse(JSON.stringify(previous)) as {
            proofs: Array<{ type: unknown }>;
        };
        const cyclic: { tag: string; self?: unknown } = { tag: 'universe' };
        cyclic.self = cyclic;
        malformed.proofs[0].type = cyclic;
        expectDiffError(
            () => compareCoreLfProofDevelopmentSources(
                malformed as unknown as typeof previous,
                current
            ),
            'INVALID_PREVIOUS_SOURCE'
        );
    });

    it('separates malformed source from declaration-compilation failure', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        const broken = sourceSnapshot('current', false, false, true);
        expectDiffError(
            () => compareCoreLfProofDevelopmentSources(
                previous,
                broken as unknown as typeof current
            ),
            'CURRENT_DECLARATION_COMPILATION_FAILED'
        );

        const unknownRoot = JSON.parse(JSON.stringify(current)) as {
            proofs: Array<{ moduleId: string }>;
        };
        unknownRoot.proofs[0].moduleId = 'fixture.diff_absent';
        expectDiffError(
            () => compareCoreLfProofDevelopmentSources(
                previous,
                unknownRoot as unknown as typeof current
            ),
            'INVALID_CURRENT_SOURCE'
        );
    });
});

describe('REFACTOR-9B selected-proof maintenance', () => {
    const controlIdentity = proofIdentity(
        controlModuleId,
        'control_identity'
    );
    const editedIdentity = proofIdentity(controlModuleId, 'edited');
    const impactedIdentity = proofIdentity(
        changedModuleId,
        'aa_uses_witness'
    );
    const removedIdentity = proofIdentity(controlModuleId, 'rename_old');
    const unresolvedIdentity = proofIdentity(
        controlModuleId,
        'zz_unresolved'
    );

    it('classifies complete, incomplete, rejected, and absent proofs', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        const complete = inspectCoreLfProofMaintenance({
            previousSource: previous,
            currentSource: current,
            proof: controlIdentity
        });
        const incomplete = inspectCoreLfProofMaintenance({
            previousSource: previous,
            currentSource: current,
            proof: editedIdentity
        });
        const rejected = inspectCoreLfProofMaintenance({
            previousSource: previous,
            currentSource: current,
            proof: impactedIdentity
        });
        const absent = inspectCoreLfProofMaintenance({
            previousSource: previous,
            currentSource: current,
            proof: removedIdentity
        });
        const unresolved = inspectCoreLfProofMaintenance({
            previousSource: previous,
            currentSource: current,
            proof: unresolvedIdentity
        });

        assert.equal(complete.outcome, 'checked-complete');
        if (complete.outcome === 'checked-complete') {
            assert.equal(
                complete.artifact.proofArtifact.state.status,
                'complete'
            );
            assert.deepEqual(complete.goalGraph.nodes, []);
        }
        assert.equal(incomplete.outcome, 'checked-incomplete');
        if (incomplete.outcome === 'checked-incomplete') {
            assert.deepEqual(
                incomplete.artifact.proofArtifact.state.goals.map(
                    goal => goal.id
                ),
                ['edited_goal']
            );
            assert.deepEqual(
                incomplete.goalGraph.nodes.map(node => node.id),
                ['edited_goal']
            );
        }
        assert.equal(rejected.outcome, 'rejected');
        if (rejected.outcome === 'rejected') {
            assert.equal(rejected.diagnostic.family, 'checker');
            assert.equal(rejected.diagnostic.code, 'TYPE_MISMATCH');
            assert.deepEqual(
                Object.keys(rejected.diagnostic).sort(),
                ['code', 'family', 'provenance']
            );
        }
        assert.equal(absent.outcome, 'absent-current');
        assert.equal(unresolved.outcome, 'rejected');
        if (unresolved.outcome === 'rejected') {
            assert.equal(unresolved.diagnostic.family, 'context');
            assert.equal(
                unresolved.diagnostic.code,
                'UNBOUND_FREE_REFERENCE'
            );
            assert.deepEqual(
                Object.keys(unresolved.diagnostic).sort(),
                ['code', 'family', 'provenance']
            );
        }
        assert.equal(
            serializeCoreLfProofMaintenanceInspection(rejected)
                .includes('"message"'),
            false
        );
        assert.equal(
            serializeCoreLfProofMaintenanceInspection(incomplete),
            serializeCoreLfProofMaintenanceInspection(
                inspectCoreLfProofMaintenance({
                    previousSource: previous,
                    currentSource: current,
                    proof: editedIdentity
                })
            )
        );
        assert.equal(complete.compilesCompleteDevelopment, false);
        assertDeepFrozen(complete);
        assertDeepFrozen(incomplete);
        assertDeepFrozen(rejected);
        assertDeepFrozen(absent);
    });

    it('proposes and freshly replays a checked exact hole replacement', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        const input = {
            previousSource: previous,
            currentSource: current,
            proof: editedIdentity,
            goalId: 'edited_goal'
        };
        const proposal = proposeCoreLfProofRepairs(input);

        assert.equal(proposal.provider.candidates.length, 1);
        assert.equal(proposal.provider.candidates[0].operation, 'exact');
        assert.deepEqual(proposal.provider.candidates[0].premise.symbol, {
            moduleId: controlModuleId,
            name: 'control_witness'
        });
        assert.equal(proposal.materializesUpdatedSource, false);
        assert.equal(
            serializeCoreLfProofRepairProposal(proposal),
            serializeCoreLfProofRepairProposal(
                proposeCoreLfProofRepairs(input)
            )
        );
        assertDeepFrozen(proposal);

        const replay = replayCoreLfProofRepairCandidate({
            previousSource: previous,
            currentSource: current,
            proposal,
            candidateIndex: 0
        });
        const repeatedReplay = replayCoreLfProofRepairCandidate({
            previousSource: previous,
            currentSource: current,
            proposal,
            candidateIndex: 0
        });
        assert.equal(replay.snapshot.result.status, 'complete');
        assert.equal(replay.snapshot.meaning, 'candidate-replayed');
        assert.equal(replay.snapshot.materializesUpdatedSource, false);
        assert.equal(replay.plan.tag, 'exact');
        assert.equal(
            replay.patch.revision,
            CORE_LF_PROOF_MAINTENANCE_PROFILE.patchRevision
        );
        assert.equal(
            serializeCoreLfProofRepairCandidateReplay(replay.snapshot),
            serializeCoreLfProofRepairCandidateReplay(
                repeatedReplay.snapshot
            )
        );
        assertDeepFrozen(replay.snapshot);
    });

    it('reports an exhausted checked search without inventing a repair', () => {
        const previous = sourceSnapshot('previous');
        const current = replaceSourceProof(
            sourceSnapshot('current'),
            'edited',
            proof => ({
                ...proof,
                type: kernelPi(
                    kernelBinder(
                        'argument',
                        kernelFree(
                            controlCore,
                            proofProvenance(61, 'no-candidate domain')
                        ),
                        proofMode,
                        proofProvenance(61, 'no-candidate binder')
                    ),
                    kernelFree(
                        controlCore,
                        proofProvenance(61, 'no-candidate codomain')
                    ),
                    proofProvenance(61, 'no-candidate target')
                ),
                provenance: proofProvenance(61, 'no-candidate proof'),
                fingerprint: fingerprint(
                    controlModuleId,
                    'proofs/edited-no-candidate.ts',
                    '6'
                )
            })
        );
        const proposal = proposeCoreLfProofRepairs({
            previousSource: previous,
            currentSource: current,
            proof: editedIdentity,
            goalId: 'edited_goal'
        });

        assert.deepEqual(proposal.provider.candidates, []);
        assert.equal(proposal.provider.termination, 'exhausted-search');
        expectMaintenanceError(
            () => replayCoreLfProofRepairCandidate({
                previousSource: previous,
                currentSource: current,
                proposal,
                candidateIndex: 0
            }),
            'INVALID_CANDIDATE_INDEX'
        );
    });

    it('rejects stale baselines, fingerprints, and forged reports', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        const proposal = proposeCoreLfProofRepairs({
            previousSource: previous,
            currentSource: current,
            proof: editedIdentity,
            goalId: 'edited_goal'
        });
        const stalePrevious = reviseSourceDevelopment(
            previous,
            'diff-development-previous-stale'
        );
        const staleCurrent = reviseSourceDevelopment(
            current,
            'diff-development-current-stale'
        );
        const staleDeclarationBaseline = sourceSnapshot(
            'current',
            false,
            false,
            false,
            '-stale'
        );
        const staleFingerprint = replaceSourceProof(
            current,
            'edited',
            proof => ({
                ...proof,
                fingerprint: fingerprint(
                    controlModuleId,
                    'proofs/edited-current.ts',
                    '9'
                )
            })
        );
        const changedReplay = replaceSourceProof(
            current,
            'edited',
            proof => ({
                ...proof,
                plan: coreProofPlanExact(
                    kernelFree(
                        controlWitnessCore,
                        proofProvenance(92, 'changed replay witness')
                    ),
                    {
                        provenance: proofProvenance(
                            92,
                            'changed replay exact'
                        )
                    }
                ),
                provenance: proofProvenance(92, 'changed replay proof'),
                fingerprint: fingerprint(
                    controlModuleId,
                    'proofs/edited-changed-replay.ts',
                    '8'
                )
            })
        );
        const forged = {
            ...proposal,
            provider: {
                ...proposal.provider,
                counts: {
                    ...proposal.provider.counts,
                    candidates: proposal.provider.counts.candidates + 1
                }
            }
        } as CoreLfProofRepairProposal;

        for (const variant of [
            { previousSource: stalePrevious, currentSource: current },
            { previousSource: previous, currentSource: staleCurrent },
            { previousSource: previous, currentSource: staleFingerprint },
            { previousSource: previous, currentSource: changedReplay },
            {
                previousSource: previous,
                currentSource: staleDeclarationBaseline
            }
        ]) {
            expectMaintenanceError(
                () => replayCoreLfProofRepairCandidate({
                    ...variant,
                    proposal,
                    candidateIndex: 0
                }),
                'STALE_PROPOSAL'
            );
        }
        expectMaintenanceError(
            () => replayCoreLfProofRepairCandidate({
                previousSource: previous,
                currentSource: current,
                proposal: forged,
                candidateIndex: 0
            }),
            'STALE_PROPOSAL'
        );
    });

    it('refuses non-hole states and malformed candidate requests', () => {
        const previous = sourceSnapshot('previous');
        const current = sourceSnapshot('current');
        for (const proof of [
            controlIdentity,
            impactedIdentity,
            removedIdentity
        ]) {
            expectMaintenanceError(
                () => proposeCoreLfProofRepairs({
                    previousSource: previous,
                    currentSource: current,
                    proof,
                    goalId: 'edited_goal'
                }),
                'PROOF_NOT_REPAIRABLE'
            );
        }
        const proposal = proposeCoreLfProofRepairs({
            previousSource: previous,
            currentSource: current,
            proof: editedIdentity,
            goalId: 'edited_goal'
        });
        expectMaintenanceError(
            () => replayCoreLfProofRepairCandidate({
                previousSource: previous,
                currentSource: current,
                proposal,
                candidateIndex: -1
            }),
            'INVALID_CANDIDATE_INDEX'
        );
        expectMaintenanceError(
            () => replayCoreLfProofRepairCandidate({
                previousSource: previous,
                currentSource: current,
                proposal: {
                    ...proposal,
                    revision: 'forged-revision'
                } as unknown as CoreLfProofRepairProposal,
                candidateIndex: 0
            }),
            'INVALID_PROPOSAL'
        );
        expectMaintenanceError(
            () => proposeCoreLfProofRepairs({
                previousSource: previous,
                currentSource: current,
                proof: editedIdentity,
                goalId: 'closed_goal'
            }),
            'GOAL_NOT_OPEN'
        );
        expectMaintenanceError(
            () => inspectCoreLfProofMaintenance({
                previousSource: previous,
                currentSource: current,
                proof: proofIdentity(controlModuleId, 'unknown_proof')
            }),
            'UNKNOWN_PROOF'
        );
    });
});
