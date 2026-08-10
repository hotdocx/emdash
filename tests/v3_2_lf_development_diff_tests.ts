/** Focused REFACTOR-9A two-revision semantic-maintenance tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfModuleSpec,
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
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelPi,
    provenance,
    reconstructCoreLfProofDevelopmentSourceSnapshot,
    serializeCoreLfDevelopmentSemanticDiff,
    sourceSpan
} from '../src/v3_2';

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
    breakDeclarationCompilation = false
): Fixture => {
    const renamed = version === 'previous' ? gone : fresh;
    const aliasTarget = version === 'previous' ? q : r;
    const revision = version === 'previous'
        ? 'diff-changed-previous'
        : 'diff-changed-current';
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
    breakDeclarationCompilation = false
) => {
    const modules = [
        changedFixture(version, breakDeclarationCompilation),
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
