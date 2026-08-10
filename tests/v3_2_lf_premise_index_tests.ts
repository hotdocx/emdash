/** Focused INDEX-SEARCH-6A exact source-visible premise-index tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfCompiledDeclarationWorkspace,
    CoreLfModuleSpec,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    compileCoreLfDeclarationWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfDeclarationWorkspace,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    kernelUniverse,
    provenance
} from '../src/v3_2';
import {
    CORE_LF_PREMISE_INDEX_PROFILE,
    CoreLfCompiledPremiseIndex,
    CoreLfPremiseIndexError,
    createCoreLfAccessiblePremiseIndex,
    searchCoreLfAccessiblePremises,
    serializeCoreLfPremiseIndexSnapshot,
    serializeCoreLfPremiseSearchResult
} from '../src/v3_2/lf_premise_index';

const unrelatedModuleId = 'fixture.index_a_unrelated';
const transitiveModuleId = 'fixture.index_b_transitive';
const providerModuleId = 'fixture.index_c_provider';
const rootModuleId = 'fixture.index_d_root';

const unrelatedType = coreLfQualifiedSymbol(
    unrelatedModuleId,
    'UnrelatedType'
);
const transitiveType = coreLfQualifiedSymbol(
    transitiveModuleId,
    'TransitiveType'
);
const providerType = coreLfQualifiedSymbol(
    providerModuleId,
    'PublicType'
);
const protectedValue = coreLfQualifiedSymbol(
    providerModuleId,
    'protected_value'
);
const privateValue = coreLfQualifiedSymbol(
    providerModuleId,
    'private_value'
);
const aliasType = coreLfQualifiedSymbol(providerModuleId, 'Alias');
const aliasWitness = coreLfQualifiedSymbol(
    providerModuleId,
    'alias_witness'
);
const groupoidUniverse = coreLfQualifiedSymbol(providerModuleId, 'Grpd');
const groupoidWitness = coreLfQualifiedSymbol(
    providerModuleId,
    'groupoid_witness'
);
const identityPremise = coreLfQualifiedSymbol(
    providerModuleId,
    'identity_premise'
);
const rootPublic = coreLfQualifiedSymbol(rootModuleId, 'root_public');
const rootPrivate = coreLfQualifiedSymbol(rootModuleId, 'root_private');
const rootExcluded = coreLfQualifiedSymbol(rootModuleId, 'root_excluded');

const providerTypeCore = 'premise_provider_type';
const providerAliasCore = 'premise_provider_alias';

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;

interface Fixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

const source = (authorityPath: string, sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const modifiers = (
    visibility: 'public' | 'protected' | 'private',
    sourceOpacity: 'transparent' | 'opaque' = 'opaque'
) => ({
    visibility,
    rigidity: 'ordinary' as const,
    sourceOpacity
});

const typeFixture = (
    moduleId: string,
    symbol: typeof unrelatedType,
    coreName: string,
    digit: string
): Fixture => {
    const authorityPath = `tests/fixtures/${moduleId}.lp`;
    const module = createCoreLfModuleSpec({
        revision: `${moduleId.replace(/\./gu, '-')}-1`,
        moduleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash(digit),
        dependencies: [],
        externalSymbols: [],
        declarations: [{
            order: 0,
            symbol,
            type: { tag: 'type' },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                `symbol ${symbol.name} : TYPE;`
            )
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
                evidence: 'INDEX-SEARCH-6A standalone type fixture'
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

const providerFixture = (): Fixture => {
    const authorityPath = 'tests/fixtures/premise_index_provider.lp';
    const declarations = [
        {
            order: 0,
            symbol: providerType,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol PublicType : TYPE;')
        },
        {
            order: 1,
            symbol: protectedValue,
            type: { tag: 'global' as const, symbol: providerType },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('protected'),
            provenance: source(
                authorityPath,
                'protected symbol protected_value : PublicType;'
            )
        },
        {
            order: 2,
            symbol: privateValue,
            type: { tag: 'global' as const, symbol: providerType },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('private'),
            provenance: source(
                authorityPath,
                'private symbol private_value : PublicType;'
            )
        },
        {
            order: 3,
            symbol: aliasType,
            type: { tag: 'type' as const },
            body: coreLfTransferExplicitBody({
                tag: 'global',
                symbol: providerType
            }),
            modifiers: modifiers('public', 'transparent'),
            provenance: source(
                authorityPath,
                'symbol Alias : TYPE ≔ PublicType;'
            )
        },
        {
            order: 4,
            symbol: aliasWitness,
            type: { tag: 'global' as const, symbol: aliasType },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol alias_witness : Alias;'
            )
        },
        {
            order: 5,
            symbol: groupoidUniverse,
            type: { tag: 'type' as const },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(authorityPath, 'symbol Grpd : TYPE;')
        },
        {
            order: 6,
            symbol: groupoidWitness,
            type: { tag: 'global' as const, symbol: groupoidUniverse },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol groupoid_witness : Grpd;'
            )
        },
        {
            order: 7,
            symbol: identityPremise,
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'value',
                    mode: {
                        plicity: 'explicit' as const,
                        variation: 'functorial' as const
                    },
                    type: { tag: 'global' as const, symbol: providerType }
                },
                body: { tag: 'global' as const, symbol: providerType }
            },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol identity_premise : Π value:PublicType, PublicType;'
            )
        }
    ];
    const module = createCoreLfModuleSpec({
        revision: 'premise-index-provider-1',
        moduleId: providerModuleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('c'),
        dependencies: [transitiveModuleId],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policies = [
        'opaque-signature',
        'opaque-signature',
        'opaque-signature',
        'checked-transparent-definition',
        'opaque-signature',
        'conformance-only',
        'opaque-signature',
        'opaque-signature'
    ] as const;
    const coreNames = [
        providerTypeCore,
        'premise_provider_protected',
        'premise_provider_private',
        providerAliasCore,
        'premise_provider_alias_witness',
        undefined,
        'premise_provider_groupoid_witness',
        'premise_provider_identity'
    ] as const;
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'premise-index-provider-policy-1',
            moduleRevision: module.revision,
            entries: declarations.map((declaration, index) => ({
                order: index,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: policies[index],
                evidence: 'INDEX-SEARCH-6A provider fixture'
            }))
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'premise-index-provider-linkage-1',
            moduleRevision: module.revision,
            entries: declarations.map((declaration, index) =>
                declaration.symbol === groupoidUniverse
                    ? {
                        order: index,
                        symbol: declaration.symbol,
                        kind: 'core-owner' as const,
                        owner: 'groupoid-universe' as const
                    }
                    : {
                        order: index,
                        symbol: declaration.symbol,
                        kind: 'free-declaration' as const,
                        coreName: coreNames[index] ?? 'unreachable_core_name',
                        backendName: declaration.symbol.name
                    }
            )
        })
    };
};

const rootFixture = (): Fixture => {
    const authorityPath = 'tests/fixtures/premise_index_root.lp';
    const declarations = [
        {
            order: 0,
            symbol: rootPublic,
            type: { tag: 'global' as const, symbol: providerType },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol root_public : PublicType;'
            )
        },
        {
            order: 1,
            symbol: rootPrivate,
            type: { tag: 'global' as const, symbol: providerType },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('private'),
            provenance: source(
                authorityPath,
                'private symbol root_private : PublicType;'
            )
        },
        {
            order: 2,
            symbol: rootExcluded,
            type: { tag: 'global' as const, symbol: providerType },
            body: coreLfTransferAbsentBody(),
            modifiers: modifiers('public'),
            provenance: source(
                authorityPath,
                'symbol root_excluded : PublicType;'
            )
        }
    ];
    const module = createCoreLfModuleSpec({
        revision: 'premise-index-root-1',
        moduleId: rootModuleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('d'),
        dependencies: [providerModuleId],
        externalSymbols: [{
            symbol: providerType,
            availability: 'dependency-module'
        }],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'premise-index-root-policy-1',
            moduleRevision: module.revision,
            entries: declarations.map((declaration, index) => ({
                order: index,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: index === 2
                    ? 'excluded' as const
                    : 'opaque-signature' as const,
                evidence: 'INDEX-SEARCH-6A root fixture'
            }))
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'premise-index-root-linkage-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    symbol: providerType,
                    kind: 'free-declaration',
                    coreName: providerTypeCore,
                    backendName: providerType.name
                },
                ...declarations.map((declaration, index) => ({
                    order: index + 1,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: `premise_root_${index}`,
                    backendName: declaration.symbol.name
                }))
            ]
        })
    };
};

type FixtureId = 'unrelated' | 'transitive' | 'provider' | 'root';

const compileFixture = (
    inputOrder: readonly FixtureId[] = [
        'root',
        'unrelated',
        'provider',
        'transitive'
    ]
): CoreLfCompiledDeclarationWorkspace => {
    const fixtures: Readonly<Record<FixtureId, Fixture>> = {
        unrelated: typeFixture(
            unrelatedModuleId,
            unrelatedType,
            'premise_unrelated_type',
            'a'
        ),
        transitive: typeFixture(
            transitiveModuleId,
            transitiveType,
            'premise_transitive_type',
            'b'
        ),
        provider: providerFixture(),
        root: rootFixture()
    };
    return compileCoreLfDeclarationWorkspace(
        createCoreLfDeclarationWorkspace({
            revision: 'premise-index-workspace-1',
            modules: inputOrder.map(id => fixtures[id])
        })
    );
};

const display = (symbol: { moduleId: string; name: string }): string =>
    `${symbol.moduleId}.${symbol.name}`;

const entry = (
    index: CoreLfCompiledPremiseIndex,
    symbol: typeof providerType
) => {
    const resolved = index.resolve(symbol);
    assert.notEqual(resolved, undefined, `missing ${display(symbol)}`);
    return resolved;
};

const captureError = (
    action: () => unknown,
    code: CoreLfPremiseIndexError['code']
): CoreLfPremiseIndexError => {
    let captured: CoreLfPremiseIndexError | undefined;
    assert.throws(action, error => {
        if (error instanceof CoreLfPremiseIndexError) captured = error;
        return error instanceof CoreLfPremiseIndexError && error.code === code;
    });
    assert.notEqual(captured, undefined);
    return captured;
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('INDEX-SEARCH-6A exact accessible premise index', () => {
    it('indexes exactly root-local and direct-public declarations', () => {
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        assert.equal(
            CORE_LF_PREMISE_INDEX_PROFILE.scopePolicy,
            'root-local-plus-direct-public-imports'
        );
        assert.deepEqual(
            index.snapshot.entries.map(candidate => display(candidate.symbol)),
            [
                display(aliasType),
                display(groupoidUniverse),
                display(providerType),
                display(aliasWitness),
                display(groupoidWitness),
                display(identityPremise),
                display(rootPrivate),
                display(rootPublic)
            ]
        );
        assert.equal(index.resolve(protectedValue), undefined);
        assert.equal(index.resolve(privateValue), undefined);
        assert.equal(index.resolve(transitiveType), undefined);
        assert.equal(index.resolve(unrelatedType), undefined);
        assert.equal(index.resolve(rootExcluded), undefined);
        assert.equal(entry(index, rootPrivate)?.entry.scope.kind, 'local');
        assert.deepEqual(entry(index, aliasWitness)?.entry.scope, {
            kind: 'direct-public-import',
            rootModuleId,
            providerModuleId,
            dependencyIndex: 0
        });
        assert.deepEqual(
            index.snapshot.modules.map(module => [
                module.moduleId,
                module.role,
                module.directDependencyIndex
            ]),
            [
                [transitiveModuleId, 'transitive-closure', undefined],
                [providerModuleId, 'direct-import', 0],
                [rootModuleId, 'root', undefined]
            ]
        );
        assert.equal(Object.isFrozen(index), true);
        assert.equal(Object.isFrozen(index.entries), true);
        index.entries.forEach(candidate =>
            assert.equal(Object.isFrozen(candidate), true)
        );
        assertDeepFrozen(index.snapshot);
        const text = serializeCoreLfPremiseIndexSnapshot(index.snapshot);
        assert.doesNotMatch(text, /"body"|"environment"|"checkedType"/u);
    });

    it('is byte-stable under workspace input permutation', () => {
        const first = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        const second = createCoreLfAccessiblePremiseIndex(
            compileFixture([
                'transitive',
                'provider',
                'root',
                'unrelated'
            ]),
            rootModuleId
        );
        assert.equal(
            serializeCoreLfPremiseIndexSnapshot(first.snapshot),
            serializeCoreLfPremiseIndexSnapshot(second.snapshot)
        );
    });

    it('normalizes heads and searches exact structural fingerprints', () => {
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        const alias = entry(index, aliasWitness)?.entry.fingerprint;
        assert.equal(alias?.conclusion.status, 'normalized');
        assert.equal(alias?.conclusion.steps, 1);
        assert.deepEqual(
            alias?.conclusion.status === 'normalized'
                ? alias.conclusion.head
                : undefined,
            { kind: 'free-reference', name: providerTypeCore }
        );
        assert.deepEqual(alias?.freeReferences, [providerAliasCore]);

        const byHead = searchCoreLfAccessiblePremises(index, {
            kind: 'conclusion-head',
            type: kernelFree(
                providerTypeCore,
                provenance('derived', 'premise-index head query')
            )
        });
        assert.deepEqual(
            byHead.matches.map(candidate => candidate.symbol),
            [aliasWitness, identityPremise, rootPrivate, rootPublic]
        );
        assert.equal(byHead.totalMatches, 4);
        assert.equal(byHead.truncated, false);

        const betaSource = provenance(
            'derived',
            'premise-index beta head query'
        );
        const byBetaHead = searchCoreLfAccessiblePremises(index, {
            kind: 'conclusion-head',
            type: kernelCall(
                kernelLambda(
                    kernelBinder(
                        'X',
                        kernelUniverse(betaSource),
                        {
                            plicity: 'explicit',
                            variation: 'functorial'
                        },
                        betaSource
                    ),
                    kernelBound(0, betaSource),
                    betaSource
                ),
                [{
                    plicity: 'explicit',
                    value: kernelFree(providerTypeCore, betaSource)
                }],
                betaSource
            )
        });
        assert.deepEqual(byBetaHead.matches, byHead.matches);
        assert.equal(
            byBetaHead.query.kind === 'conclusion-head'
                ? byBetaHead.query.conclusion.steps
                : undefined,
            1
        );

        const identity = entry(index, identityPremise)?.entry.fingerprint;
        assert.equal(identity?.conclusion.leadingBinderCount, 1);
        assert.deepEqual(
            identity?.conclusion.status === 'normalized'
                ? identity.conclusion.head
                : undefined,
            { kind: 'free-reference', name: providerTypeCore }
        );

        const byOwner = searchCoreLfAccessiblePremises(index, {
            kind: 'contains-owner',
            owner: 'groupoid-universe'
        });
        assert.deepEqual(
            byOwner.matches.map(candidate => candidate.symbol),
            [groupoidWitness]
        );
        const byReference = searchCoreLfAccessiblePremises(index, {
            kind: 'contains-free-reference',
            name: providerAliasCore
        });
        assert.deepEqual(
            byReference.matches.map(candidate => candidate.symbol),
            [aliasWitness]
        );
        const byNode = searchCoreLfAccessiblePremises(index, {
            kind: 'contains-node',
            tag: 'universe'
        });
        assert.deepEqual(
            byNode.matches.map(candidate => candidate.symbol),
            [aliasType, groupoidUniverse, providerType]
        );
        const byPi = searchCoreLfAccessiblePremises(index, {
            kind: 'contains-node',
            tag: 'pi'
        });
        assert.deepEqual(
            byPi.matches.map(candidate => candidate.symbol),
            [identityPremise]
        );
    });

    it('resolves exact IDs and reports deterministic truncation', () => {
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        const hit = searchCoreLfAccessiblePremises(index, {
            kind: 'exact-id',
            symbol: rootPrivate
        });
        assert.deepEqual(
            hit.matches.map(candidate => candidate.symbol),
            [rootPrivate]
        );
        const miss = searchCoreLfAccessiblePremises(index, {
            kind: 'exact-id',
            symbol: transitiveType
        });
        assert.equal(miss.totalMatches, 0);

        const limited = searchCoreLfAccessiblePremises(
            index,
            { kind: 'all' },
            { limit: 2 }
        );
        assert.equal(limited.totalMatches, 8);
        assert.equal(limited.truncated, true);
        assert.deepEqual(
            limited.matches.map(candidate => candidate.symbol),
            [aliasType, groupoidUniverse]
        );
        assertDeepFrozen(limited);
        assert.equal(
            serializeCoreLfPremiseSearchResult(limited),
            serializeCoreLfPremiseSearchResult(limited)
        );
    });

    it('keeps normalization exhaustion explicit and non-matching', () => {
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId,
            { normalizationStepLimit: 0 }
        );
        const alias = entry(index, aliasWitness)?.entry.fingerprint;
        assert.equal(
            alias?.conclusion.status,
            'step-limit-exceeded'
        );
        const byHead = searchCoreLfAccessiblePremises(index, {
            kind: 'conclusion-head',
            type: kernelFree(
                providerTypeCore,
                provenance('derived', 'zero-budget premise query')
            )
        });
        assert.deepEqual(
            byHead.matches.map(candidate => candidate.symbol),
            [identityPremise, rootPrivate, rootPublic]
        );
        assert.equal(byHead.totalMatches, 3);
    });

    it('rejects unsafe construction and search budgets', () => {
        captureError(
            () => createCoreLfAccessiblePremiseIndex(
                compileFixture(),
                rootModuleId,
                { typeVisitLimit: 0 }
            ),
            'TYPE_VISIT_LIMIT_EXCEEDED'
        );
        captureError(
            () => createCoreLfAccessiblePremiseIndex(
                compileFixture(),
                rootModuleId,
                {
                    normalizationStepLimit:
                        CORE_LF_PREMISE_INDEX_PROFILE
                            .maxNormalizationStepLimit + 1
                }
            ),
            'INVALID_BUDGET'
        );
        const index = createCoreLfAccessiblePremiseIndex(
            compileFixture(),
            rootModuleId
        );
        captureError(
            () => searchCoreLfAccessiblePremises(
                index,
                { kind: 'all' },
                {
                    limit:
                        CORE_LF_PREMISE_INDEX_PROFILE.maxSearchResultLimit + 1
                }
            ),
            'INVALID_BUDGET'
        );
        captureError(
            () => searchCoreLfAccessiblePremises(index, {
                kind: 'exact-id',
                symbol: {
                    moduleId: rootModuleId,
                    name: 'not valid'
                }
            }),
            'INVALID_SEARCH_QUERY'
        );
    });

    it('rejects unknown roots and reconstructed closure drift', () => {
        const workspace = compileFixture();
        captureError(
            () => createCoreLfAccessiblePremiseIndex(
                workspace,
                'fixture.index_missing'
            ),
            'UNKNOWN_ROOT_MODULE'
        );
        const modules = workspace.modules.map(module =>
            module.source.module.moduleId === providerModuleId
                ? Object.freeze({
                    ...module,
                    sourceText: `${module.sourceText} `
                })
                : module
        );
        const drifted = new CoreLfCompiledDeclarationWorkspace(
            workspace.plan,
            modules,
            workspace.environment
        );
        captureError(
            () => createCoreLfAccessiblePremiseIndex(
                drifted,
                rootModuleId
            ),
            'CLOSURE_DRIFT'
        );
    });
});
