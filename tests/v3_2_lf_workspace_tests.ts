/** Focused AI-WORKSPACE-1A declaration-graph tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE,
    CoreLfDeclarationWorkspaceError,
    CoreLfModuleSpec,
    CoreLfTransferDeclarationLink,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferPolicyOverlay,
    compareCoreLfDeclarationWorkspaceSnapshots,
    compileCoreLfDeclarationWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspaceClosureSnapshot,
    createCoreLfDeclarationWorkspaceSnapshot,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    defineCoreLfDeclarationWorkspaceModule,
    serializeCoreLfDeclarationWorkspaceClosure,
    serializeCoreLfDeclarationWorkspaceInterface,
    serializeCoreLfDeclarationWorkspaceInvalidation,
    serializeCoreLfDeclarationWorkspaceSnapshot,
    serializeCoreLfDeclarationWorkspaceSource
} from '../src/v3_2';

const baseModuleId = 'fixture.workspace_base';
const consumerModuleId = 'fixture.workspace_consumer';
const siblingModuleId = 'fixture.workspace_sibling';
const basePath = 'tests/fixtures/workspace_base.lp';
const consumerPath = 'tests/fixtures/workspace_consumer.lp';
const siblingPath = 'tests/fixtures/workspace_sibling.lp';

const base = coreLfQualifiedSymbol(baseModuleId, 'Base');
const identity = coreLfQualifiedSymbol(baseModuleId, 'identity');
const useIdentity =
    coreLfQualifiedSymbol(consumerModuleId, 'use_identity');
const siblingType =
    coreLfQualifiedSymbol(siblingModuleId, 'Sibling');

const mode = {
    plicity: 'explicit' as const,
    variation: 'functorial' as const
};

const sha = (digit: string): string => `sha256:${digit.repeat(64)}`;

const source = (
    authorityPath: string,
    sourceFragment: string
) => ({ authorityPath, sourceFragment });

const global = (
    symbol: { readonly moduleId: string; readonly name: string }
) => ({ tag: 'global' as const, symbol });

const unaryType = () => ({
    tag: 'pi' as const,
    binder: {
        hint: 'value',
        mode,
        type: global(base)
    },
    body: global(base)
});

const identityBody = () => ({
    tag: 'lambda' as const,
    binder: {
        hint: 'value',
        mode,
        type: global(base)
    },
    body: {
        tag: 'bound' as const,
        index: 0
    }
});

interface Fixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

const baseFixture = (version = '1'): Fixture => {
    const module = createCoreLfModuleSpec({
        revision: `workspace-base-${version}`,
        moduleId: baseModuleId,
        fragmentId: 'declarations',
        authorityPath: basePath,
        sourceSha256: sha(version === '1' ? 'a' : 'd'),
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: base,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: source(basePath, 'symbol Base : TYPE;')
            },
            {
                order: 1,
                symbol: identity,
                type: unaryType(),
                body: coreLfTransferExplicitBody(identityBody()),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    basePath,
                    'symbol identity (value : Base) : Base ≔ value;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: `workspace-base-policy-${version}`,
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: base
                },
                policy: 'opaque-signature',
                evidence: 'workspace fixture base type'
            },
            {
                order: 1,
                target: {
                    kind: 'declaration',
                    symbol: identity
                },
                policy: 'checked-transparent-definition',
                evidence: 'workspace fixture identity'
            }
        ]
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: `workspace-base-linkage-${version}`,
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                symbol: base,
                kind: 'free-declaration',
                coreName: 'workspace_base_type',
                backendName: 'Base'
            },
            {
                order: 1,
                symbol: identity,
                kind: 'free-declaration',
                coreName: 'workspace_base_identity',
                backendName: 'identity'
            }
        ]
    });
    return { module, policy, linkage };
};

const withOrder = (
    link: CoreLfTransferDeclarationLink,
    order: number
): CoreLfTransferDeclarationLink => link.kind === 'core-owner'
    ? {
        order,
        symbol: link.symbol,
        kind: link.kind,
        owner: link.owner
    }
    : {
        order,
        symbol: link.symbol,
        kind: link.kind,
        coreName: link.coreName,
        backendName: link.backendName
    };

const consumerFixture = (
    baseLinkage: CoreLfTransferDeclarationLinkage
): Fixture => {
    const module = createCoreLfModuleSpec({
        revision: 'workspace-consumer-1',
        moduleId: consumerModuleId,
        fragmentId: 'declarations',
        authorityPath: consumerPath,
        sourceSha256: sha('b'),
        dependencies: [baseModuleId],
        externalSymbols: [base, identity].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [{
            order: 0,
            symbol: useIdentity,
            type: unaryType(),
            body: coreLfTransferExplicitBody({
                tag: 'lambda',
                binder: {
                    hint: 'value',
                    mode,
                    type: global(base)
                },
                body: {
                    tag: 'call',
                    callee: global(identity),
                    arguments: [{
                        plicity: 'explicit',
                        value: {
                            tag: 'bound',
                            index: 0
                        }
                    }]
                }
            }),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'transparent'
            },
            provenance: source(
                consumerPath,
                'symbol use_identity (value : Base) : Base ≔ identity value;'
            )
        }],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'workspace-consumer-policy-1',
        moduleRevision: module.revision,
        entries: [{
            order: 0,
            target: {
                kind: 'declaration',
                symbol: useIdentity
            },
            policy: 'checked-transparent-definition',
            evidence: 'workspace dependency consumer'
        }]
    });
    const externalLinks = [base, identity].map((symbol, order) => {
        const link = baseLinkage.entries.find(entry =>
            entry.symbol.moduleId === symbol.moduleId &&
            entry.symbol.name === symbol.name
        );
        assert.notEqual(link, undefined);
        return withOrder(link as CoreLfTransferDeclarationLink, order);
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'workspace-consumer-linkage-1',
        moduleRevision: module.revision,
        entries: [
            ...externalLinks,
            {
                order: externalLinks.length,
                symbol: useIdentity,
                kind: 'free-declaration',
                coreName: 'workspace_use_identity',
                backendName: 'use_identity'
            }
        ]
    });
    return { module, policy, linkage };
};

const siblingFixture = (): Fixture => {
    const module = createCoreLfModuleSpec({
        revision: 'workspace-sibling-1',
        moduleId: siblingModuleId,
        fragmentId: 'declarations',
        authorityPath: siblingPath,
        sourceSha256: sha('c'),
        dependencies: [],
        externalSymbols: [],
        declarations: [{
            order: 0,
            symbol: siblingType,
            type: { tag: 'type' },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque'
            },
            provenance: source(siblingPath, 'symbol Sibling : TYPE;')
        }],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: 'workspace-sibling-policy-1',
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: siblingType
                },
                policy: 'opaque-signature',
                evidence: 'independent workspace sibling'
            }]
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: 'workspace-sibling-linkage-1',
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                symbol: siblingType,
                kind: 'free-declaration',
                coreName: 'workspace_sibling_type',
                backendName: 'Sibling'
            }]
        })
    };
};

const emptyFixture = (
    moduleId: string,
    dependencies: readonly string[],
    fragmentId = 'declarations'
): Fixture => {
    const module = createCoreLfModuleSpec({
        revision: `${moduleId.replace(/\./gu, '-')}-1`,
        moduleId,
        fragmentId,
        authorityPath: `tests/fixtures/${moduleId}.lp`,
        sourceSha256: sha('e'),
        dependencies,
        externalSymbols: [],
        declarations: [],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    return {
        module,
        policy: createCoreLfTransferPolicyOverlay(module, {
            revision: `${module.revision}-policy`,
            moduleRevision: module.revision,
            entries: []
        }),
        linkage: createCoreLfTransferDeclarationLinkage(module, {
            revision: `${module.revision}-linkage`,
            moduleRevision: module.revision,
            entries: []
        })
    };
};

const runtimeFixture = (): Fixture => {
    const original = baseFixture();
    const module = createCoreLfModuleSpec({
        revision: 'workspace-runtime-1',
        moduleId: baseModuleId,
        fragmentId: 'runtime-content',
        authorityPath: basePath,
        sourceSha256: sha('f'),
        dependencies: [],
        externalSymbols: [],
        declarations: original.module.declarations,
        inductives: [],
        runtimeRules: [{
            order: 2,
            id: 'fixture.workspace.identity.beta',
            groupId: 'fixture.workspace.identity',
            clauseOrder: 0,
            sourceOwner: identity,
            variables: [{
                name: 'value',
                type: global(base)
            }],
            left: {
                tag: 'call',
                callee: global(identity),
                arguments: [{
                    plicity: 'explicit',
                    value: {
                        tag: 'capture',
                        name: 'value'
                    }
                }]
            },
            right: {
                tag: 'capture',
                name: 'value'
            },
            provenance: source(basePath, 'rule identity $value ↪ $value;')
        }],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'workspace-runtime-policy-1',
        moduleRevision: module.revision,
        entries: [
            ...original.policy.entries.map(entry => ({ ...entry })),
            {
                order: 2,
                target: {
                    kind: 'runtime-rule' as const,
                    id: 'fixture.workspace.identity.beta'
                },
                policy: 'runtime-rewrite' as const,
                evidence: 'unsupported workspace runtime fixture'
            }
        ]
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'workspace-runtime-linkage-1',
        moduleRevision: module.revision,
        entries: original.linkage.entries.map(entry => ({ ...entry }))
    });
    return { module, policy, linkage };
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const expectWorkspaceError = (
    action: () => unknown,
    code: CoreLfDeclarationWorkspaceError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfDeclarationWorkspaceError &&
            error.code === code &&
            error.path.length > 0
    );
};

const compileFixtureWorkspace = (
    version = '1',
    inputOrder: readonly ('base' | 'consumer' | 'sibling')[] = [
        'consumer',
        'sibling',
        'base'
    ]
) => {
    const provider = baseFixture(version);
    const fixtures = {
        base: provider,
        consumer: consumerFixture(provider.linkage),
        sibling: siblingFixture()
    };
    const plan = createCoreLfDeclarationWorkspace({
        revision: `workspace-fixture-${version}`,
        modules: inputOrder.map(id => fixtures[id])
    });
    return compileCoreLfDeclarationWorkspace(plan);
};

describe('AI-WORKSPACE-1A declaration workspace', () => {
    it('plans and compiles exact dependencies independently of input order', () => {
        const first = compileFixtureWorkspace();
        const second = compileFixtureWorkspace('1', [
            'sibling',
            'base',
            'consumer'
        ]);
        assert.deepEqual(first.plan.order, [
            baseModuleId,
            consumerModuleId,
            siblingModuleId
        ]);
        assert.deepEqual(second.plan.order, first.plan.order);
        assert.equal(
            first.module(consumerModuleId)?.compiled.environment.lookup(
                'workspace_use_identity'
            )?.transparency,
            'transparent'
        );
        assert.deepEqual(
            first.module(baseModuleId)?.interface.entries.map(entry => [
                entry.symbol.name,
                entry.visibility
            ]),
            [
                ['Base', 'public'],
                ['identity', 'public']
            ]
        );
        assert.equal(
            serializeCoreLfDeclarationWorkspaceSnapshot(
                createCoreLfDeclarationWorkspaceSnapshot(first)
            ),
            serializeCoreLfDeclarationWorkspaceSnapshot(
                createCoreLfDeclarationWorkspaceSnapshot(second)
            )
        );
        assert.equal(Object.isFrozen(first), true);
        assert.equal(Object.isFrozen(first.modules), true);
        const defined = defineCoreLfDeclarationWorkspaceModule(baseFixture());
        assert.equal(Object.isFrozen(defined), true);
        assert.equal(defined.module.moduleId, baseModuleId);
        assert.equal(
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.nodeBuiltinDependency,
            false
        );
        assert.equal(
            CORE_LF_DECLARATION_WORKSPACE_PROFILE
                .computesCryptographicHashes,
            false
        );
        assert.equal(
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.executesIncrementally,
            false
        );

        const orderZ = emptyFixture('fixture.workspace_order_z', []);
        const orderA = emptyFixture(
            'fixture.workspace_order_a',
            ['fixture.workspace_order_z']
        );
        const orderB = emptyFixture('fixture.workspace_order_b', []);
        assert.deepEqual(
            createCoreLfDeclarationWorkspace({
                revision: 'workspace-order-1',
                modules: [orderA, orderZ, orderB]
            }).order,
            [
                'fixture.workspace_order_b',
                'fixture.workspace_order_z',
                'fixture.workspace_order_a'
            ]
        );
    });

    it('emits byte-stable portable source and interface hash inputs', () => {
        const compiled = compileFixtureWorkspace();
        const provider = compiled.module(baseModuleId);
        assert.notEqual(provider, undefined);
        if (provider === undefined) return;
        assert.equal(
            provider.sourceText,
            serializeCoreLfDeclarationWorkspaceSource(
                provider.sourceSnapshot
            )
        );
        assert.equal(
            provider.interfaceText,
            serializeCoreLfDeclarationWorkspaceInterface(
                provider.interfaceSnapshot
            )
        );
        assert.match(provider.sourceText, /"sourceSha256"/u);
        assert.match(provider.interfaceText, /EMDASH-CORE-SEXP-1/u);
        assert.match(provider.interfaceText, /\(lambda /u);
        assert.doesNotMatch(
            provider.interfaceText,
            /Symbol\(|builderIdentity|metaSessions|sessionIdentity/u
        );
        assert.equal(provider.sourceText.endsWith('\n'), true);
        assert.equal(provider.interfaceText.endsWith('\n'), true);
    });

    it('serializes exact dependency closures without unrelated modules', () => {
        const workspace = createCoreLfDeclarationWorkspaceSnapshot(
            compileFixtureWorkspace()
        );
        const closure =
            createCoreLfDeclarationWorkspaceClosureSnapshot(
                workspace,
                consumerModuleId
            );
        assert.deepEqual(closure.order, [
            baseModuleId,
            consumerModuleId
        ]);
        assert.equal(
            closure.modules.some(module =>
                module.moduleId === siblingModuleId
            ),
            false
        );
        const text = serializeCoreLfDeclarationWorkspaceClosure(closure);
        assert.deepEqual(
            (JSON.parse(text) as { readonly order: readonly string[] }).order,
            closure.order
        );
        assertDeepFrozen(workspace);
        assertDeepFrozen(closure);
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspaceClosureSnapshot(
                workspace,
                'fixture.workspace_missing'
            ),
            'UNKNOWN_MODULE'
        );
    });

    it('reports conservative dependency invalidation and sibling reuse', () => {
        const before = createCoreLfDeclarationWorkspaceSnapshot(
            compileFixtureWorkspace('1')
        );
        const after = createCoreLfDeclarationWorkspaceSnapshot(
            compileFixtureWorkspace('2')
        );
        const invalidation =
            compareCoreLfDeclarationWorkspaceSnapshots(before, after);
        assert.deepEqual(invalidation.changedModuleIds, [baseModuleId]);
        assert.deepEqual(invalidation.affectedModuleIds, [
            baseModuleId,
            consumerModuleId
        ]);
        assert.deepEqual(invalidation.reusableModuleIds, [siblingModuleId]);
        assert.equal(invalidation.executesIncrementally, false);
        assert.deepEqual(
            invalidation.modules.map(module => [
                module.moduleId,
                module.state,
                module.interfaceChanged
            ]),
            [
                [baseModuleId, 'changed', true],
                [consumerModuleId, 'affected', false],
                [siblingModuleId, 'reusable', false]
            ]
        );
        assert.deepEqual(
            invalidation.modules[1].reasons,
            [`dependency-affected:${baseModuleId}`]
        );
        assertDeepFrozen(invalidation);
        assert.deepEqual(
            (JSON.parse(
                serializeCoreLfDeclarationWorkspaceInvalidation(
                    invalidation
                )
            ) as { readonly affectedModuleIds: readonly string[] })
                .affectedModuleIds,
            invalidation.affectedModuleIds
        );

        const interfaceOnly = JSON.parse(JSON.stringify(before)) as
            typeof before;
        const interfaceProvider = interfaceOnly.modules.find(module =>
            module.moduleId === baseModuleId
        );
        assert.notEqual(interfaceProvider, undefined);
        if (interfaceProvider !== undefined) {
            (interfaceProvider.interface as { sourceSha256: string })
                .sourceSha256 = sha('9');
        }
        const interfaceInvalidation =
            compareCoreLfDeclarationWorkspaceSnapshots(
                before,
                interfaceOnly
            );
        assert.deepEqual(interfaceInvalidation.changedModuleIds, [
            baseModuleId
        ]);
        assert.deepEqual(interfaceInvalidation.affectedModuleIds, [
            baseModuleId,
            consumerModuleId
        ]);
        assert.deepEqual(interfaceInvalidation.modules[0].reasons, [
            'interface-changed'
        ]);

        const withoutSibling = createCoreLfDeclarationWorkspaceSnapshot(
            compileFixtureWorkspace('1', ['consumer', 'base'])
        );
        const removal = compareCoreLfDeclarationWorkspaceSnapshots(
            before,
            withoutSibling
        );
        assert.deepEqual(removal.removedModuleIds, [siblingModuleId]);
        assert.deepEqual(removal.affectedModuleIds, [siblingModuleId]);
        assert.deepEqual(removal.reusableModuleIds, [
            baseModuleId,
            consumerModuleId
        ]);
        const addition = compareCoreLfDeclarationWorkspaceSnapshots(
            withoutSibling,
            before
        );
        assert.deepEqual(addition.addedModuleIds, [siblingModuleId]);
        assert.deepEqual(addition.affectedModuleIds, [siblingModuleId]);
    });

    it('rejects empty, missing, duplicate, and cyclic module graphs', () => {
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'bad workspace',
                modules: []
            }),
            'INVALID_WORKSPACE'
        );
        const missing = emptyFixture(
            'fixture.workspace_missing_consumer',
            ['fixture.workspace_absent']
        );
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-missing-1',
                modules: [missing]
            }),
            'MISSING_DEPENDENCY'
        );
        const first = baseFixture();
        const second = baseFixture('2');
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-duplicate-1',
                modules: [first, second]
            }),
            'DUPLICATE_MODULE'
        );
        const cycleA = emptyFixture(
            'fixture.workspace_cycle_a',
            ['fixture.workspace_cycle_b']
        );
        const cycleB = emptyFixture(
            'fixture.workspace_cycle_b',
            ['fixture.workspace_cycle_a']
        );
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-cycle-1',
                modules: [cycleB, cycleA]
            }),
            'CYCLIC_DEPENDENCY'
        );
        assert.throws(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-cycle-1',
                modules: [cycleB, cycleA]
            }),
            error =>
                error instanceof CoreLfDeclarationWorkspaceError &&
                /workspace_cycle_a -> fixture\.workspace_cycle_b -> /u
                    .test(error.message)
        );
    });

    it('rejects foreign companions and same-module fragments', () => {
        const provider = baseFixture();
        const sibling = siblingFixture();
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-foreign-1',
                modules: [{
                    module: provider.module,
                    policy: sibling.policy,
                    linkage: provider.linkage
                }]
            }),
            'FOREIGN_COMPANION'
        );
        const secondFragment = emptyFixture(
            baseModuleId,
            [],
            'second-fragment'
        );
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-fragment-1',
                modules: [provider, secondFragment]
            }),
            'DUPLICATE_MODULE'
        );
    });

    it('rejects runtime content rather than guessing fragment lineage', () => {
        expectWorkspaceError(
            () => createCoreLfDeclarationWorkspace({
                revision: 'workspace-runtime-1',
                modules: [runtimeFixture()]
            }),
            'UNSUPPORTED_MODULE_CONTENT'
        );
    });

    it('rejects non-portable snapshot data and stale snapshot shape', () => {
        const snapshot = createCoreLfDeclarationWorkspaceSnapshot(
            compileFixtureWorkspace()
        );
        expectWorkspaceError(
            () => serializeCoreLfDeclarationWorkspaceSnapshot({
                ...snapshot,
                nonPortable: () => undefined
            } as typeof snapshot),
            'NON_PORTABLE_DATA'
        );
        const reversed = {
            ...snapshot,
            order: [...snapshot.order].reverse()
        } as typeof snapshot;
        expectWorkspaceError(
            () => compareCoreLfDeclarationWorkspaceSnapshots(
                snapshot,
                reversed
            ),
            'INVALID_SNAPSHOT'
        );
    });
});
