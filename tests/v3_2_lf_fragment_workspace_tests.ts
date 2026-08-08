/** Focused AI-WORKSPACE-1B2A same-module fragment-chain tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE,
    CoreLfMixedDeclarationLinkage,
    CoreLfModuleSpec,
    CoreLfSameModuleFragmentSource,
    CoreLfSameModuleFragmentWorkspaceError,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    KernelExpression,
    binderMode,
    compileCoreLfSameModuleFragmentWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfSameModuleFragmentWorkspace,
    createCoreLfSameModuleFragmentWorkspaceSourceSnapshot,
    createCoreLfSameModuleFragmentWorkspaceSnapshot,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    defineCoreLfSameModuleDeclarationFragment,
    defineCoreLfSameModuleMixedFragment,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    planCoreLfMixedPhases,
    provenance,
    serializeCoreLfSameModuleFragmentSource,
    serializeCoreLfSameModuleFragmentWorkspaceSourceSnapshot,
    serializeCoreLfSameModuleFragmentWorkspaceSnapshot
} from '../src/v3_2';

const moduleId = 'fixture.fragment_workspace';
const authorityPath = 'tests/fixtures/fragment_workspace.lp';
const sourceSha = `sha256:${'a'.repeat(64)}`;
const driftSha = `sha256:${'b'.repeat(64)}`;

const carrier = coreLfQualifiedSymbol(moduleId, 'Carrier');
const token = coreLfQualifiedSymbol(moduleId, 'token');
const normalize = coreLfQualifiedSymbol(moduleId, 'normalize');
const leftHead = coreLfQualifiedSymbol(moduleId, 'left_head');
const rightHead = coreLfQualifiedSymbol(moduleId, 'right_head');
const double = coreLfQualifiedSymbol(moduleId, 'double');
const laterHead = coreLfQualifiedSymbol(moduleId, 'later_head');

const symbols = [
    carrier,
    token,
    normalize,
    leftHead,
    rightHead,
    double,
    laterHead
];

const coreNames = new Map(symbols.map(symbol => [
    symbol.name,
    `fragment_${symbol.name}`
] as const));

const mode = binderMode('explicit', 'functorial');
const modifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const source = (sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const global = (symbol: typeof carrier) => ({
    tag: 'global' as const,
    symbol
});

const unaryType = () => ({
    tag: 'pi' as const,
    binder: {
        hint: 'value',
        mode,
        type: global(carrier)
    },
    body: global(carrier)
});

const linkEntries = (selected: readonly typeof carrier[]) =>
    selected.map((symbol, order) => ({
        order,
        symbol,
        kind: 'free-declaration' as const,
        coreName: coreNames.get(symbol.name) as string,
        backendName: symbol.name
    }));

const policyFor = (
    module: CoreLfModuleSpec,
    revision: string
): CoreLfTransferPolicyOverlay => {
    const entries = [
        ...module.declarations.map(declaration => ({
            sourceOrder: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: 'fragment workspace declaration'
        })),
        ...module.runtimeRules.map(rule => ({
            sourceOrder: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: 'fragment workspace runtime'
        })),
        ...module.proofRules.map(rule => ({
            sourceOrder: rule.order,
            target: {
                kind: 'proof-rule' as const,
                id: rule.id
            },
            policy: 'proof-unification' as const,
            evidence: 'fragment workspace proof'
        }))
    ].sort((left, right) => left.sourceOrder - right.sourceOrder);
    return createCoreLfTransferPolicyOverlay(module, {
        revision,
        moduleRevision: module.revision,
        entries: entries.map((entry, order) => ({
            order,
            target: entry.target,
            policy: entry.policy,
            evidence: entry.evidence
        }))
    });
};

const declaration = (
    order: number,
    symbol: typeof carrier,
    type: CoreLfTransferExpression
) => ({
    order,
    symbol,
    type,
    body: coreLfTransferAbsentBody(),
    modifiers,
    provenance: source(`symbol ${symbol.name};`)
});

const baseFixture = (sha256 = sourceSha) => {
    const module = createCoreLfModuleSpec({
        revision: sha256 === sourceSha
            ? 'fragment-base-1'
            : 'fragment-base-drift-1',
        moduleId,
        fragmentId: 'base-declarations',
        authorityPath,
        sourceSha256: sha256,
        dependencies: [],
        externalSymbols: [],
        declarations: [
            declaration(0, carrier, { tag: 'type' }),
            declaration(1, token, global(carrier)),
            declaration(2, normalize, unaryType()),
            declaration(3, leftHead, unaryType()),
            declaration(4, rightHead, unaryType())
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = policyFor(module, `${module.revision}-policy`);
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: `${module.revision}-linkage`,
        moduleRevision: module.revision,
        entries: linkEntries([
            carrier,
            token,
            normalize,
            leftHead,
            rightHead
        ])
    });
    return defineCoreLfSameModuleDeclarationFragment({
        module,
        policy,
        linkage
    });
};

const call = (
    builder: CoreLfTransferScopedBuilder,
    symbol: typeof normalize,
    value: ReturnType<CoreLfTransferScopedBuilder['capture']>
) => builder.call(
    builder.global(symbol),
    [{ plicity: 'explicit', value }]
);

const proofRule = (
    order: number,
    id: string,
    sourceOwner: typeof leftHead,
    rightOwner: typeof rightHead
) => {
    const pattern = new CoreLfTransferScopedBuilder();
    const template = new CoreLfTransferScopedBuilder();
    return {
        order,
        id,
        sourceOwner,
        variables: ['x', 'y'].map(name => ({
            name,
            role: 'matched' as const,
            type: global(carrier)
        })),
        problem: {
            left: pattern.pattern(call(
                pattern,
                sourceOwner,
                pattern.capture('x')
            )),
            right: pattern.pattern(call(
                pattern,
                rightOwner,
                pattern.capture('y')
            ))
        },
        generatedConstraints: [{
            left: template.template(template.capture('x')),
            right: template.template(template.capture('y'))
        }],
        provenance: source(`unif_rule ${id};`)
    };
};

const firstMixedFixture = (
    base: ReturnType<typeof baseFixture>
) => {
    const runtime = new CoreLfTransferScopedBuilder();
    const value = runtime.capture('value');
    const module = createCoreLfModuleSpec({
        revision: 'fragment-rules-a-1',
        moduleId,
        fragmentId: 'rules-a',
        authorityPath,
        sourceSha256: sourceSha,
        dependencies: [],
        externalSymbols: [
            carrier,
            normalize,
            leftHead,
            rightHead
        ].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules: [{
            order: 5,
            id: 'fixture.fragment.normalize',
            groupId: 'fixture.fragment.normalize',
            clauseOrder: 0,
            sourceOwner: normalize,
            variables: [{ name: 'value', type: global(carrier) }],
            left: runtime.pattern(call(runtime, normalize, value)),
            right: runtime.template(value),
            provenance: source('rule normalize $value ↪ $value;')
        }],
        proofRules: [proofRule(
            6,
            'fixture.fragment.heads',
            leftHead,
            rightHead
        )]
    });
    const policy = policyFor(module, 'fragment-rules-a-policy-1');
    const plan = planCoreLfMixedPhases(module, policy);
    const linkage = createCoreLfMixedDeclarationLinkage(plan, {
        revision: 'fragment-rules-a-linkage-1',
        moduleRevision: module.revision,
        entries: linkEntries([
            carrier,
            normalize,
            leftHead,
            rightHead
        ])
    });
    return defineCoreLfSameModuleMixedFragment({
        module,
        policy,
        linkage,
        externalProviders: module.externalSymbols.map(external => ({
            symbol: external.symbol,
            provider: base.identity
        }))
    });
};

interface ThirdFixtureOptions {
    readonly firstOrder?: number;
    readonly sourceSha256?: string;
    readonly normalizeProvider?:
        CoreLfSameModuleFragmentSource['identity'];
    readonly runtimeProvider?:
        CoreLfSameModuleFragmentSource['identity'];
}

const thirdMixedFixture = (
    base: ReturnType<typeof baseFixture>,
    prior: ReturnType<typeof firstMixedFixture>,
    options: ThirdFixtureOptions = {}
) => {
    const firstOrder = options.firstOrder ?? 7;
    const sha256 = options.sourceSha256 ?? sourceSha;
    const runtime = new CoreLfTransferScopedBuilder();
    const value = runtime.capture('value');
    const nested = call(runtime, normalize, value);
    const module = createCoreLfModuleSpec({
        revision: sha256 === sourceSha
            ? `fragment-rules-b-${firstOrder}`
            : `fragment-rules-b-drift-${firstOrder}`,
        moduleId,
        fragmentId: `rules-b-${firstOrder}`,
        authorityPath,
        sourceSha256: sha256,
        dependencies: [],
        externalSymbols: [carrier, normalize, rightHead].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [
            declaration(firstOrder, double, unaryType()),
            declaration(firstOrder + 1, laterHead, unaryType())
        ],
        inductives: [],
        runtimeRules: [{
            order: firstOrder + 2,
            id: `fixture.fragment.double-${firstOrder}`,
            groupId: `fixture.fragment.double-${firstOrder}`,
            clauseOrder: 0,
            sourceOwner: double,
            variables: [{ name: 'value', type: global(carrier) }],
            left: runtime.pattern(call(runtime, double, value)),
            right: runtime.template(call(runtime, normalize, nested)),
            provenance: source(
                'rule double $value ↪ normalize (normalize $value);'
            )
        }],
        proofRules: [proofRule(
            firstOrder + 3,
            `fixture.fragment.double-heads-${firstOrder}`,
            laterHead,
            rightHead
        )]
    });
    const policy = policyFor(
        module,
        `fragment-rules-b-policy-${firstOrder}`
    );
    const plan = planCoreLfMixedPhases(module, policy);
    const linkage = createCoreLfMixedDeclarationLinkage(plan, {
        revision: `fragment-rules-b-linkage-${firstOrder}`,
        moduleRevision: module.revision,
        entries: linkEntries([
            carrier,
            normalize,
            rightHead,
            double,
            laterHead
        ])
    });
    return defineCoreLfSameModuleMixedFragment({
        module,
        policy,
        linkage,
        externalProviders: module.externalSymbols.map(external => ({
            symbol: external.symbol,
            provider: external.symbol.name === normalize.name
                ? options.normalizeProvider ?? base.identity
                : base.identity
        })),
        runtimeProvider: options.runtimeProvider ?? prior.identity
    });
};

const fixture = () => {
    const base = baseFixture();
    const first = firstMixedFixture(base);
    const third = thirdMixedFixture(base, first);
    return { base, first, third };
};

const compileFixture = (
    order: readonly ('base' | 'first' | 'third')[] = [
        'third',
        'base',
        'first'
    ]
) => {
    const fragments = fixture();
    const plan = createCoreLfSameModuleFragmentWorkspace({
        revision: 'fragment-workspace-fixture-1',
        fragments: order.map(id => fragments[id])
    });
    return compileCoreLfSameModuleFragmentWorkspace(plan);
};

const expectFragmentError = (
    action: () => unknown,
    code: CoreLfSameModuleFragmentWorkspaceError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfSameModuleFragmentWorkspaceError &&
            error.code === code &&
            error.path.length > 0
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('AI-WORKSPACE-1B2A same-module fragment workspace', () => {
    it('compiles declarations, runtime, and proofs across exact fragments', () => {
        const compiled = compileFixture();
        assert.deepEqual(
            compiled.plan.fragments.map(source => source.module.fragmentId),
            ['base-declarations', 'rules-a', 'rules-b-7']
        );
        assert.deepEqual(
            compiled.declarations.environment.declarations.map(
                declaration => declaration.name
            ),
            [
                'fragment_Carrier',
                'fragment_token',
                'fragment_normalize',
                'fragment_left_head',
                'fragment_right_head',
                'fragment_double',
                'fragment_later_head'
            ]
        );
        assert.deepEqual(compiled.latestRuntime?.runtime.ruleIds, [
            'fixture.fragment.normalize',
            'fixture.fragment.double-7'
        ]);
        assert.deepEqual(compiled.proofProgram?.ruleIds, [
            'fixture.fragment.heads',
            'fixture.fragment.double-heads-7'
        ]);
        assert.deepEqual(
            compiled.latestRuntime?.dependencies.map(dependency => [
                dependency.relation,
                dependency.fragment.module.fragmentId
            ]),
            [['earlier-fragment', 'rules-a-mixed-0-runtime']]
        );

        const nodeSource = provenance(
            'derived',
            'AI-WORKSPACE-1B2A execution witness'
        );
        const tokenTerm = kernelFree('fragment_token', nodeSource);
        const doubleTerm = kernelCall(
            kernelFree('fragment_double', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const runtime = compiled.latestRuntime?.runtime;
        assert.notEqual(runtime, undefined);
        if (runtime === undefined) return;
        const runtimeRuleIds: string[] = [];
        let reduced: KernelExpression = doubleTerm;
        for (let step = 0; step < 8; step += 1) {
            const rewrite = runtime.rewriteHead(reduced);
            if (rewrite.status === 'irreducible') break;
            runtimeRuleIds.push(rewrite.ruleId);
            reduced = rewrite.after;
        }
        assert.equal(kernelExpressionEquals(reduced, tokenTerm), true);
        assert.deepEqual(runtimeRuleIds, [
            'fixture.fragment.double-7',
            'fixture.fragment.normalize',
            'fixture.fragment.normalize'
        ]);
        const laterTerm = kernelCall(
            kernelFree('fragment_later_head', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const rightTerm = kernelCall(
            kernelFree('fragment_right_head', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const proof = compiled.proofProgram?.compare(
            laterTerm,
            rightTerm,
            { stepLimit: 8 }
        );
        assert.equal(
            proof?.status,
            'solved',
            JSON.stringify(proof)
        );
        if (proof?.status === 'solved') {
            assert.deepEqual(
                proof.ruleApplications.map(application => [
                    application.ruleId,
                    application.ruleIndex
                ]),
                [['fixture.fragment.double-heads-7', 1]]
            );
        }
        assert.equal(
            CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
                .computesCryptographicHashes,
            false
        );
        assert.equal(
            CORE_LF_SAME_MODULE_FRAGMENT_WORKSPACE_PROFILE
                .supportsDependencyModules,
            false
        );
        assertDeepFrozen(compiled.plan);
    });

    it('is byte-stable across input permutations and excludes process state', () => {
        const first = compileFixture();
        const second = compileFixture(['first', 'third', 'base']);
        const firstSnapshot =
            createCoreLfSameModuleFragmentWorkspaceSnapshot(first);
        const secondSnapshot =
            createCoreLfSameModuleFragmentWorkspaceSnapshot(second);
        assert.equal(
            serializeCoreLfSameModuleFragmentWorkspaceSourceSnapshot(
                createCoreLfSameModuleFragmentWorkspaceSourceSnapshot(
                    first.plan
                )
            ),
            serializeCoreLfSameModuleFragmentWorkspaceSourceSnapshot(
                createCoreLfSameModuleFragmentWorkspaceSourceSnapshot(
                    second.plan
                )
            )
        );
        const text = serializeCoreLfSameModuleFragmentWorkspaceSnapshot(
            firstSnapshot
        );
        assert.equal(
            text,
            serializeCoreLfSameModuleFragmentWorkspaceSnapshot(secondSnapshot)
        );
        assert.equal(text.endsWith('\n'), true);
        assert.match(text, /fixture\.fragment\.double-heads-7/u);
        assert.match(text, /fragment-rules-a-policy-1/u);
        assert.doesNotMatch(
            text,
            /sessionIdentity|coreEnvironment|declarationMap|Symbol\(|function/u
        );
        assert.equal(
            serializeCoreLfSameModuleFragmentSource(
                first.fragments[0].sourceSnapshot
            ),
            first.fragments[0].sourceText
        );
        assertDeepFrozen(firstSnapshot);
    });

    it('rejects missing, stale, and forward external providers', () => {
        const { base, first, third } = fixture();
        expectFragmentError(
            () => defineCoreLfSameModuleMixedFragment({
                module: first.module,
                policy: first.policy,
                linkage: first.linkage,
                externalProviders: first.externalProviders.slice(1)
            }),
            'MISSING_PROVIDER'
        );
        expectFragmentError(
            () => defineCoreLfSameModuleMixedFragment({
                module: first.module,
                policy: first.policy,
                linkage: first.linkage,
                externalProviders: [
                    ...first.externalProviders,
                    { symbol: token, provider: base.identity }
                ]
            }),
            'INVALID_PROVIDER'
        );

        const stale = defineCoreLfSameModuleMixedFragment({
            module: third.module,
            policy: third.policy,
            linkage: third.linkage,
            externalProviders: third.externalProviders.map(external => ({
                ...external,
                provider: external.symbol.name === normalize.name
                    ? {
                        ...external.provider,
                        policyRevision: 'stale-policy'
                    }
                    : external.provider
            })),
            runtimeProvider: third.runtimeProvider
        });
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-stale-provider-1',
                fragments: [base, first, stale]
            }),
            'INVALID_PROVIDER'
        );

        const forward = defineCoreLfSameModuleMixedFragment({
            module: first.module,
            policy: first.policy,
            linkage: first.linkage,
            externalProviders: first.externalProviders.map(external => ({
                ...external,
                provider: external.symbol.name === normalize.name
                    ? third.identity
                    : external.provider
            }))
        });
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-forward-provider-1',
                fragments: [base, forward, third]
            }),
            'INVALID_PROVIDER'
        );
    });

    it('requires providers to own the symbol and preserve linkage', () => {
        const { base, first } = fixture();
        const indirect = thirdMixedFixture(base, first, {
            normalizeProvider: first.identity
        });
        const indirectPlan = createCoreLfSameModuleFragmentWorkspace({
            revision: 'fragment-indirect-provider-1',
            fragments: [base, first, indirect]
        });
        expectFragmentError(
            () => compileCoreLfSameModuleFragmentWorkspace(indirectPlan),
            'INVALID_PROVIDER'
        );

        const driftedEntries = first.linkage.entries.map(entry =>
            entry.symbol.name === normalize.name &&
            entry.kind === 'free-declaration'
                ? {
                    ...entry,
                    coreName: 'fragment_normalize_drift'
                }
                : entry
        );
        const driftedLinkage = createCoreLfMixedDeclarationLinkage(
            first.mixedPlan,
            {
                revision: 'fragment-rules-a-linkage-drift-1',
                moduleRevision: first.module.revision,
                entries: driftedEntries
            }
        );
        const drifted = defineCoreLfSameModuleMixedFragment({
            module: first.module,
            policy: first.policy,
            linkage: driftedLinkage,
            externalProviders: first.externalProviders
        });
        const driftPlan = createCoreLfSameModuleFragmentWorkspace({
            revision: 'fragment-linkage-drift-1',
            fragments: [base, drifted]
        });
        expectFragmentError(
            () => compileCoreLfSameModuleFragmentWorkspace(driftPlan),
            'PROVIDER_DRIFT'
        );
    });

    it('requires the exact latest source fragment as runtime provider', () => {
        const { base, first, third } = fixture();
        const missingRuntime = defineCoreLfSameModuleMixedFragment({
            module: third.module,
            policy: third.policy,
            linkage: third.linkage,
            externalProviders: third.externalProviders
        });
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-missing-runtime-1',
                fragments: [base, first, missingRuntime]
            }),
            'INVALID_RUNTIME_PROVIDER'
        );

        const wrongRuntime = defineCoreLfSameModuleMixedFragment({
            module: third.module,
            policy: third.policy,
            linkage: third.linkage,
            externalProviders: third.externalProviders,
            runtimeProvider: base.identity
        });
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-wrong-runtime-1',
                fragments: [base, first, wrongRuntime]
            }),
            'INVALID_RUNTIME_PROVIDER'
        );
    });

    it('rejects duplicate, overlapping, and source-pin-drifted fragments', () => {
        const { base, first } = fixture();
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-duplicate-1',
                fragments: [base, base]
            }),
            'DUPLICATE_FRAGMENT'
        );
        const overlapping = thirdMixedFixture(base, first, {
            firstOrder: 6
        });
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-overlap-1',
                fragments: [base, first, overlapping]
            }),
            'OVERLAPPING_SOURCE_ORDER'
        );
        const drifted = thirdMixedFixture(base, first, {
            sourceSha256: driftSha
        });
        expectFragmentError(
            () => createCoreLfSameModuleFragmentWorkspace({
                revision: 'fragment-pin-drift-1',
                fragments: [base, first, drifted]
            }),
            'SOURCE_PIN_DRIFT'
        );

        const canonical = createCoreLfSameModuleFragmentWorkspace({
            revision: 'fragment-canonical-plan-1',
            fragments: [base, first]
        });
        expectFragmentError(
            () => compileCoreLfSameModuleFragmentWorkspace({
                ...canonical,
                moduleId: 'fixture.fabricated'
            }),
            'INVALID_WORKSPACE'
        );
    });

    it('rejects unsupported pure and dependency-module fragments', () => {
        const base = baseFixture();
        const runtime = new CoreLfTransferScopedBuilder();
        const value = runtime.capture('value');
        const pure = createCoreLfModuleSpec({
            revision: 'fragment-pure-runtime-1',
            moduleId,
            fragmentId: 'pure-runtime',
            authorityPath,
            sourceSha256: sourceSha,
            dependencies: [],
            externalSymbols: [carrier, normalize].map(symbol => ({
                symbol,
                availability: 'earlier-fragment' as const
            })),
            declarations: [],
            inductives: [],
            runtimeRules: [{
                order: 5,
                id: 'fixture.fragment.pure',
                groupId: 'fixture.fragment.pure',
                clauseOrder: 0,
                sourceOwner: normalize,
                variables: [{ name: 'value', type: global(carrier) }],
                left: runtime.pattern(call(runtime, normalize, value)),
                right: runtime.template(value),
                provenance: source('rule pure;')
            }],
            proofRules: []
        });
        const purePolicy = policyFor(pure, 'fragment-pure-policy-1');
        const pureLinkage = createCoreLfTransferDeclarationLinkage(pure, {
            revision: 'fragment-pure-linkage-1',
            moduleRevision: pure.revision,
            entries: linkEntries([carrier, normalize])
        }) as CoreLfMixedDeclarationLinkage;
        expectFragmentError(
            () => defineCoreLfSameModuleMixedFragment({
                module: pure,
                policy: purePolicy,
                linkage: pureLinkage,
                externalProviders: pure.externalSymbols.map(external => ({
                    symbol: external.symbol,
                    provider: base.identity
                }))
            }),
            'UNSUPPORTED_FRAGMENT'
        );

        const foreign = coreLfQualifiedSymbol('fixture.foreign', 'Foreign');
        const dependencyModule = createCoreLfModuleSpec({
            revision: 'fragment-dependency-1',
            moduleId,
            fragmentId: 'dependency-mixed',
            authorityPath,
            sourceSha256: sourceSha,
            dependencies: ['fixture.foreign'],
            externalSymbols: [
                {
                    symbol: foreign,
                    availability: 'dependency-module' as const
                },
                ...[carrier, rightHead].map(symbol => ({
                    symbol,
                    availability: 'earlier-fragment' as const
                }))
            ],
            declarations: [declaration(5, double, unaryType())],
            inductives: [],
            runtimeRules: [],
            proofRules: [proofRule(
                6,
                'fixture.fragment.dependency-proof',
                double,
                rightHead
            )]
        });
        const dependencyPolicy = policyFor(
            dependencyModule,
            'fragment-dependency-policy-1'
        );
        const dependencyPlan = planCoreLfMixedPhases(
            dependencyModule,
            dependencyPolicy
        );
        const dependencyLinkage = createCoreLfMixedDeclarationLinkage(
            dependencyPlan,
            {
                revision: 'fragment-dependency-linkage-1',
                moduleRevision: dependencyModule.revision,
                entries: [
                    {
                        order: 0,
                        symbol: foreign,
                        kind: 'free-declaration',
                        coreName: 'fragment_foreign',
                        backendName: 'Foreign'
                    },
                    ...linkEntries([carrier, rightHead, double]).map(entry => ({
                        ...entry,
                        order: entry.order + 1
                    }))
                ]
            }
        );
        expectFragmentError(
            () => defineCoreLfSameModuleMixedFragment({
                module: dependencyModule,
                policy: dependencyPolicy,
                linkage: dependencyLinkage
            }),
            'UNSUPPORTED_FRAGMENT'
        );
    });
});
