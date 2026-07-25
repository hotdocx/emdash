/**
 * Focused SCALE-MIXED-PHASE-1A/1B/1C orchestration/composition tests.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_1_REPRESENTATION,
    CoreLfComposedProofProgram,
    CoreLfMixedCompilerError,
    CoreLfModuleSpec,
    CoreLfProofCompilerError,
    CoreLfTransferPolicyEntry,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    KernelExpression,
    binderMode,
    checkLambdapiProbe,
    compileCoreLfMixedPhases,
    composeCoreLfProofPrograms,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    planCoreLfMixedPhases,
    provenance
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');
const moduleId = 'fixture.mixed_phase';
const authorityPath = 'tests/fixtures/mixed_phase.lp';
const carrier = coreLfQualifiedSymbol(moduleId, 'Carrier');
const tokenType = coreLfQualifiedSymbol(moduleId, 'Token');
const token = coreLfQualifiedSymbol(moduleId, 'token');
const generatedIndToken =
    coreLfQualifiedSymbol(moduleId, 'ind_Token');
const normalize = coreLfQualifiedSymbol(moduleId, 'normalize');
const leftHead = coreLfQualifiedSymbol(moduleId, 'left_head');
const rightHead = coreLfQualifiedSymbol(moduleId, 'right_head');
const double = coreLfQualifiedSymbol(moduleId, 'double');

const source = (
    sourceFragment: string,
    path = authorityPath
) => ({ authorityPath: path, sourceFragment });

const modifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const unaryTokenType = () => ({
    tag: 'pi' as const,
    binder: {
        hint: 'value',
        mode: binderMode('explicit', 'functorial'),
        type: {
            tag: 'global' as const,
            symbol: tokenType
        }
    },
    body: {
        tag: 'global' as const,
        symbol: tokenType
    }
});

const builderCall = (
    builder: CoreLfTransferScopedBuilder,
    symbol: typeof normalize,
    values: readonly ReturnType<
        CoreLfTransferScopedBuilder['capture']
    >[]
) => builder.call(
    builder.global(symbol),
    values.map(value => ({
        plicity: 'explicit' as const,
        value
    }))
);

const normalizeRuntimeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    return {
        order: 3,
        id: 'fixture.mixed.normalize',
        groupId: 'fixture.mixed.normalize',
        clauseOrder: 0,
        sourceOwner: normalize,
        variables: [],
        left: builder.pattern(builderCall(
            builder,
            normalize,
            [builder.global(token)]
        )),
        right: builder.template(builder.global(token)),
        provenance: source('rule normalize token ↪ token;')
    };
};

const doubleRuntimeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const value = builder.capture('value');
    return {
        order: 8,
        id: 'fixture.mixed.double',
        groupId: 'fixture.mixed.double',
        clauseOrder: 0,
        sourceOwner: double,
        variables: [{
            name: 'value',
            type: {
                tag: 'global' as const,
                symbol: tokenType
            }
        }],
        left: builder.pattern(builderCall(
            builder,
            double,
            [value]
        )),
        right: builder.template(builderCall(
            builder,
            normalize,
            [builderCall(builder, normalize, [value])]
        )),
        provenance: source(
            'rule double $value ↪ normalize (normalize $value);'
        )
    };
};

const proofRule = () => {
    const pattern = new CoreLfTransferScopedBuilder();
    const template = new CoreLfTransferScopedBuilder();
    return {
        order: 6,
        id: 'fixture.mixed.heads',
        sourceOwner: leftHead,
        variables: ['x', 'y'].map(name => ({
            name,
            role: 'matched' as const,
            type: {
                tag: 'global' as const,
                symbol: tokenType
            }
        })),
        problem: {
            left: pattern.pattern(builderCall(
                pattern,
                leftHead,
                [pattern.capture('x')]
            )),
            right: pattern.pattern(builderCall(
                pattern,
                rightHead,
                [pattern.capture('y')]
            ))
        },
        generatedConstraints: [{
            left: template.template(template.capture('x')),
            right: template.template(template.capture('y'))
        }],
        provenance: source(
            'unif_rule left_head $x ≡ right_head $y ↪ [ $x ≡ $y ];'
        )
    };
};

const secondProofRule = (order: number) => {
    const pattern = new CoreLfTransferScopedBuilder();
    const template = new CoreLfTransferScopedBuilder();
    return {
        order,
        id: 'fixture.mixed.second-heads',
        sourceOwner: double,
        variables: ['x', 'y'].map(name => ({
            name,
            role: 'matched' as const,
            type: {
                tag: 'global' as const,
                symbol: tokenType
            }
        })),
        problem: {
            left: pattern.pattern(builderCall(
                pattern,
                double,
                [pattern.capture('x')]
            )),
            right: pattern.pattern(builderCall(
                pattern,
                rightHead,
                [pattern.capture('y')]
            ))
        },
        generatedConstraints: [{
            left: template.template(template.capture('x')),
            right: template.template(template.capture('y'))
        }],
        provenance: source(
            'unif_rule double $x ≡ right_head $y ↪ [ $x ≡ $y ];'
        )
    };
};

const fixtureModule = (): CoreLfModuleSpec =>
    createCoreLfModuleSpec({
        revision: 'mixed-phase-fixture-1',
        moduleId,
        fragmentId: 'mixed-source',
        authorityPath,
        sourceSha256:
            'sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc',
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: carrier,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers,
                provenance: source('symbol Carrier : TYPE;')
            },
            {
                order: 2,
                symbol: normalize,
                type: unaryTokenType(),
                body: coreLfTransferAbsentBody(),
                modifiers,
                provenance: source(
                    'symbol normalize (value : Token) : Token;'
                )
            },
            {
                order: 4,
                symbol: leftHead,
                type: unaryTokenType(),
                body: coreLfTransferAbsentBody(),
                modifiers,
                provenance: source(
                    'symbol left_head (value : Token) : Token;'
                )
            },
            {
                order: 5,
                symbol: rightHead,
                type: unaryTokenType(),
                body: coreLfTransferAbsentBody(),
                modifiers,
                provenance: source(
                    'symbol right_head (value : Token) : Token;'
                )
            },
            {
                order: 7,
                symbol: double,
                type: unaryTokenType(),
                body: coreLfTransferAbsentBody(),
                modifiers,
                provenance: source(
                    'symbol double (value : Token) : Token;'
                )
            }
        ],
        inductives: [{
            order: 1,
            symbol: tokenType,
            parameters: [],
            indices: [],
            sort: { tag: 'type' },
            constructors: [{
                order: 0,
                symbol: token,
                binders: [],
                result: {
                    tag: 'global',
                    symbol: tokenType
                },
                provenance: source('| token : Token;')
            }],
            generatedSymbols: [generatedIndToken],
            modifiers: {
                ...modifiers,
                rigidity: 'injective'
            },
            provenance: source(
                'inductive Token : TYPE ≔ | token : Token;'
            )
        }],
        runtimeRules: [
            normalizeRuntimeRule(),
            doubleRuntimeRule()
        ],
        proofRules: [proofRule()]
    });

interface PolicySource {
    readonly sourceOrder: number;
    readonly entry: Omit<CoreLfTransferPolicyEntry, 'order'>;
}

const fixturePolicy = (
    module: CoreLfModuleSpec,
    revision = `${module.revision}-policy`
): CoreLfTransferPolicyOverlay => {
    const entries: PolicySource[] = [
        ...module.declarations.map(declaration => ({
            sourceOrder: declaration.order,
            entry: {
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: 'opaque-signature' as const,
                evidence: 'mixed declaration fixture'
            }
        })),
        ...module.inductives.map(inductive => ({
            sourceOrder: inductive.order,
            entry: {
                target: {
                    kind: 'inductive' as const,
                    symbol: inductive.symbol
                },
                policy: 'opaque-signature' as const,
                evidence: 'mixed inductive signature fixture'
            }
        })),
        ...module.runtimeRules.map(rule => ({
            sourceOrder: rule.order,
            entry: {
                target: {
                    kind: 'runtime-rule' as const,
                    id: rule.id
                },
                policy: 'runtime-rewrite' as const,
                evidence: 'mixed runtime fixture'
            }
        })),
        ...module.proofRules.map(rule => ({
            sourceOrder: rule.order,
            entry: {
                target: {
                    kind: 'proof-rule' as const,
                    id: rule.id
                },
                policy: 'proof-unification' as const,
                evidence: 'mixed proof fixture'
            }
        }))
    ];
    entries.sort(
        (left, right) => left.sourceOrder - right.sourceOrder
    );
    return createCoreLfTransferPolicyOverlay(module, {
        revision,
        moduleRevision: module.revision,
        entries: entries.map(({ entry }, order) => ({
            order,
            ...entry
        }))
    });
};

const fixtureLinkage = (
    plan: ReturnType<typeof planCoreLfMixedPhases>
) => createCoreLfMixedDeclarationLinkage(plan, {
    revision: 'mixed-phase-linkage-1',
    moduleRevision: plan.sourceModule.revision,
    entries: [
        carrier,
        tokenType,
        token,
        normalize,
        leftHead,
        rightHead,
        double
    ].map((symbol, order) => ({
        order,
        symbol,
        kind: 'free-declaration' as const,
        coreName: `mixed_${symbol.name}`,
        backendName: symbol.name
    }))
});

const expectMixedError = (
    action: () => unknown,
    code: CoreLfMixedCompilerError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfMixedCompilerError &&
            error.code === code
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const proofRuntimeVisibilityProbe = (
    assertionBeforeRuntime: boolean
): string => {
    const assertion =
        'assert ⊢ @eq_refl phase_carrier phase_left : ' +
        'τ (@= phase_carrier phase_left phase_right);';
    return [
        'require open emdash.emdash3_2;',
        'injective symbol phase_carrier : Grpd;',
        'injective symbol phase_left : τ phase_carrier;',
        'injective symbol phase_right : τ phase_carrier;',
        'injective symbol later_runtime',
        '  (x : τ phase_carrier) : τ phase_carrier;',
        'injective symbol later_target',
        '  (x : τ phase_carrier) : τ phase_carrier;',
        'unif_rule phase_left ≡ phase_right',
        '  ↪ [ later_runtime phase_left ≡ later_target phase_left ];',
        ...(assertionBeforeRuntime ? [assertion] : []),
        'rule later_runtime $x ↪ later_target $x;',
        ...(assertionBeforeRuntime ? [] : [assertion]),
        ''
    ].join('\n');
};

describe('SCALE-MIXED-PHASE-1 generic source-order planner', () => {
    it('partitions every source item into a phase-pure immutable plan', () => {
        const module = fixtureModule();
        const plan = planCoreLfMixedPhases(
            module,
            fixturePolicy(module)
        );

        assert.equal(plan.semanticStatus, 'phase-plan-only');
        assert.deepEqual(
            plan.phases.map(phase => [
                phase.kind,
                phase.sourceOrders
            ]),
            [
                ['declaration', [0]],
                ['inductive-signature', [1]],
                ['declaration', [2]],
                ['runtime', [3]],
                ['declaration', [4]],
                ['declaration', [5]],
                ['proof', [6]],
                ['declaration', [7]],
                ['runtime', [8]]
            ]
        );
        const firstRuntime = plan.phases[3];
        assert.equal(firstRuntime.kind, 'runtime');
        if (firstRuntime.kind !== 'runtime') return;
        assert.equal(firstRuntime.groupId, 'fixture.mixed.normalize');
        assert.deepEqual(firstRuntime.clauseOrders, [0]);
        assert.deepEqual(
            firstRuntime.module.externalSymbols.map(external => [
                external.symbol.name,
                external.availability
            ]),
            [
                ['token', 'earlier-fragment'],
                ['normalize', 'earlier-fragment']
            ]
        );
        const inductive = plan.phases[1];
        assert.equal(inductive.kind, 'inductive-signature');
        if (inductive.kind !== 'inductive-signature') return;
        assert.deepEqual(
            inductive.lowering.module.declarations.map(
                declaration => declaration.symbol.name
            ),
            ['Token', 'token']
        );
        assertDeepFrozen(plan);
    });

    it('compiles all four phase kinds through their existing engines', () => {
        const module = fixtureModule();
        const plan = planCoreLfMixedPhases(
            module,
            fixturePolicy(module)
        );
        const compiled = compileCoreLfMixedPhases(
            plan,
            fixtureLinkage(plan)
        );

        assert.deepEqual(
            compiled.declarations.environment.declarations.map(
                declaration => declaration.name
            ),
            [
                'mixed_Carrier',
                'mixed_Token',
                'mixed_token',
                'mixed_normalize',
                'mixed_left_head',
                'mixed_right_head',
                'mixed_double'
            ]
        );
        assert.deepEqual(
            compiled.latestRuntime?.runtime.ruleIds,
            [
                'fixture.mixed.normalize',
                'fixture.mixed.double'
            ]
        );
        const finalRuntime = compiled.phases[8];
        assert.equal(finalRuntime.kind, 'runtime');
        if (finalRuntime.kind !== 'runtime') return;
        assert.deepEqual(
            finalRuntime.runtime.localProgram.rules[0]
                .checkedWithEarlierRuleIds,
            ['fixture.mixed.normalize']
        );
        assert.equal(compiled.proofPrograms.length, 1);
        assert.deepEqual(
            compiled.proofPrograms[0].ruleIds,
            ['fixture.mixed.heads']
        );
        assert.ok(
            compiled.proofProgram instanceof
                CoreLfComposedProofProgram
        );
        if (
            !(compiled.proofProgram instanceof
                CoreLfComposedProofProgram)
        ) return;
        assert.notEqual(
            compiled.proofPrograms[0].runtimeProgram,
            compiled.latestRuntime?.runtime
        );
        assert.equal(
            compiled.proofProgram.runtimeProgram,
            compiled.latestRuntime?.runtime
        );

        const nodeSource = provenance(
            'derived',
            'mixed phase executable witness'
        );
        const tokenTerm = kernelFree('mixed_token', nodeSource);
        const normalizeToken = kernelCall(
            kernelFree('mixed_normalize', nodeSource),
            [{
                plicity: 'explicit',
                value: tokenTerm
            }],
            nodeSource
        );
        const firstRewrite =
            compiled.latestRuntime?.runtime.rewriteHead(normalizeToken);
        assert.equal(firstRewrite?.status, 'rewritten');
        if (firstRewrite?.status === 'rewritten') {
            assert.equal(
                kernelExpressionEquals(
                    firstRewrite.after,
                    tokenTerm
                ),
                true
            );
        }

        const left = kernelCall(
            kernelFree('mixed_left_head', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const right = kernelCall(
            kernelFree('mixed_right_head', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const proof = compiled.proofPrograms[0].compare(
            left,
            right,
            { stepLimit: 8 }
        );
        assert.equal(proof.status, 'solved');
        assert.deepEqual(
            proof.ruleApplications.map(application =>
                application.ruleId
            ),
            ['fixture.mixed.heads']
        );
        assert.equal(Object.isFrozen(compiled), true);
        assert.equal(Object.isFrozen(compiled.phases), true);
    });

    it('plans the exact stress modules without promoting their policy', () => {
        const stress = CORE_LF_SCALE_STRESS_1_REPRESENTATION;
        const core = planCoreLfMixedPhases(
            stress.core.module,
            stress.core.policy
        );
        const nat = planCoreLfMixedPhases(
            stress.nat.module,
            stress.nat.policy
        );

        assert.deepEqual(
            core.phases.map(phase => [
                phase.kind,
                phase.sourceOrders
            ]),
            [
                ['declaration', [0]],
                ['runtime', [1]],
                ['inductive-signature', [2]],
                ['declaration', [3]],
                ['runtime', [4]],
                ['declaration', [5]],
                ['runtime', [6]]
            ]
        );
        assert.deepEqual(
            nat.phases.map(phase => [
                phase.kind,
                phase.sourceOrders
            ]),
            [
                ['declaration', [0]],
                ['runtime', [1, 2, 3]]
            ]
        );
        const natRuntime = nat.phases[1];
        assert.equal(natRuntime.kind, 'runtime');
        if (natRuntime.kind !== 'runtime') return;
        assert.deepEqual(natRuntime.clauseOrders, [0, 1, 2]);
        assert.ok(
            [...core.phases, ...nat.phases].every(phase =>
                phase.policy.entries.every(
                    entry => entry.policy === 'conformance-only'
                )
            )
        );
        assert.ok(
            core.doesNotProvide.includes(
                'generated-induction-semantics'
            )
        );
    });

    it('composes an explicit dependency-module runtime with local phases', () => {
        const baseModule = fixtureModule();
        const basePlan = planCoreLfMixedPhases(
            baseModule,
            fixturePolicy(baseModule)
        );
        const base = compileCoreLfMixedPhases(
            basePlan,
            fixtureLinkage(basePlan)
        );
        assert.notEqual(base.latestRuntime, undefined);
        if (base.latestRuntime === undefined) return;

        const consumerModuleId = 'fixture.mixed_consumer';
        const consume =
            coreLfQualifiedSymbol(consumerModuleId, 'consume');
        const builder = new CoreLfTransferScopedBuilder();
        const value = builder.capture('value');
        const module = createCoreLfModuleSpec({
            revision: 'mixed-consumer-1',
            moduleId: consumerModuleId,
            fragmentId: 'consumer',
            authorityPath: 'tests/fixtures/mixed_consumer.lp',
            sourceSha256:
                'sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd',
            dependencies: [moduleId],
            externalSymbols: [
                tokenType,
                normalize
            ].map(symbol => ({
                symbol,
                availability: 'dependency-module' as const
            })),
            declarations: [{
                order: 0,
                symbol: consume,
                type: unaryTokenType(),
                body: coreLfTransferAbsentBody(),
                modifiers,
                provenance: source(
                    'symbol consume (value : Token) : Token;',
                    'tests/fixtures/mixed_consumer.lp'
                )
            }],
            inductives: [],
            runtimeRules: [{
                order: 1,
                id: 'fixture.mixed.consume',
                groupId: 'fixture.mixed.consume',
                clauseOrder: 0,
                sourceOwner: consume,
                variables: [{
                    name: 'value',
                    type: {
                        tag: 'global',
                        symbol: tokenType
                    }
                }],
                left: builder.pattern(builderCall(
                    builder,
                    consume,
                    [value]
                )),
                right: builder.template(builderCall(
                    builder,
                    normalize,
                    [value]
                )),
                provenance: source(
                    'rule consume $value ↪ normalize $value;',
                    'tests/fixtures/mixed_consumer.lp'
                )
            }],
            proofRules: []
        });
        const policy = createCoreLfTransferPolicyOverlay(module, {
            revision: 'mixed-consumer-policy-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    target: {
                        kind: 'declaration',
                        symbol: consume
                    },
                    policy: 'opaque-signature',
                    evidence: 'mixed consumer declaration'
                },
                {
                    order: 1,
                    target: {
                        kind: 'runtime-rule',
                        id: 'fixture.mixed.consume'
                    },
                    policy: 'runtime-rewrite',
                    evidence: 'mixed consumer runtime'
                }
            ]
        });
        const plan = planCoreLfMixedPhases(module, policy);
        const linkage = createCoreLfMixedDeclarationLinkage(plan, {
            revision: 'mixed-consumer-linkage-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    symbol: tokenType,
                    kind: 'free-declaration',
                    coreName: 'mixed_Token',
                    backendName: 'Token'
                },
                {
                    order: 1,
                    symbol: normalize,
                    kind: 'free-declaration',
                    coreName: 'mixed_normalize',
                    backendName: 'normalize'
                },
                {
                    order: 2,
                    symbol: consume,
                    kind: 'free-declaration',
                    coreName: 'mixed_consume',
                    backendName: 'consume'
                }
            ]
        });
        const compiled = compileCoreLfMixedPhases(
            plan,
            linkage,
            {
                initialDeclarations: base.declarations,
                runtimeDependencies: [{
                    relation: 'dependency-module',
                    fragment: base.latestRuntime
                }]
            }
        );

        assert.deepEqual(
            compiled.latestRuntime?.runtime.ruleIds,
            [
                'fixture.mixed.normalize',
                'fixture.mixed.double',
                'fixture.mixed.consume'
            ]
        );
        assert.deepEqual(
            compiled.latestRuntime?.localProgram.rules[0]
                .checkedWithEarlierRuleIds,
            [
                'fixture.mixed.normalize',
                'fixture.mixed.double'
            ]
        );
        assert.deepEqual(
            compiled.latestRuntime?.dependencies.map(
                dependency => dependency.relation
            ),
            ['dependency-module']
        );
    });

    it('rejects a runtime group split by another source phase', () => {
        const fixture = fixtureModule();
        const runtimeRules = fixture.runtimeRules.map(
            (rule, index) => ({
                ...rule,
                groupId: 'fixture.mixed.split',
                clauseOrder: index
            })
        );
        const module = createCoreLfModuleSpec({
            ...fixture,
            revision: 'mixed-split-runtime-1',
            runtimeRules
        });
        expectMixedError(
            () => planCoreLfMixedPhases(
                module,
                fixturePolicy(module)
            ),
            'SPLIT_RUNTIME_GROUP'
        );
    });

    it('rejects a source-phase forward declaration reference', () => {
        const fixture = fixtureModule();
        const module = createCoreLfModuleSpec({
            ...fixture,
            revision: 'mixed-forward-reference-1',
            declarations: fixture.declarations.map(
                declaration =>
                    declaration.symbol.name === 'Carrier'
                        ? {
                            ...declaration,
                            type: {
                                tag: 'global' as const,
                                symbol: double
                            }
                        }
                        : declaration
            )
        });
        expectMixedError(
            () => planCoreLfMixedPhases(
                module,
                fixturePolicy(module)
            ),
            'FORWARD_PHASE_REFERENCE'
        );
    });

    it('rejects any reference to an untyped generated owner', () => {
        const fixture = fixtureModule();
        const module = createCoreLfModuleSpec({
            ...fixture,
            revision: 'mixed-generated-reference-1',
            declarations: fixture.declarations.map(
                declaration =>
                    declaration.symbol.name === 'double'
                        ? {
                            ...declaration,
                            type: {
                                tag: 'global' as const,
                                symbol: generatedIndToken
                            }
                        }
                        : declaration
            )
        });
        expectMixedError(
            () => planCoreLfMixedPhases(
                module,
                fixturePolicy(module)
            ),
            'UNTYPED_GENERATED_SYMBOL_REFERENCED'
        );
    });

    it('requires exact policy coverage before making a plan', () => {
        const module = fixtureModule();
        const policy = fixturePolicy(module);
        const incomplete = createCoreLfTransferPolicyOverlay(
            module,
            {
                revision: 'mixed-incomplete-policy-1',
                moduleRevision: module.revision,
                entries: policy.entries.slice(0, -1)
            }
        );
        expectMixedError(
            () => planCoreLfMixedPhases(module, incomplete),
            'INCOMPLETE_MIXED_POLICY'
        );
    });

    it('composes same-prefix proof phases under one queue and budget', () => {
        const fixture = fixtureModule();
        const module = createCoreLfModuleSpec({
            ...fixture,
            revision: 'mixed-separated-proof-1',
            runtimeRules: fixture.runtimeRules.filter(
                rule => rule.id === 'fixture.mixed.normalize'
            ),
            proofRules: [
                fixture.proofRules[0],
                secondProofRule(8)
            ]
        });
        const plan = planCoreLfMixedPhases(
            module,
            fixturePolicy(module)
        );
        assert.equal(
            plan.phases.filter(phase => phase.kind === 'proof').length,
            2
        );
        const compiled = compileCoreLfMixedPhases(
            plan,
            fixtureLinkage(plan)
        );
        assert.equal(compiled.proofPrograms.length, 2);
        assert.ok(
            compiled.proofProgram instanceof
                CoreLfComposedProofProgram
        );
        if (
            !(compiled.proofProgram instanceof
                CoreLfComposedProofProgram)
        ) return;
        assert.deepEqual(compiled.proofProgram.ruleIds, [
            'fixture.mixed.heads',
            'fixture.mixed.second-heads'
        ]);
        assert.deepEqual(
            compiled.proofProgram.phases.map(phase => [
                phase.ruleIds,
                phase.precedingRuleIds
            ]),
            [
                [['fixture.mixed.heads'], []],
                [[
                    'fixture.mixed.second-heads'
                ], ['fixture.mixed.heads']]
            ]
        );
        assert.equal(
            compiled.proofProgram.runtimeProgram,
            compiled.proofPrograms[0].runtimeProgram
        );
        assert.equal(
            compiled.proofProgram.runtimeProgram,
            compiled.latestRuntime?.runtime
        );

        const nodeSource = provenance(
            'derived',
            'composed proof phase witness'
        );
        const tokenTerm = kernelFree('mixed_token', nodeSource);
        const doubleTerm = kernelCall(
            kernelFree('mixed_double', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const right = kernelCall(
            kernelFree('mixed_right_head', nodeSource),
            [{ plicity: 'explicit', value: tokenTerm }],
            nodeSource
        );
        const bounded = compiled.proofProgram.compare(
            doubleTerm,
            right,
            { stepLimit: 0 }
        );
        assert.equal(bounded.status, 'step-limit-exceeded');
        if (bounded.status === 'step-limit-exceeded') {
            assert.deepEqual(bounded.next, {
                kind: 'proof-rule',
                ruleId: 'fixture.mixed.second-heads',
                orientation: 'forward'
            });
        }
        const solved = compiled.proofProgram.compare(
            doubleTerm,
            right,
            { stepLimit: 4 }
        );
        assert.equal(solved.status, 'solved');
        assert.deepEqual(
            solved.ruleApplications.map(application => [
                application.ruleId,
                application.ruleIndex
            ]),
            [['fixture.mixed.second-heads', 1]]
        );
    });

    it('uses the completed runtime for divergent proof prefixes', () => {
        const fixture = fixtureModule();
        const module = createCoreLfModuleSpec({
            ...fixture,
            revision: 'mixed-divergent-proof-runtime-1',
            proofRules: [
                fixture.proofRules[0],
                secondProofRule(9)
            ]
        });
        const plan = planCoreLfMixedPhases(
            module,
            fixturePolicy(module)
        );
        const compiled = compileCoreLfMixedPhases(
            plan,
            fixtureLinkage(plan)
        );
        assert.deepEqual(
            compiled.proofPrograms.map(program =>
                program.runtimeProgram?.ruleIds
            ),
            [
                ['fixture.mixed.normalize'],
                [
                    'fixture.mixed.normalize',
                    'fixture.mixed.double'
                ]
            ]
        );
        assert.ok(
            compiled.proofProgram instanceof
                CoreLfComposedProofProgram
        );
        if (
            !(compiled.proofProgram instanceof
                CoreLfComposedProofProgram)
        ) return;
        assert.equal(
            compiled.proofProgram.runtimeProgram,
            compiled.latestRuntime?.runtime
        );

        const nodeSource = provenance(
            'derived',
            'completed proof runtime witness'
        );
        const tokenTerm = kernelFree('mixed_token', nodeSource);
        const call = (
            name: string,
            value: KernelExpression
        ) => kernelCall(
            kernelFree(name, nodeSource),
            [{ plicity: 'explicit', value }],
            nodeSource
        );
        const doubleTerm = call('mixed_double', tokenTerm);
        const expanded = call(
            'mixed_normalize',
            call('mixed_normalize', tokenTerm)
        );
        const final = compiled.proofProgram.compare(
            doubleTerm,
            expanded,
            { stepLimit: 4 }
        );
        assert.equal(final.status, 'solved');
        assert.deepEqual(
            final.trace.flatMap(entry =>
                entry.kind === 'reduction' &&
                entry.reduction.kind === 'runtime'
                    ? [entry.reduction.ruleId]
                    : []
            ),
            ['fixture.mixed.double']
        );
        assert.deepEqual(final.ruleApplications, []);

        assert.throws(
            () => composeCoreLfProofPrograms(
                compiled.proofPrograms,
                compiled.declarations,
                {
                    executionRuntimeProgram:
                        compiled.proofPrograms[0].runtimeProgram
                }
            ),
            error =>
                error instanceof CoreLfProofCompilerError &&
                error.code === 'INVALID_PROOF_COMPOSITION' &&
                /does not extend/u.test(error.message)
        );
    });

    it(
        'matches Lambdapi final-signature proof/runtime visibility',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_SCALE_PROBES !== '1'
        },
        () => {
            const options = {
                packageRoot: resolve(repositoryRoot, 'emdash2'),
                timeoutMs: 30_000
            };
            const completed = checkLambdapiProbe(
                {
                    source: proofRuntimeVisibilityProbe(false),
                    sourceMap: []
                },
                options
            );
            assert.equal(
                completed.accepted,
                true,
                completed.diagnostics
            );
            assert.equal(completed.timedOut, false);

            const sourcePosition = checkLambdapiProbe(
                {
                    source: proofRuntimeVisibilityProbe(true),
                    sourceMap: []
                },
                options
            );
            assert.equal(sourcePosition.accepted, false);
            assert.equal(sourcePosition.timedOut, false);
            assert.match(
                sourcePosition.diagnostics,
                /Assertion failed/u
            );
        }
    );

    it('keeps orchestration owner-free and outside the browser API', () => {
        const implementation = readFileSync(
            resolve(
                repositoryRoot,
                'src/v3_2/lf_transfer_mixed.ts'
            ),
            'utf8'
        );
        assert.doesNotMatch(
            implementation,
            /ind_eqr|Pi_grpd|τΣ_|Struct_sigma|nat_add/u
        );
        assert.equal('planCoreLfMixedPhases' in browser, false);
        assert.equal('compileCoreLfMixedPhases' in browser, false);
    });
});
