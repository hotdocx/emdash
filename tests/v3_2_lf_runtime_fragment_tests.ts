/**
 * Representation-only SCALE-RUNTIME-DEPS-1 tests for explicit immutable
 * runtime-fragment dependency closure and deterministic composition.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreLfCompiledRuntimeFragment,
    CoreLfModuleSpec,
    CoreLfRuntimeCompilerError,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    compileCoreDirectedContinuationRuntimeTransfer,
    compileCoreLfDeclarations,
    compileCoreLfRuntimeFragment,
    compileCoreLfRuntimeProgram,
    coreLfCombinedWeakHead,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const expectRuntimeError = (
    action: () => unknown,
    code: CoreLfRuntimeCompilerError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfRuntimeCompilerError &&
            error.code === code
    );
};

const symbolModuleId = 'fixture.runtime_dependency_symbols';
const nat = coreLfQualifiedSymbol(symbolModuleId, 'Nat');
const zero = coreLfQualifiedSymbol(symbolModuleId, 'zero');
const first = coreLfQualifiedSymbol(symbolModuleId, 'first');
const second = coreLfQualifiedSymbol(symbolModuleId, 'second');
const third = coreLfQualifiedSymbol(symbolModuleId, 'third');
const sibling = coreLfQualifiedSymbol(symbolModuleId, 'sibling');
const top = coreLfQualifiedSymbol(symbolModuleId, 'top');
const familyCode =
    coreLfQualifiedSymbol(symbolModuleId, 'FamilyCode');
const aliasCode =
    coreLfQualifiedSymbol(symbolModuleId, 'alias_code');
const baseCode =
    coreLfQualifiedSymbol(symbolModuleId, 'base_code');
const decodeCode =
    coreLfQualifiedSymbol(symbolModuleId, 'decode_code');
const baseWitness =
    coreLfQualifiedSymbol(symbolModuleId, 'base_witness');
const consumeAlias =
    coreLfQualifiedSymbol(symbolModuleId, 'consume_alias');

const source = (
    authorityPath: string,
    sourceFragment: string
) => ({ authorityPath, sourceFragment });

const declarationModifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const unaryNatType = () => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'x',
        builder.global(nat),
        _ => builder.global(nat)
    ));
};

const decoderType = () => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'code',
        builder.global(familyCode),
        _ => builder.type()
    ));
};

const decodedType = (codeSymbol: typeof aliasCode) => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.call(
        builder.global(decodeCode),
        [{
            plicity: 'explicit',
            value: builder.global(codeSymbol)
        }]
    ));
};

const consumeAliasType = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const decodedAlias = builder.call(
        builder.global(decodeCode),
        [{
            plicity: 'explicit',
            value: builder.global(aliasCode)
        }]
    );
    return builder.term(builder.pi(
        'x',
        decodedAlias,
        _ => builder.call(
            builder.global(decodeCode),
            [{
                plicity: 'explicit',
                value: builder.global(aliasCode)
            }]
        )
    ));
};

const compileDeclarations = () => {
    const authorityPath =
        'tests/fixtures/runtime_dependency_symbols.lp';
    const module = createCoreLfModuleSpec({
        revision: 'runtime-dependency-declarations-1',
        moduleId: symbolModuleId,
        fragmentId: 'runtime-dependency-declarations',
        authorityPath,
        sourceSha256:
            'sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc',
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: nat,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol Nat : TYPE;'
                )
            },
            {
                order: 1,
                symbol: zero,
                type: { tag: 'global', symbol: nat },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol zero : Nat;'
                )
            },
            ...[first, second, third, sibling, top].map(
                (symbol, index) => ({
                    order: index + 2,
                    symbol,
                    type: unaryNatType(),
                    body: coreLfTransferAbsentBody(),
                    modifiers: declarationModifiers,
                    provenance: source(
                        authorityPath,
                        `symbol ${symbol.name} (x : Nat) : Nat;`
                    )
                })
            ),
            {
                order: 7,
                symbol: familyCode,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol FamilyCode : TYPE;'
                )
            },
            {
                order: 8,
                symbol: aliasCode,
                type: { tag: 'global', symbol: familyCode },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol alias_code : FamilyCode;'
                )
            },
            {
                order: 9,
                symbol: baseCode,
                type: { tag: 'global', symbol: familyCode },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol base_code : FamilyCode;'
                )
            },
            {
                order: 10,
                symbol: decodeCode,
                type: decoderType(),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol decode_code (c : FamilyCode) : TYPE;'
                )
            },
            {
                order: 11,
                symbol: baseWitness,
                type: decodedType(baseCode),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol base_witness : decode_code base_code;'
                )
            },
            {
                order: 12,
                symbol: consumeAlias,
                type: consumeAliasType(),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: source(
                    authorityPath,
                    'symbol consume_alias ' +
                        '(x : decode_code alias_code) : ' +
                        'decode_code alias_code;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'runtime-dependency-declaration-policy-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: 'runtime dependency declaration fixture'
        }))
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'runtime-dependency-linkage-1',
        moduleRevision: module.revision,
        entries: module.declarations.map((declaration, order) => ({
            order,
            symbol: declaration.symbol,
            kind: 'free-declaration' as const,
            coreName: `runtime_dependency_${declaration.symbol.name}`,
            backendName: declaration.symbol.name
        }))
    });
    return compileCoreLfDeclarations(module, policy, linkage);
};

const runtimePolicy = (
    module: CoreLfModuleSpec
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision: `${module.revision}-policy`,
        moduleRevision: module.revision,
        entries: module.runtimeRules.map((rule, order) => ({
            order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: 'runtime dependency representation fixture'
        }))
    });

interface RuntimeModuleInput {
    readonly revision: string;
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly dependencies: readonly string[];
    readonly head?: typeof first;
    readonly target?: typeof first;
    readonly ruleId?: string;
}

const runtimeModule = (
    input: RuntimeModuleInput
): CoreLfModuleSpec => {
    const authorityPath =
        `tests/fixtures/${input.moduleId.replace(/\./gu, '_')}.lp`;
    const runtimeRules = input.head === undefined
        ? []
        : (() => {
            assert.notEqual(input.ruleId, undefined);
            const pattern = new CoreLfTransferScopedBuilder();
            const template = new CoreLfTransferScopedBuilder();
            const left = pattern.pattern(pattern.call(
                pattern.global(input.head),
                [{
                    plicity: 'explicit',
                    value: pattern.capture('x')
                }]
            ));
            const right = input.target === undefined
                ? template.template(template.capture('x'))
                : template.template(template.call(
                    template.global(input.target),
                    [{
                        plicity: 'explicit',
                        value: template.capture('x')
                    }]
                ));
            return [{
                order: 0,
                id: input.ruleId!,
                groupId: input.ruleId!,
                clauseOrder: 0,
                sourceOwner: input.head,
                variables: [{
                    name: 'x',
                    type: { tag: 'global' as const, symbol: nat }
                }],
                left,
                right,
                provenance: source(
                    authorityPath,
                    `rule ${input.head.name} $x ↪ ` +
                        (input.target === undefined
                            ? '$x;'
                            : `${input.target.name} $x;`)
                )
            }];
        })();
    const referenced = [
        ...(input.head === undefined ? [] : [nat, input.head]),
        ...(input.target === undefined ? [] : [input.target])
    ];
    const dependencies = referenced.length === 0
        ? input.dependencies
        : [
            symbolModuleId,
            ...input.dependencies.filter(
                dependency => dependency !== symbolModuleId
            )
        ];
    return createCoreLfModuleSpec({
        revision: input.revision,
        moduleId: input.moduleId,
        fragmentId: input.fragmentId,
        authorityPath,
        sourceSha256:
            'sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd',
        dependencies,
        externalSymbols: referenced.map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules,
        proofRules: []
    });
};

const compileBaseClosure = () => {
    const declarations = compileDeclarations();
    const baseModule = runtimeModule({
        revision: 'runtime-dependency-base-1',
        moduleId: 'fixture.runtime_dependency_base',
        fragmentId: 'base-rules',
        dependencies: [],
        head: first,
        ruleId: 'fixture.first.evaluate'
    });
    const base = compileCoreLfRuntimeFragment(
        baseModule,
        runtimePolicy(baseModule),
        declarations,
        { dependencies: [] }
    );

    const consumerModule = runtimeModule({
        revision: 'runtime-dependency-consumer-1',
        moduleId: 'fixture.runtime_dependency_consumer',
        fragmentId: 'consumer-rules',
        dependencies: ['fixture.runtime_dependency_base'],
        head: second,
        target: first,
        ruleId: 'fixture.second.evaluate'
    });
    const consumer = compileCoreLfRuntimeFragment(
        consumerModule,
        runtimePolicy(consumerModule),
        declarations,
        {
            dependencies: [{
                relation: 'dependency-module',
                fragment: base
            }]
        }
    );

    const laterModule = runtimeModule({
        revision: 'runtime-dependency-later-1',
        moduleId: 'fixture.runtime_dependency_consumer',
        fragmentId: 'later-rules',
        dependencies: [],
        head: third,
        target: second,
        ruleId: 'fixture.third.evaluate'
    });
    const later = compileCoreLfRuntimeFragment(
        laterModule,
        runtimePolicy(laterModule),
        declarations,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: consumer
            }]
        }
    );
    return { declarations, base, consumer, later };
};

const freeTerm = (
    closure: ReturnType<typeof compileBaseClosure>,
    symbol: typeof nat
) => {
    const link = closure.declarations.declaration(symbol)?.link;
    assert.equal(link?.kind, 'free-declaration');
    if (link?.kind !== 'free-declaration') {
        assert.fail(`Missing fixture declaration ${symbol.name}`);
    }
    return kernelFree(
        link.coreName,
        provenance('derived', `runtime dependency ${symbol.name}`)
    );
};

const application = (
    closure: ReturnType<typeof compileBaseClosure>,
    symbol: typeof first,
    argument: ReturnType<typeof kernelFree>
) => closure.declarations.application(
    symbol,
    [argument],
    provenance(
        'derived',
        `runtime dependency ${symbol.name} application`
    )
);

describe('SCALE-RUNTIME-DEPS-1 generic runtime composition', () => {
    it('composes dependency-module then earlier-fragment prefixes', () => {
        const closure = compileBaseClosure();
        assert.deepEqual(closure.base.runtime.ruleIds, [
            'fixture.first.evaluate'
        ]);
        assert.deepEqual(closure.consumer.runtime.ruleIds, [
            'fixture.first.evaluate',
            'fixture.second.evaluate'
        ]);
        assert.deepEqual(closure.later.runtime.ruleIds, [
            'fixture.first.evaluate',
            'fixture.second.evaluate',
            'fixture.third.evaluate'
        ]);
        assert.deepEqual(
            closure.consumer.localProgram.rules[0]
                .checkedWithEarlierRuleIds,
            ['fixture.first.evaluate']
        );
        assert.deepEqual(
            closure.later.localProgram.rules[0]
                .checkedWithEarlierRuleIds,
            [
                'fixture.first.evaluate',
                'fixture.second.evaluate'
            ]
        );
        assert.deepEqual(
            closure.later.runtime.fragments.map(fragment =>
                `${fragment.module.moduleId}/${fragment.module.fragmentId}`
            ),
            [
                'fixture.runtime_dependency_base/base-rules',
                'fixture.runtime_dependency_consumer/consumer-rules',
                'fixture.runtime_dependency_consumer/later-rules'
            ]
        );
    });

    it('executes the transitive closure under one combined budget', () => {
        const closure = compileBaseClosure();
        const zeroTerm = freeTerm(closure, zero);
        const redex = application(closure, third, zeroTerm);
        const result = coreLfCombinedWeakHead(
            closure.declarations.environment,
            redex,
            3,
            undefined,
            closure.later.runtime
        );
        assert.equal(result.status, 'weak-head-normal');
        assert.equal(result.steps, 3);
        assert.deepEqual(
            result.trace.map(entry =>
                entry.kind === 'runtime' ? entry.ruleId : entry.kind
            ),
            [
                'fixture.third.evaluate',
                'fixture.second.evaluate',
                'fixture.first.evaluate'
            ]
        );
        assert.equal(
            kernelExpressionEquals(result.expression, zeroTerm),
            true
        );
        const bounded = coreLfCombinedWeakHead(
            closure.declarations.environment,
            redex,
            2,
            undefined,
            closure.later.runtime
        );
        assert.equal(bounded.status, 'step-limit-exceeded');
        if (bounded.status === 'step-limit-exceeded') {
            assert.deepEqual(bounded.next, {
                kind: 'runtime',
                ruleId: 'fixture.first.evaluate',
                ruleIndex: 0
            });
        }
    });

    it('checks a local subject only against its explicit prior runtime', () => {
        const closure = compileBaseClosure();
        const priorAuthority =
            'tests/fixtures/runtime_type_dependency.lp';
        const priorPattern = new CoreLfTransferScopedBuilder();
        const priorTemplate = new CoreLfTransferScopedBuilder();
        const priorModule = createCoreLfModuleSpec({
            revision: 'runtime-type-dependency-prior-1',
            moduleId: 'fixture.runtime_type_dependency',
            fragmentId: 'type-prior',
            authorityPath: priorAuthority,
            sourceSha256:
                'sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee',
            dependencies: [symbolModuleId],
            externalSymbols: [aliasCode, baseCode].map(symbol => ({
                symbol,
                availability: 'dependency-module' as const
            })),
            declarations: [],
            inductives: [],
            runtimeRules: [{
                order: 0,
                id: 'fixture.alias-code.evaluate',
                groupId: 'fixture.alias-code.evaluate',
                clauseOrder: 0,
                sourceOwner: aliasCode,
                variables: [],
                left: priorPattern.pattern(
                    priorPattern.global(aliasCode)
                ),
                right: priorTemplate.template(
                    priorTemplate.global(baseCode)
                ),
                provenance: source(
                    priorAuthority,
                    'rule alias_code ↪ base_code;'
                )
            }],
            proofRules: []
        });
        const prior = compileCoreLfRuntimeFragment(
            priorModule,
            runtimePolicy(priorModule),
            closure.declarations,
            { dependencies: [] }
        );

        const localPattern = new CoreLfTransferScopedBuilder();
        const localTemplate = new CoreLfTransferScopedBuilder();
        const localModule = createCoreLfModuleSpec({
            revision: 'runtime-type-dependency-local-1',
            moduleId: 'fixture.runtime_type_consumer',
            fragmentId: 'type-local',
            authorityPath: priorAuthority,
            sourceSha256:
                'sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee',
            dependencies: [
                symbolModuleId,
                priorModule.moduleId
            ],
            externalSymbols: [
                aliasCode,
                decodeCode,
                consumeAlias,
                baseWitness
            ].map(symbol => ({
                symbol,
                availability: 'dependency-module' as const
            })),
            declarations: [],
            inductives: [],
            runtimeRules: [{
                order: 0,
                id: 'fixture.consume-alias.evaluate',
                groupId: 'fixture.consume-alias.evaluate',
                clauseOrder: 0,
                sourceOwner: consumeAlias,
                variables: [{
                    name: 'x',
                    type: decodedType(aliasCode)
                }],
                left: localPattern.pattern(localPattern.call(
                    localPattern.global(consumeAlias),
                    [{
                        plicity: 'explicit',
                        value: localPattern.capture('x')
                    }]
                )),
                right: localTemplate.template(
                    localTemplate.global(baseWitness)
                ),
                provenance: source(
                    priorAuthority,
                    'rule consume_alias $x ↪ base_witness;'
                )
            }],
            proofRules: []
        });
        const localPolicy = runtimePolicy(localModule);
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                localModule,
                localPolicy,
                closure.declarations
            ),
            'INVALID_RUNTIME_RULE_TYPE'
        );
        const compiled = compileCoreLfRuntimeFragment(
            localModule,
            localPolicy,
            closure.declarations,
            {
                dependencies: [{
                    relation: 'dependency-module',
                    fragment: prior
                }]
            }
        );
        assert.deepEqual(
            compiled.localProgram.rules[0]
                .checkedWithEarlierRuleIds,
            ['fixture.alias-code.evaluate']
        );
        assert.equal(
            compiled.localProgram.rules[0]
                .subjectValidation.kind,
            'typescript-checked'
        );
    });

    it('deduplicates a shared transitive dependency in a diamond', () => {
        const closure = compileBaseClosure();
        const siblingModule = runtimeModule({
            revision: 'runtime-dependency-sibling-1',
            moduleId: 'fixture.runtime_dependency_sibling',
            fragmentId: 'sibling-rules',
            dependencies: ['fixture.runtime_dependency_base'],
            head: sibling,
            target: first,
            ruleId: 'fixture.sibling.evaluate'
        });
        const siblingFragment = compileCoreLfRuntimeFragment(
            siblingModule,
            runtimePolicy(siblingModule),
            closure.declarations,
            {
                dependencies: [{
                    relation: 'dependency-module',
                    fragment: closure.base
                }]
            }
        );
        const topModule = runtimeModule({
            revision: 'runtime-dependency-top-1',
            moduleId: 'fixture.runtime_dependency_top',
            fragmentId: 'top-rules',
            dependencies: [
                'fixture.runtime_dependency_consumer',
                'fixture.runtime_dependency_sibling'
            ],
            head: top,
            target: third,
            ruleId: 'fixture.top.evaluate'
        });
        const topFragment = compileCoreLfRuntimeFragment(
            topModule,
            runtimePolicy(topModule),
            closure.declarations,
            {
                dependencies: [
                    {
                        relation: 'dependency-module',
                        fragment: closure.later
                    },
                    {
                        relation: 'dependency-module',
                        fragment: siblingFragment
                    }
                ]
            }
        );
        assert.deepEqual(topFragment.runtime.ruleIds, [
            'fixture.first.evaluate',
            'fixture.second.evaluate',
            'fixture.third.evaluate',
            'fixture.sibling.evaluate',
            'fixture.top.evaluate'
        ]);
        assert.deepEqual(
            topFragment.localProgram.rules[0]
                .checkedWithEarlierRuleIds,
            topFragment.runtime.ruleIds.slice(0, -1)
        );
        assert.equal(
            topFragment.runtime.fragments.filter(fragment =>
                fragment.module.fragmentId === 'base-rules'
            ).length,
            1
        );
    });

    it('rejects relation drift, dependency reordering, and cycles', () => {
        const closure = compileBaseClosure();
        const foreignModule = runtimeModule({
            revision: 'runtime-dependency-foreign-relation-1',
            moduleId: 'fixture.runtime_dependency_foreign',
            fragmentId: 'foreign-rules',
            dependencies: ['fixture.runtime_dependency_base']
        });
        expectRuntimeError(
            () => compileCoreLfRuntimeFragment(
                foreignModule,
                runtimePolicy(foreignModule),
                closure.declarations,
                {
                    dependencies: [{
                        relation: 'earlier-fragment',
                        fragment: closure.base
                    }]
                }
            ),
            'INVALID_RUNTIME_DEPENDENCY'
        );

        const siblingModule = runtimeModule({
            revision: 'runtime-dependency-order-sibling-1',
            moduleId: 'fixture.runtime_dependency_order_sibling',
            fragmentId: 'order-sibling',
            dependencies: []
        });
        const siblingFragment = compileCoreLfRuntimeFragment(
            siblingModule,
            runtimePolicy(siblingModule),
            closure.declarations,
            { dependencies: [] }
        );
        const reorderedModule = runtimeModule({
            revision: 'runtime-dependency-reordered-1',
            moduleId: 'fixture.runtime_dependency_reordered',
            fragmentId: 'reordered',
            dependencies: [
                siblingModule.moduleId,
                closure.base.module.moduleId
            ]
        });
        expectRuntimeError(
            () => compileCoreLfRuntimeFragment(
                reorderedModule,
                runtimePolicy(reorderedModule),
                closure.declarations,
                {
                    dependencies: [
                        {
                            relation: 'dependency-module',
                            fragment: closure.base
                        },
                        {
                            relation: 'dependency-module',
                            fragment: siblingFragment
                        }
                    ]
                }
            ),
            'INVALID_RUNTIME_DEPENDENCY'
        );

        const placeholderModule = runtimeModule({
            revision: 'runtime-dependency-cycle-placeholder-1',
            moduleId: 'fixture.runtime_dependency_cycle_a',
            fragmentId: 'target',
            dependencies: []
        });
        const placeholder = compileCoreLfRuntimeFragment(
            placeholderModule,
            runtimePolicy(placeholderModule),
            closure.declarations,
            { dependencies: [] }
        );
        const bridgeModule = runtimeModule({
            revision: 'runtime-dependency-cycle-bridge-1',
            moduleId: 'fixture.runtime_dependency_cycle_b',
            fragmentId: 'bridge',
            dependencies: [placeholderModule.moduleId]
        });
        const bridge = compileCoreLfRuntimeFragment(
            bridgeModule,
            runtimePolicy(bridgeModule),
            closure.declarations,
            {
                dependencies: [{
                    relation: 'dependency-module',
                    fragment: placeholder
                }]
            }
        );
        const cycleModule = runtimeModule({
            revision: 'runtime-dependency-cycle-target-2',
            moduleId: placeholderModule.moduleId,
            fragmentId: placeholderModule.fragmentId,
            dependencies: [bridgeModule.moduleId]
        });
        expectRuntimeError(
            () => compileCoreLfRuntimeFragment(
                cycleModule,
                runtimePolicy(cycleModule),
                closure.declarations,
                {
                    dependencies: [{
                        relation: 'dependency-module',
                        fragment: bridge
                    }]
                }
            ),
            'CYCLIC_RUNTIME_DEPENDENCY'
        );
    });

    it('rejects rule-ID collisions across the flattened closure', () => {
        const closure = compileBaseClosure();
        const collisionModule = runtimeModule({
            revision: 'runtime-dependency-collision-1',
            moduleId: 'fixture.runtime_dependency_collision',
            fragmentId: 'collision',
            dependencies: [closure.base.module.moduleId],
            head: top,
            target: first,
            ruleId: 'fixture.first.evaluate'
        });
        expectRuntimeError(
            () => compileCoreLfRuntimeFragment(
                collisionModule,
                runtimePolicy(collisionModule),
                closure.declarations,
                {
                    dependencies: [{
                        relation: 'dependency-module',
                        fragment: closure.base
                    }]
                }
            ),
            'DUPLICATE_RUNTIME_RULE_ID'
        );
    });

    it('is immutable, owner-agnostic, and preserves reviewed semantics', () => {
        const closure = compileBaseClosure();
        assert.equal(
            closure.later instanceof CoreLfCompiledRuntimeFragment,
            true
        );
        assertDeepFrozen(closure.later.runtime);
        assertDeepFrozen(closure.later.dependencies);
        assert.equal(
            compileCoreDirectedContinuationRuntimeTransfer()
                .runtime.ruleIds.length,
            10
        );
        assert.equal(
            'compileCoreLfRuntimeFragment' in browser,
            false
        );
        const implementation = readFileSync(
            resolve(repositoryRoot, 'src/v3_2/lf_transfer_runtime.ts'),
            'utf8'
        );
        assert.doesNotMatch(
            implementation,
            /Const_catd|Sigma_cat|Functord|Transfd/u
        );
    });
});
