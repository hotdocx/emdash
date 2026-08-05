import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfStructureAvailableGlobalInput,
    CoreLfStructureDeclarationExpansion,
    CoreLfStructureExpression,
    CoreLfStructureMacroError,
    CoreLfStructureMacroScope,
    CoreLfTransferExpression,
    CoreLfTransferPolicyEntry,
    CoreLfTransferPolicyOverlay,
    binderMode,
    checkLambdapiProbe,
    compileCoreLfMixedPhases,
    coreLfTransferAbsentBody,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay,
    emitCoreLfStructureLambdapiFragment,
    kernelExpressionEquals,
    kernelFree,
    planCoreLfMixedPhases,
    provenance
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const moduleId = 'fixture.structure_macro';
const authorityPath = 'tests/fixtures/structure_macro.lp';
const kernelModule = 'emdash.emdash3_2';

const symbol = (
    name: string,
    owner = moduleId
): CoreLfQualifiedSymbol => ({ moduleId: owner, name });

const code = symbol('Code');
const el = symbol('El');
const codeFor = symbol('CodeFor');

const global = (
    value: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({ tag: 'global', symbol: value });

const bound = (index: number): CoreLfTransferExpression => ({
    tag: 'bound',
    index
});

const call = (
    callee: CoreLfTransferExpression,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => ({
    tag: 'call',
    callee,
    arguments: arguments_
});

const explicit = (value: CoreLfTransferExpression) => ({
    plicity: 'explicit' as const,
    value
});

const implicit = (value: CoreLfTransferExpression) => ({
    plicity: 'implicit' as const,
    value
});

const pi = (
    hint: string,
    mode: ReturnType<typeof binderMode>,
    type: CoreLfTransferExpression,
    body: CoreLfTransferExpression
): CoreLfTransferExpression => ({
    tag: 'pi',
    binder: { hint, mode, type },
    body
});

const explicitMode = binderMode('explicit', 'functorial');
const implicitMode = binderMode('implicit', 'functorial');

const source = (sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const availableFixture = ():
readonly CoreLfStructureAvailableGlobalInput[] => [
    {
        symbol: code,
        type: { tag: 'type' },
        availability: 'earlier-fragment',
        order: 0
    },
    {
        symbol: el,
        type: pi(
            'code',
            explicitMode,
            global(code),
            { tag: 'type' }
        ),
        availability: 'earlier-fragment',
        order: 1
    },
    {
        symbol: codeFor,
        type: pi(
            'A',
            implicitMode,
            global(code),
            pi(
                'y',
                explicitMode,
                call(global(el), [explicit(bound(0))]),
                global(code)
            )
        ),
        availability: 'earlier-fragment',
        order: 2
    }
];

const expandFixture = (
    scope = new CoreLfStructureMacroScope(
        moduleId,
        availableFixture()
    ),
    onCallback: () => void = () => undefined
): CoreLfStructureDeclarationExpansion => {
    const resolvedCode = scope.resolve(code);
    const resolvedEl = scope.resolve(el);
    return scope.declareStructure({
        order: 3,
        carrierName: 'Record',
        constructorName: 'ReviewRecord',
        fields(builder) {
            onCallback();
            const A = builder.field({
                binderName: 'A',
                projectionName: 'record_A',
                mode: implicitMode,
                type: builder.global(resolvedCode)
            });
            const x = builder.field({
                binderName: 'x',
                projectionName: 'record_x',
                mode: explicitMode,
                type: builder.apply(builder.global(resolvedEl), A)
            });
            const P = builder.field({
                binderName: 'P',
                projectionName: 'record_P',
                mode: implicitMode,
                type: builder.pi(
                    'y',
                    builder.apply(builder.global(resolvedEl), A),
                    () => builder.global(resolvedCode)
                )
            });
            builder.field({
                binderName: 'u',
                projectionName: 'record_u',
                mode: explicitMode,
                type: builder.apply(
                    builder.global(resolvedEl),
                    builder.apply(P, x)
                )
            });
        },
        provenance: source('structure Record with primitive projections')
    });
};

const projectionCall = (
    name: string,
    recordIndex = 0
): CoreLfTransferExpression => call(
    global(symbol(name)),
    [explicit(bound(recordIndex))]
);

const expectedConstructorType = (): CoreLfTransferExpression => pi(
    'A',
    implicitMode,
    global(code),
    pi(
        'x',
        explicitMode,
        call(global(el), [explicit(bound(0))]),
        pi(
            'P',
            implicitMode,
            pi(
                'y',
                explicitMode,
                call(global(el), [explicit(bound(1))]),
                global(code)
            ),
            pi(
                'u',
                explicitMode,
                call(global(el), [
                    explicit(call(bound(0), [explicit(bound(1))]))
                ]),
                global(symbol('Record'))
            )
        )
    )
);

const expectedProjectionTypes = (): readonly CoreLfTransferExpression[] => {
    const recordBinder = (
        body: CoreLfTransferExpression
    ): CoreLfTransferExpression => pi(
        'record',
        explicitMode,
        global(symbol('Record')),
        body
    );
    const A = projectionCall('record_A');
    const x = projectionCall('record_x');
    const P = projectionCall('record_P');
    return [
        recordBinder(global(code)),
        recordBinder(call(global(el), [explicit(A)])),
        recordBinder(pi(
            'y',
            explicitMode,
            call(global(el), [explicit(A)]),
            global(code)
        )),
        recordBinder(call(global(el), [
            explicit(call(P, [explicit(x)]))
        ]))
    ];
};

const initialDeclarations = () => [{
    order: 0,
    symbol: code,
    type: { tag: 'type' as const },
    body: coreLfTransferAbsentBody(),
    modifiers: {
        visibility: 'public' as const,
        rigidity: 'constant' as const,
        sourceOpacity: 'opaque' as const
    },
    provenance: source('constant symbol Code : TYPE;')
}, {
    order: 1,
    symbol: el,
    type: pi(
        'code',
        explicitMode,
        global(code),
        { tag: 'type' }
    ),
    body: coreLfTransferAbsentBody(),
    modifiers: {
        visibility: 'public' as const,
        rigidity: 'constant' as const,
        sourceOpacity: 'opaque' as const
    },
    provenance: source('constant symbol El (code : Code) : TYPE;')
}, {
    order: 2,
    symbol: codeFor,
    type: pi(
        'A',
        implicitMode,
        global(code),
        pi(
            'y',
            explicitMode,
            call(global(el), [explicit(bound(0))]),
            global(code)
        )
    ),
    body: coreLfTransferAbsentBody(),
    modifiers: {
        visibility: 'public' as const,
        rigidity: 'constant' as const,
        sourceOpacity: 'opaque' as const
    },
    provenance: source(
        'constant symbol CodeFor [A : Code] (y : El A) : Code;'
    )
}];

const fixtureModule = (
    expansion: CoreLfStructureDeclarationExpansion
): CoreLfModuleSpec => createCoreLfModuleSpec({
    revision: 'structure-macro-fixture-1',
    moduleId,
    fragmentId: 'structure-source',
    authorityPath,
    sourceSha256:
        'sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd',
    dependencies: [],
    externalSymbols: [],
    declarations: [
        ...initialDeclarations(),
        ...expansion.declarations
    ],
    inductives: [],
    runtimeRules: expansion.runtimeRules,
    proofRules: []
});

interface PolicySource {
    readonly sourceOrder: number;
    readonly entry: Omit<CoreLfTransferPolicyEntry, 'order'>;
}

const fixturePolicy = (
    module: CoreLfModuleSpec
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
                evidence: 'generated structure declaration fixture'
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
                evidence: 'generated structure projection beta'
            }
        }))
    ];
    entries.sort((left, right) => left.sourceOrder - right.sourceOrder);
    return createCoreLfTransferPolicyOverlay(module, {
        revision: 'structure-macro-policy-1',
        moduleRevision: module.revision,
        entries: entries.map(({ entry }, order) => ({
            order,
            ...entry
        }))
    });
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const throwsMacro = (
    action: () => unknown,
    code_: CoreLfStructureMacroError['code'],
    path?: string
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfStructureMacroError &&
            error.code === code_ &&
            (path === undefined || error.path === path)
    );
};

const fixtureEmission = [
    'constant symbol Record : TYPE;',
    '',
    'injective symbol ReviewRecord : Π [A : Code], Π (x : El A), ' +
        'Π [P : Π (y : El A), Code], ' +
        'Π (u : El (P x)), Record;',
    '',
    'symbol record_A : Π (record : Record), Code;',
    '',
    'symbol record_x : Π (record : Record), El (record_A record);',
    '',
    'symbol record_P : Π (record : Record), ' +
        'Π (y : El (record_A record)), Code;',
    '',
    'symbol record_u : Π (record : Record), ' +
        'El ((record_P record) (record_x record));',
    '',
    'rule record_A (@ReviewRecord $A $x $P $u) ↪ $A;',
    '',
    'rule record_x (@ReviewRecord $A $x $P $u) ↪ $x;',
    '',
    'rule record_P (@ReviewRecord $A $x $P $u) ↪ $P;',
    '',
    'rule record_u (@ReviewRecord $A $x $P $u) ↪ $u;',
    ''
].join('\n');

const liveExpansion = (): CoreLfStructureDeclarationExpansion => {
    const Grpd = symbol('Grpd', kernelModule);
    const tau = symbol('τ', kernelModule);
    const scope = new CoreLfStructureMacroScope(
        'review.structure_consumer',
        [{
            symbol: Grpd,
            type: { tag: 'type' },
            availability: 'dependency-module'
        }, {
            symbol: tau,
            type: pi(
                'A',
                explicitMode,
                global(Grpd),
                { tag: 'type' }
            ),
            availability: 'dependency-module'
        }]
    );
    const resolvedGrpd = scope.resolve(Grpd);
    const resolvedTau = scope.resolve(tau);
    return scope.declareStructure({
        order: 0,
        carrierName: 'ReviewRecord',
        constructorName: 'MkReviewRecord',
        fields(builder) {
            const A = builder.field({
                binderName: 'A',
                projectionName: 'review_record_A',
                mode: implicitMode,
                type: builder.global(resolvedGrpd)
            });
            const x = builder.field({
                binderName: 'x',
                projectionName: 'review_record_x',
                mode: explicitMode,
                type: builder.apply(builder.global(resolvedTau), A)
            });
            const P = builder.field({
                binderName: 'P',
                projectionName: 'review_record_P',
                mode: implicitMode,
                type: builder.pi(
                    'y',
                    builder.apply(builder.global(resolvedTau), A),
                    () => builder.global(resolvedGrpd)
                )
            });
            builder.field({
                binderName: 'u',
                projectionName: 'review_record_u',
                mode: explicitMode,
                type: builder.apply(
                    builder.global(resolvedTau),
                    builder.apply(P, x)
                )
            });
        },
        provenance: {
            authorityPath: 'tests/generated/structure_consumer.lp',
            sourceFragment: 'generated primitive structure'
        }
    });
};

const liveSource = (): string => {
    const expansion = liveExpansion();
    const fragment = emitCoreLfStructureLambdapiFragment(
        expansion,
        { backendName: value => value.name }
    );
    return [
        'require open emdash.emdash3_2;',
        '',
        fragment.trimEnd(),
        '',
        'assert [A : Grpd]',
        '  (x : τ A)',
        '  [P : τ A → Grpd]',
        '  (u : τ (P x))',
        '  ⊢ review_record_A (@MkReviewRecord A x P u) ≡ A;',
        '',
        'assert [A : Grpd]',
        '  (x : τ A)',
        '  [P : τ A → Grpd]',
        '  (u : τ (P x))',
        '  ⊢ review_record_x (@MkReviewRecord A x P u) ≡ x;',
        '',
        'assert [A : Grpd]',
        '  (x : τ A)',
        '  [P : τ A → Grpd]',
        '  (u : τ (P x))',
        '  ⊢ review_record_P (@MkReviewRecord A x P u) ≡ P;',
        '',
        'assert [A : Grpd]',
        '  (x : τ A)',
        '  [P : τ A → Grpd]',
        '  (u : τ (P x))',
        '  ⊢ review_record_u (@MkReviewRecord A x P u) ≡ u;',
        '',
        '// The primitive package deliberately installs no record eta.',
        'assertnot (r : ReviewRecord) ⊢',
        '  @MkReviewRecord',
        '    (review_record_A r)',
        '    (review_record_x r)',
        '    (review_record_P r)',
        '    (review_record_u r)',
        '  ≡ r;',
        ''
    ].join('\n');
};

describe('outer LF dependent structure declaration macro', () => {
    it('expands atomically in source order and invokes its callback once', () => {
        let callbackCount = 0;
        const expansion = expandFixture(
            undefined,
            () => callbackCount++
        );

        assert.equal(callbackCount, 1);
        assert.deepEqual(expansion.sourceOrders, [
            3, 4, 5, 6, 7, 8, 9, 10, 11, 12
        ]);
        assert.equal(expansion.nextOrder, 13);
        assert.deepEqual(
            expansion.declarations.map(declaration => [
                declaration.order,
                declaration.symbol.name,
                declaration.modifiers.rigidity,
                declaration.body.kind
            ]),
            [
                [3, 'Record', 'constant', 'absent'],
                [4, 'ReviewRecord', 'injective', 'absent'],
                [5, 'record_A', 'ordinary', 'absent'],
                [6, 'record_x', 'ordinary', 'absent'],
                [7, 'record_P', 'ordinary', 'absent'],
                [8, 'record_u', 'ordinary', 'absent']
            ]
        );
        assert.deepEqual(
            expansion.runtimeRules.map(rule => [
                rule.order,
                rule.id,
                rule.groupId,
                rule.sourceOwner.name
            ]),
            [
                [9, 'structure.Record.record_A.beta',
                    'structure.Record.record_A.beta', 'record_A'],
                [10, 'structure.Record.record_x.beta',
                    'structure.Record.record_x.beta', 'record_x'],
                [11, 'structure.Record.record_P.beta',
                    'structure.Record.record_P.beta', 'record_P'],
                [12, 'structure.Record.record_u.beta',
                    'structure.Record.record_u.beta', 'record_u']
            ]
        );
        assert.deepEqual(
            expansion.handle.projections.map(projection => [
                projection.ordinal,
                projection.binderName,
                projection.symbol.name,
                projection.betaRuleId
            ]),
            [
                [0, 'A', 'record_A',
                    'structure.Record.record_A.beta'],
                [1, 'x', 'record_x',
                    'structure.Record.record_x.beta'],
                [2, 'P', 'record_P',
                    'structure.Record.record_P.beta'],
                [3, 'u', 'record_u',
                    'structure.Record.record_u.beta']
            ]
        );
        assertDeepFrozen(expansion);
    });

    it('lowers dependent fields into constructor and projection scopes', () => {
        const expansion = expandFixture();
        assert.deepEqual(
            expansion.declarations[1].type,
            expectedConstructorType()
        );
        assert.deepEqual(
            expansion.declarations.slice(2).map(
                declaration => declaration.type
            ),
            expectedProjectionTypes()
        );
    });

    it('lowers each beta to typed captures and the selected field', () => {
        const expansion = expandFixture();
        const variableNames = ['A', 'x', 'P', 'u'];
        const expectedVariableTypes: readonly CoreLfTransferExpression[] = [
            global(code),
            call(global(el), [{
                plicity: 'explicit',
                value: { tag: 'capture', name: 'A' }
            }]),
            pi(
                'y',
                explicitMode,
                call(global(el), [{
                    plicity: 'explicit',
                    value: { tag: 'capture', name: 'A' }
                }]),
                global(code)
            ),
            call(global(el), [explicit(call(
                { tag: 'capture', name: 'P' },
                [{
                    plicity: 'explicit',
                    value: { tag: 'capture', name: 'x' }
                }]
            ))])
        ];

        expansion.runtimeRules.forEach((rule, fieldIndex) => {
            assert.deepEqual(
                rule.variables.map(variable => variable.name),
                variableNames
            );
            assert.deepEqual(
                rule.variables.map(variable => variable.type),
                expectedVariableTypes
            );
            assert.deepEqual(rule.right, {
                tag: 'capture',
                name: variableNames[fieldIndex]
            });
            assert.deepEqual(rule.left, call(
                global(symbol(variableNames.map(
                    (_name, index) => [
                        'record_A', 'record_x', 'record_P', 'record_u'
                    ][index]
                )[fieldIndex])),
                [explicit(call(
                    global(symbol('ReviewRecord')),
                    [
                        { plicity: 'implicit', value: {
                            tag: 'capture', name: 'A'
                        } },
                        { plicity: 'explicit', value: {
                            tag: 'capture', name: 'x'
                        } },
                        { plicity: 'implicit', value: {
                            tag: 'capture', name: 'P'
                        } },
                        { plicity: 'explicit', value: {
                            tag: 'capture', name: 'u'
                        } }
                    ]
                ))]
            ));
        });
    });

    it('emits a deterministic Lambdapi fragment with no eta or parser node', () => {
        const first = expandFixture();
        const second = expandFixture();
        assert.deepEqual(first, second);
        assert.equal(
            emitCoreLfStructureLambdapiFragment(
                first,
                { backendName: value => value.name }
            ),
            fixtureEmission
        );
        assert.equal('CoreLfStructureMacroScope' in browser, false);
    });

    it('compiles every generated beta with TypeScript subject reduction', () => {
        const expansion = expandFixture();
        const module = fixtureModule(expansion);
        const policy = fixturePolicy(module);
        const plan = planCoreLfMixedPhases(module, policy);
        const declarationSymbols = [...module.declarations]
            .sort((left, right) => left.order - right.order)
            .map(declaration => declaration.symbol);
        const linkage = createCoreLfMixedDeclarationLinkage(plan, {
            revision: 'structure-macro-linkage-1',
            moduleRevision: module.revision,
            entries: declarationSymbols.map((value, order) => ({
                order,
                symbol: value,
                kind: 'free-declaration' as const,
                coreName: `structure_${value.name}`,
                backendName: value.name
            }))
        });
        const compiled = compileCoreLfMixedPhases(plan, linkage);

        assert.deepEqual(
            plan.phases.map(phase => [phase.kind, phase.sourceOrders]),
            [
                ['declaration', [0]],
                ['declaration', [1]],
                ['declaration', [2]],
                ['declaration', [3]],
                ['declaration', [4]],
                ['declaration', [5]],
                ['declaration', [6]],
                ['declaration', [7]],
                ['declaration', [8]],
                ['runtime', [9]],
                ['runtime', [10]],
                ['runtime', [11]],
                ['runtime', [12]]
            ]
        );
        assert.deepEqual(
            compiled.latestRuntime?.runtime.ruleIds,
            expansion.runtimeRules.map(rule => rule.id)
        );

        const witnessSource = provenance(
            'derived',
            'generated structure runtime witness'
        );
        const bindings = ['A', 'x', 'P', 'u'].map(name =>
            kernelFree(`witness_${name}`, witnessSource)
        );
        const runtimePhases = compiled.phases.filter(
            phase => phase.kind === 'runtime'
        );
        assert.equal(runtimePhases.length, 4);
        runtimePhases.forEach((phase, fieldIndex) => {
            if (phase.kind !== 'runtime') return;
            const local = phase.runtime.localProgram;
            const rule = local.rules[0];
            assert.equal(
                rule.subjectValidation.kind,
                'typescript-checked'
            );
            assert.deepEqual(
                rule.checkedWithEarlierRuleIds,
                expansion.runtimeRules
                    .slice(0, fieldIndex)
                    .map(candidate => candidate.id)
            );
            const redex = local.instantiateRuleLeft(
                rule,
                bindings,
                witnessSource
            );
            const rewritten = phase.runtime.runtime.rewriteHead(redex);
            assert.equal(rewritten.status, 'rewritten');
            if (rewritten.status !== 'rewritten') return;
            assert.equal(rewritten.ruleId, rule.id);
            assert.equal(
                kernelExpressionEquals(
                    rewritten.after,
                    bindings[fieldIndex]
                ),
                true
            );
        });
    });

    it('rejects empty, duplicate, and colliding generated packages', () => {
        const scope = new CoreLfStructureMacroScope(
            moduleId,
            availableFixture()
        );
        const base = {
            order: 3,
            carrierName: 'Empty',
            constructorName: 'MkEmpty',
            provenance: source('invalid structure fixture')
        };
        throwsMacro(
            () => scope.declareStructure({ ...base, fields() {} }),
            'INVALID_COMMAND',
            'command.fields'
        );
        throwsMacro(
            () => scope.declareStructure({
                ...base,
                fields(builder) {
                    const type = builder.type();
                    builder.field({
                        binderName: 'x',
                        projectionName: 'first',
                        mode: explicitMode,
                        type
                    });
                    builder.field({
                        binderName: 'x',
                        projectionName: 'second',
                        mode: explicitMode,
                        type
                    });
                }
            }),
            'INVALID_FIELD',
            'command.fields[1].binderName'
        );
        throwsMacro(
            () => scope.declareStructure({
                ...base,
                fields(builder) {
                    const type = builder.type();
                    builder.field({
                        binderName: 'x',
                        projectionName: 'same',
                        mode: explicitMode,
                        type
                    });
                    builder.field({
                        binderName: 'y',
                        projectionName: 'same',
                        mode: explicitMode,
                        type
                    });
                }
            }),
            'DUPLICATE_SYMBOL',
            'command.fields[1].projectionName'
        );
        throwsMacro(
            () => scope.declareStructure({
                ...base,
                fields(builder) {
                    builder.field({
                        binderName: 'x',
                        projectionName: 'not-valid',
                        mode: explicitMode,
                        type: builder.type()
                    });
                }
            }),
            'INVALID_FIELD',
            'command.fields[0].projectionName'
        );
        throwsMacro(
            () => scope.declareStructure({
                ...base,
                carrierName: 'Code',
                fields(builder) {
                    builder.field({
                        binderName: 'x',
                        projectionName: 'only',
                        mode: explicitMode,
                        type: builder.type()
                    });
                }
            }),
            'DUPLICATE_SYMBOL',
            'command.carrierName'
        );
    });

    it('rejects foreign, forward, and binder-escaping references', () => {
        const scope = new CoreLfStructureMacroScope(
            moduleId,
            availableFixture()
        );
        const foreignScope = new CoreLfStructureMacroScope(
            moduleId,
            availableFixture()
        );
        const foreignCode = foreignScope.resolve(code);
        throwsMacro(
            () => scope.declareStructure({
                order: 3,
                carrierName: 'Foreign',
                constructorName: 'MkForeign',
                fields(builder) {
                    builder.field({
                        binderName: 'x',
                        projectionName: 'foreign_x',
                        mode: explicitMode,
                        type: builder.global(foreignCode)
                    });
                },
                provenance: source('foreign global fixture')
            }),
            'FOREIGN_GLOBAL',
            'global.value'
        );

        let foreignExpression: CoreLfStructureExpression | undefined;
        scope.declareStructure({
            order: 3,
            carrierName: 'Source',
            constructorName: 'MkSource',
            fields(builder) {
                foreignExpression = builder.type();
                builder.field({
                    binderName: 'x',
                    projectionName: 'source_x',
                    mode: explicitMode,
                    type: foreignExpression
                });
            },
            provenance: source('foreign expression source')
        });
        throwsMacro(
            () => scope.declareStructure({
                order: 3,
                carrierName: 'Target',
                constructorName: 'MkTarget',
                fields(builder) {
                    builder.field({
                        binderName: 'x',
                        projectionName: 'target_x',
                        mode: explicitMode,
                        type: foreignExpression as CoreLfStructureExpression
                    });
                },
                provenance: source('foreign expression target')
            }),
            'FOREIGN_EXPRESSION',
            'command.fields[0].type'
        );

        let escaped: CoreLfStructureExpression | undefined;
        throwsMacro(
            () => scope.declareStructure({
                order: 3,
                carrierName: 'Escaped',
                constructorName: 'MkEscaped',
                fields(builder) {
                    builder.pi(
                        'y',
                        builder.type(),
                        token => {
                            escaped = token;
                            return builder.type();
                        }
                    );
                    builder.field({
                        binderName: 'x',
                        projectionName: 'escaped_x',
                        mode: explicitMode,
                        type: escaped as CoreLfStructureExpression
                    });
                },
                provenance: source('escaped binder fixture')
            }),
            'ESCAPED_BINDER',
            'command.fields[0].type'
        );

        const future = symbol('Future');
        const forwardScope = new CoreLfStructureMacroScope(
            moduleId,
            [...availableFixture(), {
                symbol: future,
                type: { tag: 'type' },
                availability: 'earlier-fragment',
                order: 20
            }]
        );
        const resolvedFuture = forwardScope.resolve(future);
        throwsMacro(
            () => forwardScope.declareStructure({
                order: 20,
                carrierName: 'Forward',
                constructorName: 'MkForward',
                fields(builder) {
                    builder.field({
                        binderName: 'x',
                        projectionName: 'forward_x',
                        mode: explicitMode,
                        type: builder.global(resolvedFuture)
                    });
                },
                provenance: source('forward fixture')
            }),
            'FORWARD_GLOBAL',
            'global.value'
        );
    });

    it('validates the host boundary without mutating caller inputs', () => {
        const available = availableFixture().map(entry => ({ ...entry }));
        const before = structuredClone(available);
        const scope = new CoreLfStructureMacroScope(moduleId, available);
        expandFixture(scope);
        assert.deepEqual(available, before);
        assert.equal(Object.isFrozen(available), false);
        assert.equal(Object.isFrozen(available[0]), false);

        throwsMacro(
            () => new CoreLfStructureMacroScope(moduleId, [{
                symbol: code,
                type: { tag: 'capture', name: 'x' },
                availability: 'earlier-fragment',
                order: 0
            }]),
            'INVALID_SCOPE',
            'scope.availableGlobals[0].type'
        );
        throwsMacro(
            () => scope.declareStructure({
                order: -1,
                carrierName: 'Bad',
                constructorName: 'MkBad',
                fields(builder) {
                    builder.field({
                        binderName: 'x',
                        projectionName: 'bad_x',
                        mode: explicitMode,
                        type: builder.type()
                    });
                },
                provenance: source('bad order')
            }),
            'INVALID_COMMAND',
            'command.order'
        );
        throwsMacro(
            () => scope.declareStructure({
                order: 3,
                carrierName: 'Async',
                constructorName: 'MkAsync',
                fields: (() => Promise.resolve()) as never,
                provenance: source('async fixture')
            }),
            'INVALID_COMMAND',
            'command.fields'
        );
    });

    it(
        'has generated beta and no-eta evidence accepted by Lambdapi',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_STRUCTURE_PROBES !== '1'
        },
        () => {
            const generated = liveSource();
            const result = checkLambdapiProbe(
                { source: generated, sourceMap: [] },
                {
                    packageRoot: resolve(__dirname, '../emdash2'),
                    timeoutMs: 55_000
                }
            );
            assert.equal(result.timedOut, false, result.diagnostics);
            assert.equal(
                result.accepted,
                true,
                `Generated structure consumer was rejected:\n` +
                    `${result.diagnostics}\n${generated}`
            );
        }
    );
});
