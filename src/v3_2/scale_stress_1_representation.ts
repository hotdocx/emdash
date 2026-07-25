/**
 * Representation-only typed lowering of the first acquired stress corpus.
 *
 * The two mixed module specs and their policy overlays contain active
 * mathematical names as data. They install nothing and deliberately retain
 * conformance-only policy until the applicable semantic and engine gates.
 */

import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import { binderMode } from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';
import {
    CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION,
    CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
} from './scale_stress_1_acquisition';

const coreModuleId = 'emdash.emdash3_2';
const natModuleId = 'emdash.emdash3_2_nat_arithmetic';

const coreSymbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(coreModuleId, name);
const natSymbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(natModuleId, name);

const grpd = coreSymbol('Grpd');
const tau = coreSymbol('τ');
const equality = coreSymbol('=');
const eqRefl = coreSymbol('eq_refl');
const indEqr = coreSymbol('ind_eqr');
const tauSigma = coreSymbol('τΣ_');
const structSigma = coreSymbol('Struct_sigma');
const generatedIndTauSigma = coreSymbol('ind_τΣ_');
const sigmaInd = coreSymbol('sigma_ind');
const piGrpd = coreSymbol('Pi_grpd');
const natGrpd = coreSymbol('Nat_grpd');
const zero = coreSymbol('zero');
const succ = coreSymbol('succ');
const natAdd = natSymbol('nat_add');

const implicitMode = binderMode('implicit', 'functorial');

interface BuilderArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: CoreLfTransferBuilderExpression;
}

const call = (
    builder: CoreLfTransferScopedBuilder,
    callee: CoreLfTransferBuilderExpression,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    builder.call(callee, arguments_);

const globalCall = (
    builder: CoreLfTransferScopedBuilder,
    symbol: CoreLfQualifiedSymbol,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    call(builder, builder.global(symbol), arguments_);

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, tau, [{
        plicity: 'explicit',
        value: classifier
    }]);

const equalityType = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, equality, [
        { plicity: 'implicit', value: classifier },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const reflexivity = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression,
    value: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, eqRefl, [
        { plicity: 'implicit', value: classifier },
        { plicity: 'explicit', value }
    ]);

const applyExplicit = (
    builder: CoreLfTransferScopedBuilder,
    callee: CoreLfTransferBuilderExpression,
    values: readonly CoreLfTransferBuilderExpression[]
): CoreLfTransferBuilderExpression =>
    call(
        builder,
        callee,
        values.map(value => ({
            plicity: 'explicit' as const,
            value
        }))
    );

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number,
    authorityPath = 'emdash2/emdash3_2.lp'
) => ({
    authorityPath,
    sourceFragment,
    canonicalCommandOrdinal
});

const publicModifiers = (
    rigidity: 'ordinary' | 'constant' | 'injective'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity: 'opaque' as const
});

const indEqrType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(grpd),
        a => builder.pi(
            'y',
            decode(builder, a),
            y => builder.pi(
                'P',
                builder.pi(
                    'x',
                    decode(builder, a),
                    x => builder.pi(
                        'p',
                        decode(
                            builder,
                            equalityType(builder, a, x, y)
                        ),
                        _ => builder.global(grpd)
                    )
                ),
                P => builder.pi(
                    'u',
                    decode(
                        builder,
                        applyExplicit(builder, P, [
                            y,
                            reflexivity(builder, a, y)
                        ])
                    ),
                    _u => builder.pi(
                        'x',
                        decode(builder, a),
                        x => builder.pi(
                            'p',
                            decode(
                                builder,
                                equalityType(builder, a, x, y)
                            ),
                            p => decode(
                                builder,
                                applyExplicit(builder, P, [x, p])
                            )
                        ),
                        implicitMode
                    )
                )
            )
        ),
        implicitMode
    ));
};

const sigmaIndType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(grpd),
        A => builder.pi(
            'P',
            builder.pi(
                'x',
                decode(builder, A),
                _ => builder.global(grpd)
            ),
            P => builder.pi(
                'Q',
                builder.pi(
                    's',
                    globalCall(builder, tauSigma, [
                        { plicity: 'implicit', value: A },
                        { plicity: 'explicit', value: P }
                    ]),
                    _ => builder.global(grpd)
                ),
                Q => builder.pi(
                    'c',
                    builder.pi(
                        'x',
                        decode(builder, A),
                        x => builder.pi(
                            'u',
                            decode(
                                builder,
                                applyExplicit(builder, P, [x])
                            ),
                            u => decode(
                                builder,
                                applyExplicit(builder, Q, [
                                    globalCall(builder, structSigma, [
                                        {
                                            plicity: 'implicit',
                                            value: A
                                        },
                                        {
                                            plicity: 'implicit',
                                            value: P
                                        },
                                        {
                                            plicity: 'explicit',
                                            value: x
                                        },
                                        {
                                            plicity: 'explicit',
                                            value: u
                                        }
                                    ])
                                ])
                            )
                        )
                    ),
                    _c => builder.pi(
                        's',
                        globalCall(builder, tauSigma, [
                            { plicity: 'implicit', value: A },
                            { plicity: 'explicit', value: P }
                        ]),
                        s => decode(
                            builder,
                            applyExplicit(builder, Q, [s])
                        )
                    )
                )
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const piGrpdType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(grpd),
        A => builder.pi(
            'B',
            builder.pi(
                'x',
                decode(builder, A),
                _ => builder.global(grpd)
            ),
            _ => builder.global(grpd)
        ),
        implicitMode
    ));
};

const jRuntimeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const a = builder.capture('a');
    const y = builder.capture('y');
    const P = builder.capture('P');
    const u = builder.capture('u');
    const pType = builder.pi(
        'x',
        decode(builder, a),
        x => builder.pi(
            'p',
            decode(
                builder,
                equalityType(builder, a, x, y)
            ),
            _ => builder.global(grpd)
        )
    );
    const variables = [
        {
            name: 'a',
            type: builder.template(builder.global(grpd))
        },
        {
            name: 'y',
            type: builder.template(decode(builder, a))
        },
        {
            name: 'P',
            type: builder.template(pType)
        },
        {
            name: 'u',
            type: builder.template(decode(
                builder,
                applyExplicit(builder, P, [
                    y,
                    reflexivity(builder, a, y)
                ])
            ))
        }
    ];
    const left = builder.pattern(globalCall(builder, indEqr, [
        { plicity: 'implicit', value: a },
        { plicity: 'implicit', value: y },
        /*
         * Canonical `_` is lowered to one typed, RHS-unused capture. The
         * separate assessment preserves that acquisition decision.
         */
        { plicity: 'explicit', value: P },
        { plicity: 'explicit', value: u },
        { plicity: 'implicit', value: y },
        {
            plicity: 'explicit',
            value: reflexivity(builder, a, y)
        }
    ]));
    return {
        order: 1,
        id: 'stress.outer-j.reflexivity',
        groupId: 'stress.outer-j',
        clauseOrder: 0,
        sourceOwner: indEqr,
        variables,
        left,
        right: builder.template(u),
        provenance: source(
            'rule @ind_eqr $a $y _ $u $y ' +
                '(@eq_refl $a $y) ↪ $u;',
            14
        )
    };
};

const sigmaRuntimeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const P = builder.capture('P');
    const Q = builder.capture('Q');
    const c = builder.capture('c');
    const x = builder.capture('x');
    const u = builder.capture('u');
    const sigma = (first: CoreLfTransferBuilderExpression) =>
        globalCall(builder, tauSigma, [
            { plicity: 'implicit', value: A },
            { plicity: 'explicit', value: first }
        ]);
    const pair = globalCall(builder, structSigma, [
        { plicity: 'implicit', value: A },
        { plicity: 'implicit', value: P },
        { plicity: 'explicit', value: x },
        { plicity: 'explicit', value: u }
    ]);
    return {
        order: 4,
        id: 'stress.sigma.eliminator-beta',
        groupId: 'stress.sigma.eliminator',
        clauseOrder: 0,
        sourceOwner: sigmaInd,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(grpd))
            },
            {
                name: 'P',
                type: builder.template(builder.pi(
                    'x',
                    decode(builder, A),
                    _ => builder.global(grpd)
                ))
            },
            {
                name: 'Q',
                type: builder.template(builder.pi(
                    's',
                    sigma(P),
                    _ => builder.global(grpd)
                ))
            },
            {
                name: 'c',
                type: builder.template(builder.pi(
                    'x',
                    decode(builder, A),
                    x_ => builder.pi(
                        'u',
                        decode(
                            builder,
                            applyExplicit(builder, P, [x_])
                        ),
                        u_ => decode(
                            builder,
                            applyExplicit(builder, Q, [
                                globalCall(builder, structSigma, [
                                    {
                                        plicity: 'implicit',
                                        value: A
                                    },
                                    {
                                        plicity: 'implicit',
                                        value: P
                                    },
                                    {
                                        plicity: 'explicit',
                                        value: x_
                                    },
                                    {
                                        plicity: 'explicit',
                                        value: u_
                                    }
                                ])
                            ])
                        )
                    )
                ))
            },
            {
                name: 'x',
                type: builder.template(decode(builder, A))
            },
            {
                name: 'u',
                type: builder.template(decode(
                    builder,
                    applyExplicit(builder, P, [x])
                ))
            }
        ],
        left: builder.pattern(globalCall(builder, sigmaInd, [
            { plicity: 'implicit', value: A },
            { plicity: 'implicit', value: P },
            /*
             * The canonical motive wildcard becomes a typed, RHS-unused
             * capture for exact dependent subject reconstruction.
             */
            { plicity: 'explicit', value: Q },
            { plicity: 'explicit', value: c },
            { plicity: 'explicit', value: pair }
        ])),
        right: builder.template(
            applyExplicit(builder, c, [x, u])
        ),
        provenance: source(
            'rule sigma_ind _ $c ' +
                '(Struct_sigma $x $u) ↪ $c $x $u;',
            64
        )
    };
};

const piRuntimeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const variables = [
        {
            name: 'A',
            type: builder.template(builder.global(grpd))
        },
        {
            name: 'B',
            type: builder.template(builder.pi(
                'x',
                decode(builder, A),
                _ => builder.global(grpd)
            ))
        }
    ];
    return {
        order: 6,
        id: 'stress.pi-grpd.decode',
        groupId: 'stress.pi-grpd',
        clauseOrder: 0,
        sourceOwner: tau,
        variables,
        left: builder.pattern(globalCall(builder, tau, [{
            plicity: 'explicit',
            value: globalCall(builder, piGrpd, [
                { plicity: 'implicit', value: A },
                { plicity: 'explicit', value: B }
            ])
        }])),
        right: builder.template(builder.pi(
            'x',
            decode(builder, A),
            x => decode(
                builder,
                applyExplicit(builder, B, [x])
            )
        )),
        provenance: source(
            'rule τ (@Pi_grpd $A $B) ' +
                '↪ Π x : τ $A, τ ($B x);',
            75
        )
    };
};

const sigmaInductive = () => ({
    order: 2,
    symbol: tauSigma,
    parameters: [
        {
            hint: 'a',
            mode: implicitMode,
            type: {
                tag: 'global' as const,
                symbol: grpd
            }
        },
        {
            hint: 'P',
            mode: binderMode('explicit', 'functorial'),
            type: {
                tag: 'pi' as const,
                binder: {
                    hint: 'x',
                    mode: binderMode('explicit', 'functorial'),
                    type: {
                        tag: 'call' as const,
                        callee: {
                            tag: 'global' as const,
                            symbol: tau
                        },
                        arguments: [{
                            plicity: 'explicit' as const,
                            value: {
                                tag: 'bound' as const,
                                index: 0
                            }
                        }]
                    }
                },
                body: {
                    tag: 'global' as const,
                    symbol: grpd
                }
            }
        }
    ],
    indices: [],
    sort: { tag: 'type' as const },
    constructors: [{
        order: 0,
        symbol: structSigma,
        binders: [
            {
                hint: 'sigma_Fst',
                mode: binderMode('explicit', 'functorial'),
                type: {
                    tag: 'call' as const,
                    callee: {
                        tag: 'global' as const,
                        symbol: tau
                    },
                    arguments: [{
                        plicity: 'explicit' as const,
                        value: {
                            tag: 'bound' as const,
                            index: 1
                        }
                    }]
                }
            },
            {
                hint: 'sigma_Snd',
                mode: binderMode('explicit', 'functorial'),
                type: {
                    tag: 'call' as const,
                    callee: {
                        tag: 'global' as const,
                        symbol: tau
                    },
                    arguments: [{
                        plicity: 'explicit' as const,
                        value: {
                            tag: 'call' as const,
                            callee: {
                                tag: 'bound' as const,
                                index: 1
                            },
                            arguments: [{
                                plicity: 'explicit' as const,
                                value: {
                                    tag: 'bound' as const,
                                    index: 0
                                }
                            }]
                        }
                    }]
                }
            }
        ],
        result: {
            tag: 'call' as const,
            callee: {
                tag: 'global' as const,
                symbol: tauSigma
            },
            arguments: [
                {
                    plicity: 'implicit' as const,
                    value: {
                        tag: 'bound' as const,
                        index: 3
                    }
                },
                {
                    plicity: 'explicit' as const,
                    value: {
                        tag: 'bound' as const,
                        index: 2
                    }
                }
            ]
        },
        provenance: source(
            '| Struct_sigma [a P] : Π ' +
                '(sigma_Fst : τ a) (sigma_Snd : τ (P sigma_Fst)), ' +
                '@τΣ_ a P;',
            54
        )
    }],
    generatedSymbols: [generatedIndTauSigma],
    modifiers: publicModifiers('injective'),
    provenance: source(
        'inductive τΣ_ [a : Grpd] ' +
            '(P : τ a → Grpd) : TYPE ≔',
        54
    )
});

const createCoreRepresentation = (): CoreLfModuleSpec =>
    createCoreLfModuleSpec({
        revision: 'SCALE-STRESS-1A-CORE-REPRESENTATION-1',
        moduleId: coreModuleId,
        fragmentId: 'scale-stress-1a-core-representation',
        authorityPath:
            CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION.authorityPath,
        sourceSha256:
            CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION.sourceSha256,
        canonicalExport: {
            exporterVersion:
                CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION
                    .canonicalExport.exporterVersion,
            sha256:
                CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION
                    .canonicalExport.sha256
        },
        dependencies: [],
        externalSymbols: [
            grpd,
            tau,
            equality,
            eqRefl
        ].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [
            {
                order: 0,
                symbol: indEqr,
                type: indEqrType(),
                body: coreLfTransferAbsentBody(),
                modifiers: publicModifiers('ordinary'),
                provenance: source(
                    'symbol ind_eqr\n  [a : Grpd]',
                    13
                )
            },
            {
                order: 3,
                symbol: sigmaInd,
                type: sigmaIndType(),
                body: coreLfTransferAbsentBody(),
                modifiers: publicModifiers('ordinary'),
                provenance: source(
                    'symbol sigma_ind\n  [A : Grpd]',
                    63
                )
            },
            {
                order: 5,
                symbol: piGrpd,
                type: piGrpdType(),
                body: coreLfTransferAbsentBody(),
                modifiers: publicModifiers('constant'),
                provenance: source(
                    'constant symbol Pi_grpd\n  [A : Grpd]',
                    74
                )
            }
        ],
        inductives: [sigmaInductive()],
        runtimeRules: [
            jRuntimeRule(),
            sigmaRuntimeRule(),
            piRuntimeRule()
        ],
        proofRules: []
    });

const createCorePolicy = (
    module: CoreLfModuleSpec
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision: 'SCALE-STRESS-1A-CORE-POLICY-1',
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: indEqr
                },
                policy: 'conformance-only',
                evidence:
                    'SCALE-STRESS-1A representation; no semantic profile'
            },
            {
                order: 1,
                target: {
                    kind: 'runtime-rule',
                    id: 'stress.outer-j.reflexivity'
                },
                policy: 'conformance-only',
                evidence:
                    'J wildcard lowering and subject guards await review'
            },
            {
                order: 2,
                target: {
                    kind: 'inductive',
                    symbol: tauSigma
                },
                policy: 'conformance-only',
                evidence:
                    'Generic inductive compilation is not implemented'
            },
            {
                order: 3,
                target: {
                    kind: 'declaration',
                    symbol: sigmaInd
                },
                policy: 'conformance-only',
                evidence:
                    'Sigma eliminator remains representation-only'
            },
            {
                order: 4,
                target: {
                    kind: 'runtime-rule',
                    id: 'stress.sigma.eliminator-beta'
                },
                policy: 'conformance-only',
                evidence:
                    'Sigma beta depends on the uncompiled inductive phase'
            },
            {
                order: 5,
                target: {
                    kind: 'declaration',
                    symbol: piGrpd
                },
                policy: 'conformance-only',
                evidence:
                    'Groupoidal Pi is not in an approved stress profile'
            },
            {
                order: 6,
                target: {
                    kind: 'runtime-rule',
                    id: 'stress.pi-grpd.decode'
                },
                policy: 'conformance-only',
                evidence:
                    'Binder-producing Pi beta awaits semantic review'
            }
        ]
    });

const natAddType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    const natType = decode(builder, builder.global(natGrpd));
    return builder.term(builder.pi(
        'm',
        natType,
        _ => builder.pi(
            'n',
            natType,
            _ => natType
        )
    ));
};

const natRule = (
    order: number,
    id: string,
    clauseOrder: number,
    variableNames: readonly string[],
    left: (
        builder: CoreLfTransferScopedBuilder,
        captures: Readonly<Record<
            string,
            CoreLfTransferBuilderExpression
        >>
    ) => CoreLfTransferBuilderExpression,
    right: (
        builder: CoreLfTransferScopedBuilder,
        captures: Readonly<Record<
            string,
            CoreLfTransferBuilderExpression
        >>
    ) => CoreLfTransferBuilderExpression,
    sourceFragment: string
) => {
    const builder = new CoreLfTransferScopedBuilder();
    const captures = Object.fromEntries(
        variableNames.map(name => [name, builder.capture(name)])
    );
    const natType = decode(builder, builder.global(natGrpd));
    return {
        order,
        id,
        groupId: 'stress.nat-add',
        clauseOrder,
        sourceOwner: natAdd,
        variables: variableNames.map(name => ({
            name,
            type: builder.template(natType)
        })),
        left: builder.pattern(left(builder, captures)),
        right: builder.template(right(builder, captures)),
        provenance: source(
            sourceFragment,
            4,
            'emdash2/emdash3_2_nat_arithmetic.lp'
        )
    };
};

const natAddCall = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
) => globalCall(builder, natAdd, [
    { plicity: 'explicit', value: left },
    { plicity: 'explicit', value: right }
]);

const succCall = (
    builder: CoreLfTransferScopedBuilder,
    value: CoreLfTransferBuilderExpression
) => globalCall(builder, succ, [{
    plicity: 'explicit',
    value
}]);

const createNatRepresentation = (): CoreLfModuleSpec =>
    createCoreLfModuleSpec({
        revision: 'SCALE-STRESS-1A-NAT-REPRESENTATION-1',
        moduleId: natModuleId,
        fragmentId: 'scale-stress-1a-nat-representation',
        authorityPath:
            CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION.authorityPath,
        sourceSha256:
            CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION.sourceSha256,
        canonicalExport: {
            exporterVersion:
                CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
                    .canonicalExport.exporterVersion,
            sha256:
                CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
                    .canonicalExport.sha256
        },
        dependencies: [coreModuleId],
        externalSymbols: [
            tau,
            natGrpd,
            zero,
            succ
        ].map(symbol => ({
            symbol,
            availability: 'dependency-module' as const
        })),
        declarations: [{
            order: 0,
            symbol: natAdd,
            type: natAddType(),
            body: coreLfTransferAbsentBody(),
            modifiers: publicModifiers('injective'),
            provenance: source(
                'injective symbol nat_add\n  (m n : τ Nat_grpd)',
                3,
                'emdash2/emdash3_2_nat_arithmetic.lp'
            )
        }],
        inductives: [],
        runtimeRules: [
            natRule(
                1,
                'stress.nat-add.zero-left',
                0,
                ['n'],
                (builder, captures) => natAddCall(
                    builder,
                    builder.global(zero),
                    captures.n
                ),
                (_builder, captures) => captures.n,
                'rule @nat_add zero $n ↪ $n'
            ),
            natRule(
                2,
                'stress.nat-add.succ-left',
                1,
                ['m', 'n'],
                (builder, captures) => natAddCall(
                    builder,
                    succCall(builder, captures.m),
                    captures.n
                ),
                (builder, captures) => succCall(
                    builder,
                    natAddCall(
                        builder,
                        captures.m,
                        captures.n
                    )
                ),
                'with @nat_add (succ $m) $n ' +
                    '↪ succ (@nat_add $m $n)'
            ),
            natRule(
                3,
                'stress.nat-add.zero-right',
                2,
                ['m'],
                (builder, captures) => natAddCall(
                    builder,
                    captures.m,
                    builder.global(zero)
                ),
                (_builder, captures) => captures.m,
                'with @nat_add $m zero ↪ $m;'
            )
        ],
        proofRules: []
    });

const createNatPolicy = (
    module: CoreLfModuleSpec
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision: 'SCALE-STRESS-1A-NAT-POLICY-1',
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: natAdd
                },
                policy: 'conformance-only',
                evidence:
                    'Imported Nat declaration awaits semantic review'
            },
            ...module.runtimeRules.map((rule, index) => ({
                order: index + 1,
                target: {
                    kind: 'runtime-rule' as const,
                    id: rule.id
                },
                policy: 'conformance-only' as const,
                evidence:
                    'Grouped Nat recursion remains representation-only'
            }))
        ]
    });

export interface CoreLfScaleStressMechanismAssessment {
    readonly mechanism:
        | 'outer-dependent-j'
        | 'decoded-groupoidal-pi'
        | 'decoded-dependent-sigma'
        | 'imported-grouped-nat-recursion';
    readonly commandIds: readonly string[];
    readonly typedRepresentation: string;
    readonly currentBoundary: string;
    readonly nextRequirement: string;
}

export interface CoreLfScaleStress1Representation {
    readonly revision: 'SCALE-STRESS-1A-REPRESENTATION-1';
    readonly core: {
        readonly module: CoreLfModuleSpec;
        readonly policy: CoreLfTransferPolicyOverlay;
    };
    readonly nat: {
        readonly module: CoreLfModuleSpec;
        readonly policy: CoreLfTransferPolicyOverlay;
    };
    readonly assessments:
        readonly CoreLfScaleStressMechanismAssessment[];
    readonly semanticStatus: 'representation-only';
    readonly productEffects: readonly [];
    readonly doesNotAuthorize: readonly [
        'active-declaration-installation',
        'active-runtime-execution',
        'inductive-compilation',
        'browser-export',
        'lambdapi-source-change',
        'mechanical-transfer-qualification'
    ];
}

export type CoreLfScaleStress1RepresentationErrorCode =
    | 'INVALID_REPRESENTATION_BOUNDARY'
    | 'REPRESENTATION_DRIFT';

export class CoreLfScaleStress1RepresentationError extends Error {
    constructor(
        public readonly code:
            CoreLfScaleStress1RepresentationErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleStress1RepresentationError';
    }
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const coreRepresentation = createCoreRepresentation();
const natRepresentation = createNatRepresentation();

const rawRepresentation: CoreLfScaleStress1Representation = {
    revision: 'SCALE-STRESS-1A-REPRESENTATION-1',
    core: {
        module: coreRepresentation,
        policy: createCorePolicy(coreRepresentation)
    },
    nat: {
        module: natRepresentation,
        policy: createNatPolicy(natRepresentation)
    },
    assessments: [
        {
            mechanism: 'outer-dependent-j',
            commandIds: [
                'outer-j.declaration',
                'outer-j.reflexivity-beta'
            ],
            typedRepresentation:
                'canonical wildcard lowered to one typed RHS-unused ' +
                'motive capture; category and endpoint guards repeated',
            currentBoundary:
                'mixed IR is complete; generic source-ordered phase ' +
                'planning and active policy are absent',
            nextRequirement:
                'generic mixed-phase planner, exact isolated semantic ' +
                'proposal, and guarded positive, foreign-category, ' +
                'wrong-endpoint, and raw-proof witnesses'
        },
        {
            mechanism: 'decoded-groupoidal-pi',
            commandIds: [
                'pi.decoded-classifier',
                'pi.decoding-beta'
            ],
            typedRepresentation:
                'dependent Pi declaration and binder-producing RHS use ' +
                'the existing locally nameless pi node',
            currentBoundary:
                'mixed IR is complete; generic source-ordered phase ' +
                'planning and active policy are absent',
            nextRequirement:
                'generic mixed-phase planner, exact isolated semantic ' +
                'proposal, and binder RHS subject-reduction/conformance ' +
                'witnesses'
        },
        {
            mechanism: 'decoded-dependent-sigma',
            commandIds: [
                'sigma.decoded-inductive',
                'sigma.eliminator',
                'sigma.eliminator-beta'
            ],
            typedRepresentation:
                'parameterized inductive, dependent constructor, generated ' +
                'eliminator identity, and eliminator beta are explicit',
            currentBoundary:
                'the shared IR represents inductives but no generic ' +
                'inductive compiler or mixed-phase planner exists',
            nextRequirement:
                'generic immutable inductive declaration/constructor/' +
                'generated-owner compiler plus mixed-phase planning before ' +
                'semantic execution'
        },
        {
            mechanism: 'imported-grouped-nat-recursion',
            commandIds: [
                'nat.import-core',
                'nat.addition',
                'nat.addition-grouped-recursion'
            ],
            typedRepresentation:
                'dependency-module import plus three ordered clauses and ' +
                'recursive RHS are explicit',
            currentBoundary:
                'generic grouping and runtime-fragment seams exist; mixed ' +
                'phase/dependency planning and active policy are absent',
            nextRequirement:
                'generic mixed-phase/dependency planning, exact imported ' +
                'semantic proposal, and positive, overlap, open-term, ' +
                'recursion-budget, and near-miss witnesses'
        }
    ],
    semanticStatus: 'representation-only',
    productEffects: [],
    doesNotAuthorize: [
        'active-declaration-installation',
        'active-runtime-execution',
        'inductive-compilation',
        'browser-export',
        'lambdapi-source-change',
        'mechanical-transfer-qualification'
    ]
};

export const CORE_LF_SCALE_STRESS_1_REPRESENTATION =
    deepFreeze(rawRepresentation);

export function validateCoreLfScaleStress1Representation(
    representation: CoreLfScaleStress1Representation =
        CORE_LF_SCALE_STRESS_1_REPRESENTATION
): void {
    validateCoreLfScaleEngineReview();
    if (
        representation.semanticStatus !== 'representation-only' ||
        representation.productEffects.length !== 0 ||
        representation.core.policy.entries.some(
            entry => entry.policy !== 'conformance-only'
        ) ||
        representation.nat.policy.entries.some(
            entry => entry.policy !== 'conformance-only'
        )
    ) {
        throw new CoreLfScaleStress1RepresentationError(
            'INVALID_REPRESENTATION_BOUNDARY',
            'SCALE-STRESS-1A must remain conformance-only and have no ' +
                'product effects'
        );
    }
    if (!sameData(representation, rawRepresentation)) {
        throw new CoreLfScaleStress1RepresentationError(
            'REPRESENTATION_DRIFT',
            'SCALE-STRESS-1A representation differs from the exact ' +
                'reviewed source and mechanism classification'
        );
    }
}

validateCoreLfScaleStress1Representation();
