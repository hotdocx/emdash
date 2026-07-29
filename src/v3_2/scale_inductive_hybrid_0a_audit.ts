/**
 * SCALE-INDUCTIVE-HYBRID-0A lean generated-owner transfer audit.
 *
 * Lambdapi has already checked the source inductive and exposes `ind_nat` as
 * one explicit declaration plus two ordinary rewrite rules. This isolated
 * audit asks whether those expanded artifacts and the existing `nat_elim`
 * consumer pass through the generic TypeScript engines without a recursive
 * generated-owner association or a new positivity checker.
 */

import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferInductiveBlock,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    compileCoreLfInductiveSignatures,
    lowerCoreLfInductiveSignatures
} from './lf_transfer_inductive';
import {
    CoreLfCompiledMixedModule,
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import {
    CORE_LF_SCALE_STRESS_1B_PROPOSAL
} from './scale_stress_1b_proposal';

export const CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_REVISION =
    'SCALE-INDUCTIVE-HYBRID-0A-AUDIT-1' as const;

const coreModuleId = 'emdash.emdash3_2';

const coreSymbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(coreModuleId, name);

const grpd = coreSymbol('Grpd');
const tau = coreSymbol('τ');
const nat = coreSymbol('nat');
const zero = coreSymbol('zero');
const succ = coreSymbol('succ');
const natGrpd = coreSymbol('Nat_grpd');
const generatedIndNat = coreSymbol('ind_nat');
const natElim = coreSymbol('nat_elim');

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

const applyExplicit = (
    builder: CoreLfTransferScopedBuilder,
    callee: CoreLfTransferBuilderExpression,
    values: readonly CoreLfTransferBuilderExpression[]
): CoreLfTransferBuilderExpression =>
    call(
        builder,
        callee,
        values.map(value => ({
            plicity: 'explicit',
            value
        }))
    );

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, tau, [{
        plicity: 'explicit',
        value: classifier
    }]);

const successor = (
    builder: CoreLfTransferScopedBuilder,
    predecessor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    applyExplicit(
        builder,
        builder.global(succ),
        [predecessor]
    );

const familyType = (
    builder: CoreLfTransferScopedBuilder,
    carrier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'n',
        carrier,
        _n => builder.global(grpd)
    );

const familyAt = (
    builder: CoreLfTransferScopedBuilder,
    family: CoreLfTransferBuilderExpression,
    index: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    applyExplicit(builder, family, [index]);

const successorBranchType = (
    builder: CoreLfTransferScopedBuilder,
    family: CoreLfTransferBuilderExpression,
    carrier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'n',
        carrier,
        n => builder.pi(
            'ih',
            decode(builder, familyAt(builder, family, n)),
            _ih => decode(
                builder,
                familyAt(builder, family, successor(builder, n))
            )
        )
    );

const generatedIndNatType = () => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'P',
        familyType(builder, builder.global(nat)),
        P => builder.pi(
            'u_zero',
            decode(
                builder,
                familyAt(builder, P, builder.global(zero))
            ),
            _uZero => builder.pi(
                'u_succ',
                successorBranchType(
                    builder,
                    P,
                    builder.global(nat)
                ),
                _uSucc => builder.pi(
                    'n',
                    builder.global(nat),
                    n => decode(builder, familyAt(builder, P, n))
                )
            )
        )
    ));
};

const natElimType = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const decodedNat = decode(builder, builder.global(natGrpd));
    return builder.term(builder.pi(
        'P',
        familyType(builder, decodedNat),
        P => builder.pi(
            'u_zero',
            decode(
                builder,
                familyAt(builder, P, builder.global(zero))
            ),
            _uZero => builder.pi(
                'u_succ',
                successorBranchType(builder, P, decodedNat),
                _uSucc => builder.pi(
                    'n',
                    decodedNat,
                    n => decode(builder, familyAt(builder, P, n))
                )
            )
        )
    ));
};

const natElimBody = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const decodedNat = decode(builder, builder.global(natGrpd));
    return builder.term(builder.lam(
        'P',
        familyType(builder, decodedNat),
        P => builder.lam(
            'u_zero',
            decode(
                builder,
                familyAt(builder, P, builder.global(zero))
            ),
            uZero => builder.lam(
                'u_succ',
                successorBranchType(builder, P, decodedNat),
                uSucc => builder.lam(
                    'n',
                    decodedNat,
                    n => applyExplicit(
                        builder,
                        builder.global(generatedIndNat),
                        [P, uZero, uSucc, n]
                    )
                )
            )
        )
    ));
};

const generatedZeroRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const P = builder.capture('P');
    const uZero = builder.capture('u_zero');
    const uSucc = builder.capture('u_succ');
    return {
        order: 1,
        id: 'inductive.expanded.nat-zero',
        groupId: 'inductive.expanded.nat',
        clauseOrder: 0,
        sourceOwner: generatedIndNat,
        variables: [
            {
                name: 'P',
                type: builder.template(
                    familyType(builder, builder.global(nat))
                )
            },
            {
                name: 'u_zero',
                type: builder.template(decode(
                    builder,
                    familyAt(builder, P, builder.global(zero))
                ))
            },
            {
                name: 'u_succ',
                type: builder.template(successorBranchType(
                    builder,
                    P,
                    builder.global(nat)
                ))
            }
        ],
        left: builder.pattern(applyExplicit(
            builder,
            builder.global(generatedIndNat),
            [P, uZero, uSucc, builder.global(zero)]
        )),
        right: builder.template(uZero),
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            sourceFragment:
                'generated rule ind_nat P u_zero u_succ zero ↪ u_zero'
        }
    };
};

const generatedSuccessorRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const P = builder.capture('P');
    const uZero = builder.capture('u_zero');
    const uSucc = builder.capture('u_succ');
    const predecessor = builder.capture('predecessor');
    return {
        order: 2,
        id: 'inductive.expanded.nat-succ',
        groupId: 'inductive.expanded.nat',
        clauseOrder: 1,
        sourceOwner: generatedIndNat,
        variables: [
            {
                name: 'P',
                type: builder.template(
                    familyType(builder, builder.global(nat))
                )
            },
            {
                name: 'u_zero',
                type: builder.template(decode(
                    builder,
                    familyAt(builder, P, builder.global(zero))
                ))
            },
            {
                name: 'u_succ',
                type: builder.template(successorBranchType(
                    builder,
                    P,
                    builder.global(nat)
                ))
            },
            {
                name: 'predecessor',
                type: builder.template(builder.global(nat))
            }
        ],
        left: builder.pattern(applyExplicit(
            builder,
            builder.global(generatedIndNat),
            [
                P,
                uZero,
                uSucc,
                successor(builder, predecessor)
            ]
        )),
        right: builder.template(applyExplicit(
            builder,
            uSucc,
            [
                predecessor,
                applyExplicit(
                    builder,
                    builder.global(generatedIndNat),
                    [P, uZero, uSucc, predecessor]
                )
            ]
        )),
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            sourceFragment:
                'generated rule ind_nat P u_zero u_succ ' +
                '(succ n) ↪ u_succ n (ind_nat P u_zero u_succ n)'
        }
    };
};

const natDecodeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    return {
        order: 4,
        id: 'inductive.expanded.nat-grpd-decode',
        groupId: 'inductive.expanded.nat-grpd',
        clauseOrder: 0,
        sourceOwner: tau,
        variables: [],
        left: builder.pattern(decode(
            builder,
            builder.global(natGrpd)
        )),
        right: builder.template(builder.global(nat)),
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            sourceFragment: 'rule τ Nat_grpd ↪ nat;'
        }
    };
};

const sourceNatBlock = (): CoreLfTransferInductiveBlock => {
    const block =
        CORE_LF_SCALE_STRESS_1B_PROPOSAL.core.module.inductives
            .find(candidate =>
                candidate.symbol.moduleId === nat.moduleId &&
                candidate.symbol.name === nat.name
            );
    if (
        block === undefined ||
        block.parameters.length !== 0 ||
        block.indices.length !== 0 ||
        block.constructors.length !== 2 ||
        block.constructors[0].symbol.name !== 'zero' ||
        block.constructors[1].symbol.name !== 'succ'
    ) {
        throw new Error(
            'Acquired native Nat inductive shape drifted'
        );
    }
    return block;
};

const authority =
    CORE_LF_SCALE_STRESS_1B_PROPOSAL.core.module;

const signatureModule = createCoreLfModuleSpec({
    revision: 'SCALE-INDUCTIVE-HYBRID-0A-NAT-SIGNATURE-1',
    moduleId: coreModuleId,
    fragmentId: 'scale-inductive-hybrid-0a-nat-signature',
    authorityPath: authority.authorityPath,
    sourceSha256: authority.sourceSha256,
    dependencies: [],
    externalSymbols: [],
    declarations: [],
    inductives: [sourceNatBlock()],
    runtimeRules: [],
    proofRules: []
});

const signaturePolicy = createCoreLfTransferPolicyOverlay(
    signatureModule,
    {
        revision:
            'SCALE-INDUCTIVE-HYBRID-0A-NAT-SIGNATURE-POLICY-1',
        moduleRevision: signatureModule.revision,
        entries: [{
            order: 0,
            target: {
                kind: 'inductive',
                symbol: nat
            },
            policy: 'opaque-signature',
            evidence:
                'isolated expanded-generated-owner audit only'
        }]
    }
);

const contractModule = createCoreLfModuleSpec({
    revision: 'SCALE-INDUCTIVE-HYBRID-0A-NAT-CONTRACT-1',
    moduleId: coreModuleId,
    fragmentId: 'scale-inductive-hybrid-0a-nat-contract',
    authorityPath: authority.authorityPath,
    sourceSha256: authority.sourceSha256,
    dependencies: [],
    externalSymbols: [
        { symbol: grpd, availability: 'existing-core' },
        { symbol: tau, availability: 'existing-core' },
        { symbol: nat, availability: 'earlier-fragment' },
        { symbol: zero, availability: 'earlier-fragment' },
        { symbol: succ, availability: 'earlier-fragment' }
    ],
    declarations: [
        {
            order: 0,
            symbol: generatedIndNat,
            type: generatedIndNatType(),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque',
                /*
                 * Retained as inert provenance. This audit deliberately
                 * invokes no generated-owner association validator.
                 */
                generatedBy: nat
            },
            provenance: {
                authorityPath: authority.authorityPath,
                sourceFragment: 'generated print ind_nat;'
            }
        },
        {
            order: 3,
            symbol: natGrpd,
            type: {
                tag: 'global',
                symbol: grpd
            },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'constant',
                sourceOpacity: 'opaque'
            },
            provenance: {
                authorityPath: authority.authorityPath,
                sourceFragment: 'constant symbol Nat_grpd : Grpd;'
            }
        },
        {
            order: 5,
            symbol: natElim,
            type: natElimType(),
            body: {
                kind: 'explicit-term',
                term: natElimBody()
            },
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'transparent'
            },
            provenance: {
                authorityPath: authority.authorityPath,
                sourceFragment:
                    'symbol nat_elim ... ≔ ind_nat P u_zero u_succ n;'
            }
        }
    ],
    inductives: [],
    runtimeRules: [
        generatedZeroRule(),
        generatedSuccessorRule(),
        natDecodeRule()
    ],
    proofRules: []
});

const contractPolicy = createCoreLfTransferPolicyOverlay(
    contractModule,
    {
        revision:
            'SCALE-INDUCTIVE-HYBRID-0A-NAT-CONTRACT-POLICY-1',
        moduleRevision: contractModule.revision,
        entries: [
            {
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: generatedIndNat
                },
                policy: 'opaque-signature',
                evidence:
                    'exact printed expanded generated declaration'
            },
            {
                order: 1,
                target: {
                    kind: 'runtime-rule',
                    id: 'inductive.expanded.nat-zero'
                },
                policy: 'runtime-rewrite',
                evidence: 'exact printed generated zero beta'
            },
            {
                order: 2,
                target: {
                    kind: 'runtime-rule',
                    id: 'inductive.expanded.nat-succ'
                },
                policy: 'runtime-rewrite',
                evidence:
                    'exact printed generated recursive successor beta'
            },
            {
                order: 3,
                target: {
                    kind: 'declaration',
                    symbol: natGrpd
                },
                policy: 'opaque-signature',
                evidence: 'active Nat classifier'
            },
            {
                order: 4,
                target: {
                    kind: 'runtime-rule',
                    id: 'inductive.expanded.nat-grpd-decode'
                },
                policy: 'runtime-rewrite',
                evidence: 'active Nat classifier decoding beta'
            },
            {
                order: 5,
                target: {
                    kind: 'declaration',
                    symbol: natElim
                },
                policy: 'checked-transparent-definition',
                evidence:
                    'exact active recursive generated-owner consumer'
            }
        ]
    }
);

const contractPlan = planCoreLfMixedPhases(
    contractModule,
    contractPolicy
);

const contractLinkage = createCoreLfMixedDeclarationLinkage(
    contractPlan,
    {
        revision:
            'SCALE-INDUCTIVE-HYBRID-0A-NAT-CONTRACT-LINKAGE-1',
        moduleRevision: contractModule.revision,
        entries: [
            {
                order: 0,
                symbol: grpd,
                kind: 'core-owner',
                owner: 'groupoid-universe'
            },
            {
                order: 1,
                symbol: tau,
                kind: 'core-owner',
                owner: 'decode'
            },
            {
                order: 2,
                symbol: nat,
                kind: 'free-declaration',
                coreName: 'scale_inductive_hybrid_nat',
                backendName: 'nat'
            },
            {
                order: 3,
                symbol: zero,
                kind: 'free-declaration',
                coreName: 'scale_inductive_hybrid_zero',
                backendName: 'zero'
            },
            {
                order: 4,
                symbol: succ,
                kind: 'free-declaration',
                coreName: 'scale_inductive_hybrid_succ',
                backendName: 'succ'
            },
            {
                order: 5,
                symbol: generatedIndNat,
                kind: 'free-declaration',
                coreName: 'scale_inductive_hybrid_ind_nat',
                backendName: 'ind_nat'
            },
            {
                order: 6,
                symbol: natGrpd,
                kind: 'free-declaration',
                coreName: 'scale_inductive_hybrid_Nat_grpd',
                backendName: 'Nat_grpd'
            },
            {
                order: 7,
                symbol: natElim,
                kind: 'free-declaration',
                coreName: 'scale_inductive_hybrid_nat_elim',
                backendName: 'nat_elim'
            }
        ]
    }
);

export interface CoreLfScaleInductiveHybrid0aCompilation {
    readonly signatureModule: CoreLfModuleSpec;
    readonly contractModule: CoreLfModuleSpec;
    readonly contract: CoreLfCompiledMixedModule;
}

/**
 * Compile the expanded generated owner entirely through existing engines.
 *
 * No generated-owner association function participates in this path.
 */
export function compileCoreLfScaleInductiveHybrid0aAudit():
CoreLfScaleInductiveHybrid0aCompilation {
    const lowering = lowerCoreLfInductiveSignatures(
        signatureModule,
        signaturePolicy
    );
    const declarations = lowering.module.declarations;
    const signatureLinkage = createCoreLfTransferDeclarationLinkage(
        lowering.module,
        {
            revision:
                'SCALE-INDUCTIVE-HYBRID-0A-NAT-' +
                'SIGNATURE-LINKAGE-1',
            moduleRevision: lowering.module.revision,
            entries: [
                {
                    order: 0,
                    symbol: declarations[0].symbol,
                    kind: 'free-declaration',
                    coreName: 'scale_inductive_hybrid_nat',
                    backendName: 'nat'
                },
                {
                    order: 1,
                    symbol: declarations[1].symbol,
                    kind: 'free-declaration',
                    coreName: 'scale_inductive_hybrid_zero',
                    backendName: 'zero'
                },
                {
                    order: 2,
                    symbol: declarations[2].symbol,
                    kind: 'free-declaration',
                    coreName: 'scale_inductive_hybrid_succ',
                    backendName: 'succ'
                }
            ]
        }
    );
    const signature = compileCoreLfInductiveSignatures(
        lowering,
        signatureLinkage
    );
    const contract = compileCoreLfMixedPhases(
        contractPlan,
        contractLinkage,
        { initialDeclarations: signature }
    );
    return Object.freeze({
        signatureModule,
        contractModule,
        contract
    });
}

export interface CoreLfScaleInductiveHybrid0aAudit {
    readonly revision:
        typeof CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_REVISION;
    readonly row: 'SCALE-INDUCTIVE-HYBRID-0A';
    readonly status: 'executable-read-only-audit';
    readonly measuredAuthority: {
        readonly generatedDeclarationCount: 1;
        readonly generatedRuntimeRuleCount: 2;
        readonly recursiveInductionHypothesisLocation:
            'successor-rule-right-hand-side';
        readonly existingConsumer: 'nat_elim';
    };
    readonly conclusion: {
        readonly semanticTransferBaseline:
            'ordinary-explicit-declaration-and-runtime-rules';
        readonly generatedByMetadata:
            'retained-inert-provenance';
        readonly associationDependency: 'none';
        readonly positivityRequirement:
            'not-required-for-expanded-symbol-transfer';
        readonly positivityBecomesRelevantFor: readonly [
            'typescript-source-inductive-generation',
            'untrusted-inductive-source-validation'
        ];
    };
    readonly nextBoundary:
        'freeze-minimal-expanded-symbol-SCALE-INDUCTIVE-1B2-proposal';
    readonly productEffects: readonly [];
    readonly doesNotAuthorize: readonly [
        'recursive-association-generalization',
        'typescript-positivity-checker',
        'automatic-eliminator-synthesis',
        'end-user-inductive-declaration-api',
        'active-profile-or-browser-promotion',
        'lambdapi-source-change'
    ];
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

export const CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_AUDIT =
    deepFreeze<CoreLfScaleInductiveHybrid0aAudit>({
        revision: CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_REVISION,
        row: 'SCALE-INDUCTIVE-HYBRID-0A',
        status: 'executable-read-only-audit',
        measuredAuthority: {
            generatedDeclarationCount: 1,
            generatedRuntimeRuleCount: 2,
            recursiveInductionHypothesisLocation:
                'successor-rule-right-hand-side',
            existingConsumer: 'nat_elim'
        },
        conclusion: {
            semanticTransferBaseline:
                'ordinary-explicit-declaration-and-runtime-rules',
            generatedByMetadata: 'retained-inert-provenance',
            associationDependency: 'none',
            positivityRequirement:
                'not-required-for-expanded-symbol-transfer',
            positivityBecomesRelevantFor: [
                'typescript-source-inductive-generation',
                'untrusted-inductive-source-validation'
            ]
        },
        nextBoundary:
            'freeze-minimal-expanded-symbol-SCALE-INDUCTIVE-1B2-proposal',
        productEffects: [],
        doesNotAuthorize: [
            'recursive-association-generalization',
            'typescript-positivity-checker',
            'automatic-eliminator-synthesis',
            'end-user-inductive-declaration-api',
            'active-profile-or-browser-promotion',
            'lambdapi-source-change'
        ]
    });

export const CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_SYMBOLS =
    Object.freeze({
        nat,
        zero,
        succ,
        generatedIndNat,
        natGrpd,
        natElim
    });
