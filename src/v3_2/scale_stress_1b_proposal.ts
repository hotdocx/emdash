/**
 * Exact semantic-policy proposal for SCALE-STRESS-1B.
 *
 * This builds one isolated, dependency-closed qualification profile in active
 * Lambdapi source order. It does not install that profile in the product or
 * authorize its execution outside proposal/conformance evidence.
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
    CoreLfCanonicalSelectionContract,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition';
import {
    CoreLfCompiledMixedModule,
    CoreLfMixedDeclarationLinkage,
    CoreLfMixedPhasePlan,
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import {
    createCoreLfCompiledModuleInterface
} from './lf_transfer_visibility';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';
import {
    CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
} from './scale_stress_1_acquisition';
import {
    CORE_LF_SCALE_STRESS_1_REPRESENTATION,
    validateCoreLfScaleStress1Representation
} from './scale_stress_1_representation';

const coreModuleId = 'emdash.emdash3_2';

const coreSymbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(coreModuleId, name);

const grpd = coreSymbol('Grpd');
const tau = coreSymbol('τ');
const equality = coreSymbol('=');
const eqRefl = coreSymbol('eq_refl');
const indEqr = coreSymbol('ind_eqr');
const nat = coreSymbol('nat');
const zero = coreSymbol('zero');
const succ = coreSymbol('succ');
const generatedIndNat = coreSymbol('ind_nat');
const natGrpd = coreSymbol('Nat_grpd');
const tauSigma = coreSymbol('τΣ_');
const structSigma = coreSymbol('Struct_sigma');
const sigmaInd = coreSymbol('sigma_ind');
const piGrpd = coreSymbol('Pi_grpd');

const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

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

const equalityType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(grpd),
        a => builder.pi(
            'left',
            decode(builder, a),
            _left => builder.pi(
                'right',
                decode(builder, a),
                _right => builder.global(grpd)
            )
        ),
        implicitMode
    ));
};

const eqReflType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(grpd),
        a => builder.pi(
            'x',
            decode(builder, a),
            x => decode(
                builder,
                globalCall(builder, equality, [
                    {
                        plicity: 'implicit',
                        value: a
                    },
                    {
                        plicity: 'explicit',
                        value: x
                    },
                    {
                        plicity: 'explicit',
                        value: x
                    }
                ])
            )
        ),
        implicitMode
    ));
};

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
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

const natInductive = () => ({
    order: 4,
    symbol: nat,
    parameters: [],
    indices: [],
    sort: {
        tag: 'type' as const
    },
    constructors: [
        {
            order: 0,
            symbol: zero,
            binders: [],
            result: {
                tag: 'global' as const,
                symbol: nat
            },
            provenance: source('| zero : nat', 38)
        },
        {
            order: 1,
            symbol: succ,
            binders: [{
                hint: 'predecessor',
                mode: explicitMode,
                type: {
                    tag: 'global' as const,
                    symbol: nat
                }
            }],
            result: {
                tag: 'global' as const,
                symbol: nat
            },
            provenance: source('| succ : nat → nat;', 38)
        }
    ],
    generatedSymbols: [generatedIndNat],
    modifiers: publicModifiers('injective'),
    provenance: source('inductive nat : TYPE ≔', 38)
});

const natDecodeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    return {
        order: 6,
        id: 'stress.nat-grpd.decode',
        groupId: 'stress.nat-grpd',
        clauseOrder: 0,
        sourceOwner: tau,
        variables: [],
        left: builder.pattern(globalCall(builder, tau, [{
            plicity: 'explicit',
            value: builder.global(natGrpd)
        }])),
        right: builder.template(builder.global(nat)),
        provenance: source('rule τ Nat_grpd ↪ nat;', 40)
    };
};

const sourceCore =
    CORE_LF_SCALE_STRESS_1_REPRESENTATION.core.module;

const sourceDeclaration = (
    symbol: CoreLfQualifiedSymbol
) => {
    const declaration = sourceCore.declarations.find(candidate =>
        candidate.symbol.moduleId === symbol.moduleId &&
        candidate.symbol.name === symbol.name
    );
    if (declaration === undefined) {
        throw new Error(
            `Missing SCALE-STRESS-1A declaration '${symbol.name}'`
        );
    }
    return declaration;
};

const sourceRuntimeRule = (id: string) => {
    const rule = sourceCore.runtimeRules.find(candidate =>
        candidate.id === id
    );
    if (rule === undefined) {
        throw new Error(
            `Missing SCALE-STRESS-1A runtime rule '${id}'`
        );
    }
    return rule;
};

const sourceSigmaInductive = () => {
    const block = sourceCore.inductives.find(candidate =>
        candidate.symbol.moduleId === tauSigma.moduleId &&
        candidate.symbol.name === tauSigma.name
    );
    if (block === undefined) {
        throw new Error(
            "Missing SCALE-STRESS-1A inductive 'τΣ_'"
        );
    }
    return block;
};

const createCoreQualificationModule = (): CoreLfModuleSpec =>
    createCoreLfModuleSpec({
        revision: 'SCALE-STRESS-1B-CORE-PROPOSAL-1',
        moduleId: coreModuleId,
        fragmentId: 'scale-stress-1b-core-proposal',
        authorityPath: sourceCore.authorityPath,
        sourceSha256: sourceCore.sourceSha256,
        canonicalExport: sourceCore.canonicalExport,
        dependencies: [],
        externalSymbols: [
            grpd,
            tau
        ].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [
            {
                order: 0,
                symbol: equality,
                type: equalityType(),
                body: coreLfTransferAbsentBody(),
                modifiers: publicModifiers('injective'),
                provenance: source(
                    'injective symbol = : Π [a: Grpd], ' +
                        'τ a → τ a → Grpd;',
                    10
                )
            },
            {
                order: 1,
                symbol: eqRefl,
                type: eqReflType(),
                body: coreLfTransferAbsentBody(),
                modifiers: publicModifiers('injective'),
                provenance: source(
                    'injective symbol eq_refl : Π [a: Grpd], ' +
                        'Π x: τ a, τ (x = x);',
                    12
                )
            },
            {
                ...sourceDeclaration(indEqr),
                order: 2
            },
            {
                order: 5,
                symbol: natGrpd,
                type: {
                    tag: 'global',
                    symbol: grpd
                },
                body: coreLfTransferAbsentBody(),
                modifiers: publicModifiers('constant'),
                provenance: source(
                    'constant symbol Nat_grpd : Grpd;',
                    39
                )
            },
            {
                ...sourceDeclaration(sigmaInd),
                order: 8
            },
            {
                ...sourceDeclaration(piGrpd),
                order: 10
            }
        ],
        inductives: [
            natInductive(),
            {
                ...sourceSigmaInductive(),
                order: 7
            }
        ],
        runtimeRules: [
            {
                ...sourceRuntimeRule(
                    'stress.outer-j.reflexivity'
                ),
                order: 3
            },
            natDecodeRule(),
            {
                ...sourceRuntimeRule(
                    'stress.sigma.eliminator-beta'
                ),
                order: 9
            },
            {
                ...sourceRuntimeRule('stress.pi-grpd.decode'),
                order: 11
            }
        ],
        proofRules: []
    });

const policyEntry = (
    order: number,
    target:
        | {
            readonly kind: 'declaration' | 'inductive';
            readonly symbol: CoreLfQualifiedSymbol;
        }
        | {
            readonly kind: 'runtime-rule';
            readonly id: string;
        },
    policy: 'opaque-signature' | 'runtime-rewrite',
    evidence: string
) => ({
    order,
    target,
    policy,
    evidence
});

const createCoreQualificationPolicy = (
    module: CoreLfModuleSpec
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision: 'SCALE-STRESS-1B-CORE-PROPOSED-POLICY-1',
        moduleRevision: module.revision,
        entries: [
            policyEntry(
                0,
                { kind: 'declaration', symbol: equality },
                'opaque-signature',
                'proposed exact active equality signature'
            ),
            policyEntry(
                1,
                { kind: 'declaration', symbol: eqRefl },
                'opaque-signature',
                'proposed exact active reflexivity signature'
            ),
            policyEntry(
                2,
                { kind: 'declaration', symbol: indEqr },
                'opaque-signature',
                'proposed exact active right-J signature'
            ),
            policyEntry(
                3,
                {
                    kind: 'runtime-rule',
                    id: 'stress.outer-j.reflexivity'
                },
                'runtime-rewrite',
                'proposed exact active right-J beta'
            ),
            policyEntry(
                4,
                { kind: 'inductive', symbol: nat },
                'opaque-signature',
                'proposed native Nat signature erasure only'
            ),
            policyEntry(
                5,
                { kind: 'declaration', symbol: natGrpd },
                'opaque-signature',
                'proposed exact active Nat classifier signature'
            ),
            policyEntry(
                6,
                {
                    kind: 'runtime-rule',
                    id: 'stress.nat-grpd.decode'
                },
                'runtime-rewrite',
                'proposed exact active Nat decoding beta'
            ),
            policyEntry(
                7,
                { kind: 'inductive', symbol: tauSigma },
                'opaque-signature',
                'proposed decoded Sigma signature erasure only'
            ),
            policyEntry(
                8,
                { kind: 'declaration', symbol: sigmaInd },
                'opaque-signature',
                'proposed exact active Sigma eliminator signature'
            ),
            policyEntry(
                9,
                {
                    kind: 'runtime-rule',
                    id: 'stress.sigma.eliminator-beta'
                },
                'runtime-rewrite',
                'proposed exact active Sigma eliminator beta'
            ),
            policyEntry(
                10,
                { kind: 'declaration', symbol: piGrpd },
                'opaque-signature',
                'proposed exact active decoded Pi signature'
            ),
            policyEntry(
                11,
                {
                    kind: 'runtime-rule',
                    id: 'stress.pi-grpd.decode'
                },
                'runtime-rewrite',
                'proposed exact active decoded Pi beta'
            )
        ]
    });

const coreLinkageEntries = [
    {
        symbol: grpd,
        kind: 'core-owner' as const,
        owner: 'groupoid-universe' as const
    },
    {
        symbol: tau,
        kind: 'core-owner' as const,
        owner: 'decode' as const
    },
    ...[
        [equality, 'stress_eq', '='],
        [eqRefl, 'stress_eq_refl', 'eq_refl'],
        [indEqr, 'stress_ind_eqr', 'ind_eqr'],
        [nat, 'stress_nat', 'nat'],
        [zero, 'stress_zero', 'zero'],
        [succ, 'stress_succ', 'succ'],
        [natGrpd, 'stress_Nat_grpd', 'Nat_grpd'],
        [tauSigma, 'stress_tau_sigma', 'τΣ_'],
        [structSigma, 'stress_struct_sigma', 'Struct_sigma'],
        [sigmaInd, 'stress_sigma_ind', 'sigma_ind'],
        [piGrpd, 'stress_Pi_grpd', 'Pi_grpd']
    ].map(([symbol, coreName, backendName]) => ({
        symbol: symbol as CoreLfQualifiedSymbol,
        kind: 'free-declaration' as const,
        coreName: coreName as string,
        backendName: backendName as string
    }))
].map((entry, order) => ({
    order,
    ...entry
}));

const createNatQualificationPolicy = (
    module: CoreLfModuleSpec
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision: 'SCALE-STRESS-1B-NAT-PROPOSED-POLICY-1',
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: module.declarations[0].symbol
                },
                policy: 'opaque-signature',
                evidence: 'proposed exact active nat_add signature'
            },
            ...module.runtimeRules.map((rule, index) => ({
                order: index + 1,
                target: {
                    kind: 'runtime-rule' as const,
                    id: rule.id
                },
                policy: 'runtime-rewrite' as const,
                evidence:
                    'proposed exact active grouped nat_add recursion'
            }))
        ]
    });

const natLinkageEntries = [
    {
        symbol: tau,
        kind: 'core-owner' as const,
        owner: 'decode' as const
    },
    ...[
        [natGrpd, 'stress_Nat_grpd', 'Nat_grpd'],
        [zero, 'stress_zero', 'zero'],
        [succ, 'stress_succ', 'succ'],
        [
            CORE_LF_SCALE_STRESS_1_REPRESENTATION
                .nat.module.declarations[0].symbol,
            'stress_nat_add',
            'nat_add'
        ]
    ].map(([symbol, coreName, backendName]) => ({
        symbol: symbol as CoreLfQualifiedSymbol,
        kind: 'free-declaration' as const,
        coreName: coreName as string,
        backendName: backendName as string
    }))
].map((entry, order) => ({
    order,
    ...entry
}));

export const CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'SCALE-STRESS-1B-CORE-ACQUISITION-1',
        moduleId: coreModuleId,
        authorityPath: sourceCore.authorityPath,
        sourceSha256: sourceCore.sourceSha256,
        canonicalExport: {
            exporterVersion:
                sourceCore.canonicalExport?.exporterVersion ?? '',
            sha256: sourceCore.canonicalExport?.sha256 ?? '',
            imports: []
        },
        commands: [
            {
                id: 'foundation.equality',
                ordinal: 10,
                kind: 'symbol',
                textSha256:
                    'sha256:50a1fda97d4c395d8bfe9cc4e5134d516881add6989d47cbc7f6b474fdac0a8c',
                name: '=',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'foundation.reflexivity',
                ordinal: 12,
                kind: 'symbol',
                textSha256:
                    'sha256:83c1cd0946efdcf3a18beb467e35390082e617f396244c7e815d65f2aaf7955d',
                name: 'eq_refl',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'outer-j.declaration',
                ordinal: 13,
                kind: 'symbol',
                textSha256:
                    'sha256:341581476ee754882c2953cac7bd649f38c24001fe9cd45a8c06a4129bd06e9d',
                name: 'ind_eqr',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'outer-j.reflexivity-beta',
                ordinal: 14,
                kind: 'rule',
                textSha256:
                    'sha256:5a4af969f473058ce7e16c00a7ebff00f39c273b936e48b35da718ddb14cbece',
                clauseCount: 1
            },
            {
                id: 'foundation.nat-inductive',
                ordinal: 38,
                kind: 'inductive',
                textSha256:
                    'sha256:d9103633acf968d3f50b70f6ce37c3f844f2186a77e0e479644529159b3897e0',
                name: 'nat',
                constructorCount: 2
            },
            {
                id: 'foundation.nat-classifier',
                ordinal: 39,
                kind: 'symbol',
                textSha256:
                    'sha256:aca097ad43e44237fdbcc5a7cbdc2f9b4cd5eb48ec182cf7758e772da8456756',
                name: 'Nat_grpd',
                modifiers: ['constant'],
                hasBody: false
            },
            {
                id: 'foundation.nat-decode',
                ordinal: 40,
                kind: 'rule',
                textSha256:
                    'sha256:f044f387bef29806e4b6636140d68ae1c777f9d52ce7bea6d73e5ea1cf9b57f1',
                clauseCount: 1
            },
            {
                id: 'sigma.decoded-inductive',
                ordinal: 54,
                kind: 'inductive',
                textSha256:
                    'sha256:db4b03158723bda9d432dc5750a68bf36d30a40c7914034fbef5550cabd83f69',
                name: 'τΣ_',
                constructorCount: 1
            },
            {
                id: 'sigma.eliminator',
                ordinal: 63,
                kind: 'symbol',
                textSha256:
                    'sha256:e8a96705d438ed6d60682a30b0bea9b8124ac544453cb0bafa00c213dabc5e31',
                name: 'sigma_ind',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'sigma.eliminator-beta',
                ordinal: 64,
                kind: 'rule',
                textSha256:
                    'sha256:cdc48cbc3a997be41f8825b0f933015ed6151e25dfaf6eafd485cf4f8ac01526',
                clauseCount: 1
            },
            {
                id: 'pi.decoded-classifier',
                ordinal: 74,
                kind: 'symbol',
                textSha256:
                    'sha256:fe57925af572af813e027eca081bdebe09ce46f847e46b2803b1fb56e9d15b34',
                name: 'Pi_grpd',
                modifiers: ['constant'],
                hasBody: false
            },
            {
                id: 'pi.decoding-beta',
                ordinal: 75,
                kind: 'rule',
                textSha256:
                    'sha256:65f25ecd277a108aac576af30659ab8ddc08b4197f8e57d5e41ccd91c2119dad',
                clauseCount: 1
            }
        ]
    });

export const CORE_LF_SCALE_STRESS_1B_ACQUISITION_CONTRACTS =
    Object.freeze([
        CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION,
        CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
    ]);

const coreModule = createCoreQualificationModule();
const corePolicy = createCoreQualificationPolicy(coreModule);
const corePlan = planCoreLfMixedPhases(coreModule, corePolicy);
const coreLinkage = createCoreLfMixedDeclarationLinkage(
    corePlan,
    {
        revision: 'SCALE-STRESS-1B-CORE-PROPOSED-LINKAGE-1',
        moduleRevision: coreModule.revision,
        entries: coreLinkageEntries
    }
);

const natModule =
    CORE_LF_SCALE_STRESS_1_REPRESENTATION.nat.module;
const natPolicy = createNatQualificationPolicy(natModule);
const natPlan = planCoreLfMixedPhases(natModule, natPolicy);
const natLinkage = createCoreLfMixedDeclarationLinkage(
    natPlan,
    {
        revision: 'SCALE-STRESS-1B-NAT-PROPOSED-LINKAGE-1',
        moduleRevision: natModule.revision,
        entries: natLinkageEntries
    }
);

export interface CoreLfScaleStress1bProposal {
    readonly revision: 'SCALE-STRESS-1B-PROPOSAL-1';
    readonly gate: 'H-DTTLF-SCALE-STRESS-01';
    readonly decision: 'D-DTTLF-SCALE-STRESS-001';
    readonly status: 'proposal-awaiting-human-approval';
    readonly core: {
        readonly module: CoreLfModuleSpec;
        readonly policy: CoreLfTransferPolicyOverlay;
        readonly plan: CoreLfMixedPhasePlan;
        readonly linkage: CoreLfMixedDeclarationLinkage;
    };
    readonly nat: {
        readonly module: CoreLfModuleSpec;
        readonly policy: CoreLfTransferPolicyOverlay;
        readonly plan: CoreLfMixedPhasePlan;
        readonly linkage: CoreLfMixedDeclarationLinkage;
    };
    readonly proposedEnvelope: {
        readonly intrinsicOwners: readonly [
            'groupoid-universe',
            'decode'
        ];
        readonly opaqueSignatures: readonly string[];
        readonly runtimeRules: readonly string[];
        readonly proofRules: readonly [];
        readonly generatedOwnersWithheld: readonly [
            'ind_nat',
            'ind_τΣ_'
        ];
        readonly executionScope:
            'isolated-root-development-qualification-profile';
        readonly integrationPolicy:
            'later-batch-must-deduplicate-existing-signatures';
    };
    readonly requiredWitnesses: readonly string[];
    readonly productEffects: readonly [];
    readonly doesNotAuthorize: readonly string[];
    readonly decisionQuestion: string;
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

const rawProposal: CoreLfScaleStress1bProposal = {
    revision: 'SCALE-STRESS-1B-PROPOSAL-1',
    gate: 'H-DTTLF-SCALE-STRESS-01',
    decision: 'D-DTTLF-SCALE-STRESS-001',
    status: 'proposal-awaiting-human-approval',
    core: {
        module: coreModule,
        policy: corePolicy,
        plan: corePlan,
        linkage: coreLinkage
    },
    nat: {
        module: natModule,
        policy: natPolicy,
        plan: natPlan,
        linkage: natLinkage
    },
    proposedEnvelope: {
        intrinsicOwners: [
            'groupoid-universe',
            'decode'
        ],
        opaqueSignatures: [
            '=',
            'eq_refl',
            'ind_eqr',
            'nat',
            'zero',
            'succ',
            'Nat_grpd',
            'τΣ_',
            'Struct_sigma',
            'sigma_ind',
            'Pi_grpd',
            'nat_add'
        ],
        runtimeRules: [
            'stress.outer-j.reflexivity',
            'stress.nat-grpd.decode',
            'stress.sigma.eliminator-beta',
            'stress.pi-grpd.decode',
            'stress.nat-add.zero-left',
            'stress.nat-add.succ-left',
            'stress.nat-add.zero-right'
        ],
        proofRules: [],
        generatedOwnersWithheld: [
            'ind_nat',
            'ind_τΣ_'
        ],
        executionScope:
            'isolated-root-development-qualification-profile',
        integrationPolicy:
            'later-batch-must-deduplicate-existing-signatures'
    },
    requiredWitnesses: [
        'TypeScript declaration and runtime subject checking',
        'right-J positive and guarded negative reduction',
        'decoded dependent Pi binder-producing reduction',
        'decoded Sigma eliminator beta reduction',
        'grouped Nat recursion priority and overlap',
        'bounded Lambdapi positive/negative differential conformance',
        'frozen MVP and reviewed directed-continuation non-regression'
    ],
    productEffects: [],
    doesNotAuthorize: [
        'default-or-browser-profile-change',
        'frozen-mvp-or-directed-continuation-change',
        'generated-induction-or-eliminator-semantics',
        'recursive-indexed-or-strict-positivity-qualification',
        'kind-level-binder-policy-change',
        'merge-with-reviewed-29-signature-continuation',
        'new-groupoidal-closure-mathematics',
        'lambdapi-source-change',
        'mechanical-transfer-graduation',
        'release-publication-or-git-remote-mutation'
    ],
    decisionQuestion:
        'Approve H-DTTLF-SCALE-STRESS-01/' +
        'D-DTTLF-SCALE-STRESS-001 as proposed.'
};

export const CORE_LF_SCALE_STRESS_1B_PROPOSAL:
CoreLfScaleStress1bProposal = deepFreeze(rawProposal);

export type CoreLfScaleStress1bProposalErrorCode =
    | 'INVALID_PROPOSAL_BOUNDARY'
    | 'PROPOSAL_DRIFT';

export class CoreLfScaleStress1bProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfScaleStress1bProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleStress1bProposalError';
    }
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreLfScaleStress1bProposal(
    proposal: CoreLfScaleStress1bProposal =
        CORE_LF_SCALE_STRESS_1B_PROPOSAL
): void {
    validateCoreLfScaleEngineReview();
    validateCoreLfScaleStress1Representation();
    if (
        proposal.status !== 'proposal-awaiting-human-approval' ||
        proposal.productEffects.length !== 0 ||
        proposal.proposedEnvelope.proofRules.length !== 0
    ) {
        throw new CoreLfScaleStress1bProposalError(
            'INVALID_PROPOSAL_BOUNDARY',
            'SCALE-STRESS-1B proposal crossed its non-active boundary'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        throw new CoreLfScaleStress1bProposalError(
            'PROPOSAL_DRIFT',
            'SCALE-STRESS-1B proposal differs from its exact review input'
        );
    }
}

export interface CoreLfScaleStress1bProposalCompilation {
    readonly core: CoreLfCompiledMixedModule;
    readonly nat: CoreLfCompiledMixedModule;
}

/**
 * Compile the proposed profile as isolated review evidence. Calling this
 * function does not register it in any catalog or product entry point.
 */
export function compileCoreLfScaleStress1bProposal(
): CoreLfScaleStress1bProposalCompilation {
    validateCoreLfScaleStress1bProposal();
    const compiledCore = compileCoreLfMixedPhases(
        corePlan,
        coreLinkage
    );
    if (compiledCore.latestRuntime === undefined) {
        throw new CoreLfScaleStress1bProposalError(
            'INVALID_PROPOSAL_BOUNDARY',
            'Proposed core profile did not produce its runtime prefix'
        );
    }
    const compiledNat = compileCoreLfMixedPhases(
        natPlan,
        natLinkage,
        {
            initialDeclarations: compiledCore.declarations,
            dependencyInterfaces: [
                createCoreLfCompiledModuleInterface(
                    compiledCore.declarations.modules
                )
            ],
            runtimeDependencies: [{
                relation: 'dependency-module',
                fragment: compiledCore.latestRuntime
            }]
        }
    );
    return deepFreeze({
        core: compiledCore,
        nat: compiledNat
    });
}

validateCoreLfScaleStress1bProposal();
