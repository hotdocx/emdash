/**
 * FIBRED-PRODUCT-0B / H-DTTLF-USABILITY-02 proposal.
 *
 * This immutable record compares three owner positions for the first
 * fibrewise-product transport consumer. It recommends two existing-owner
 * runtime projections and authorizes nothing by itself.
 */

import {
    CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION
} from './categorical_context_dependencies';

export type CoreCategoricalFibredProductAlternativeId =
    | 'broad-generic-product-off-diagonal'
    | 'stable-product-catd-head'
    | 'narrow-shared-base-existing-owner';

export interface CoreCategoricalFibredProductAlternative {
    readonly id: CoreCategoricalFibredProductAlternativeId;
    readonly familyPresentation:
        | 'transparent-existing-owner-composite'
        | 'new-injective-product-catd-head';
    readonly newDeclarations: 0 | 1;
    readonly newRuntimeRules: 2;
    readonly pointwiseFibreComputes: true;
    readonly baseArrowTransportComputes: true;
    readonly warningInventory: {
        readonly baselineCriticalPairs: 1010;
        readonly candidateCriticalPairs: 1010 | 1013 | 1015;
        readonly criticalPairDelta: 0 | 3 | 5;
        readonly baselineReplaceablePatterns: 159;
        readonly candidateReplaceablePatterns: 159;
    };
    readonly disposition:
        | 'defer-broad-rule-until-higher-naturality-closure'
        | 'reject-first-slice-duplicates-semantics-and-adds-overlaps'
        | 'recommend-bounded-shared-base-slice';
    readonly reason: string;
}

export type CoreCategoricalFibredProductRuntimeRuleId =
    | 'cat-valued-postcomposition-capped-action'
    | 'shared-base-product-action-projection';

export interface CoreCategoricalFibredProductRuntimeRuleProposal {
    readonly order: 0 | 1;
    readonly id: CoreCategoricalFibredProductRuntimeRuleId;
    readonly activeOwner:
        | 'hom_postcomp_fapp0'
        | 'Product_cat_fapp1_fapp0_functord';
    readonly ownerPosition:
        | '4a-covariant-represented-hom-postcomposition'
        | '7a-internalized-product-formation-and-product-maps';
    readonly orientation: 'runtime-projection-to-stable-action';
    readonly lhs: string;
    readonly rhs: string;
    readonly sameBaseArrowRequired: boolean;
    readonly introducesOwner: false;
}

export interface CoreCategoricalFibredProductProposalInput {
    readonly revision: 'FIBRED-PRODUCT-0B-PROPOSAL-1';
    readonly status:
        'proposal-awaiting-h-dttlf-usability-02';
    readonly reviewGate:
        'H-DTTLF-USABILITY-02';
    readonly decisionId: 'D-DTTLF-USABILITY-004';
    readonly prerequisite: {
        readonly categoricalContextRevision:
            'FIBRED-CONTEXT-0B';
        readonly transparentProbeResult:
            'fibre-computes-transport-stuck';
        readonly completedOrdinaryAndD003BehaviorUnchanged: true;
    };
    readonly firstConsumer: {
        readonly context:
            'Γ,a:A,b:B(a),c:C(a)';
        readonly semanticFamily:
            'uncurry(Product_cat_func) ∘ Struct_sigma(B,C)';
        readonly pointwiseFibre:
            'Product_cat(Fibre_cat(B,k),Fibre_cat(C,k))';
        readonly baseArrowTransport:
            'Product_map_func(catd_transport_func(B,p),catd_transport_func(C,p))';
        readonly genericTotalCategoryPullbackAssumed: false;
    };
    readonly alternatives:
        readonly [
            CoreCategoricalFibredProductAlternative,
            CoreCategoricalFibredProductAlternative,
            CoreCategoricalFibredProductAlternative
        ];
    readonly recommendation: {
        readonly selected:
            'narrow-shared-base-existing-owner';
        readonly verdict:
            'approve-two-existing-owner-runtime-projections';
        readonly activeProductCatdDeclarationRequired: false;
        readonly transparentSurfaceAliasRequired: false;
        readonly newMathematicalOwnerRequired: false;
        readonly newRuntimeRulesRequired: 2;
        readonly newProofTimeRulesRequired: 0;
        readonly authorityAuthorized: false;
    };
    readonly proposedRuntimeRules:
        readonly [
            CoreCategoricalFibredProductRuntimeRuleProposal,
            CoreCategoricalFibredProductRuntimeRuleProposal
        ];
    readonly measuredEvidence: {
        readonly quietOwnerPositionProbePassed: true;
        readonly warningEnabledOwnerPositionProbePassed: true;
        readonly strictLhsAudit: {
            readonly unreviewedCompoundSlots: 0;
            readonly annotatedSlots: 45;
            readonly intentionalClauses: 27;
        };
        readonly recommendedWarningInventory: {
            readonly criticalPairs: 1010;
            readonly replaceablePatterns: 159;
            readonly deltaFromActiveBaseline: 0;
        };
        readonly positiveConversions:
            readonly [
                'pointwise-fibre',
                'componentwise-base-arrow-transport'
            ];
        readonly negativeConversions:
            readonly [
                'opaque-family-does-not-collapse',
                'functord-category-does-not-runtime-collapse-to-product',
                'pullback-stability-does-not-runtime-convert'
            ];
        readonly failedProofTimeAttempt:
            'existing-unification-does-not-prove-pullback-stability';
    };
    readonly higherActionBoundary: {
        readonly returnedTransport:
            'stable-Product_map_func-with-existing-full-and-capped-hom-action';
        readonly arbitraryProductOffDiagonalAction:
            'deferred-broad-rule-has-three-unjoined-naturality-overlaps';
        readonly baseTwoCellAction:
            'not-yet-qualified';
        readonly displayedProjectionPairingSwapDiagonal:
            'next-consumer-row-not-yet-implemented';
    };
    readonly comparisonPolicy: {
        readonly familyLevelFunctordProduct:
            'derive-from-projection-and-pairing-functors-not-global-runtime-collapse';
        readonly pullbackStability:
            'separate-later-owner-or-proof-time-audit';
        readonly totalCategoryComparison:
            'deferred-theorem-without-generic-pullback-assumption';
    };
    readonly implementationAfterApproval: readonly [
        'promote-the-two-probed-rules-at-active-owner-positions',
        'run-full-lambdapi-warning-audit-catalog-health-examples-and-ci',
        'transfer-only-the-two-rule-closure-through-generic-typescript-runtime',
        'lower-the-first-grouped-sibling-transport-to-transparent-explicit-core',
        'preserve-all-frozen-and-browser-profiles'
    ];
    readonly nonEffects: readonly [
        'does-not-add-a-product-catd-primitive',
        'does-not-add-a-notation-only-kernel-alias',
        'does-not-install-the-broad-off-diagonal-rule',
        'does-not-claim-full-base-two-cell-action',
        'does-not-add-functord-product-category-conversion',
        'does-not-add-pullback-stability',
        'does-not-add-a-total-category-pullback',
        'does-not-complete-projection-pairing-swap-or-diagonal',
        'does-not-promote-a-browser-or-frozen-profile',
        'does-not-resume-parsing-acquisition-or-bulk-transfer'
    ];
    readonly decisionQuestion: string;
}

export type CoreCategoricalFibredProductProposalErrorCode =
    | 'FIBRED_PRODUCT_PREREQUISITE_DRIFT'
    | 'FIBRED_PRODUCT_RECOMMENDATION_DRIFT'
    | 'FIBRED_PRODUCT_EVIDENCE_DRIFT'
    | 'FIBRED_PRODUCT_BOUNDARY_DRIFT';

export class CoreCategoricalFibredProductProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalFibredProductProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalFibredProductProposalError';
    }
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

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const alternatives:
CoreCategoricalFibredProductProposalInput['alternatives'] = [
    {
        id: 'broad-generic-product-off-diagonal',
        familyPresentation:
            'transparent-existing-owner-composite',
        newDeclarations: 0,
        newRuntimeRules: 2,
        pointwiseFibreComputes: true,
        baseArrowTransportComputes: true,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1013,
            criticalPairDelta: 3,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159
        },
        disposition:
            'defer-broad-rule-until-higher-naturality-closure',
        reason:
            'The unrestricted (F * 1)[G] to Product_map_func(F,G) fold ' +
            'solves the consumer but opens three currently unjoined ' +
            'naturality cuts, including the still-deferred higher action.'
    },
    {
        id: 'stable-product-catd-head',
        familyPresentation:
            'new-injective-product-catd-head',
        newDeclarations: 1,
        newRuntimeRules: 2,
        pointwiseFibreComputes: true,
        baseArrowTransportComputes: true,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1015,
            criticalPairDelta: 5,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159
        },
        disposition:
            'reject-first-slice-duplicates-semantics-and-adds-overlaps',
        reason:
            'A stable family head duplicates a semantic composite, adds ' +
            'two fibre-projection and three transport overlaps, and still ' +
            'does not supply reindexing or the full base two-cell action.'
    },
    {
        id: 'narrow-shared-base-existing-owner',
        familyPresentation:
            'transparent-existing-owner-composite',
        newDeclarations: 0,
        newRuntimeRules: 2,
        pointwiseFibreComputes: true,
        baseArrowTransportComputes: true,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1010,
            criticalPairDelta: 0,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159
        },
        disposition:
            'recommend-bounded-shared-base-slice',
        reason:
            'The semantic family stays transparent while the existing ' +
            'postcomposition and product owners compute exactly when both ' +
            'factors are family actions over the same base arrow.'
    }
];

const proposedRuntimeRules:
CoreCategoricalFibredProductProposalInput['proposedRuntimeRules'] = [
    {
        order: 0,
        id: 'cat-valued-postcomposition-capped-action',
        activeOwner: 'hom_postcomp_fapp0',
        ownerPosition:
            '4a-covariant-represented-hom-postcomposition',
        orientation: 'runtime-projection-to-stable-action',
        lhs:
            'fapp1_fapp0(hom_postcomp_fapp0(E,p,G),q)',
        rhs:
            'fapp1_fapp0(catd_transport_func(E,p),' +
            'fapp1_fapp0(G,q))',
        sameBaseArrowRequired: false,
        introducesOwner: false
    },
    {
        order: 1,
        id: 'shared-base-product-action-projection',
        activeOwner:
            'Product_cat_fapp1_fapp0_functord',
        ownerPosition:
            '7a-internalized-product-formation-and-product-maps',
        orientation: 'runtime-projection-to-stable-action',
        lhs:
            'tapp1_fapp0(' +
            'Product_cat_fapp1_fapp0_functord(B[p]),C[p])',
        rhs: 'Product_map_func(B[p],C[p])',
        sameBaseArrowRequired: true,
        introducesOwner: false
    }
];

const rawProposal:
CoreCategoricalFibredProductProposalInput = {
    revision: 'FIBRED-PRODUCT-0B-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-02',
    reviewGate: 'H-DTTLF-USABILITY-02',
    decisionId: 'D-DTTLF-USABILITY-004',
    prerequisite: {
        categoricalContextRevision: 'FIBRED-CONTEXT-0B',
        transparentProbeResult:
            'fibre-computes-transport-stuck',
        completedOrdinaryAndD003BehaviorUnchanged: true
    },
    firstConsumer: {
        context: 'Γ,a:A,b:B(a),c:C(a)',
        semanticFamily:
            'uncurry(Product_cat_func) ∘ Struct_sigma(B,C)',
        pointwiseFibre:
            'Product_cat(Fibre_cat(B,k),Fibre_cat(C,k))',
        baseArrowTransport:
            'Product_map_func(catd_transport_func(B,p),catd_transport_func(C,p))',
        genericTotalCategoryPullbackAssumed: false
    },
    alternatives,
    recommendation: {
        selected: 'narrow-shared-base-existing-owner',
        verdict:
            'approve-two-existing-owner-runtime-projections',
        activeProductCatdDeclarationRequired: false,
        transparentSurfaceAliasRequired: false,
        newMathematicalOwnerRequired: false,
        newRuntimeRulesRequired: 2,
        newProofTimeRulesRequired: 0,
        authorityAuthorized: false
    },
    proposedRuntimeRules,
    measuredEvidence: {
        quietOwnerPositionProbePassed: true,
        warningEnabledOwnerPositionProbePassed: true,
        strictLhsAudit: {
            unreviewedCompoundSlots: 0,
            annotatedSlots: 45,
            intentionalClauses: 27
        },
        recommendedWarningInventory: {
            criticalPairs: 1010,
            replaceablePatterns: 159,
            deltaFromActiveBaseline: 0
        },
        positiveConversions: [
            'pointwise-fibre',
            'componentwise-base-arrow-transport'
        ],
        negativeConversions: [
            'opaque-family-does-not-collapse',
            'functord-category-does-not-runtime-collapse-to-product',
            'pullback-stability-does-not-runtime-convert'
        ],
        failedProofTimeAttempt:
            'existing-unification-does-not-prove-pullback-stability'
    },
    higherActionBoundary: {
        returnedTransport:
            'stable-Product_map_func-with-existing-full-and-capped-hom-action',
        arbitraryProductOffDiagonalAction:
            'deferred-broad-rule-has-three-unjoined-naturality-overlaps',
        baseTwoCellAction: 'not-yet-qualified',
        displayedProjectionPairingSwapDiagonal:
            'next-consumer-row-not-yet-implemented'
    },
    comparisonPolicy: {
        familyLevelFunctordProduct:
            'derive-from-projection-and-pairing-functors-not-global-runtime-collapse',
        pullbackStability:
            'separate-later-owner-or-proof-time-audit',
        totalCategoryComparison:
            'deferred-theorem-without-generic-pullback-assumption'
    },
    implementationAfterApproval: [
        'promote-the-two-probed-rules-at-active-owner-positions',
        'run-full-lambdapi-warning-audit-catalog-health-examples-and-ci',
        'transfer-only-the-two-rule-closure-through-generic-typescript-runtime',
        'lower-the-first-grouped-sibling-transport-to-transparent-explicit-core',
        'preserve-all-frozen-and-browser-profiles'
    ],
    nonEffects: [
        'does-not-add-a-product-catd-primitive',
        'does-not-add-a-notation-only-kernel-alias',
        'does-not-install-the-broad-off-diagonal-rule',
        'does-not-claim-full-base-two-cell-action',
        'does-not-add-functord-product-category-conversion',
        'does-not-add-pullback-stability',
        'does-not-add-a-total-category-pullback',
        'does-not-complete-projection-pairing-swap-or-diagonal',
        'does-not-promote-a-browser-or-frozen-profile',
        'does-not-resume-parsing-acquisition-or-bulk-transfer'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-004 as ' +
        'proposed: keep the fibrewise product as the transparent existing-' +
        'owner composite; add only the probed Cat-valued postcomposition ' +
        'capped-action rule and the shared-base product projection ' +
        '(B[p] * 1)[C[p]] -> Product_map_func(B[p],C[p]); transfer only ' +
        'that two-rule closure and first grouped-sibling transport to ' +
        'TypeScript; and retain the broad off-diagonal action, a primitive ' +
        'Product_catd head, base two-cell action, Functord product ' +
        'comparison, pullback stability, structural maps, total pullback, ' +
        'and profile promotion as separate unapproved work?'
};

export const CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreCategoricalFibredProductProposal(
    proposal: CoreCategoricalFibredProductProposalInput =
        CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL
): void {
    if (
        CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION !==
            'FIBRED-CONTEXT-0B' ||
        proposal.prerequisite.categoricalContextRevision !==
            CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION
    ) {
        throw new CoreCategoricalFibredProductProposalError(
            'FIBRED_PRODUCT_PREREQUISITE_DRIFT',
            'The completed categorical dependency adapter drifted'
        );
    }
    if (
        proposal.recommendation.selected !==
            'narrow-shared-base-existing-owner' ||
        proposal.recommendation.activeProductCatdDeclarationRequired ||
        proposal.recommendation.transparentSurfaceAliasRequired ||
        proposal.recommendation.newMathematicalOwnerRequired ||
        proposal.recommendation.newRuntimeRulesRequired !== 2 ||
        proposal.recommendation.newProofTimeRulesRequired !== 0 ||
        proposal.recommendation.authorityAuthorized
    ) {
        throw new CoreCategoricalFibredProductProposalError(
            'FIBRED_PRODUCT_RECOMMENDATION_DRIFT',
            'The bounded existing-owner recommendation drifted'
        );
    }
    const selected = proposal.alternatives.find(
        alternative =>
            alternative.id === proposal.recommendation.selected
    );
    if (
        !selected ||
        selected.warningInventory.criticalPairDelta !== 0 ||
        proposal.measuredEvidence.recommendedWarningInventory
            .criticalPairs !== 1010 ||
        proposal.measuredEvidence.recommendedWarningInventory
            .replaceablePatterns !== 159 ||
        proposal.measuredEvidence.strictLhsAudit
            .unreviewedCompoundSlots !== 0
    ) {
        throw new CoreCategoricalFibredProductProposalError(
            'FIBRED_PRODUCT_EVIDENCE_DRIFT',
            'The owner-position evidence or warning baseline drifted'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        throw new CoreCategoricalFibredProductProposalError(
            'FIBRED_PRODUCT_BOUNDARY_DRIFT',
            'FIBRED-PRODUCT-0B proposal drifted'
        );
    }
}

validateCoreCategoricalFibredProductProposal();
