/**
 * FIBRED-STRUCTURE-0A / H-DTTLF-USABILITY-02 proposal.
 *
 * This immutable record selects the smallest tested fixed-base structural
 * package for independent displayed siblings. It authorizes nothing by
 * itself.
 */

import {
    CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION
} from './categorical_context_dependencies';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL
} from './categorical_fibred_product_proposal';

export type CoreCategoricalFibredStructureAlternativeId =
    | 'fixed-base-displayed-universal-property'
    | 'universe-level-projection-prewhiskering'
    | 'semantic-composition-reindex-rule'
    | 'stable-pullback-reindex-rule'
    | 'stable-product-family-head';

export interface CoreCategoricalFibredStructureAlternative {
    readonly id: CoreCategoricalFibredStructureAlternativeId;
    readonly newMathematicalOwners: 0 | 1 | 2 | 3;
    readonly newRuntimeRules: 1 | 2 | 8 | 11;
    readonly projectionPointComputes: boolean;
    readonly projectionFullActionIterable: boolean;
    readonly pairingComputes: boolean;
    readonly swapAndDiagonalDerivable: boolean;
    readonly stableOuterPullbackComputes: boolean;
    readonly warningInventory: {
        readonly baselineCriticalPairs: 1010;
        readonly candidateCriticalPairs:
            1010 | 1012 | 1015 | 1016 | 1019;
        readonly criticalPairDelta: 0 | 2 | 5 | 6 | 9;
        readonly baselineReplaceablePatterns: 159;
        readonly candidateReplaceablePatterns: 159 | 165;
        readonly replaceablePatternDelta: 0 | 6;
    };
    readonly disposition:
        | 'recommend-smallest-complete-fixed-base-package'
        | 'defer-until-generic-prewhiskering-and-pairing-close'
        | 'reject-does-not-close-stable-pullback-presentation'
        | 'reject-broad-overlap-without-required-consumer'
        | 'reject-duplicates-transparent-family-semantics';
    readonly reason: string;
}

export type CoreCategoricalFibredStructureOwnerName =
    | 'Product_projL_funcd'
    | 'Product_projR_funcd'
    | 'Product_pair_funcd';

export interface CoreCategoricalFibredStructureOwnerProposal {
    readonly order: 0 | 1 | 2;
    readonly name: CoreCategoricalFibredStructureOwnerName;
    readonly kind: 'new-injective-mathematical-owner';
    readonly ownerPosition:
        '8b-displayed-functor-calculus-before-section-categories';
    readonly type: string;
    readonly meaning: string;
    readonly productFamilyHeadIntroduced: false;
}

export type CoreCategoricalFibredStructureRuntimeRuleId =
    | 'left-projection-point'
    | 'left-projection-full-action'
    | 'left-projection-capped-action'
    | 'right-projection-point'
    | 'right-projection-full-action'
    | 'right-projection-capped-action'
    | 'pairing-point'
    | 'pairing-full-action'
    | 'pairing-capped-action'
    | 'left-projection-pairing-beta'
    | 'right-projection-pairing-beta';

export interface CoreCategoricalFibredStructureRuntimeRuleProposal {
    readonly order:
        0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10;
    readonly id: CoreCategoricalFibredStructureRuntimeRuleId;
    readonly owner:
        | CoreCategoricalFibredStructureOwnerName
        | 'comp_fapp0';
    readonly projection:
        | 'tapp0_fapp0'
        | 'tapp1_func'
        | 'tapp1_fapp0'
        | 'whole-displayed-composition';
    readonly orientation: 'runtime-projection';
    readonly lhs: string;
    readonly rhs: string;
    readonly higherIterable: boolean;
}

export interface CoreCategoricalFibredStructureProposalInput {
    readonly revision: 'FIBRED-STRUCTURE-0A-PROPOSAL-1';
    readonly status:
        'proposal-awaiting-h-dttlf-usability-02';
    readonly reviewGate: 'H-DTTLF-USABILITY-02';
    readonly decisionId: 'D-DTTLF-USABILITY-006';
    readonly prerequisite: {
        readonly categoricalContextRevision:
            'FIBRED-CONTEXT-0B';
        readonly productDecision:
            'D-DTTLF-USABILITY-004-complete';
        readonly productFamily:
            'transparent-uncurry-product-over-Struct_sigma';
        readonly activeProductCatdOwnerAbsent: true;
        readonly completedOrdinaryD003ComprehensionAndProductBehaviorUnchanged:
            true;
    };
    readonly activeAuthorityInventory: {
        readonly ordinaryLeftProjection: 'Product_projL_func';
        readonly ordinaryRightProjection: 'Product_projR_func';
        readonly ordinaryPairing: 'Product_pair';
        readonly ordinaryProductMap: 'Product_map_func';
        readonly displayedIdentity: 'id_funcd';
        readonly displayedComposition: 'comp_catd_fapp0';
        readonly familyReindexing: 'Pullback_catd';
        readonly fullTransforAction: 'tapp1_func';
        readonly cappedTransforAction: 'tapp1_fapp0';
        readonly missingBoundary:
            'fixed-base-displayed-product-projections-and-pairing';
    };
    readonly semanticFamily: {
        readonly notation: 'P(B,C)';
        readonly explicitCore:
            'uncurry(Product_cat_func) ∘ Struct_sigma(B,C)';
        readonly newProductFamilyOwnerRequired: false;
        readonly newProductFamilyAliasRequired: false;
    };
    readonly alternatives: readonly [
        CoreCategoricalFibredStructureAlternative,
        CoreCategoricalFibredStructureAlternative,
        CoreCategoricalFibredStructureAlternative,
        CoreCategoricalFibredStructureAlternative,
        CoreCategoricalFibredStructureAlternative
    ];
    readonly recommendation: {
        readonly selected:
            'fixed-base-displayed-universal-property';
        readonly verdict:
            'approve-three-owners-and-eleven-runtime-projections';
        readonly newMathematicalOwnersRequired: 3;
        readonly newRuntimeRulesRequired: 11;
        readonly newProofTimeRulesRequired: 0;
        readonly activeProductCatdOwnerRequired: false;
        readonly activeSwapOwnerRequired: false;
        readonly activeDiagonalOwnerRequired: false;
        readonly kernelReindexingRuleRequired: false;
        readonly authorityAuthorized: false;
    };
    readonly proposedOwners: readonly [
        CoreCategoricalFibredStructureOwnerProposal,
        CoreCategoricalFibredStructureOwnerProposal,
        CoreCategoricalFibredStructureOwnerProposal
    ];
    readonly proposedRuntimeRules: readonly [
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal,
        CoreCategoricalFibredStructureRuntimeRuleProposal
    ];
    readonly derivedOperations: {
        readonly swap:
            'Product_pair_funcd(Product_projR_funcd,Product_projL_funcd)';
        readonly diagonal:
            'Product_pair_funcd(id_funcd,id_funcd)';
        readonly primitiveSwapOwnerRequired: false;
        readonly primitiveDiagonalOwnerRequired: false;
    };
    readonly reindexingPolicy: {
        readonly surfaceInput:
            'reindex(groupedProduct(B,C),F)';
        readonly emittedCanonicalCore:
            'P(Pullback_catd(B,F),Pullback_catd(C,F))';
        readonly nonCanonicalCore:
            'Pullback_catd(P(B,C),F)';
        readonly dependencyGraphSelectsCanonicalForm: true;
        readonly kernelRuntimeConversionClaimed: false;
        readonly kernelProofTimeEqualityClaimed: false;
        readonly kernelReindexingRuleAdded: false;
        readonly rationale: string;
    };
    readonly measuredEvidence: {
        readonly quietFixedBaseProbePassed: true;
        readonly warningEnabledFixedBaseProbePassed: true;
        readonly recommendedWarningInventory: {
            readonly criticalPairs: 1010;
            readonly replaceablePatterns: 159;
            readonly criticalPairDeltaFromActiveBaseline: 0;
            readonly replaceablePatternDeltaFromActiveBaseline: 0;
        };
        readonly positiveConversions: readonly [
            'left-projection-point',
            'pairing-point',
            'left-projection-base-arrow',
            'pairing-base-arrow',
            'swap-point',
            'diagonal-point',
            'left-projection-pairing-beta',
            'right-projection-pairing-beta'
        ];
        readonly higherEvidence: readonly [
            'projection-full-action-returns-an-iterable-functor',
            'projection-action-accepts-a-genuine-next-cell',
            'pairing-full-action-returns-an-iterable-product-functor',
            'pairing-next-cell-left-component-computes',
            'pairing-next-cell-right-component-computes'
        ];
        readonly negativeConversions: readonly [
            'opaque-family-does-not-collapse-to-product-family',
            'functord-category-does-not-globally-collapse-to-product',
            'raw-pullback-of-transparent-product-does-not-convert-to-canonical-reindexed-product'
        ];
        readonly genericSemanticReindexRuleDelta: {
            readonly criticalPairs: 6;
            readonly replaceablePatterns: 0;
        };
        readonly stablePullbackReindexRuleDelta: {
            readonly criticalPairs: 9;
            readonly replaceablePatterns: 0;
        };
        readonly universalProjectionAlternativeDelta: {
            readonly criticalPairs: 2;
            readonly replaceablePatterns: 6;
            readonly fixedBasePointConsumerComputes: false;
            readonly displayedPairingDerived: false;
        };
    };
    readonly implementationAfterApproval: readonly [
        'promote-exactly-the-three-fixed-base-owners-at-the-probed-owner-position',
        'promote-only-the-eleven-probed-runtime-projections-and-betas',
        'derive-swap-and-diagonal-as-transparent-typescript-core-composites',
        'canonicalize-grouped-product-reindexing-before-core-emission',
        'transfer-the-three-owner-eleven-rule-closure-through-the-generic-typescript-engines',
        'add-positive-negative-and-next-cell-lambdapi-conformance-consumers',
        'run-bounded-warning-lhs-catalog-health-examples-and-full-ci-gates',
        'preserve-all-frozen-and-browser-profiles'
    ];
    readonly nonEffects: readonly [
        'does-not-add-a-product-catd-owner-or-kernel-alias',
        'does-not-add-universe-level-product-projection-transfors',
        'does-not-add-a-primitive-swap-or-diagonal-owner',
        'does-not-add-a-generic-composition-reindexing-rule',
        'does-not-add-a-stable-pullback-product-reindexing-rule',
        'does-not-claim-kernel-conversion-between-the-two-reindexing-presentations',
        'does-not-add-a-global-functord-product-category-conversion',
        'does-not-add-a-generic-total-category-pullback',
        'does-not-complete-dependent-chain-exchange',
        'does-not-implement-direct-fd-or-nd-binders',
        'does-not-promote-a-browser-or-frozen-profile',
        'does-not-resume-parsing-acquisition-or-bulk-transfer'
    ];
    readonly decisionQuestion: string;
}

export type CoreCategoricalFibredStructureProposalErrorCode =
    | 'FIBRED_STRUCTURE_PREREQUISITE_DRIFT'
    | 'FIBRED_STRUCTURE_RECOMMENDATION_DRIFT'
    | 'FIBRED_STRUCTURE_EVIDENCE_DRIFT'
    | 'FIBRED_STRUCTURE_REINDEXING_DRIFT'
    | 'FIBRED_STRUCTURE_BOUNDARY_DRIFT';

export class CoreCategoricalFibredStructureProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalFibredStructureProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalFibredStructureProposalError';
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
CoreCategoricalFibredStructureProposalInput['alternatives'] = [
    {
        id: 'fixed-base-displayed-universal-property',
        newMathematicalOwners: 3,
        newRuntimeRules: 11,
        projectionPointComputes: true,
        projectionFullActionIterable: true,
        pairingComputes: true,
        swapAndDiagonalDerivable: true,
        stableOuterPullbackComputes: false,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1010,
            criticalPairDelta: 0,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159,
            replaceablePatternDelta: 0
        },
        disposition:
            'recommend-smallest-complete-fixed-base-package',
        reason:
            'Three fixed-base universal-property owners compute point, full, ' +
            'capped, beta, swap, diagonal, and next-cell consumers while ' +
            'retaining the transparent product family and the active warning ' +
            'inventory.'
    },
    {
        id: 'universe-level-projection-prewhiskering',
        newMathematicalOwners: 2,
        newRuntimeRules: 8,
        projectionPointComputes: false,
        projectionFullActionIterable: true,
        pairingComputes: false,
        swapAndDiagonalDerivable: false,
        stableOuterPullbackComputes: false,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1012,
            criticalPairDelta: 2,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 165,
            replaceablePatternDelta: 6
        },
        disposition:
            'defer-until-generic-prewhiskering-and-pairing-close',
        reason:
            'The universal projection transfors and whole projection folds ' +
            'typecheck, but generic prewhiskering leaves the first fixed-base ' +
            'point consumer stuck and supplies no displayed pairing.'
    },
    {
        id: 'semantic-composition-reindex-rule',
        newMathematicalOwners: 0,
        newRuntimeRules: 1,
        projectionPointComputes: false,
        projectionFullActionIterable: false,
        pairingComputes: false,
        swapAndDiagonalDerivable: false,
        stableOuterPullbackComputes: false,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1016,
            criticalPairDelta: 6,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159,
            replaceablePatternDelta: 0
        },
        disposition:
            'reject-does-not-close-stable-pullback-presentation',
        reason:
            'Distributing raw composition over a paired Cat diagram computes ' +
            'the semantic form, but the canonical Pullback_catd presentation ' +
            'remains distinct and the rule opens six unrelated cuts.'
    },
    {
        id: 'stable-pullback-reindex-rule',
        newMathematicalOwners: 0,
        newRuntimeRules: 1,
        projectionPointComputes: false,
        projectionFullActionIterable: false,
        pairingComputes: false,
        swapAndDiagonalDerivable: false,
        stableOuterPullbackComputes: true,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1019,
            criticalPairDelta: 9,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159,
            replaceablePatternDelta: 0
        },
        disposition:
            'reject-broad-overlap-without-required-consumer',
        reason:
            'A generic Pullback_catd rule can distribute an explicitly paired ' +
            'diagram, but it is broader than the grouped-sibling consumer, ' +
            'adds nine diagnosed cuts, and does not make a nested transparent ' +
            'product alias a reliable rewrite discriminator.'
    },
    {
        id: 'stable-product-family-head',
        newMathematicalOwners: 1,
        newRuntimeRules: 2,
        projectionPointComputes: false,
        projectionFullActionIterable: false,
        pairingComputes: false,
        swapAndDiagonalDerivable: false,
        stableOuterPullbackComputes: false,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1015,
            criticalPairDelta: 5,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159,
            replaceablePatternDelta: 0
        },
        disposition:
            'reject-duplicates-transparent-family-semantics',
        reason:
            'The previously probed Product_catd head duplicates the selected ' +
            'transparent family and adds five overlaps before supplying any ' +
            'of this slice’s projection or pairing structure.'
    }
];

const proposedOwners:
CoreCategoricalFibredStructureProposalInput['proposedOwners'] = [
    {
        order: 0,
        name: 'Product_projL_funcd',
        kind: 'new-injective-mathematical-owner',
        ownerPosition:
            '8b-displayed-functor-calculus-before-section-categories',
        type: '[K:Cat](B C:Catd K) -> Functord(P(B,C),B)',
        meaning:
            'the ordinary left product projection in every fibre, natural in the shared base',
        productFamilyHeadIntroduced: false
    },
    {
        order: 1,
        name: 'Product_projR_funcd',
        kind: 'new-injective-mathematical-owner',
        ownerPosition:
            '8b-displayed-functor-calculus-before-section-categories',
        type: '[K:Cat](B C:Catd K) -> Functord(P(B,C),C)',
        meaning:
            'the ordinary right product projection in every fibre, natural in the shared base',
        productFamilyHeadIntroduced: false
    },
    {
        order: 2,
        name: 'Product_pair_funcd',
        kind: 'new-injective-mathematical-owner',
        ownerPosition:
            '8b-displayed-functor-calculus-before-section-categories',
        type:
            '[K:Cat][E B C:Catd K](FF:Functord(E,B))(GG:Functord(E,C)) -> Functord(E,P(B,C))',
        meaning:
            'pointwise pairing of two displayed functors with one literal shared source family',
        productFamilyHeadIntroduced: false
    }
];

const proposedRuntimeRules:
CoreCategoricalFibredStructureProposalInput['proposedRuntimeRules'] = [
    {
        order: 0,
        id: 'left-projection-point',
        owner: 'Product_projL_funcd',
        projection: 'tapp0_fapp0',
        orientation: 'runtime-projection',
        lhs: 'Product_projL_funcd(B,C)[k]',
        rhs: 'Product_projL_func(B[k],C[k])',
        higherIterable: false
    },
    {
        order: 1,
        id: 'left-projection-full-action',
        owner: 'Product_projL_funcd',
        projection: 'tapp1_func',
        orientation: 'runtime-projection',
        lhs: 'tapp1_func(Product_projL_funcd(B,C),x,y)',
        rhs:
            'comp_cat_con_func(Product_projL_func(B[x],C[x])) ∘ fapp1_func(B,x,y)',
        higherIterable: true
    },
    {
        order: 2,
        id: 'left-projection-capped-action',
        owner: 'Product_projL_funcd',
        projection: 'tapp1_fapp0',
        orientation: 'runtime-projection',
        lhs: 'Product_projL_funcd(B,C)[p]',
        rhs:
            'hom_precomp_along_fapp0(Product_projL_func(B[x],C[x]),B[p])',
        higherIterable: true
    },
    {
        order: 3,
        id: 'right-projection-point',
        owner: 'Product_projR_funcd',
        projection: 'tapp0_fapp0',
        orientation: 'runtime-projection',
        lhs: 'Product_projR_funcd(B,C)[k]',
        rhs: 'Product_projR_func(B[k],C[k])',
        higherIterable: false
    },
    {
        order: 4,
        id: 'right-projection-full-action',
        owner: 'Product_projR_funcd',
        projection: 'tapp1_func',
        orientation: 'runtime-projection',
        lhs: 'tapp1_func(Product_projR_funcd(B,C),x,y)',
        rhs:
            'comp_cat_con_func(Product_projR_func(B[x],C[x])) ∘ fapp1_func(C,x,y)',
        higherIterable: true
    },
    {
        order: 5,
        id: 'right-projection-capped-action',
        owner: 'Product_projR_funcd',
        projection: 'tapp1_fapp0',
        orientation: 'runtime-projection',
        lhs: 'Product_projR_funcd(B,C)[p]',
        rhs:
            'hom_precomp_along_fapp0(Product_projR_func(B[x],C[x]),C[p])',
        higherIterable: true
    },
    {
        order: 6,
        id: 'pairing-point',
        owner: 'Product_pair_funcd',
        projection: 'tapp0_fapp0',
        orientation: 'runtime-projection',
        lhs: 'Product_pair_funcd(FF,GG)[k]',
        rhs: 'Struct_sigma(FF[k],GG[k])',
        higherIterable: false
    },
    {
        order: 7,
        id: 'pairing-full-action',
        owner: 'Product_pair_funcd',
        projection: 'tapp1_func',
        orientation: 'runtime-projection',
        lhs: 'tapp1_func(Product_pair_funcd(FF,GG),x,y)',
        rhs: 'Struct_sigma(tapp1_func(FF,x,y),tapp1_func(GG,x,y))',
        higherIterable: true
    },
    {
        order: 8,
        id: 'pairing-capped-action',
        owner: 'Product_pair_funcd',
        projection: 'tapp1_fapp0',
        orientation: 'runtime-projection',
        lhs: 'Product_pair_funcd(FF,GG)[p]',
        rhs: 'Struct_sigma(FF[p],GG[p])',
        higherIterable: true
    },
    {
        order: 9,
        id: 'left-projection-pairing-beta',
        owner: 'comp_fapp0',
        projection: 'whole-displayed-composition',
        orientation: 'runtime-projection',
        lhs: 'Product_projL_funcd(B,C) ∘ Product_pair_funcd(FF,GG)',
        rhs: 'FF',
        higherIterable: true
    },
    {
        order: 10,
        id: 'right-projection-pairing-beta',
        owner: 'comp_fapp0',
        projection: 'whole-displayed-composition',
        orientation: 'runtime-projection',
        lhs: 'Product_projR_funcd(B,C) ∘ Product_pair_funcd(FF,GG)',
        rhs: 'GG',
        higherIterable: true
    }
];

const rawProposal:
CoreCategoricalFibredStructureProposalInput = {
    revision: 'FIBRED-STRUCTURE-0A-PROPOSAL-1',
    status: 'proposal-awaiting-h-dttlf-usability-02',
    reviewGate: 'H-DTTLF-USABILITY-02',
    decisionId: 'D-DTTLF-USABILITY-006',
    prerequisite: {
        categoricalContextRevision: 'FIBRED-CONTEXT-0B',
        productDecision: 'D-DTTLF-USABILITY-004-complete',
        productFamily:
            'transparent-uncurry-product-over-Struct_sigma',
        activeProductCatdOwnerAbsent: true,
        completedOrdinaryD003ComprehensionAndProductBehaviorUnchanged:
            true
    },
    activeAuthorityInventory: {
        ordinaryLeftProjection: 'Product_projL_func',
        ordinaryRightProjection: 'Product_projR_func',
        ordinaryPairing: 'Product_pair',
        ordinaryProductMap: 'Product_map_func',
        displayedIdentity: 'id_funcd',
        displayedComposition: 'comp_catd_fapp0',
        familyReindexing: 'Pullback_catd',
        fullTransforAction: 'tapp1_func',
        cappedTransforAction: 'tapp1_fapp0',
        missingBoundary:
            'fixed-base-displayed-product-projections-and-pairing'
    },
    semanticFamily: {
        notation: 'P(B,C)',
        explicitCore:
            'uncurry(Product_cat_func) ∘ Struct_sigma(B,C)',
        newProductFamilyOwnerRequired: false,
        newProductFamilyAliasRequired: false
    },
    alternatives,
    recommendation: {
        selected: 'fixed-base-displayed-universal-property',
        verdict:
            'approve-three-owners-and-eleven-runtime-projections',
        newMathematicalOwnersRequired: 3,
        newRuntimeRulesRequired: 11,
        newProofTimeRulesRequired: 0,
        activeProductCatdOwnerRequired: false,
        activeSwapOwnerRequired: false,
        activeDiagonalOwnerRequired: false,
        kernelReindexingRuleRequired: false,
        authorityAuthorized: false
    },
    proposedOwners,
    proposedRuntimeRules,
    derivedOperations: {
        swap:
            'Product_pair_funcd(Product_projR_funcd,Product_projL_funcd)',
        diagonal:
            'Product_pair_funcd(id_funcd,id_funcd)',
        primitiveSwapOwnerRequired: false,
        primitiveDiagonalOwnerRequired: false
    },
    reindexingPolicy: {
        surfaceInput: 'reindex(groupedProduct(B,C),F)',
        emittedCanonicalCore:
            'P(Pullback_catd(B,F),Pullback_catd(C,F))',
        nonCanonicalCore: 'Pullback_catd(P(B,C),F)',
        dependencyGraphSelectsCanonicalForm: true,
        kernelRuntimeConversionClaimed: false,
        kernelProofTimeEqualityClaimed: false,
        kernelReindexingRuleAdded: false,
        rationale:
            'grouped-sibling structure is explicit before Core emission, ' +
            'so both elaboration routes can select one backend-neutral term ' +
            'without requiring a brittle transparent-family rewrite ' +
            'discriminator'
    },
    measuredEvidence: {
        quietFixedBaseProbePassed: true,
        warningEnabledFixedBaseProbePassed: true,
        recommendedWarningInventory: {
            criticalPairs: 1010,
            replaceablePatterns: 159,
            criticalPairDeltaFromActiveBaseline: 0,
            replaceablePatternDeltaFromActiveBaseline: 0
        },
        positiveConversions: [
            'left-projection-point',
            'pairing-point',
            'left-projection-base-arrow',
            'pairing-base-arrow',
            'swap-point',
            'diagonal-point',
            'left-projection-pairing-beta',
            'right-projection-pairing-beta'
        ],
        higherEvidence: [
            'projection-full-action-returns-an-iterable-functor',
            'projection-action-accepts-a-genuine-next-cell',
            'pairing-full-action-returns-an-iterable-product-functor',
            'pairing-next-cell-left-component-computes',
            'pairing-next-cell-right-component-computes'
        ],
        negativeConversions: [
            'opaque-family-does-not-collapse-to-product-family',
            'functord-category-does-not-globally-collapse-to-product',
            'raw-pullback-of-transparent-product-does-not-convert-to-canonical-reindexed-product'
        ],
        genericSemanticReindexRuleDelta: {
            criticalPairs: 6,
            replaceablePatterns: 0
        },
        stablePullbackReindexRuleDelta: {
            criticalPairs: 9,
            replaceablePatterns: 0
        },
        universalProjectionAlternativeDelta: {
            criticalPairs: 2,
            replaceablePatterns: 6,
            fixedBasePointConsumerComputes: false,
            displayedPairingDerived: false
        }
    },
    implementationAfterApproval: [
        'promote-exactly-the-three-fixed-base-owners-at-the-probed-owner-position',
        'promote-only-the-eleven-probed-runtime-projections-and-betas',
        'derive-swap-and-diagonal-as-transparent-typescript-core-composites',
        'canonicalize-grouped-product-reindexing-before-core-emission',
        'transfer-the-three-owner-eleven-rule-closure-through-the-generic-typescript-engines',
        'add-positive-negative-and-next-cell-lambdapi-conformance-consumers',
        'run-bounded-warning-lhs-catalog-health-examples-and-full-ci-gates',
        'preserve-all-frozen-and-browser-profiles'
    ],
    nonEffects: [
        'does-not-add-a-product-catd-owner-or-kernel-alias',
        'does-not-add-universe-level-product-projection-transfors',
        'does-not-add-a-primitive-swap-or-diagonal-owner',
        'does-not-add-a-generic-composition-reindexing-rule',
        'does-not-add-a-stable-pullback-product-reindexing-rule',
        'does-not-claim-kernel-conversion-between-the-two-reindexing-presentations',
        'does-not-add-a-global-functord-product-category-conversion',
        'does-not-add-a-generic-total-category-pullback',
        'does-not-complete-dependent-chain-exchange',
        'does-not-implement-direct-fd-or-nd-binders',
        'does-not-promote-a-browser-or-frozen-profile',
        'does-not-resume-parsing-acquisition-or-bulk-transfer'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-006 as ' +
        'proposed: retain P(B,C) as the transparent uncurry/product ' +
        'composite; add exactly Product_projL_funcd, ' +
        'Product_projR_funcd, and Product_pair_funcd with the eleven ' +
        'probed point/full/capped/beta rules; derive swap and diagonal ' +
        'transparently; canonicalize grouped-product reindexing in the ' +
        'dependency-aware TypeScript frontend to ' +
        'P(Pullback_catd(B,F),Pullback_catd(C,F)); and retain a ' +
        'Product_catd head, universe-level projection transfors, kernel ' +
        'reindexing rules or equality claims, global Functord product ' +
        'conversion, direct fd/nd binders, and profile promotion as ' +
        'separate unapproved work?'
};

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreCategoricalFibredStructureProposal(
    proposal: CoreCategoricalFibredStructureProposalInput =
        CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL
): void {
    if (
        CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION !==
            'FIBRED-CONTEXT-0B' ||
        proposal.prerequisite.categoricalContextRevision !==
            CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION ||
        CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL
            .recommendation.selected !==
            'narrow-shared-base-existing-owner' ||
        CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL
            .recommendation.activeProductCatdDeclarationRequired
    ) {
        throw new CoreCategoricalFibredStructureProposalError(
            'FIBRED_STRUCTURE_PREREQUISITE_DRIFT',
            'The completed context or transparent product prerequisite drifted'
        );
    }
    if (
        proposal.recommendation.selected !==
            'fixed-base-displayed-universal-property' ||
        proposal.recommendation.newMathematicalOwnersRequired !== 3 ||
        proposal.recommendation.newRuntimeRulesRequired !== 11 ||
        proposal.recommendation.newProofTimeRulesRequired !== 0 ||
        proposal.recommendation.activeProductCatdOwnerRequired ||
        proposal.recommendation.activeSwapOwnerRequired ||
        proposal.recommendation.activeDiagonalOwnerRequired ||
        proposal.recommendation.kernelReindexingRuleRequired ||
        proposal.recommendation.authorityAuthorized
    ) {
        throw new CoreCategoricalFibredStructureProposalError(
            'FIBRED_STRUCTURE_RECOMMENDATION_DRIFT',
            'The fixed-base structural recommendation drifted'
        );
    }
    const selected = proposal.alternatives.find(
        alternative =>
            alternative.id === proposal.recommendation.selected
    );
    if (
        !selected ||
        selected.warningInventory.criticalPairDelta !== 0 ||
        selected.warningInventory.replaceablePatternDelta !== 0 ||
        proposal.measuredEvidence.recommendedWarningInventory
            .criticalPairs !== 1010 ||
        proposal.measuredEvidence.recommendedWarningInventory
            .replaceablePatterns !== 159 ||
        proposal.proposedOwners.length !== 3 ||
        proposal.proposedRuntimeRules.length !== 11
    ) {
        throw new CoreCategoricalFibredStructureProposalError(
            'FIBRED_STRUCTURE_EVIDENCE_DRIFT',
            'The owner-position evidence or exact closure drifted'
        );
    }
    if (
        proposal.reindexingPolicy.emittedCanonicalCore !==
            'P(Pullback_catd(B,F),Pullback_catd(C,F))' ||
        proposal.reindexingPolicy.kernelRuntimeConversionClaimed ||
        proposal.reindexingPolicy.kernelProofTimeEqualityClaimed ||
        proposal.reindexingPolicy.kernelReindexingRuleAdded
    ) {
        throw new CoreCategoricalFibredStructureProposalError(
            'FIBRED_STRUCTURE_REINDEXING_DRIFT',
            'The frontend-only reindexing boundary drifted'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        throw new CoreCategoricalFibredStructureProposalError(
            'FIBRED_STRUCTURE_BOUNDARY_DRIFT',
            'FIBRED-STRUCTURE-0A proposal drifted'
        );
    }
}

validateCoreCategoricalFibredStructureProposal();
