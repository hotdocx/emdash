/**
 * FIBRED-COMPREHENSION-0B / H-DTTLF-USABILITY-02 proposal.
 *
 * This immutable record compares the first computational contextual-pair
 * owner positions. It recommends one asymmetric family-pullback totalization
 * owner with two runtime projections and authorizes nothing by itself.
 */

import {
    CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION
} from './categorical_context_dependencies';

export type CoreCategoricalComprehensionAlternativeId =
    | 'semantic-sigma-intro-composite'
    | 'direct-contextual-pair-owner'
    | 'asymmetric-pullback-total-owner';

export interface CoreCategoricalComprehensionAlternative {
    readonly id: CoreCategoricalComprehensionAlternativeId;
    readonly newDeclarations: 0 | 1;
    readonly newRuntimeRules: 0 | 2 | 3;
    readonly contextualPairTypeChecks: true;
    readonly contextualPairObjectComputes: boolean;
    readonly contextualPairArrowComputes: boolean;
    readonly dependentSubstitutionComputes: boolean;
    readonly wholeFirstProjectionComputes: boolean;
    readonly warningInventory: {
        readonly baselineCriticalPairs: 1010;
        readonly candidateCriticalPairs: 1010 | 1012;
        readonly criticalPairDelta: 0 | 2;
        readonly baselineReplaceablePatterns: 159;
        readonly candidateReplaceablePatterns: 159;
    };
    readonly disposition:
        | 'reject-computationally-stuck'
        | 'reject-specialized-owner-and-identity-overlaps'
        | 'recommend-general-base-change-owner';
    readonly reason: string;
}

export type CoreCategoricalComprehensionRuntimeRuleId =
    | 'pullback-total-object-action'
    | 'pullback-total-structured-arrow-action';

export interface CoreCategoricalComprehensionRuntimeRuleProposal {
    readonly order: 0 | 1;
    readonly id: CoreCategoricalComprehensionRuntimeRuleId;
    readonly proposedOwner: 'sigma_pullback_total_func';
    readonly ownerPosition:
        | '9b-sigma-total-maps'
        | '17-pullback-capped-transport-cut';
    readonly orientation: 'runtime-projection';
    readonly lhs: string;
    readonly rhs: string;
    readonly structuredSigmaInputRequired: true;
}

export interface CoreCategoricalComprehensionProposalInput {
    readonly revision:
        'FIBRED-COMPREHENSION-0B-PROPOSAL-1';
    readonly status:
        'proposal-awaiting-h-dttlf-usability-02';
    readonly reviewGate: 'H-DTTLF-USABILITY-02';
    readonly decisionId: 'D-DTTLF-USABILITY-005';
    readonly prerequisite: {
        readonly categoricalContextRevision:
            'FIBRED-CONTEXT-0B';
        readonly generalDependentChainsRepresented: true;
        readonly productDecisionIndependent:
            'D-DTTLF-USABILITY-004-remains-separate';
        readonly completedOrdinaryAndD003BehaviorUnchanged: true;
    };
    readonly activeAuthorityInventory: {
        readonly familyPullback: 'Pullback_catd';
        readonly familyPullbackFunctor: 'Pullback_catd_func';
        readonly sameBaseTotalMap: 'sigma_map_func';
        readonly totalCategory: 'Sigma_cat';
        readonly firstProjection: 'Sigma_proj1_func';
        readonly sectionPullback: 'section_pullback_func';
        readonly fibreInclusion: 'sigma_intro_transf';
        readonly missingBoundary:
            'base-changing-total-map-of-an-asymmetric-family-pullback';
    };
    readonly proposedOwner: {
        readonly name: 'sigma_pullback_total_func';
        readonly kind: 'new-injective-mathematical-owner';
        readonly type:
            '[A K : Cat](F : Functor A K)(D : Catd K) -> Functor(Sigma_cat(Pullback_catd(D,F)),Sigma_cat(D))';
        readonly objectMeaning: '(a,u) -> (F[a],u)';
        readonly arrowMeaning: '(p,alpha) -> (F[p],alpha)';
        readonly arbitraryTotalFunctorPullback: false;
        readonly genericTotalCategoryPullback: false;
    };
    readonly alternatives: readonly [
        CoreCategoricalComprehensionAlternative,
        CoreCategoricalComprehensionAlternative,
        CoreCategoricalComprehensionAlternative
    ];
    readonly recommendation: {
        readonly selected:
            'asymmetric-pullback-total-owner';
        readonly verdict:
            'approve-one-owner-and-two-runtime-projections';
        readonly newMathematicalOwnersRequired: 1;
        readonly newRuntimeRulesRequired: 2;
        readonly newProofTimeRulesRequired: 0;
        readonly directContextualPairOwnerRequired: false;
        readonly directSigmaIntroArrowRuleRequired: false;
        readonly wholeFirstProjectionBetaRequired: false;
        readonly authorityAuthorized: false;
    };
    readonly proposedRuntimeRules: readonly [
        CoreCategoricalComprehensionRuntimeRuleProposal,
        CoreCategoricalComprehensionRuntimeRuleProposal
    ];
    readonly transparentContextualPair: {
        readonly input:
            'F : Functor A K; E : Catd K; s : Obj(Pi_cat(Pullback_catd(E,F)))';
        readonly result: 'Functor A (Sigma_cat E)';
        readonly factorization: readonly [
            'A -> Sigma_cat(Const_catd(A,Terminal_cat))',
            'sigma_map_func(s) -> Sigma_cat(Pullback_catd(E,F))',
            'sigma_pullback_total_func(F,E) -> Sigma_cat(E)'
        ];
        readonly terminalTotalMap:
            'Struct_sigma(id_func(A),Const_func(A,Terminal_cat,Terminal_obj))';
        readonly dedicatedPairOwnerIntroduced: false;
    };
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
            readonly criticalPairDeltaFromActiveBaseline: 0;
            readonly replaceableDeltaFromActiveBaseline: 0;
        };
        readonly positiveConversions: readonly [
            'pullback-total-object-action',
            'pullback-total-structured-arrow-action',
            'contextual-pair-object-action',
            'contextual-pair-arrow-action',
            'further-family-object-substitution',
            'further-family-base-arrow-substitution',
            'pointwise-first-projection'
        ];
        readonly negativeConversions: readonly [
            'whole-contextual-pair-first-projection-does-not-runtime-convert',
            'opaque-total-functor-does-not-collapse-to-pullback-total-owner',
            'no-arbitrary-total-category-pullback-is-introduced'
        ];
        readonly subjectReductionPlacement:
            'arrow-rule-after-active-pullback-capped-transport';
    };
    readonly directSigmaIntroductionAudit: {
        readonly candidate:
            'sigma_intro_tapp0_func(E,k)[alpha] -> (id_k,alpha)';
        readonly neededForRecommendedContextualPair: false;
        readonly candidateCriticalPairs: 1020;
        readonly criticalPairDelta: 10;
        readonly candidateReplaceablePatterns: 160;
        readonly replaceablePatternDelta: 1;
        readonly overlapFamilies: readonly [
            'generic-identity-action',
            'off-diagonal-naturality',
            'precomposition',
            'postcomposition',
            'composition-and-higher-action'
        ];
        readonly disposition:
            'defer-as-separate-owner-closure-not-bundled-with-contextual-pair';
    };
    readonly interactionPolicy: {
        readonly sameBaseSigmaMap:
            'reuse-sigma-map-func-for-the-middle-factor';
        readonly familyPullback:
            'reuse-active-asymmetric-pullback-not-arbitrary-total-pullback';
        readonly firstProjection:
            'pointwise-computation-only-whole-functor-beta-deferred';
        readonly displayedProduct:
            'independent-d-004-gate-composes-later-without-being-assumed';
        readonly higherAction:
            'ordinary-generic-functor-action-remains-the-owner';
    };
    readonly implementationAfterApproval: readonly [
        'promote-sigma-pullback-total-func-at-the-probed-owner-position',
        'promote-only-its-object-and-structured-arrow-runtime-projections',
        'run-full-lambdapi-warning-audit-catalog-health-examples-and-ci',
        'transfer-the-one-owner-two-rule-closure-through-generic-typescript-engines',
        'lower-contextual-pairing-as-the-transparent-three-factor-explicit-core-composite',
        'exercise-one-genuine-dependent-chain-with-object-and-arrow-substitution',
        'preserve-all-frozen-and-browser-profiles'
    ];
    readonly nonEffects: readonly [
        'does-not-add-a-dedicated-sigma-pair-owner',
        'does-not-add-the-direct-sigma-introduction-arrow-rule',
        'does-not-add-a-whole-first-projection-runtime-beta',
        'does-not-add-a-generic-total-category-pullback',
        'does-not-approve-or-implement-d-dttlf-usability-004',
        'does-not-complete-displayed-product-structural-maps',
        'does-not-promote-a-browser-or-frozen-profile',
        'does-not-resume-parsing-acquisition-or-bulk-transfer',
        'does-not-claim-general-displayed-usability-graduation'
    ];
    readonly decisionQuestion: string;
}

export type CoreCategoricalComprehensionProposalErrorCode =
    | 'FIBRED_COMPREHENSION_PREREQUISITE_DRIFT'
    | 'FIBRED_COMPREHENSION_RECOMMENDATION_DRIFT'
    | 'FIBRED_COMPREHENSION_EVIDENCE_DRIFT'
    | 'FIBRED_COMPREHENSION_BOUNDARY_DRIFT';

export class CoreCategoricalComprehensionProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalComprehensionProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalComprehensionProposalError';
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
CoreCategoricalComprehensionProposalInput['alternatives'] = [
    {
        id: 'semantic-sigma-intro-composite',
        newDeclarations: 0,
        newRuntimeRules: 0,
        contextualPairTypeChecks: true,
        contextualPairObjectComputes: false,
        contextualPairArrowComputes: false,
        dependentSubstitutionComputes: false,
        wholeFirstProjectionComputes: false,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1010,
            criticalPairDelta: 0,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159
        },
        disposition: 'reject-computationally-stuck',
        reason:
            'Pulling back sigma_intro_transf and composing with the section ' +
            'has the right semantic type, but ordinary object, arrow, and ' +
            'projection consumers remain stuck.'
    },
    {
        id: 'direct-contextual-pair-owner',
        newDeclarations: 1,
        newRuntimeRules: 3,
        contextualPairTypeChecks: true,
        contextualPairObjectComputes: true,
        contextualPairArrowComputes: true,
        dependentSubstitutionComputes: true,
        wholeFirstProjectionComputes: true,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1012,
            criticalPairDelta: 2,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159
        },
        disposition:
            'reject-specialized-owner-and-identity-overlaps',
        reason:
            'The dedicated pair computes, including a whole projection beta, ' +
            'but duplicates a reusable base-change construction and its ' +
            'arbitrary-arrow rule opens two generic identity-action cuts.'
    },
    {
        id: 'asymmetric-pullback-total-owner',
        newDeclarations: 1,
        newRuntimeRules: 2,
        contextualPairTypeChecks: true,
        contextualPairObjectComputes: true,
        contextualPairArrowComputes: true,
        dependentSubstitutionComputes: true,
        wholeFirstProjectionComputes: false,
        warningInventory: {
            baselineCriticalPairs: 1010,
            candidateCriticalPairs: 1010,
            criticalPairDelta: 0,
            baselineReplaceablePatterns: 159,
            candidateReplaceablePatterns: 159
        },
        disposition: 'recommend-general-base-change-owner',
        reason:
            'The total map of active asymmetric family pullback is more ' +
            'general than contextual pairing, restricts arrow computation ' +
            'to structured Sigma arrows, and adds no warning delta.'
    }
];

const proposedRuntimeRules:
CoreCategoricalComprehensionProposalInput['proposedRuntimeRules'] = [
    {
        order: 0,
        id: 'pullback-total-object-action',
        proposedOwner: 'sigma_pullback_total_func',
        ownerPosition: '9b-sigma-total-maps',
        orientation: 'runtime-projection',
        lhs: 'sigma_pullback_total_func(F,D)[(a,u)]',
        rhs: '(F[a],u)',
        structuredSigmaInputRequired: true
    },
    {
        order: 1,
        id: 'pullback-total-structured-arrow-action',
        proposedOwner: 'sigma_pullback_total_func',
        ownerPosition: '17-pullback-capped-transport-cut',
        orientation: 'runtime-projection',
        lhs: 'sigma_pullback_total_func(F,D)[(p,alpha)]',
        rhs: '(F[p],alpha)',
        structuredSigmaInputRequired: true
    }
];

const rawProposal:
CoreCategoricalComprehensionProposalInput = {
    revision: 'FIBRED-COMPREHENSION-0B-PROPOSAL-1',
    status: 'proposal-awaiting-h-dttlf-usability-02',
    reviewGate: 'H-DTTLF-USABILITY-02',
    decisionId: 'D-DTTLF-USABILITY-005',
    prerequisite: {
        categoricalContextRevision: 'FIBRED-CONTEXT-0B',
        generalDependentChainsRepresented: true,
        productDecisionIndependent:
            'D-DTTLF-USABILITY-004-remains-separate',
        completedOrdinaryAndD003BehaviorUnchanged: true
    },
    activeAuthorityInventory: {
        familyPullback: 'Pullback_catd',
        familyPullbackFunctor: 'Pullback_catd_func',
        sameBaseTotalMap: 'sigma_map_func',
        totalCategory: 'Sigma_cat',
        firstProjection: 'Sigma_proj1_func',
        sectionPullback: 'section_pullback_func',
        fibreInclusion: 'sigma_intro_transf',
        missingBoundary:
            'base-changing-total-map-of-an-asymmetric-family-pullback'
    },
    proposedOwner: {
        name: 'sigma_pullback_total_func',
        kind: 'new-injective-mathematical-owner',
        type:
            '[A K : Cat](F : Functor A K)(D : Catd K) -> Functor(Sigma_cat(Pullback_catd(D,F)),Sigma_cat(D))',
        objectMeaning: '(a,u) -> (F[a],u)',
        arrowMeaning: '(p,alpha) -> (F[p],alpha)',
        arbitraryTotalFunctorPullback: false,
        genericTotalCategoryPullback: false
    },
    alternatives,
    recommendation: {
        selected: 'asymmetric-pullback-total-owner',
        verdict:
            'approve-one-owner-and-two-runtime-projections',
        newMathematicalOwnersRequired: 1,
        newRuntimeRulesRequired: 2,
        newProofTimeRulesRequired: 0,
        directContextualPairOwnerRequired: false,
        directSigmaIntroArrowRuleRequired: false,
        wholeFirstProjectionBetaRequired: false,
        authorityAuthorized: false
    },
    proposedRuntimeRules,
    transparentContextualPair: {
        input:
            'F : Functor A K; E : Catd K; s : Obj(Pi_cat(Pullback_catd(E,F)))',
        result: 'Functor A (Sigma_cat E)',
        factorization: [
            'A -> Sigma_cat(Const_catd(A,Terminal_cat))',
            'sigma_map_func(s) -> Sigma_cat(Pullback_catd(E,F))',
            'sigma_pullback_total_func(F,E) -> Sigma_cat(E)'
        ],
        terminalTotalMap:
            'Struct_sigma(id_func(A),Const_func(A,Terminal_cat,Terminal_obj))',
        dedicatedPairOwnerIntroduced: false
    },
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
            criticalPairDeltaFromActiveBaseline: 0,
            replaceableDeltaFromActiveBaseline: 0
        },
        positiveConversions: [
            'pullback-total-object-action',
            'pullback-total-structured-arrow-action',
            'contextual-pair-object-action',
            'contextual-pair-arrow-action',
            'further-family-object-substitution',
            'further-family-base-arrow-substitution',
            'pointwise-first-projection'
        ],
        negativeConversions: [
            'whole-contextual-pair-first-projection-does-not-runtime-convert',
            'opaque-total-functor-does-not-collapse-to-pullback-total-owner',
            'no-arbitrary-total-category-pullback-is-introduced'
        ],
        subjectReductionPlacement:
            'arrow-rule-after-active-pullback-capped-transport'
    },
    directSigmaIntroductionAudit: {
        candidate:
            'sigma_intro_tapp0_func(E,k)[alpha] -> (id_k,alpha)',
        neededForRecommendedContextualPair: false,
        candidateCriticalPairs: 1020,
        criticalPairDelta: 10,
        candidateReplaceablePatterns: 160,
        replaceablePatternDelta: 1,
        overlapFamilies: [
            'generic-identity-action',
            'off-diagonal-naturality',
            'precomposition',
            'postcomposition',
            'composition-and-higher-action'
        ],
        disposition:
            'defer-as-separate-owner-closure-not-bundled-with-contextual-pair'
    },
    interactionPolicy: {
        sameBaseSigmaMap:
            'reuse-sigma-map-func-for-the-middle-factor',
        familyPullback:
            'reuse-active-asymmetric-pullback-not-arbitrary-total-pullback',
        firstProjection:
            'pointwise-computation-only-whole-functor-beta-deferred',
        displayedProduct:
            'independent-d-004-gate-composes-later-without-being-assumed',
        higherAction:
            'ordinary-generic-functor-action-remains-the-owner'
    },
    implementationAfterApproval: [
        'promote-sigma-pullback-total-func-at-the-probed-owner-position',
        'promote-only-its-object-and-structured-arrow-runtime-projections',
        'run-full-lambdapi-warning-audit-catalog-health-examples-and-ci',
        'transfer-the-one-owner-two-rule-closure-through-generic-typescript-engines',
        'lower-contextual-pairing-as-the-transparent-three-factor-explicit-core-composite',
        'exercise-one-genuine-dependent-chain-with-object-and-arrow-substitution',
        'preserve-all-frozen-and-browser-profiles'
    ],
    nonEffects: [
        'does-not-add-a-dedicated-sigma-pair-owner',
        'does-not-add-the-direct-sigma-introduction-arrow-rule',
        'does-not-add-a-whole-first-projection-runtime-beta',
        'does-not-add-a-generic-total-category-pullback',
        'does-not-approve-or-implement-d-dttlf-usability-004',
        'does-not-complete-displayed-product-structural-maps',
        'does-not-promote-a-browser-or-frozen-profile',
        'does-not-resume-parsing-acquisition-or-bulk-transfer',
        'does-not-claim-general-displayed-usability-graduation'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-005 as ' +
        'proposed: add sigma_pullback_total_func as the asymmetric family-' +
        'pullback total map with only object (a,u) -> (F[a],u) and ' +
        'structured-arrow (p,alpha) -> (F[p],alpha) runtime projections; ' +
        'derive contextual pairing as the transparent terminal-total, ' +
        'sigma_map_func, and pullback-total composite; transfer only that ' +
        'one-owner/two-rule closure and one genuine dependent-chain ' +
        'consumer to TypeScript; and retain a dedicated pair owner, the ' +
        'direct sigma-introduction arrow rule, whole first-projection beta, ' +
        'generic total pullback, D-004 product work, and profile promotion ' +
        'as separate unapproved work?'
};

export const CORE_CATEGORICAL_COMPREHENSION_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreCategoricalComprehensionProposal(
    proposal: CoreCategoricalComprehensionProposalInput =
        CORE_CATEGORICAL_COMPREHENSION_PROPOSAL
): void {
    if (
        CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION !==
            'FIBRED-CONTEXT-0B' ||
        proposal.prerequisite.categoricalContextRevision !==
            CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION
    ) {
        throw new CoreCategoricalComprehensionProposalError(
            'FIBRED_COMPREHENSION_PREREQUISITE_DRIFT',
            'The completed categorical dependency adapter drifted'
        );
    }
    if (
        proposal.recommendation.selected !==
            'asymmetric-pullback-total-owner' ||
        proposal.recommendation.newMathematicalOwnersRequired !== 1 ||
        proposal.recommendation.newRuntimeRulesRequired !== 2 ||
        proposal.recommendation.newProofTimeRulesRequired !== 0 ||
        proposal.recommendation.directContextualPairOwnerRequired ||
        proposal.recommendation.directSigmaIntroArrowRuleRequired ||
        proposal.recommendation.wholeFirstProjectionBetaRequired ||
        proposal.recommendation.authorityAuthorized
    ) {
        throw new CoreCategoricalComprehensionProposalError(
            'FIBRED_COMPREHENSION_RECOMMENDATION_DRIFT',
            'The bounded asymmetric-totalization recommendation drifted'
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
            .unreviewedCompoundSlots !== 0 ||
        proposal.directSigmaIntroductionAudit
            .criticalPairDelta !== 10
    ) {
        throw new CoreCategoricalComprehensionProposalError(
            'FIBRED_COMPREHENSION_EVIDENCE_DRIFT',
            'The comprehension owner-position evidence drifted'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        throw new CoreCategoricalComprehensionProposalError(
            'FIBRED_COMPREHENSION_BOUNDARY_DRIFT',
            'FIBRED-COMPREHENSION-0B proposal drifted'
        );
    }
}

validateCoreCategoricalComprehensionProposal();
