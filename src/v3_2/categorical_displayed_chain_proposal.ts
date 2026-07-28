/**
 * Executable DISPLAYED-CHAIN-0A proposal.
 *
 * This artifact compares the three presentations of one genuine dependent
 * telescope edge and freezes the smallest owner-position closure found by
 * full-kernel probes. It authorizes no semantic change by itself.
 */

import {
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY
} from './categorical_comprehension_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION
} from './categorical_displayed_evaluation_transfer';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
} from './categorical_fibred_transfd_transfer';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
} from './categorical_fibred_weaken_reindex_transfer';

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

const rawProposal = {
    revision: 'DISPLAYED-CHAIN-0A-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-chain-01',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-01',
    decisionId: 'D-DTTLF-USABILITY-012',
    prerequisite: {
        displayedEvaluationTransferRevision:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION,
        displayedEvaluationSourceSha256:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
        displayedEvaluationImplementationCheckpoint:
            '1a7ce3f023391aa22c34dc5626057710429bc7c3',
        displayedEvaluationLedgerCheckpoint:
            '0ae40ba0f0a904d0005eebe0385e9d1e9a56aac7',
        displayedEvaluationOwnerCount:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount,
        displayedEvaluationRuntimeRuleCount:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newMathematicalRuntimeRuleCount,
        comprehensionStatus:
            CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY.status,
        weakeningStatus:
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
                .status,
        displayedActionStatus:
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY.status,
        measuredRootGate: {
            tests: 904,
            passed: 857,
            skipped: 47,
            failed: 0
        },
        implementationAuthorizedBeforeDecision: false
    },
    clarifiedArchitecture: {
        sourceBoundary: 'existing-typed-typescript-construction-ir',
        targetBoundary: 'backend-neutral-explicit-emdash-core',
        genericCheckerReused: true,
        recursiveCompilerReused: true,
        rawExprLayerAdded: false,
        bidirectionalCheckerAdded: false,
        parserAdded: false,
        bracketPunctuationAdded: false,
        wholeBodyRecognizerAdded: false,
        intrinsicCoreOwnerAdded: false,
        contextRepresentation: 'sequential-sigma-totalization',
        substitutionRepresentation:
            'recursive-pullback-sigma-map-and-pullback-totalization',
        termRepresentation:
            'direct-displayed-functor-with-explicit-sigma-section-bridge',
        relationship:
            'complementary-presentations-not-a-total-category-equivalence'
    },
    representativeTelescope: {
        declaration:
            'k : K; a : A[k]; b : B[(k,a)]',
        authorityTypes: [
            'A : Catd K',
            'B : Catd(Sigma_cat A)'
        ],
        sequentialContext:
            'Sigma_cat B with objects ((k,a),b)',
        oneEdgeSubstitution:
            'F_A = sigma_pullback_total_func(F,A) o sigma_map_func(eta)',
        secondEdgeSubstitution:
            'F_B = sigma_pullback_total_func(F_A,B) o sigma_map_func(theta)',
        outerOccurrence:
            'a weakened through b by section_pullback along Sigma_proj1(B)',
        directClassifier:
            'Functord_cat(B,Sigma_proj1_pullback_catd(B,' +
            'Sigma_proj1_pullback_catd(A,A)))'
    },
    alternatives: [
        {
            id: 'sequential-totalization-only',
            contextObjectsCompute: true,
            contextArrowsCompute: true,
            recursiveSubstitutionComputes: false,
            directVariableOccurrenceComputes: false,
            disposition: 'retain-as-context-layout-not-complete-lowering',
            reason:
                'Sigma totals are the canonical telescope categories, but ' +
                'ordinary total-context brackets alone erase the direct ' +
                'displayed classifier needed by recursive fapp/tapp lowering'
        },
        {
            id: 'repeated-pullback-sigma-only',
            contextObjectsCompute: true,
            contextArrowsCompute: true,
            recursiveSubstitutionComputes: true,
            directVariableOccurrenceComputes: false,
            disposition:
                'retain-as-substitution-recursion-not-complete-lowering',
            reason:
                'sigma_map_func followed by sigma_pullback_total_func ' +
                'extends substitutions mechanically, but does not alone ' +
                'give the direct term represented by an outer variable'
        },
        {
            id: 'proof-time-direct-reinterpretation',
            contextObjectsCompute: true,
            contextArrowsCompute: false,
            recursiveSubstitutionComputes: true,
            directVariableOccurrenceComputes: false,
            disposition: 'reject-subject-reduction-failure',
            reason:
                'The Pi/Sigma proof-time comparison types the two ' +
                'presentations, but a global rule reinterpreting an ' +
                'arbitrary section term as a displayed functor fails ' +
                'owner-position subject reduction'
        },
        {
            id: 'hybrid-sequential-recursive-direct',
            contextObjectsCompute: true,
            contextArrowsCompute: true,
            recursiveSubstitutionComputes: true,
            directVariableOccurrenceComputes: true,
            disposition: 'recommend',
            reason:
                'Use Sigma totals for context shape, repeated pullback/' +
                'totalization for substitutions, and a stable explicit ' +
                'Sigma-section bridge for recursively weakened direct terms'
        }
    ],
    activeAuthorityInventory: {
        contextAndSubstitution: [
            'Sigma_cat',
            'sigma_arrow',
            'Pullback_catd',
            'sigma_map_func',
            'sigma_pullback_total_func'
        ],
        directTermsAndSections: [
            'Functord_cat',
            'Pi_cat',
            'Sigma_proj1_func',
            'Sigma_proj1_pullback_catd',
            'section_pullback_func',
            'section_pullback_sec'
        ],
        genericAction: [
            'tapp0_fapp0',
            'fapp1_fapp0',
            'fdapp1_int_cell',
            'fdapp1_int_hom_fapp0'
        ],
        siblingStructureStillSeparate: [
            'Product_projL_funcd',
            'Product_projR_funcd',
            'Product_pair_funcd'
        ],
        exactGaps: [
            'stable-explicit-displayed-functor-to-sigma-section-term',
            'sigma-first-projection-structured-arrow',
            'sigma-projection-pullback-structured-arrow',
            'sigma-section-object-and-arrow-components',
            'projection-section-pullback-direct-object-and-arrow-components'
        ],
        absentGenericOwnerConfirmed: true
    },
    selectedClosure: {
        newOwner: {
            name: 'sigma_functord_sec',
            kind: 'new-injective-term-owner',
            type:
                '[K : Cat][R D : Catd K](FF : Functord R D) -> ' +
                'Obj(Pi_cat(Sigma_cat R,' +
                'Sigma_proj1_pullback_catd(R,D)))',
            objectMeaning: 'sigma_functord_sec(FF)[(k,r)] = FF[k](r)',
            arrowMeaning:
                'sigma_functord_sec(FF)[(p,alpha)] = ' +
                'fdapp1_int_hom_fapp0(FF,p,r,alpha)',
            necessityEvidence:
                'generic-unwrapped-rule-fails-subject-reduction',
            genericTotalEquivalenceClaimed: false
        },
        runtimeRules: [
            {
                order: 0,
                id: 'sigma-first-projection-structured-arrow',
                ownerPosition: '9a-sigma-first-projection',
                lhs:
                    'fapp1_fapp0(Sigma_proj1_func(R),' +
                    '((x,r),(y,s)),(p,alpha))',
                rhs: 'p'
            },
            {
                order: 1,
                id: 'sigma-projection-pullback-structured-arrow',
                ownerPosition: '9a-projection-pullback-family',
                lhs:
                    'fapp1_fapp0(Sigma_proj1_pullback_catd(R,D),' +
                    '((x,r),(y,s)),(p,alpha))',
                rhs: 'fapp1_fapp0(D,x,y,p)'
            },
            {
                order: 2,
                id: 'sigma-functord-section-object-component',
                ownerPosition: '9a-sigma-section-uncurrying',
                lhs: 'sigma_functord_sec(FF)[(k,r)]',
                rhs: 'Obj_func(FF[k](r))'
            },
            {
                order: 3,
                id: 'sigma-functord-section-arrow-component',
                ownerPosition: '16c-section-action',
                lhs:
                    'fdapp1_int_cell(sigma_functord_sec(FF),' +
                    '(p,alpha),Terminal_obj)',
                rhs: 'fdapp1_int_hom_fapp0(FF,p,r,alpha)'
            },
            {
                order: 4,
                id: 'section-pullback-direct-object-component',
                ownerPosition: '17e-section-pullback',
                lhs:
                    'tapp0_fapp0(section_pullback_sec(' +
                    'Sigma_proj1_func(R),E,s),z)',
                rhs: 'Const_func(R[z],E[z],piapp0(s,z))'
            },
            {
                order: 5,
                id: 'section-pullback-direct-arrow-component',
                ownerPosition: '17e-section-pullback',
                lhs:
                    'fdapp1_int_cell(section_pullback_sec(' +
                    'Sigma_proj1_func(R),E,s),q,r)',
                rhs:
                    'fdapp1_int_cell(Const(Terminal),E,s,q,Terminal_obj)'
            }
        ],
        newMathematicalOwnerCount: 1,
        newMathematicalRuntimeRuleCount: 6,
        newMathematicalProofRuleCount: 0,
        genericFappTappRuleCount: 0,
        directContextualPairOwnerCount: 0
    },
    transferClosure: {
        existingDeclarationPrerequisites: [
            'sigma_map_func',
            'fdapp1_int_cell',
            'fdapp1_int_hom_fapp0'
        ],
        existingRuntimeRulePrerequisites: [
            'sigma_map_func-object-action',
            'sigma_map_func-structured-arrow-action'
        ],
        alreadyTransferredDependencies: [
            'sigma_arrow',
            'sigma_pullback_total_func',
            'Sigma_proj1_func',
            'Sigma_proj1_pullback_catd',
            'section_pullback_func',
            'section_pullback_sec',
            'functord_transport_lhs_func',
            'functord_transport_rhs_func',
            'Fibre_func'
        ],
        allDeclarationsUseGenericTransferCompiler: true,
        allRuntimeRulesUseGenericRuntimeCompiler: true,
        intrinsicCoreCaseRequired: false,
        stringAcquisitionRequired: false,
        genericLambdapiParserRequired: false
    },
    warningEvidence: {
        baseline: {
            total: 1171,
            unjoinableCriticalPairs: 1012,
            replaceablePatternVariables: 159
        },
        candidate: {
            total: 1179,
            unjoinableCriticalPairs: 1020,
            replaceablePatternVariables: 159
        },
        delta: {
            total: 8,
            unjoinableCriticalPairs: 8,
            replaceablePatternVariables: 0
        },
        overlapClassification: [
            'sigma-constant-family-totalization-versus-projection-action',
            'sigma-constant-family-totalization-versus-pullback-action',
            'sigma-constant-family-totalization-versus-wrapper-components',
            'generic-component-composition-versus-direct-section-component'
        ],
        warningIsSelectionVeto: false,
        quietOwnerPositionProbePassed: true,
        warningOwnerPositionProbePassed: true,
        strictLhsAudit: {
            unreviewedCompoundSlots: 0,
            annotatedSlots: 52,
            intentionalClauses: 32
        }
    },
    recursiveEvidence: {
        directTotalizationObjectPassed: true,
        directTotalizationStructuredArrowPassed: true,
        secondDependencyEdgeObjectPassed: true,
        immediateVariableObjectPassed: true,
        weakenedOuterVariableObjectPassed: true,
        immediateVariableArrowPassed: true,
        weakenedOuterVariableArrowPassed: true,
        reindexingPassed: true,
        arbitraryTotalFunctorNonCollapsePassed: true,
        genericSectionNonCollapsePassed: true,
        depthClaim:
            'two-substitution-edges-and-one-recursively-weakened-variable-edge'
    },
    typescriptConsumer: {
        proposedProfile: 'fibred-displayed-chain-1',
        proposedMethod: 'displayedDependentContextLambda',
        example:
            'displayedDependentContextLambda(' +
            '[a : A, b : B], D, ([a,b]) => body)',
        bindingInterpretation: [
            'A : Catd K',
            'B : Catd(Sigma_cat A)',
            'body : D[((k,a),b)]'
        ],
        callbackEvaluationCount: 1,
        recursiveNodeCompilation: true,
        tokenOccurrenceMayAppearUnderSupportedSubexpressions: true,
        explicitInternalBracketRequired: false,
        stringParserRequired: false,
        newAstLayerRequired: false,
        newCheckerRequired: false,
        unsupportedNodePolicy: 'fail-closed-with-source-provenance',
        pipeline: [
            'typed-typescript-construction-ir',
            'recursive-contextual-occurrence-compiler',
            'sequential-sigma-and-direct-displayed-lowering',
            'backend-neutral-explicit-core',
            'generic-checker-and-evaluator'
        ]
    },
    positiveCorpus: [
        'immediate-dependent-variable-object',
        'outer-variable-object-under-one-dependent-binder',
        'immediate-dependent-variable-arrow',
        'outer-variable-arrow-under-one-dependent-binder',
        'closed-displayed-functor-applied-to-recursive-variable',
        'recursive-sigma-map-and-pullback-total-substitution',
        'second-dependent-edge-object-substitution',
        'reindexing-before-dependent-extension'
    ],
    negativeCorpus: [
        'wrong-next-family-base',
        'escaped-dependent-slot',
        'foreign-program-dependent-slot',
        'arbitrary-total-functor-does-not-collapse',
        'generic-section-does-not-collapse-without-explicit-wrapper',
        'independent-sibling-exchange-not-applied-across-dependent-edge',
        'no-total-category-equality-or-equivalence-inferred',
        'unsupported-higher-cell-fails-closed'
    ],
    feasibilityAssessment: {
        architectureForOneGenuineEdgeSettledByProposal: true,
        recursiveExtensionInvariantIdentified: true,
        mechanicalAdditionalObjectLevelEdgesExpected: true,
        mechanicalAdditionalArrowLevelEdgesExpected: true,
        proofOfArbitraryTelescopeDepthClaimed: false,
        fullGeneralNdCoherenceClaimed: false,
        arbitraryMixedVarianceClaimed: false,
        groupoidalClosureClaimed: false,
        remainingWork:
            'implement-and-qualify-the-frozen-owner-rule-and-typescript-' +
            'closure-before-claiming-general-dependent-usability'
    },
    implementationAfterApproval: [
        'promote-one-owner-and-six-rules-at-the-probed-kernel-positions',
        'add-focused-permanent-object-arrow-and-noncollapse-checks',
        'run-warning-audit-catalog-health-examples-and-ci',
        'transfer-three-existing-prerequisite-signatures-and-two-existing-rules',
        'transfer-the-one-owner-six-rule-semantic-delta-generically',
        'add-fibred-displayed-chain-1-profile-and-recursive-consumer',
        'exercise-positive-negative-and-reindexing-corpus',
        'run-frozen-and-live-lambdapi-conformance',
        'synchronize-ledgers-and-create-a-bounded-local-checkpoint'
    ],
    nonEffects: [
        'does-not-add-rawexpr-or-a-second-checker',
        'does-not-add-a-parser-or-generic-lambdapi-acquisition',
        'does-not-add-explicit-bracket-punctuation',
        'does-not-add-a-generic-total-category-pullback-or-equivalence',
        'does-not-identify-sequential-and-grouped-total-categories',
        'does-not-add-arbitrary-mixed-domain-coercion',
        'does-not-complete-general-nd-coherence',
        'does-not-promote-a-browser-profile',
        'does-not-broaden-git-or-publication-authority'
    ],
    decisionEffects: {
        proposalSelfAuthorizesImplementation: false,
        authorizesKernelOwnerOrRuleBeforeSeparateDecision: false,
        authorizesTypescriptSemanticContinuationBeforeSeparateDecision: false,
        authorizesParserOrAcquisition: false,
        authorizesBrowserPromotion: false,
        broadensGitAuthority: false
    },
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/' +
        'D-DTTLF-USABILITY-012 as proposed: select the complementary ' +
        'sequential-Sigma, recursive pullback/totalization, and direct ' +
        'displayed-term architecture; authorize after the separate review ' +
        'exactly one sigma_functord_sec owner, six measured runtime rules, ' +
        'three existing-signature/two existing-rule transfer ' +
        'prerequisites, and the fibred-displayed-chain-1 recursive ' +
        'TypeScript consumer; retain the +8 diagnostic critical-pair ' +
        'inventory; and preserve every stated non-effect and Git boundary?'
} as const;

export type CoreCategoricalDisplayedChainProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedChainProposalErrorCode =
    | 'DISPLAYED_CHAIN_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_ARCHITECTURE_DRIFT'
    | 'DISPLAYED_CHAIN_AUTHORITY_DRIFT'
    | 'DISPLAYED_CHAIN_EVIDENCE_DRIFT'
    | 'DISPLAYED_CHAIN_BOUNDARY_DRIFT';

export class CoreCategoricalDisplayedChainProposalError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedChainProposalError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreCategoricalDisplayedChainProposal(
    proposal: CoreCategoricalDisplayedChainProposalInput =
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL
): void {
    if (
        proposal.prerequisite.displayedEvaluationTransferRevision !==
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION ||
        proposal.prerequisite.displayedEvaluationSourceSha256 !==
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256 ||
        proposal.prerequisite.displayedEvaluationOwnerCount !== 2 ||
        proposal.prerequisite.displayedEvaluationRuntimeRuleCount !== 2 ||
        proposal.prerequisite.measuredRootGate.tests !== 904 ||
        proposal.prerequisite.measuredRootGate.failed !== 0 ||
        proposal.prerequisite.implementationAuthorizedBeforeDecision
    ) {
        throw new CoreCategoricalDisplayedChainProposalError(
            'DISPLAYED_CHAIN_PREREQUISITE_DRIFT',
            'The completed DISPLAYED-EVAL-1A prerequisite drifted'
        );
    }

    const architecture = proposal.clarifiedArchitecture;
    if (
        architecture.sourceBoundary !==
            'existing-typed-typescript-construction-ir' ||
        architecture.targetBoundary !==
            'backend-neutral-explicit-emdash-core' ||
        !architecture.genericCheckerReused ||
        !architecture.recursiveCompilerReused ||
        architecture.rawExprLayerAdded ||
        architecture.bidirectionalCheckerAdded ||
        architecture.parserAdded ||
        architecture.bracketPunctuationAdded ||
        architecture.wholeBodyRecognizerAdded ||
        architecture.intrinsicCoreOwnerAdded ||
        architecture.relationship !==
            'complementary-presentations-not-a-total-category-equivalence'
    ) {
        throw new CoreCategoricalDisplayedChainProposalError(
            'DISPLAYED_CHAIN_ARCHITECTURE_DRIFT',
            'The complementary recursive lowering architecture drifted'
        );
    }

    const selected = proposal.alternatives.find(
        alternative => alternative.disposition === 'recommend'
    );
    if (
        proposal.alternatives.length !== 4 ||
        selected?.id !== 'hybrid-sequential-recursive-direct' ||
        proposal.selectedClosure.newOwner.name !==
            'sigma_functord_sec' ||
        proposal.selectedClosure.runtimeRules.length !== 6 ||
        proposal.selectedClosure.newMathematicalOwnerCount !== 1 ||
        proposal.selectedClosure.newMathematicalRuntimeRuleCount !== 6 ||
        proposal.selectedClosure.newMathematicalProofRuleCount !== 0 ||
        proposal.selectedClosure.genericFappTappRuleCount !== 0 ||
        proposal.activeAuthorityInventory.absentGenericOwnerConfirmed !==
            true
    ) {
        throw new CoreCategoricalDisplayedChainProposalError(
            'DISPLAYED_CHAIN_AUTHORITY_DRIFT',
            'The selected owner/rule closure drifted'
        );
    }

    if (
        proposal.transferClosure.existingDeclarationPrerequisites.length !==
            3 ||
        proposal.transferClosure.existingRuntimeRulePrerequisites.length !==
            2 ||
        !proposal.transferClosure.allDeclarationsUseGenericTransferCompiler ||
        !proposal.transferClosure.allRuntimeRulesUseGenericRuntimeCompiler ||
        proposal.transferClosure.intrinsicCoreCaseRequired ||
        proposal.warningEvidence.baseline.unjoinableCriticalPairs !== 1012 ||
        proposal.warningEvidence.candidate.unjoinableCriticalPairs !== 1020 ||
        proposal.warningEvidence.delta.unjoinableCriticalPairs !== 8 ||
        proposal.warningEvidence.delta.replaceablePatternVariables !== 0 ||
        proposal.warningEvidence.warningIsSelectionVeto ||
        proposal.warningEvidence.strictLhsAudit.unreviewedCompoundSlots !== 0 ||
        !Object.values(proposal.recursiveEvidence).every(
            value => typeof value === 'string' || value === true
        )
    ) {
        throw new CoreCategoricalDisplayedChainProposalError(
            'DISPLAYED_CHAIN_EVIDENCE_DRIFT',
            'The transfer, warning, or recursive probe evidence drifted'
        );
    }

    if (
        proposal.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-01' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-01' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-012' ||
        proposal.typescriptConsumer.proposedProfile !==
            'fibred-displayed-chain-1' ||
        proposal.typescriptConsumer.newAstLayerRequired ||
        proposal.typescriptConsumer.newCheckerRequired ||
        proposal.typescriptConsumer.stringParserRequired ||
        proposal.decisionEffects.proposalSelfAuthorizesImplementation ||
        proposal.decisionEffects
            .authorizesKernelOwnerOrRuleBeforeSeparateDecision ||
        proposal.decisionEffects
            .authorizesTypescriptSemanticContinuationBeforeSeparateDecision ||
        proposal.decisionEffects.authorizesParserOrAcquisition ||
        proposal.decisionEffects.authorizesBrowserPromotion ||
        proposal.decisionEffects.broadensGitAuthority ||
        !proposal.nonEffects.includes(
            'does-not-add-a-generic-total-category-pullback-or-equivalence'
        )
    ) {
        throw new CoreCategoricalDisplayedChainProposalError(
            'DISPLAYED_CHAIN_BOUNDARY_DRIFT',
            'The non-self-authorizing DISPLAYED-CHAIN-0A boundary drifted'
        );
    }
}
