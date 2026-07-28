/**
 * Separate immutable explicit-human review record for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/D-DTTLF-USABILITY-012.
 *
 * The pre-review DISPLAYED-CHAIN-0A proposal remains unchanged and
 * non-self-authorizing. This artifact records the user's exact approval and
 * authorizes only the frozen DISPLAYED-CHAIN-1A implementation row.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL,
    CoreCategoricalDisplayedChainProposalInput,
    validateCoreCategoricalDisplayedChainProposal
} from './categorical_displayed_chain_proposal';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

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

const proposal = CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL;

const rawReview = {
    revision: 'DISPLAYED-CHAIN-0A-REVIEWED-1',
    status: 'reviewed-approved-by-explicit-human-decision',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-01',
        decisionId: 'D-DTTLF-USABILITY-012',
        decision: 'approved-as-proposed',
        authority: 'explicit-human-decision',
        recordedOn: '2026-07-28',
        decisionEvidence:
            'Approve H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/' +
            'D-DTTLF-USABILITY-012 as proposed.'
    },
    /**
     * Immutable snapshot of the exact pre-review proposal. Its pending
     * status remains historical evidence and is not mutated by approval.
     */
    recommendation:
        cloneData(proposal) as CoreCategoricalDisplayedChainProposalInput,
    authorization: {
        implementationRow: 'DISPLAYED-CHAIN-1A',
        implementationAuthorized: true,
        selectedArchitecture:
            'hybrid-sequential-recursive-direct',
        exactKernelOwners: [
            'sigma_functord_sec'
        ],
        exactKernelOwnerCount: 1,
        exactRuntimeRuleIds: proposal.selectedClosure.runtimeRules.map(
            rule => rule.id
        ),
        exactRuntimeRuleCount: 6,
        existingDeclarationPrerequisites:
            cloneData(
                proposal.transferClosure.existingDeclarationPrerequisites
            ),
        existingDeclarationPrerequisiteCount: 3,
        existingRuntimeRulePrerequisites:
            cloneData(
                proposal.transferClosure.existingRuntimeRulePrerequisites
            ),
        existingRuntimeRulePrerequisiteCount: 2,
        activeLambdapiOwnerAndRuleEditAuthorized: true,
        genericDeclarationAndRuntimeTransferAuthorized: true,
        intrinsicCoreOwnerAuthorized: false,
        profile: 'fibred-displayed-chain-1',
        visibility: 'root-only',
        method: 'displayedDependentContextLambda',
        existingTypedConstructionIrRequired: true,
        existingRecursiveContextualCompilerRequired: true,
        existingExplicitCoreRequired: true,
        existingGenericCheckerAndEvaluatorRequired: true,
        warningDeltaIsDiagnosticNotVeto: true,
        rawExprOrSecondCheckerAuthorized: false,
        parserOrBulkAcquisitionAuthorized: false,
        wholeBodyRecognizerAuthorized: false,
        genericTotalPullbackOrEquivalenceAuthorized: false,
        arbitraryMixedDomainCoercionAuthorized: false,
        generalNdCoherenceAuthorized: false,
        browserOrDeployedPromotionAuthorized: false
    },
    retainedBoundaries: {
        clarifiedArchitecture:
            cloneData(proposal.clarifiedArchitecture),
        representativeTelescope:
            cloneData(proposal.representativeTelescope),
        selectedClosure:
            cloneData(proposal.selectedClosure),
        transferClosure:
            cloneData(proposal.transferClosure),
        warningEvidence:
            cloneData(proposal.warningEvidence),
        recursiveEvidence:
            cloneData(proposal.recursiveEvidence),
        typescriptConsumer:
            cloneData(proposal.typescriptConsumer),
        positiveCorpus:
            cloneData(proposal.positiveCorpus),
        negativeCorpus:
            cloneData(proposal.negativeCorpus),
        feasibilityAssessment:
            cloneData(proposal.feasibilityAssessment),
        nonEffects:
            cloneData(proposal.nonEffects),
        preReviewDecisionEffects:
            cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision: 'DISPLAYED-CHAIN-0A-PROPOSAL-1',
        proposalCheckpoint:
            'aba1c957afbeb18f2bfe25add56bfa6aacfa4dda',
        proposalLedgerCheckpoint:
            '359149617e96c0e3868496ad979728dc53a041f9',
        proposalRootGate:
            '914-tests-867-pass-47-intentional-skip-zero-fail',
        focusedReviewGate: '9-tests-required',
        rootReviewGate:
            '923-tests-876-pass-47-intentional-skip-zero-fail',
        liveConformanceGate: 'required-before-semantic-checkpoint',
        boundedKernelGate: 'required-before-semantic-checkpoint'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-approval',
        localCheckpointRequired: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false,
        preservedTimeoutArtifactsUntouched: true
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-itself-install-the-owner-or-rules',
        'does-not-add-an-intrinsic-core-owner-or-second-checker',
        'does-not-add-rawexpr-parser-or-whole-body-recognition',
        'does-not-add-a-generic-total-pullback-or-equivalence',
        'does-not-authorize-arbitrary-mixed-domain-coercion',
        'does-not-complete-general-nd-coherence',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-authorize-bulk-acquisition-or-transfer',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-chain-1a-exact-implementation-ready'
} as const;

export type CoreCategoricalDisplayedChainReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedChainReviewErrorCode =
    | 'DISPLAYED_CHAIN_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_CHAIN_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_CHAIN_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedChainReviewError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedChainReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedChainReview(
    review: CoreCategoricalDisplayedChainReviewInput =
        CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW
): void {
    if (
        review.revision !== 'DISPLAYED-CHAIN-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-by-explicit-human-decision' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-012' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !== 'explicit-human-decision' ||
        review.approval.recordedOn !== '2026-07-28' ||
        review.approval.decisionEvidence !==
            'Approve H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/' +
            'D-DTTLF-USABILITY-012 as proposed.'
    ) {
        throw new CoreCategoricalDisplayedChainReviewError(
            'DISPLAYED_CHAIN_REVIEW_DECISION_DRIFT',
            'The review must preserve the exact explicit D-012 decision'
        );
    }

    try {
        validateCoreCategoricalDisplayedChainProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedChainReviewError(
            'DISPLAYED_CHAIN_REVIEW_PREREQUISITE_DRIFT',
            'The approved DISPLAYED-CHAIN-0A proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-01' ||
        review.recommendation.decisionId !== 'D-DTTLF-USABILITY-012'
    ) {
        throw new CoreCategoricalDisplayedChainReviewError(
            'DISPLAYED_CHAIN_REVIEW_PROPOSAL_DRIFT',
            'The reviewed recommendation is not the exact immutable ' +
                'pre-review proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !== 'DISPLAYED-CHAIN-1A' ||
        !authorization.implementationAuthorized ||
        authorization.selectedArchitecture !==
            'hybrid-sequential-recursive-direct' ||
        authorization.exactKernelOwners.join(',') !==
            'sigma_functord_sec' ||
        authorization.exactKernelOwnerCount !== 1 ||
        authorization.exactRuntimeRuleIds.join(',') !==
            proposal.selectedClosure.runtimeRules
                .map(rule => rule.id)
                .join(',') ||
        authorization.exactRuntimeRuleCount !== 6 ||
        authorization.existingDeclarationPrerequisites.join(',') !==
            'sigma_map_func,fdapp1_int_cell,fdapp1_int_hom_fapp0' ||
        authorization.existingDeclarationPrerequisiteCount !== 3 ||
        authorization.existingRuntimeRulePrerequisites.join(',') !==
            'sigma_map_func-object-action,' +
            'sigma_map_func-structured-arrow-action' ||
        authorization.existingRuntimeRulePrerequisiteCount !== 2 ||
        !authorization.activeLambdapiOwnerAndRuleEditAuthorized ||
        !authorization.genericDeclarationAndRuntimeTransferAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization.profile !== 'fibred-displayed-chain-1' ||
        authorization.visibility !== 'root-only' ||
        authorization.method !== 'displayedDependentContextLambda' ||
        !authorization.existingTypedConstructionIrRequired ||
        !authorization.existingRecursiveContextualCompilerRequired ||
        !authorization.existingExplicitCoreRequired ||
        !authorization.existingGenericCheckerAndEvaluatorRequired ||
        !authorization.warningDeltaIsDiagnosticNotVeto ||
        authorization.rawExprOrSecondCheckerAuthorized ||
        authorization.parserOrBulkAcquisitionAuthorized ||
        authorization.wholeBodyRecognizerAuthorized ||
        authorization.genericTotalPullbackOrEquivalenceAuthorized ||
        authorization.arbitraryMixedDomainCoercionAuthorized ||
        authorization.generalNdCoherenceAuthorized ||
        authorization.browserOrDeployedPromotionAuthorized ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        !review.gitBoundary.preservedTimeoutArtifactsUntouched ||
        review.nextDependencyState !==
            'displayed-chain-1a-exact-implementation-ready'
    ) {
        throw new CoreCategoricalDisplayedChainReviewError(
            'DISPLAYED_CHAIN_REVIEW_AUTHORIZATION_DRIFT',
            'The explicit approval exceeds the frozen semantic or Git ' +
                'boundary'
        );
    }

    if (
        !sameData(
            review.retainedBoundaries,
            rawReview.retainedBoundaries
        ) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalDisplayedChainReviewError(
            'DISPLAYED_CHAIN_REVIEW_AUTHORIZATION_DRIFT',
            'The retained evidence, claims, or non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedChainReview();
