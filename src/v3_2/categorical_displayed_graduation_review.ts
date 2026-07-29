/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01/
 * D-DTTLF-USABILITY-016.
 *
 * The pre-review DISPLAYED-BRACKET-GRADUATE-1 proposal remains unchanged
 * and non-self-authorizing. This artifact records the user's plan-specific
 * unattended delegation after no immediate human response to the exact
 * presented proposal. It records only the qualified demonstrated envelope
 * and authorizes only the frozen zero-delta DISPLAYED-CHAIN-2A stress.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL,
    CoreCategoricalDisplayedGraduationProposalInput,
    validateCoreCategoricalDisplayedGraduationProposal
} from './categorical_displayed_graduation_proposal';

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

const proposal = CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL;
const successor = proposal.successorStress;
const closure = successor.mathematicalClosure;

const rawReview = {
    revision: 'DISPLAYED-BRACKET-GRADUATE-1-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01',
        decisionId: 'D-DTTLF-USABILITY-016',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-29',
        humanDecisionSupersedes: true,
        decisionEvidence:
            'The user authorized the coding agent to approve a frozen ' +
            'proposal during unattended continuation when no immediate ' +
            'human response follows, provided the Git checkpoint SOP is ' +
            'followed'
    },
    /**
     * Immutable snapshot of the exact pre-review proposal. Its pending
     * status and false authority fields remain historical evidence and are
     * not mutated by approval.
     */
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedGraduationProposalInput,
    authorization: {
        qualifiedDisplayedGraduationRecorded: true,
        qualifiedEnvelope:
            proposal.recommendation.architectureEnvelope,
        mechanicallyReusableWithinEnvelope: true,
        arbitraryTelescopeDepthClaimed: false,
        arbitraryMixedVarianceClaimed: false,
        generalNdCoherenceComplete: false,
        wholeDevelopmentTransferClaimed: false,
        implementationRow: 'DISPLAYED-CHAIN-2A',
        implementationAuthorized: true,
        method: successor.frontendApi.method,
        exactBindingNames:
            cloneData(successor.frontendApi.exactBindingNames),
        callbackTokenOrder:
            cloneData(successor.frontendApi.callbackTokenOrder),
        callbackEvaluationCount:
            successor.frontendApi.callbackEvaluationCount,
        dependencyFlagsSuppliedByUser: false,
        siblingGroup:
            cloneData(successor.telescope.siblingGroup),
        displayedLevels: successor.telescope.displayedLevels,
        exactExistingOwners:
            cloneData(closure.existingOwners),
        exactExistingOwnerCount: closure.existingOwners.length,
        expectedDelta: {
            lambdapiOwners: closure.expectedNewLambdapiOwners,
            lambdapiRuntimeRules:
                closure.expectedNewLambdapiRuntimeRules,
            lambdapiProofRules:
                closure.expectedNewLambdapiProofRules,
            intrinsicCoreOwners:
                closure.expectedNewIntrinsicCoreOwners,
            ownerSpecificCheckerBranches:
                closure.expectedOwnerSpecificCheckerBranches,
            ownerSpecificEvaluatorBranches:
                closure.expectedOwnerSpecificEvaluatorBranches,
            transferEntries:
                closure.existingTransferEntryExpansionExpected
        },
        closureDriftRequiresSeparateDecision: true,
        exactFrozenApiAndCorpusRequired: true,
        existingTypedConstructionIrRequired: true,
        existingRecursiveContextualCompilerRequired: true,
        existingExplicitCoreRequired: true,
        existingGenericCheckerAndEvaluatorRequired: true,
        newParallelFrontendMethodAuthorized: false,
        activeLambdapiOwnerOrRuleEditAuthorized: false,
        transferClosureExpansionAuthorized: false,
        intrinsicCoreOwnerAuthorized: false,
        ownerSpecificCheckerOrEvaluatorBranchAuthorized: false,
        generalNdImplementationAuthorized: false,
        parserOrBulkTransferAuthorized: false,
        browserOrDeployedPromotionAuthorized: false,
        externalOrDestructiveGitActionAuthorized: false
    },
    retainedBoundaries: {
        settledArchitecture:
            cloneData(proposal.settledArchitecture),
        compilationPipeline:
            cloneData(proposal.compilationPipeline),
        architectureDistinction:
            cloneData(proposal.architectureDistinction),
        evidenceMatrix:
            cloneData(proposal.evidenceMatrix),
        implementedEnvelope:
            cloneData(proposal.implementedEnvelope),
        implementationRevisions:
            cloneData(proposal.implementationRevisions),
        latestTransferEvidence:
            cloneData(proposal.latestTransferEvidence),
        successorStress:
            cloneData(proposal.successorStress),
        residualGaps:
            cloneData(proposal.residualGaps),
        deferredInfrastructure:
            cloneData(proposal.deferredInfrastructure),
        followingSequence:
            cloneData(proposal.followingSequence),
        trustBoundary:
            cloneData(proposal.trustBoundary),
        claimBoundary:
            cloneData(proposal.claimBoundary),
        preReviewAuthority:
            cloneData(proposal.authority)
    },
    validation: {
        proposalRevision:
            'DISPLAYED-BRACKET-GRADUATE-1-PROPOSAL-1',
        proposalCheckpoint:
            '6c06cb10ea6eb9fa298544d084df5f129950a3a1',
        proposalLedgerCheckpoint:
            '00615423616b833cce9ac42b7eb59c803eebbc2a',
        focusedProposalGate: '12-tests-pass',
        rootProposalGate:
            '985-tests-938-pass-47-intentional-skip-zero-fail',
        completeProposalRepositoryGate:
            '19-live-conformance-41-kernel-health-and-all-' +
            'documentation-gates-pass',
        focusedReviewGate: '10-tests-required',
        rootReviewGate:
            '995-tests-948-pass-47-intentional-skip-zero-fail-required',
        liveConformanceReviewGate:
            '19-judgments-global-60-second-pass-required',
        activeKernelReviewGate: 'bounded-make-check-pass'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-delegation',
        localCheckpointRequired: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-itself-implement-displayed-chain-2a',
        'does-not-authorize-an-owner-rule-or-transfer-closure-delta',
        'does-not-claim-arbitrary-telescope-depth',
        'does-not-complete-general-nd-coherence-or-higher-action',
        'does-not-add-a-rawexpr-parser-or-second-checker',
        'does-not-authorize-mixed-variance-or-groupoidal-binding',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-resume-bulk-or-whole-development-transfer',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-chain-2a-exact-zero-delta-implementation-ready'
} as const;

export type CoreCategoricalDisplayedGraduationReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedGraduationReviewErrorCode =
    | 'DISPLAYED_GRADUATION_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_GRADUATION_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_GRADUATION_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedGraduationReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedGraduationReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedGraduationReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedGraduationReview(
    review: CoreCategoricalDisplayedGraduationReviewInput =
        CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
): void {
    if (
        review.revision !==
            'DISPLAYED-BRACKET-GRADUATE-1-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-016' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-29' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedGraduationReviewError(
            'DISPLAYED_GRADUATION_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-016 decision, ' +
                'authority, condition, and human-supersession boundary'
        );
    }

    try {
        validateCoreCategoricalDisplayedGraduationProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedGraduationReviewError(
            'DISPLAYED_GRADUATION_REVIEW_PREREQUISITE_DRIFT',
            'The approved DISPLAYED-BRACKET-GRADUATE-1 proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-graduate-01' ||
        review.recommendation.decisionId !==
            'D-DTTLF-USABILITY-016' ||
        review.recommendation.recommendation
            .currentSuccessorImplementationAuthorized ||
        review.recommendation.recommendation
            .semanticAuthorityAuthorized ||
        Object.values(
            review.recommendation.authority.currentProposalEffects
        ).some(Boolean)
    ) {
        throw new CoreCategoricalDisplayedGraduationReviewError(
            'DISPLAYED_GRADUATION_REVIEW_PROPOSAL_DRIFT',
            'The reviewed recommendation is not the exact immutable ' +
                'non-self-authorizing pre-review proposal'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.qualifiedDisplayedGraduationRecorded ||
        authorization.qualifiedEnvelope !==
            proposal.recommendation.architectureEnvelope ||
        !authorization.mechanicallyReusableWithinEnvelope ||
        authorization.arbitraryTelescopeDepthClaimed ||
        authorization.arbitraryMixedVarianceClaimed ||
        authorization.generalNdCoherenceComplete ||
        authorization.wholeDevelopmentTransferClaimed ||
        authorization.implementationRow !== 'DISPLAYED-CHAIN-2A' ||
        !authorization.implementationAuthorized ||
        authorization.method !== 'displayedDependentContextLambda' ||
        authorization.exactBindingNames.join(',') !== 'a,b,c,d' ||
        authorization.callbackTokenOrder.join(',') !== 'a,b,c,d' ||
        authorization.callbackEvaluationCount !== 1 ||
        authorization.dependencyFlagsSuppliedByUser ||
        authorization.siblingGroup.join(',') !== 'b,c' ||
        authorization.displayedLevels !== 3 ||
        !sameData(
            authorization.exactExistingOwners,
            closure.existingOwners
        ) ||
        authorization.exactExistingOwnerCount !==
            closure.existingOwners.length ||
        Object.values(authorization.expectedDelta).some(
            value => value !== 0
        ) ||
        !authorization.closureDriftRequiresSeparateDecision ||
        !authorization.exactFrozenApiAndCorpusRequired ||
        !authorization.existingTypedConstructionIrRequired ||
        !authorization.existingRecursiveContextualCompilerRequired ||
        !authorization.existingExplicitCoreRequired ||
        !authorization.existingGenericCheckerAndEvaluatorRequired ||
        authorization.newParallelFrontendMethodAuthorized ||
        authorization.activeLambdapiOwnerOrRuleEditAuthorized ||
        authorization.transferClosureExpansionAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization
            .ownerSpecificCheckerOrEvaluatorBranchAuthorized ||
        authorization.generalNdImplementationAuthorized ||
        authorization.parserOrBulkTransferAuthorized ||
        authorization.browserOrDeployedPromotionAuthorized ||
        authorization.externalOrDestructiveGitActionAuthorized ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nextDependencyState !==
            'displayed-chain-2a-exact-zero-delta-implementation-ready'
    ) {
        throw new CoreCategoricalDisplayedGraduationReviewError(
            'DISPLAYED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'The delegated approval exceeds the frozen mixed-telescope, ' +
                'zero-delta, or Git boundary'
        );
    }

    if (
        !sameData(
            review.retainedBoundaries,
            rawReview.retainedBoundaries
        ) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalDisplayedGraduationReviewError(
            'DISPLAYED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'The retained evidence, corpus, deferred claims, or ' +
                'non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedGraduationReview();
