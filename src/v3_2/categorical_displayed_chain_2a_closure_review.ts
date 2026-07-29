/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01/
 * D-DTTLF-USABILITY-017.
 *
 * The checkpointed closure proposal remains unchanged and
 * non-self-authorizing. This review records the user's standing unattended
 * delegation after the exact green gate was presented, retains human
 * supersession, and authorizes only the measured closure frozen there.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL,
    CoreCategoricalDisplayedChain2aClosureProposalInput,
    validateCoreCategoricalDisplayedChain2aClosureProposal
} from './categorical_displayed_chain_2a_closure_proposal';

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

const proposal =
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL;
const implementation = proposal.proposedImplementation;
const closure = proposal.typescriptClosure;

const rawReview = {
    revision: 'DISPLAYED-CHAIN-2A-CLOSURE-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate:
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01',
        decisionId: 'D-DTTLF-USABILITY-017',
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
     * Immutable snapshot of the exact checkpointed proposal. Its pending
     * status and false authority fields remain historical evidence.
     */
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedChain2aClosureProposalInput,
    authorization: {
        implementationRow: 'DISPLAYED-CHAIN-2A',
        closureRow: 'DISPLAYED-CHAIN-2A-CLOSURE-0A',
        implementationAuthorized: true,
        frontendMethod:
            implementation.frontendMethod,
        frontendShape:
            implementation.frontendShapeRemainsExactly,
        activeLambdapiSymbolDelta:
            implementation.activeLambdapiSymbolDelta,
        activeLambdapiRuntimeRuleDelta:
            implementation.activeLambdapiRuntimeRuleDelta,
        activeLambdapiProofRuleDelta:
            implementation.activeLambdapiProofRuleDelta,
        exactLambdapiOwner:
            proposal.activeLambdapiCandidate.owner,
        exactLambdapiPairedOwner:
            proposal.activeLambdapiCandidate.pairedOwner,
        typescriptExistingDeclarationTransferCount:
            implementation.typescriptExistingDeclarationTransferCount,
        typescriptRuntimeRuleCount:
            implementation.typescriptRuntimeRuleCount,
        typescriptExactExistingRuntimeRuleCount:
            implementation.typescriptExactExistingRuntimeRuleCount,
        typescriptDerivedRuntimeRuleCount:
            implementation.typescriptDerivedRuntimeRuleCount,
        typescriptNewRuntimeRuleCount:
            implementation.typescriptNewRuntimeRuleCount,
        exactExistingDeclarations:
            cloneData(closure.existingDeclarations),
        exactExistingRuntimeRuleIds:
            cloneData(closure.exactExistingRuntimeRuleIds),
        exactDerivedRuntimeRuleIds:
            cloneData(closure.derivedRuntimeRuleIds),
        exactNewRuntimeRuleIds:
            cloneData(closure.newRuntimeRuleIds),
        isolatedContinuationModule:
            closure.isolatedContinuationModule,
        isolatedProfile: closure.isolatedProfile,
        genericCheckerBudgetPlumbingCount:
            implementation.genericCheckerBudgetPlumbingCount,
        defaultCoreComparisonBudget:
            closure.checkerBudgetPlumbing.defaultCoreBudgetRemains,
        continuationComparisonBudget:
            closure.checkerBudgetPlumbing.selectedContinuationBudget,
        typedPatternCorrectionCount:
            closure.typedPatternCorrectionCount,
        intrinsicCoreOwnerDelta:
            implementation.intrinsicCoreOwnerDelta,
        ownerSpecificCheckerEvaluatorDelta:
            implementation.ownerSpecificCheckerEvaluatorDelta,
        externalOracleDelta:
            implementation.externalOracleDelta,
        newProfileCount: implementation.newProfileCount,
        exactValidationPlanRequired: true,
        generalNdImplementationAuthorized: false,
        arbitraryTelescopeOrMixedVarianceAuthorized: false,
        groupoidalClosureAuthorized: false,
        parserOrSecondFrontendAuthorized: false,
        browserPromotionAuthorized: false,
        bulkWholeLibraryTransferAuthorized: false,
        declarationRefinementAuthorized: false,
        externalOrDestructiveGitActionAuthorized: false
    },
    retainedBoundary: {
        prerequisite: cloneData(proposal.prerequisite),
        auditVerdict: cloneData(proposal.auditVerdict),
        activeLambdapiCandidate:
            cloneData(proposal.activeLambdapiCandidate),
        typescriptClosure: cloneData(proposal.typescriptClosure),
        prototypeEvidence: cloneData(proposal.prototypeEvidence),
        alternatives: cloneData(proposal.alternatives),
        proposedImplementation:
            cloneData(proposal.proposedImplementation),
        validationPlan: cloneData(proposal.validationPlan),
        nonEffects: cloneData(proposal.nonEffects),
        preReviewDecisionEffects:
            cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision:
            'DISPLAYED-CHAIN-2A-CLOSURE-0A-PROPOSAL-1',
        proposalCheckpoint:
            'f647791281095e02c6ebe3f1490e272b4e58c7a0',
        proposalLedgerCheckpoint:
            'd99de0eed09c766f740d555cc7f71d645ff20286',
        focusedProposalGate: '7-tests-pass',
        rootProposalGate:
            '1002-tests-955-pass-47-intentional-skip-zero-fail',
        liveConformanceProposalGate:
            '19-judgments-global-60-second-pass',
        activeKernelProposalGate:
            'bounded-make-check-pass',
        completeProposalRepositoryGate:
            'kernel-examples-metrics-support-doc-book-rule-audit-' +
            'and-strict-catalog-pass',
        focusedReviewGate: '8-tests-required',
        rootReviewGate:
            '1010-tests-963-pass-47-intentional-skip-zero-fail-required',
        liveConformanceReviewGate:
            '19-judgments-global-60-second-pass-required',
        activeKernelReviewGate: 'bounded-make-check-pass-required'
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
        'does-not-rewrite-or-falsify-d016-history',
        'does-not-authorize-a-new-lambdapi-symbol',
        'does-not-authorize-a-proof-time-rule',
        'does-not-authorize-an-intrinsic-core-owner',
        'does-not-authorize-an-owner-specific-checker-or-evaluator-branch',
        'does-not-authorize-an-external-subject-reduction-oracle',
        'does-not-authorize-a-second-frontend-or-string-parser',
        'does-not-authorize-general-nd-or-arbitrary-telescope-depth',
        'does-not-authorize-mixed-variance-or-groupoidal-closure',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-authorize-bulk-or-whole-development-transfer',
        'does-not-authorize-decl-refine-1a',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-chain-2a-exact-closure-implementation-ready'
} as const;

export type CoreCategoricalDisplayedChain2aClosureReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedChain2aClosureReviewErrorCode =
    | 'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedChain2aClosureReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChain2aClosureReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChain2aClosureReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedChain2aClosureReview(
    review: CoreCategoricalDisplayedChain2aClosureReviewInput =
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW
): void {
    if (
        review.revision !==
            'DISPLAYED-CHAIN-2A-CLOSURE-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-017' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-29' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureReviewError(
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-017 decision, ' +
                'condition, and human-supersession boundary'
        );
    }

    try {
        validateCoreCategoricalDisplayedChain2aClosureProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedChain2aClosureReviewError(
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_PREREQUISITE_DRIFT',
            'The checkpointed D-017 proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-2a-' +
            'closure-01' ||
        review.recommendation.decisionId !==
            'D-DTTLF-USABILITY-017' ||
        review.recommendation.decisionEffects.authorityAuthorized ||
        review.recommendation.decisionEffects.implementationAuthorized
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureReviewError(
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_PROPOSAL_DRIFT',
            'The recommendation is not the exact immutable ' +
                'non-self-authorizing D-017 proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !== 'DISPLAYED-CHAIN-2A' ||
        authorization.closureRow !==
            'DISPLAYED-CHAIN-2A-CLOSURE-0A' ||
        !authorization.implementationAuthorized ||
        authorization.frontendMethod !==
            'existing-displayedDependentContextLambda' ||
        authorization.frontendShape !==
            'a; independent-siblings-b-c; d-dependent-on-pair' ||
        authorization.activeLambdapiSymbolDelta !== 0 ||
        authorization.activeLambdapiRuntimeRuleDelta !== 1 ||
        authorization.activeLambdapiProofRuleDelta !== 0 ||
        authorization.exactLambdapiOwner !== 'fdapp1_int_cell' ||
        authorization.exactLambdapiPairedOwner !==
            'Product_pair_funcd' ||
        authorization.typescriptExistingDeclarationTransferCount !== 3 ||
        authorization.typescriptRuntimeRuleCount !== 9 ||
        authorization.typescriptExactExistingRuntimeRuleCount !== 6 ||
        authorization.typescriptDerivedRuntimeRuleCount !== 2 ||
        authorization.typescriptNewRuntimeRuleCount !== 1 ||
        authorization.exactExistingDeclarations.join(',') !==
            'sigma_Fst,sigma_Snd,Product_grpd' ||
        authorization.isolatedContinuationModule !==
            'categorical_displayed_chain_2a_closure_transfer' ||
        authorization.isolatedProfile !== 'fibred-displayed-chain-2a' ||
        authorization.genericCheckerBudgetPlumbingCount !== 1 ||
        authorization.defaultCoreComparisonBudget !== 256 ||
        authorization.continuationComparisonBudget !== 512 ||
        authorization.typedPatternCorrectionCount !== 2 ||
        authorization.intrinsicCoreOwnerDelta !== 0 ||
        authorization.ownerSpecificCheckerEvaluatorDelta !== 0 ||
        authorization.externalOracleDelta !== 0 ||
        authorization.newProfileCount !== 1 ||
        !authorization.exactValidationPlanRequired ||
        authorization.generalNdImplementationAuthorized ||
        authorization.arbitraryTelescopeOrMixedVarianceAuthorized ||
        authorization.groupoidalClosureAuthorized ||
        authorization.parserOrSecondFrontendAuthorized ||
        authorization.browserPromotionAuthorized ||
        authorization.bulkWholeLibraryTransferAuthorized ||
        authorization.declarationRefinementAuthorized ||
        authorization.externalOrDestructiveGitActionAuthorized
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureReviewError(
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_AUTHORIZATION_DRIFT',
            'The delegated approval exceeds the exact measured closure'
        );
    }

    if (
        !sameData(review.retainedBoundary.prerequisite,
            proposal.prerequisite) ||
        !sameData(review.retainedBoundary.auditVerdict,
            proposal.auditVerdict) ||
        !sameData(review.retainedBoundary.activeLambdapiCandidate,
            proposal.activeLambdapiCandidate) ||
        !sameData(review.retainedBoundary.typescriptClosure,
            proposal.typescriptClosure) ||
        !sameData(review.retainedBoundary.prototypeEvidence,
            proposal.prototypeEvidence) ||
        !sameData(review.retainedBoundary.alternatives,
            proposal.alternatives) ||
        !sameData(review.retainedBoundary.proposedImplementation,
            proposal.proposedImplementation) ||
        !sameData(review.retainedBoundary.validationPlan,
            proposal.validationPlan) ||
        !sameData(review.retainedBoundary.nonEffects,
            proposal.nonEffects) ||
        !sameData(review.retainedBoundary.preReviewDecisionEffects,
            proposal.decisionEffects) ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nonEffects.length !== 14 ||
        review.nextDependencyState !==
            'displayed-chain-2a-exact-closure-implementation-ready' ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureReviewError(
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_AUTHORIZATION_DRIFT',
            'The retained evidence, non-effects, or Git boundary drifted'
        );
    }
}

validateCoreCategoricalDisplayedChain2aClosureReview();
