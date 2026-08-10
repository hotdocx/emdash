/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-FOUNDATION-1B0 proposal v2.
 *
 * Proposal v1 was rejected during review because its predecessor lacked
 * `hom_`. This review approves only checkpointed v2 under the user's standing
 * unattended delegation, with later human supersession.
 */

import {
    CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL,
    CorePathoutFoundation1b0Proposal,
    validateCorePathoutFoundation1b0Proposal
} from './pathout_foundation_proposal';

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

const proposal = CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL;

const rawReview = {
    revision: 'PATHOUT-LIBRARY-FOUNDATION-1B0-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHOUT-FOUNDATION-01',
        decisionId: 'D-TS-EMDASH-PATHOUT-FOUNDATION-001',
        decision: 'corrected-proposal-v2-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-corrected-' +
            'proposal-and-ledger-checkpoints',
        recordedOn: '2026-08-10',
        humanDecisionSupersedes: true,
        rejectedProposalCheckpoint: 'dd69325',
        approvedProposalCheckpoint: 'b3d6d71'
    },
    recommendation:
        cloneData(proposal) as CorePathoutFoundation1b0Proposal,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-FOUNDATION-1B',
        implementationAuthorized: true,
        exactImplementation:
            cloneData(proposal.exactImplementation),
        exactDependencyClosure:
            cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor:
            cloneData(proposal.selectedPredecessor),
        prerequisiteDeclarationCount: 3,
        runtimeRuleCount: 5,
        proofRuleCount: 1,
        transparentLibraryDefinitionCount: 9,
        positiveConsumerCount: 7,
        negativeConsumerCount: 8,
        boundedOracleAssertionCount: 6,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        fixedSourcePathInductionAuthorized: false,
        internalizedPathInductionAuthorized: false,
        transitivityAuthorized: false,
        sigmaMapHigherActionAuthorized: false,
        newCoreOrCheckerPrimitiveAuthorized: false,
        ordinarySafeLibraryRuleRegistrationAuthorized: false,
        textOrDeclarationParserAuthorized: false,
        browserOrPublicPackageExportAuthorized: false,
        activeLambdapiSourceChangeAuthorized: false,
        externalIntegrationOrReleaseAuthorized: false
    },
    validation: {
        correctedProposalCheckpoint: 'b3d6d71',
        correctedProposalLedgerCheckpoint: '75d0604',
        workspaceContract: 'passed-pnpm-11.16.0-node-24.11.1',
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '8-tests-8-pass-zero-fail',
        LambdapiProposalGate: 'not-required-no-behavior',
        longAggregateGate:
            'intentionally-omitted-under-standing-proportional-policy'
    },
    gitBoundary: {
        rollbackEvidence:
            'v1-rejection-and-corrected-v2-checkpoints-preserved',
        localImplementationCheckpointAuthorized: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-checkpointed-v2-proposal',
        'does-not-approve-superseded-v1',
        'does-not-itself-implement-foundation-1b',
        'does-not-authorize-path-induction-or-transitivity',
        'does-not-authorize-sigma-map-higher-action',
        'does-not-add-a-Core-owner-checker-or-evaluator-branch',
        'does-not-authorize-safe-library-rule-registration',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState: 'pathout-foundation-1b-implementation-ready'
} as const;

export type CorePathoutFoundation1b0Review = typeof rawReview;

export type CorePathoutFoundation1b0ReviewErrorCode =
    | 'PATHOUT_FOUNDATION_REVIEW_DECISION_DRIFT'
    | 'PATHOUT_FOUNDATION_REVIEW_PROPOSAL_DRIFT'
    | 'PATHOUT_FOUNDATION_REVIEW_AUTHORIZATION_DRIFT';

export class CorePathoutFoundation1b0ReviewError extends Error {
    constructor(
        public readonly code: CorePathoutFoundation1b0ReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutFoundation1b0ReviewError';
    }
}

export const CORE_PATHOUT_FOUNDATION_1B0_REVIEW =
    deepFreeze(rawReview);

export function validateCorePathoutFoundation1b0Review(
    review: CorePathoutFoundation1b0Review =
        CORE_PATHOUT_FOUNDATION_1B0_REVIEW
): void {
    validateCorePathoutFoundation1b0Proposal(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-FOUNDATION-1B0-REVIEWED-1' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHOUT-FOUNDATION-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHOUT-FOUNDATION-001' ||
        review.approval.decision !==
            'corrected-proposal-v2-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-10' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.rejectedProposalCheckpoint !== 'dd69325' ||
        review.approval.approvedProposalCheckpoint !== 'b3d6d71'
    ) {
        throw new CorePathoutFoundation1b0ReviewError(
            'PATHOUT_FOUNDATION_REVIEW_DECISION_DRIFT',
            'The exact corrected-v2 delegated decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-2' ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.decision.implementationAuthorized
    ) {
        throw new CorePathoutFoundation1b0ReviewError(
            'PATHOUT_FOUNDATION_REVIEW_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v2'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'PATHOUT-LIBRARY-FOUNDATION-1B' ||
        !authorization.implementationAuthorized ||
        !sameData(
            authorization.exactImplementation,
            proposal.exactImplementation
        ) ||
        !sameData(
            authorization.exactDependencyClosure,
            proposal.dependencyClosure
        ) ||
        !sameData(
            authorization.exactSelectedPredecessor,
            proposal.selectedPredecessor
        ) ||
        authorization.prerequisiteDeclarationCount !== 3 ||
        authorization.runtimeRuleCount !== 5 ||
        authorization.proofRuleCount !== 1 ||
        authorization.transparentLibraryDefinitionCount !== 9 ||
        authorization.positiveConsumerCount !== 7 ||
        authorization.negativeConsumerCount !== 8 ||
        authorization.boundedOracleAssertionCount !== 6 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        authorization.fixedSourcePathInductionAuthorized ||
        authorization.internalizedPathInductionAuthorized ||
        authorization.transitivityAuthorized ||
        authorization.sigmaMapHigherActionAuthorized ||
        authorization.newCoreOrCheckerPrimitiveAuthorized ||
        authorization.ordinarySafeLibraryRuleRegistrationAuthorized ||
        authorization.textOrDeclarationParserAuthorized ||
        authorization.browserOrPublicPackageExportAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized ||
        !sameData(review.validation, rawReview.validation) ||
        !sameData(review.gitBoundary, rawReview.gitBoundary) ||
        !sameData(review.nonEffects, rawReview.nonEffects) ||
        review.nextDependencyState !==
            'pathout-foundation-1b-implementation-ready'
    ) {
        throw new CorePathoutFoundation1b0ReviewError(
            'PATHOUT_FOUNDATION_REVIEW_AUTHORIZATION_DRIFT',
            'The review exceeded the exact root-only 3/5/1/9 boundary'
        );
    }
}
