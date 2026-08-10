/**
 * Supersession record for the separate review of
 * PATHOUT-LIBRARY-FOUNDATION-1B0 proposal v7.
 *
 * Generic transfer validation requires a nonempty generated-constraint list.
 * The v7 authorization is withdrawn while proposal v8 records the reflexive
 * TypeScript representative of the source's `tt ≡ tt` discharge.
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
    revision: 'PATHOUT-LIBRARY-FOUNDATION-1B0-REVIEW-SUPERSEDED-7',
    status: 'proposal-v7-review-superseded-v8-awaiting-separate-review',
    approval: {
        gate: 'H-TS-EMDASH-PATHOUT-FOUNDATION-01',
        decisionId: 'D-TS-EMDASH-PATHOUT-FOUNDATION-001',
        decision:
            'corrected-proposal-v7-superseded-after-measured-' +
            'nonempty-proof-constraint-invariant',
        authority: 'measured-implementation-forward-correction',
        condition:
            'generic-module-validation-rejects-zero-generated-' +
            'constraints-and-the-predecessor-does-not-expose-native-tt',
        recordedOn: '2026-08-10',
        humanDecisionSupersedes: true,
        rejectedProposalCheckpoint: 'dd69325',
        supersededProposalCheckpoint: 'b3d6d71',
        supersededReviewCheckpoint: '38ef8ae',
        supersededV3ProposalCheckpoint: '640d5ec',
        supersededV3ReviewCheckpoint: '36c368e',
        supersededV4ProposalCheckpoint: '681d954',
        supersededV4ReviewCheckpoint: 'ab556a9',
        supersededV5ProposalCheckpoint: '622a496',
        supersededV5ReviewCheckpoint: 'c4dd293',
        supersededV6ProposalCheckpoint: 'f006ccb',
        supersededV6ReviewCheckpoint: 'bdcef29',
        supersededV7ProposalCheckpoint: '2460ae9',
        supersededV7ReviewCheckpoint: '7035922',
        replacementProposalCheckpoint: 'pending-separate-checkpoint'
    },
    recommendation:
        cloneData(proposal) as CorePathoutFoundation1b0Proposal,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-FOUNDATION-1B',
        implementationAuthorized: false,
        exactImplementation:
            cloneData(proposal.exactImplementation),
        exactDependencyClosure:
            cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor:
            cloneData(proposal.selectedPredecessor),
        prerequisiteDeclarationCount: 5,
        runtimeRuleCount: 12,
        proofRuleCount: 2,
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
        supersededV7ProposalCheckpoint: '2460ae9',
        supersededV7ReviewCheckpoint: '7035922',
        measuredFailure:
            'generic-module-validation-rejects-identity-family-proof-' +
            'rule-with-zero-generated-constraints-before-compilation',
        replacementProposalRevision:
            'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-8',
        replacementReviewGate: 'required-before-implementation-resumes'
    },
    gitBoundary: {
        rollbackEvidence:
            'v1-v7-proposals-and-reviews-preserved-as-superseded',
        localImplementationCheckpointAuthorized: false,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'preserves-v7-proposal-and-review-as-Git-backtracking-evidence',
        'does-not-approve-superseded-v1-v2-v3-v4-v5-v6-or-v7',
        'does-not-revive-any-superseded-review',
        'does-not-approve-replacement-v8',
        'does-not-itself-implement-foundation-1b',
        'does-not-authorize-path-induction-or-transitivity',
        'does-not-authorize-sigma-map-higher-action',
        'does-not-add-a-Core-owner-checker-or-evaluator-branch',
        'does-not-authorize-safe-library-rule-registration',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-foundation-1b0-v8-awaiting-separate-review'
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
            'PATHOUT-LIBRARY-FOUNDATION-1B0-REVIEW-SUPERSEDED-7' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHOUT-FOUNDATION-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHOUT-FOUNDATION-001' ||
        review.approval.decision !==
            'corrected-proposal-v7-superseded-after-measured-' +
                'nonempty-proof-constraint-invariant' ||
        review.approval.authority !==
            'measured-implementation-forward-correction' ||
        review.approval.recordedOn !== '2026-08-10' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.rejectedProposalCheckpoint !== 'dd69325' ||
        review.approval.supersededProposalCheckpoint !== 'b3d6d71' ||
        review.approval.supersededReviewCheckpoint !== '38ef8ae' ||
        review.approval.supersededV3ProposalCheckpoint !== '640d5ec' ||
        review.approval.supersededV3ReviewCheckpoint !== '36c368e' ||
        review.approval.supersededV4ProposalCheckpoint !== '681d954' ||
        review.approval.supersededV4ReviewCheckpoint !== 'ab556a9' ||
        review.approval.supersededV5ProposalCheckpoint !== '622a496' ||
        review.approval.supersededV5ReviewCheckpoint !== 'c4dd293' ||
        review.approval.supersededV6ProposalCheckpoint !== 'f006ccb' ||
        review.approval.supersededV6ReviewCheckpoint !== 'bdcef29' ||
        review.approval.supersededV7ProposalCheckpoint !== '2460ae9' ||
        review.approval.supersededV7ReviewCheckpoint !== '7035922' ||
        review.approval.replacementProposalCheckpoint !==
            'pending-separate-checkpoint'
    ) {
        throw new CorePathoutFoundation1b0ReviewError(
            'PATHOUT_FOUNDATION_REVIEW_DECISION_DRIFT',
            'The exact corrected-v7 supersession decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-8' ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.decision.implementationAuthorized
    ) {
        throw new CorePathoutFoundation1b0ReviewError(
            'PATHOUT_FOUNDATION_REVIEW_PROPOSAL_DRIFT',
            'The supersession must retain exact non-authorizing proposal v8'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'PATHOUT-LIBRARY-FOUNDATION-1B' ||
        authorization.implementationAuthorized ||
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
        authorization.prerequisiteDeclarationCount !== 5 ||
        authorization.runtimeRuleCount !== 12 ||
        authorization.proofRuleCount !== 2 ||
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
            'pathout-foundation-1b0-v8-awaiting-separate-review'
    ) {
        throw new CorePathoutFoundation1b0ReviewError(
            'PATHOUT_FOUNDATION_REVIEW_AUTHORIZATION_DRIFT',
            'The superseded review reauthorized implementation or drifted'
        );
    }
}
