/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01/
 * D-DTTLF-USABILITY-016.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW,
    CoreCategoricalDisplayedGraduationReviewError,
    validateCoreCategoricalDisplayedGraduationReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertReviewError = (
    mutate: (review: any) => void,
    expected: CoreCategoricalDisplayedGraduationReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalDisplayedGraduationReview(review),
        error =>
            error instanceof
                CoreCategoricalDisplayedGraduationReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed displayed-bracket graduation', () => {
    it('records the delegated D-016 approval separately and exactly', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW.approval,
            {
                gate:
                    'H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01',
                decisionId: 'D-DTTLF-USABILITY-016',
                decision: 'approved-as-proposed',
                authority: 'user-delegated-unattended-approval',
                condition:
                    'no-immediate-human-response-after-presented-' +
                    'frozen-proposal',
                recordedOn: '2026-07-29',
                humanDecisionSupersedes: true,
                decisionEvidence:
                    'The user authorized the coding agent to approve a ' +
                    'frozen proposal during unattended continuation when ' +
                    'no immediate human response follows, provided the ' +
                    'Git checkpoint SOP is followed'
            }
        );
    });

    it('retains an immutable snapshot of the pending proposal', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
        );
        assert.equal(
            review.recommendation.recommendation
                .currentSuccessorImplementationAuthorized,
            false
        );
        assert.equal(
            review.recommendation.recommendation
                .semanticAuthorityAuthorized,
            false
        );
    });

    it('graduates only the exact demonstrated envelope', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
                .authorization;
        assert.equal(
            authorization.qualifiedDisplayedGraduationRecorded,
            true
        );
        assert.equal(
            authorization.mechanicallyReusableWithinEnvelope,
            true
        );
        assert.equal(
            authorization.arbitraryTelescopeDepthClaimed,
            false
        );
        assert.equal(
            authorization.arbitraryMixedVarianceClaimed,
            false
        );
        assert.equal(
            authorization.wholeDevelopmentTransferClaimed,
            false
        );
    });

    it('authorizes only the frozen four-binding mixed telescope', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
                .authorization;
        assert.equal(
            authorization.implementationRow,
            'DISPLAYED-CHAIN-2A'
        );
        assert.equal(authorization.implementationAuthorized, true);
        assert.equal(
            authorization.method,
            'displayedDependentContextLambda'
        );
        assert.deepEqual(
            authorization.exactBindingNames,
            ['a', 'b', 'c', 'd']
        );
        assert.deepEqual(authorization.siblingGroup, ['b', 'c']);
        assert.equal(authorization.displayedLevels, 3);
        assert.equal(authorization.callbackEvaluationCount, 1);
        assert.equal(
            authorization.dependencyFlagsSuppliedByUser,
            false
        );
    });

    it('freezes every semantic and transfer delta at zero', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
                .authorization;
        assert.deepEqual(authorization.expectedDelta, {
            lambdapiOwners: 0,
            lambdapiRuntimeRules: 0,
            lambdapiProofRules: 0,
            intrinsicCoreOwners: 0,
            ownerSpecificCheckerBranches: 0,
            ownerSpecificEvaluatorBranches: 0,
            transferEntries: 0
        });
        assert.equal(
            authorization.closureDriftRequiresSeparateDecision,
            true
        );
        assert.equal(
            authorization.activeLambdapiOwnerOrRuleEditAuthorized,
            false
        );
        assert.equal(
            authorization.transferClosureExpansionAuthorized,
            false
        );
    });

    it('retains the exact object, arrow, reindexing, and negative corpus', () => {
        const stress =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
                .retainedBoundaries.successorStress;
        assert.equal(stress.requiredCorpus.object.length, 5);
        assert.equal(
            stress.requiredCorpus.internalizedArrow.length,
            4
        );
        assert.equal(stress.requiredCorpus.reindexing.length, 2);
        assert.equal(stress.requiredCorpus.negative.length, 9);
        assert.deepEqual(
            stress.requiredCorpus.evidenceRequirements,
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                .successorStress.requiredCorpus.evidenceRequirements
        );
    });

    it('requires the existing typed recursive pipeline and authority', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW
                .authorization;
        assert.equal(
            authorization.existingTypedConstructionIrRequired,
            true
        );
        assert.equal(
            authorization.existingRecursiveContextualCompilerRequired,
            true
        );
        assert.equal(
            authorization.existingExplicitCoreRequired,
            true
        );
        assert.equal(
            authorization.existingGenericCheckerAndEvaluatorRequired,
            true
        );
        assert.deepEqual(
            authorization.exactExistingOwners,
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                .successorStress.mathematicalClosure.existingOwners
        );
    });

    it('keeps nd, parsing, bulk transfer, and deployment closed', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW;
        assert.equal(
            review.authorization.generalNdImplementationAuthorized,
            false
        );
        assert.equal(
            review.authorization.parserOrBulkTransferAuthorized,
            false
        );
        assert.equal(
            review.authorization.browserOrDeployedPromotionAuthorized,
            false
        );
        assert.equal(
            review.retainedBoundaries.claimBoundary.generalNd,
            'withheld'
        );
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /categorical_displayed_graduation|DISPLAYED-CHAIN-2A/u
        );
    });

    it('is deeply frozen and preserves the checkpoint-only Git boundary', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_GRADUATION_REVIEW;
        assertDeepFrozen(review);
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedGraduationReview()
        );
        assert.equal(
            review.gitBoundary.rollbackEvidence,
            'proposal-and-ledger-checkpoints-recorded-before-delegation'
        );
        assert.equal(review.gitBoundary.localCheckpointRequired, true);
        assert.equal(
            review.gitBoundary.exactStagedDiffReviewRequired,
            true
        );
        assert.equal(
            review.gitBoundary.pushMergePublishAuthorized,
            false
        );
        assert.equal(review.gitBoundary.cleanupAuthorized, false);
    });

    it('rejects decision, proposal, zero-delta, and Git drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'explicit-human-decision';
            },
            'DISPLAYED_GRADUATION_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.successorStress
                    .requiredCorpus.negative.pop();
            },
            'DISPLAYED_GRADUATION_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.expectedDelta.transferEntries = 1;
            },
            'DISPLAYED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
