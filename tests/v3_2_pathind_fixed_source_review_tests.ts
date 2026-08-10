/**
 * Focused separate-review tests for PATHIND-TRUSTED-PROFILE-1C.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
} from '../src/v3_2/pathind_fixed_source_proposal';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW,
    CorePathindFixedSource1cReview,
    CorePathindFixedSource1cReviewError,
    validateCorePathindFixedSource1cReview
} from '../src/v3_2/pathind_fixed_source_review';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReview =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW
    )) as CorePathindFixedSource1cReview;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertReviewError = (
    mutate: (review: CorePathindFixedSource1cReview) => void,
    expected: CorePathindFixedSource1cReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReview(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewError &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C separate review', () => {
    it('approves only checkpointed proposal v1 under delegated authority',
        () => {
            const review = validateCorePathindFixedSource1cReview();
            assertDeepFrozen(review);
            assert.deepEqual(
                [
                    review.approval.approvedProposalCheckpoint,
                    review.approval.authority,
                    review.approval.humanDecisionSupersedes,
                    review.recommendation.revision,
                    review.recommendation.decision.implementationAuthorized
                ],
                [
                    'cc639fc',
                    'user-delegated-unattended-approval',
                    true,
                    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-1',
                    false
                ]
            );
            assert.deepEqual(
                review.recommendation,
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
            );
        });

    it('authorizes exactly the root-only 5/6/0/6 implementation',
        () => {
            const authorization =
                CORE_PATHIND_FIXED_SOURCE_1C_REVIEW.authorization;
            assert.deepEqual(
                [
                    authorization.implementationAuthorized,
                    authorization.trustedDeclarationCount,
                    authorization.runtimeRuleCount,
                    authorization.proofRuleCount,
                    authorization.transparentDefinitionCount,
                    authorization.typedLibraryConsumerCount,
                    authorization.negativeConsumerCount,
                    authorization.boundedOracleAssertionCount,
                    authorization.genericEnginesOnly,
                    authorization.rootOnlyQualification
                ],
                [true, 5, 6, 0, 6, 1, 8, 7, true, true]
            );
        });

    it('preserves every later-layer and public denial', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.PathIndFuncAuthorized,
                authorization.PathIndTransfdAuthorized,
                authorization.internalizedPathInductionAuthorized,
                authorization.transitivityDefinitionsAuthorized,
                authorization.pathCategoryProofBridgeAuthorized,
                authorization.newCoreOrCheckerPrimitiveAuthorized,
                authorization.ordinarySafeLibraryRuleRegistrationAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            [false, false, false, false, false, false, false, false, false,
                false]
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    internalizedPathInductionAuthorized: boolean;
                }).internalizedPathInductionAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, or browser barrels', () => {
        for (
            const path of [
                'src/v3_2/index.ts',
                'src/v3_2/package_core.ts',
                'src/v3_2/package_authoring.ts',
                'src/v3_2/package_workspace.ts',
                'src/v3_2/browser.ts'
            ]
        ) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, path), 'utf8'),
                /pathind_fixed_source_review|CORE_PATHIND_FIXED_SOURCE/u,
                path
            );
        }
    });
});
