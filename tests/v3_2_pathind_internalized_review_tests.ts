/**
 * Focused separate review tests for PATHOUT-LIBRARY-INTERNALIZED-1D.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL
} from '../src/v3_2/pathind_internalized_proposal';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW,
    CorePathindInternalized1dReview,
    CorePathindInternalized1dReviewError,
    validateCorePathindInternalized1dReview
} from '../src/v3_2/pathind_internalized_review';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReview =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW
    )) as CorePathindInternalized1dReview;

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
    mutate: (review: CorePathindInternalized1dReview) => void,
    expected: CorePathindInternalized1dReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReview(review),
        error =>
            error instanceof CorePathindInternalized1dReviewError &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D separate review', () => {
    it('approves only checkpoint 188b8e5 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReview();
        assertDeepFrozen(review);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.authority,
                review.approval.condition,
                review.approval.humanDecisionSupersedes
            ],
            [
                '188b8e5',
                'user-delegated-unattended-approval',
                'no-immediate-human-objection-after-proposal-checkpoint',
                true
            ]
        );
        assert.equal(
            review.approval.approvedProposalSha256,
            'da30d4fc2a9d54737e8fce9b0256e9b066b6b4f463d054d0d38741cdaedddd63'
        );
    });

    it('embeds the exact immutable proposal and predecessor boundary', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL.exactImplementation
        );
        assert.deepEqual(
            review.authorization.exactDependencyClosure,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL.dependencyClosure
        );
        assert.deepEqual(
            review.authorization.exactSelectedPredecessor,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL.selectedPredecessor
        );
    });

    it('authorizes exactly 4/4/0/10 through generic root-only engines',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW.authorization;
            assert.deepEqual(
                [
                    authorization.trustedDeclarationCount,
                    authorization.runtimeRuleCount,
                    authorization.proofRuleCount,
                    authorization.transparentDefinitionCount,
                    authorization.genericEnginesOnly,
                    authorization.rootOnlyQualification
                ],
                [4, 4, 0, 10, true, true]
            );
            assert.equal(authorization.primaryTheoremIsPathIndTransfd, true);
            assert.equal(
                authorization.pathIndFuncdIsTransparentDerivedPresentation,
                true
            );
            assert.equal(
                authorization.sourceArrowMustRemainInternallyOwned,
                true
            );
            assert.equal(
                authorization.higherActionMustRemainInternallyOwned,
                true
            );
        });

    it('denies every whole-profile, external-naturality, and later effect',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW.authorization;
            assert.deepEqual(
                [
                    authorization.wholeScaleStress2b3ImportAuthorized,
                    authorization.externalNaturalitySquareAuthorized,
                    authorization
                        .arbitraryNonCartesianSigmaNaturalityAuthorized,
                    authorization.transitivityDefinitionsAuthorized,
                    authorization.pathCategoryProofBridgeAuthorized,
                    authorization.newCoreOrCheckerPrimitiveAuthorized,
                    authorization
                        .ordinarySafeLibraryRuleRegistrationAuthorized,
                    authorization.textOrDeclarationParserAuthorized,
                    authorization.browserOrPublicPackageExportAuthorized,
                    authorization.activeLambdapiSourceChangeAuthorized,
                    authorization.externalIntegrationOrReleaseAuthorized
                ],
                [
                    false,
                    false,
                    false,
                    false,
                    false,
                    false,
                    false,
                    false,
                    false,
                    false,
                    false
                ]
            );
            assert.equal(
                CORE_PATHIND_INTERNALIZED_1D_REVIEW
                    .gitBoundary.pushMergePublishAuthorized,
                false
            );
        });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .transparentDefinitions as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    transitivityDefinitionsAuthorized: boolean;
                }).transitivityDefinitionsAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
        () => {
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
                    /pathind_internalized|CORE_PATHIND_INTERNALIZED/u,
                    path
                );
            }
        });
});
