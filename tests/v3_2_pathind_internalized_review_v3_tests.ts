/**
 * Focused separate review tests for corrected internalized PathInd v3.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3
} from '../src/v3_2/pathind_internalized_proposal_v3';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3,
    CorePathindInternalized1dReviewV3,
    CorePathindInternalized1dReviewV3Error,
    validateCorePathindInternalized1dReviewV3
} from '../src/v3_2/pathind_internalized_review_v3';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV3 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3
    )) as CorePathindInternalized1dReviewV3;

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
    mutate: (review: CorePathindInternalized1dReviewV3) => void,
    expected: CorePathindInternalized1dReviewV3Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV3(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV3Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v3 separate review', () => {
    it('approves only checkpoint 5a1d635 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV3();
        assertDeepFrozen(review);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.supersededProposalCheckpoint,
                review.approval.supersededReviewCheckpoint,
                review.approval.authority,
                review.approval.humanDecisionSupersedes
            ],
            [
                '5a1d635',
                '4c9b60411a7b1c98b3da44fdd6919360a3cf65a18e862c163d5f911a214308e3',
                'fbfc4dd',
                '2a250fb',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v3 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3.exactImplementation
        );
    });

    it('authorizes one post-prefix support replacement at 4/5/0/10',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3.authorization;
            assert.deepEqual(
                [
                    authorization.trustedDeclarationCount,
                    authorization.runtimeRuleCount,
                    authorization.mathematicalRuntimeProjectionCount,
                    authorization.derivedRuntimeSupportRuleCount,
                    authorization.proofRuleCount,
                    authorization.transparentDefinitionCount,
                    authorization.componentPostPrefixSubjectFusionAuthorized,
                    authorization
                        .componentPostPrefixSubjectFusionIsMathematicalRule,
                    authorization.v2PrePrefixSubjectFusionRetained,
                    authorization.additionalRuntimeRuleAuthorized
                ],
                [4, 5, 4, 1, 0, 10, true, false, false, false]
            );
            assert.equal(
                authorization.componentPostPrefixSubjectFusionRuleId,
                'pathind.internalized.' +
                    'path-ind-functor-component-post-prefix-subject-fusion'
            );
        });

    it('denies generic widening, failed substitutes, and later effects',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3.authorization;
            assert.deepEqual(
                [
                    authorization.genericRuntimeMatcherChangeAuthorized,
                    authorization.genericCheckerChangeAuthorized,
                    authorization.inheritedProofProgramDependencyAuthorized,
                    authorization
                        .genericFixedEvaluationRuntimeImportAuthorized,
                    authorization.alternatePathIndTypeAuthorized,
                    authorization.alternatePathIndComponentBodyAuthorized,
                    authorization.retainedTemporaryObserverAuthorized,
                    authorization.wholeScaleStress2b3ImportAuthorized,
                    authorization.externalNaturalitySquareAuthorized,
                    authorization.transitivityDefinitionsAuthorized,
                    authorization.newCoreOrCheckerPrimitiveAuthorized,
                    authorization.browserOrPublicPackageExportAuthorized,
                    authorization.activeLambdapiSourceChangeAuthorized,
                    authorization.externalIntegrationOrReleaseAuthorized
                ],
                Array.from({ length: 14 }, () => false)
            );
        });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V3_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V3_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    v2PrePrefixSubjectFusionRetained: boolean;
                }).v2PrePrefixSubjectFusionRetained = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V3_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_review_v3|REVIEW_V3/u,
                    path
                );
            }
        });
});
