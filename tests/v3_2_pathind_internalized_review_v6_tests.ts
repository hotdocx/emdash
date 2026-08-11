/**
 * Focused separate-review tests for corrected internalized PathInd v6.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6
} from '../src/v3_2/pathind_internalized_proposal_v6';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6,
    CorePathindInternalized1dReviewV6,
    CorePathindInternalized1dReviewV6Error,
    validateCorePathindInternalized1dReviewV6
} from '../src/v3_2/pathind_internalized_review_v6';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV6 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6
    )) as CorePathindInternalized1dReviewV6;

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
    mutate: (review: CorePathindInternalized1dReviewV6) => void,
    expected: CorePathindInternalized1dReviewV6Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV6(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV6Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v6 separate review', () => {
    it('approves only checkpoint 19eb941 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV6();
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
                '19eb941',
                '5f9181e4db004e4a1922d2d5ec72ee6862c7dbeaa40a44ecb88423355bffcf17',
                'fe0306d',
                'a94c2f7',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v6 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6.exactImplementation
        );
    });

    it('authorizes five projections plus three supports at 4/8/0/10',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6.authorization;
            assert.deepEqual(
                [
                    authorization.trustedDeclarationCount,
                    authorization.runtimeRuleCount,
                    authorization.mathematicalRuntimeProjectionCount,
                    authorization.derivedRuntimeSupportRuleCount,
                    authorization.proofRuleCount,
                    authorization.transparentDefinitionCount,
                    authorization.exactFiveMathematicalProjectionsAuthorized,
                    authorization.exactThreeDerivedSupportRulesAuthorized
                ],
                [4, 8, 5, 3, 0, 10, true, true]
            );
            assert.equal(
                authorization.motiveTransportCategoryPresentationFusionRuleId,
                'pathind.internalized.' +
                    'motive-transport-functor-category-presentation-fusion'
            );
        });

    it('requires comparison v2 and denies generic semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6.authorization;
        assert.deepEqual(
            [
                authorization.genericComparisonPrerequisite
                    .proposalCheckpoint,
                authorization.genericComparisonPrerequisite
                    .reviewCheckpoint,
                authorization.genericComparisonPrerequisite
                    .originalSourceRootReplayRequired
            ],
            ['a42ffc9', '5277885', true]
        );
        assert.deepEqual(
            [
                authorization.newRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.underlyingCategoryCollapseAuthorized,
                authorization.genericTwoSidedCategoryFusionAuthorized,
                authorization.genericDeclarationProofIntegrationAuthorized,
                authorization.genericRuntimeMatcherChangeAuthorized,
                authorization.genericCheckerChangeAuthorized,
                authorization.retainedTemporaryObserverAuthorized,
                authorization.wholeScaleStress2b3ImportAuthorized,
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
            'PATHIND_INTERNALIZED_REVIEW_V6_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V6_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V6_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_review_v6|REVIEW_V6/u,
                    path
                );
            }
        });
});
