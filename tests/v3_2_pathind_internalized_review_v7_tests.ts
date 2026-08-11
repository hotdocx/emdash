/**
 * Focused separate-review tests for corrected internalized PathInd v7.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7
} from '../src/v3_2/pathind_internalized_proposal_v7';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7,
    CorePathindInternalized1dReviewV7,
    CorePathindInternalized1dReviewV7Error,
    validateCorePathindInternalized1dReviewV7
} from '../src/v3_2/pathind_internalized_review_v7';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV7 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7
    )) as CorePathindInternalized1dReviewV7;

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
    mutate: (review: CorePathindInternalized1dReviewV7) => void,
    expected: CorePathindInternalized1dReviewV7Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV7(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV7Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v7 separate review', () => {
    it('approves only checkpoint ef761e4 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV7();
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
                'ef761e4',
                'e56b79f367dd7d92cae10a649a6f9cb5e13c563ddc39f4e4812b32ed2a270313',
                '19eb941',
                '2112543',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v7 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7.exactImplementation
        );
    });

    it('authorizes five projections plus four supports at 4/9/0/10', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.exactFiveMathematicalProjectionsAuthorized,
                authorization.exactFourDerivedSupportRulesAuthorized
            ],
            [4, 9, 5, 4, 0, 10, true, true]
        );
        assert.equal(
            authorization
                .motiveTransportActionCategoryPresentationFusionRuleId,
            'pathind.internalized.' +
                'motive-transport-action-category-presentation-fusion'
        );
    });

    it('requires e560551 and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites
                    .sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.genericPrerequisites
                    .originalSourceRootReplayRequired,
                authorization.genericPrerequisites
                    .exactRequestedBudgetPropagationRequired
            ],
            ['e560551', true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.underlyingCategoryCollapseAuthorized,
                authorization.genericActionCategoryFusionAuthorized,
                authorization.genericDeclarationProofIntegrationAuthorized,
                authorization.genericRuntimeMatcherChangeAuthorized,
                authorization.genericCheckerChangeAuthorized,
                authorization.pathIndSpecificComparisonBudgetAuthorized,
                authorization.retainedTemporaryObserverAuthorized,
                authorization.wholeScaleStress2b3ImportAuthorized,
                authorization.transitivityDefinitionsAuthorized,
                authorization.newCoreOrCheckerPrimitiveAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            Array.from({ length: 15 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V7_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V7_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V7_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels', () => {
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
                /pathind_internalized_review_v7|REVIEW_V7/u,
                path
            );
        }
    });
});
