/**
 * Focused separate-review tests for corrected PATHIND proposal v7.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7
} from '../src/v3_2/pathind_fixed_source_proposal_v7';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V7,
    CorePathindFixedSource1cReviewV7,
    CorePathindFixedSource1cReviewV7Error,
    validateCorePathindFixedSource1cReviewV7
} from '../src/v3_2/pathind_fixed_source_review_v7';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV7 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V7
    )) as CorePathindFixedSource1cReviewV7;

const assertReviewError = (
    mutate: (review: CorePathindFixedSource1cReviewV7) => void,
    expected: CorePathindFixedSource1cReviewV7Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV7(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV7Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v7 review', () => {
    it('approves only checkpointed v7 and supersedes v6 review', () => {
        const review = validateCorePathindFixedSource1cReviewV7();
        assert.equal(Object.isFrozen(review), true);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.supersededProposalCheckpoint,
                review.approval.supersededReviewCheckpoint,
                review.approval.authority,
                review.approval.humanDecisionSupersedes,
                review.recommendation.revision,
                review.recommendation.decision.implementationAuthorized
            ],
            [
                'f0fd4a6',
                'b41c3b0',
                '9b22034',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-7',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7
        );
    });

    it('authorizes exactly the root-only 5/12/0/6 correction', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V7.authorization;
        assert.deepEqual(
            [
                authorization.implementationAuthorized,
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.typedLibraryConsumerCount,
                authorization.negativeConsumerCount,
                authorization.selectedRuntimeObservationCount,
                authorization.boundedOracleAssertionCount,
                authorization
                    .fixedEvaluationSourcePresentationFusionAuthorized,
                authorization
                    .fixedEvaluationSourcePresentationFusionAuthorityLines
            ],
            [
                true, 5, 12, 0, 6, 1, 8, 5, 9, true,
                [5457, 19067, 19068, 19069, 19072]
            ]
        );
    });

    it('preserves engine, category-collapse, and public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V7.authorization;
        assert.deepEqual(
            [
                authorization
                    .directRuntimeFunctorCategoryCollapseAuthorized,
                authorization.genericDeclarationProofIntegrationAuthorized,
                authorization.genericDeclarationUnfoldingAuthorized,
                authorization.genericNestedRuntimeNormalizationAuthorized,
                authorization.genericCheckerChangeAuthorized,
                authorization.PathIndFuncAuthorized,
                authorization.PathIndTransfdAuthorized,
                authorization.internalizedPathInductionAuthorized,
                authorization.transitivityDefinitionsAuthorized,
                authorization.newCoreOrCheckerPrimitiveAuthorized,
                authorization.ordinarySafeLibraryRuleRegistrationAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            [
                false, false, false, false, false, false, false,
                false, false, false, false, false, false, false
            ]
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V7_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V7_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    directRuntimeFunctorCategoryCollapseAuthorized: boolean;
                }).directRuntimeFunctorCategoryCollapseAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V7_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v7/u,
                path
            );
        }
    });
});
