/**
 * Focused separate-review tests for corrected PATHIND proposal v8.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8
} from '../src/v3_2/pathind_fixed_source_proposal_v8';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V8,
    CorePathindFixedSource1cReviewV8,
    CorePathindFixedSource1cReviewV8Error,
    validateCorePathindFixedSource1cReviewV8
} from '../src/v3_2/pathind_fixed_source_review_v8';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV8 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V8
    )) as CorePathindFixedSource1cReviewV8;

const assertReviewError = (
    mutate: (review: CorePathindFixedSource1cReviewV8) => void,
    expected: CorePathindFixedSource1cReviewV8Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV8(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV8Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v8 review', () => {
    it('approves only checkpointed v8 and supersedes v7 review', () => {
        const review = validateCorePathindFixedSource1cReviewV8();
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
                '65656e5',
                'f0fd4a6',
                '0cefb73',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-8',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8
        );
    });

    it('authorizes exact replacement at root-only 5/12/0/6', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V8.authorization;
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
                    .fixedEvaluationPostDeltaPresentationFusionAuthorized,
                authorization
                    .fixedEvaluationPostDeltaPresentationFusionAuthorityLines,
                authorization.v7PreDeltaFusionRetained,
                authorization.thirteenthRuntimeRuleAuthorized
            ],
            [
                true, 5, 12, 0, 6, 1, 8, 5, 9, true,
                [3316, 3317, 5457, 19067, 19068, 19069, 19072],
                false, false
            ]
        );
    });

    it('preserves trace, engine, category, and public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V8.authorization;
        assert.deepEqual(
            [
                authorization.diagnosticWrapperAuthorized,
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
                false, false, false, false, false, false, false, false
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
            'PATHIND_FIXED_SOURCE_REVIEW_V8_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V8_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    thirteenthRuntimeRuleAuthorized: boolean;
                }).thirteenthRuntimeRuleAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V8_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v8/u,
                path
            );
        }
    });
});
