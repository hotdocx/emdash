/**
 * Focused separate-review tests for corrected internalized PathInd v12.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12
} from '../src/v3_2/pathind_internalized_proposal_v12';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V12,
    CorePathindInternalized1dReviewV12,
    CorePathindInternalized1dReviewV12Error,
    validateCorePathindInternalized1dReviewV12
} from '../src/v3_2/pathind_internalized_review_v12';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV12 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V12
    )) as CorePathindInternalized1dReviewV12;

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
    mutate: (review: CorePathindInternalized1dReviewV12) => void,
    expected: CorePathindInternalized1dReviewV12Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV12(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV12Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v12 separate review', () => {
    it('approves only checkpoint 39abb02 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV12();
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
                '39abb02',
                'b8e3e43438bc4bb3d8c3c9b9223ee45e58eab8fc13f6df5dfdf240f81df5e5e9',
                '2e1e593',
                '731dc32',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v12 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V12;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12.exactImplementation
        );
    });

    it('authorizes exactly the staged seven-support boundary', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V12.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.baseRuntimeRuleCount,
                authorization.prefixTransparentDefinitionCount,
                authorization.extensionRuntimeRuleCount,
                authorization.suffixTransparentDefinitionCount
            ],
            [4, 12, 5, 7, 0, 10, 9, 3, 3, 4]
        );
        assert.equal(
            authorization
                .pathoutPiTransportFunctorPresentationFusionRuleId,
            'pathind.internalized.' +
                'pathout-pi-transport-functor-presentation-fusion'
        );
    });

    it('requires existing authority and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V12.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites.sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization
                    .pathoutPiTransportFusionClosesCompleteFunctorParent,
                authorization
                    .pathoutPiTransportFusionUsesActiveSectionFacadeOnly,
                authorization
                    .pathoutPiTransportFusionUsesActiveSectionPullbackOnly
            ],
            ['e560551', true, true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.declarationBodyOrTypeChangeAuthorized,
                authorization.declarationSourceOrderChangeAuthorized,
                authorization.underlyingCategoryEqualityAuthorized,
                authorization.genericSectionCategoryRuntimeRuleAuthorized,
                authorization.genericPullbackRuleChangeAuthorized,
                authorization.genericComparisonChangeAuthorized,
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
            Array.from({ length: 19 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V12_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V12_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V12_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_review_v12|REVIEW_V12/u,
                path
            );
        }
    });
});
