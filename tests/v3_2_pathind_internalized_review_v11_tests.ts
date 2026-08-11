/**
 * Focused separate-review tests for corrected internalized PathInd v11.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11
} from '../src/v3_2/pathind_internalized_proposal_v11';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11,
    CorePathindInternalized1dReviewV11,
    CorePathindInternalized1dReviewV11Error,
    validateCorePathindInternalized1dReviewV11
} from '../src/v3_2/pathind_internalized_review_v11';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV11 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11
    )) as CorePathindInternalized1dReviewV11;

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
    mutate: (review: CorePathindInternalized1dReviewV11) => void,
    expected: CorePathindInternalized1dReviewV11Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV11(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV11Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v11 separate review', () => {
    it('approves only checkpoint 2e1e593 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV11();
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
                '2e1e593',
                '82fb6f02cf2be16b2dfe8b240ee6d4abcdacc2bfb2cb135b03affdc8bd3097d2',
                '270da40',
                '302c4a9',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v11 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11.exactImplementation
        );
    });

    it('authorizes exactly the staged six-support boundary', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11.authorization;
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
            [4, 11, 5, 6, 0, 10, 9, 3, 2, 4]
        );
        assert.equal(
            authorization.transportedMotiveReflexiveFibreFusionRuleId,
            'pathind.internalized.' +
                'transported-motive-reflexive-fibre-' +
                'presentation-fusion'
        );
    });

    it('requires existing authority and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites.sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.targetFibreFusionUsesActivePullbackFibreOnly,
                authorization.targetFibreFusionUsesQualifiedPathoutActionOnly
            ],
            ['e560551', true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.declarationBodyOrTypeChangeAuthorized,
                authorization.declarationSourceOrderChangeAuthorized,
                authorization.underlyingCategoryEqualityAuthorized,
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
            Array.from({ length: 18 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V11_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V11_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V11_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_review_v11|REVIEW_V11/u,
                path
            );
        }
    });
});
