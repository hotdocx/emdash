/**
 * Focused separate-review tests for corrected internalized PathInd v10.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10
} from '../src/v3_2/pathind_internalized_proposal_v10';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10,
    CorePathindInternalized1dReviewV10,
    CorePathindInternalized1dReviewV10Error,
    validateCorePathindInternalized1dReviewV10
} from '../src/v3_2/pathind_internalized_review_v10';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV10 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10
    )) as CorePathindInternalized1dReviewV10;

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
    mutate: (review: CorePathindInternalized1dReviewV10) => void,
    expected: CorePathindInternalized1dReviewV10Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV10(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV10Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v10 separate review', () => {
    it('approves only checkpoint 270da40 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV10();
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
                '270da40',
                '898cbcd3d56859ae69c0b8646f45bc5792ff5205739720289c22699f3435324b',
                'a735c40',
                '7b466d5',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v10 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10.exactImplementation
        );
    });

    it('authorizes exactly the staged five-support boundary', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10.authorization;
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
            [4, 10, 5, 5, 0, 10, 9, 3, 1, 4]
        );
        assert.equal(
            authorization.stagedSourceFibreFusionRuleId,
            'pathind.internalized.' +
                'path-ind-source-fibre-at-sigma-pair-presentation-fusion'
        );
        assert.equal(
            authorization.sourceFibreFusionMustCompileAfterPrefix,
            true
        );
    });

    it('requires e560551 and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites.sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.declarationOrderPreserved,
                authorization.sourceFibreFusionBeforePrefixAuthorized
            ],
            ['e560551', true, true, false]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.declarationBodyOrTypeChangeAuthorized,
                authorization.declarationSourceOrderChangeAuthorized,
                authorization.underlyingCategoryEqualityAuthorized,
                authorization.genericSigmaFibreRuleAuthorized,
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
            'PATHIND_INTERNALIZED_REVIEW_V10_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V10_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V10_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_review_v10|REVIEW_V10/u,
                path
            );
        }
    });
});
