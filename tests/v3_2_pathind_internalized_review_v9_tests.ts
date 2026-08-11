/**
 * Focused separate-review tests for corrected internalized PathInd v9.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9
} from '../src/v3_2/pathind_internalized_proposal_v9';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V9,
    CorePathindInternalized1dReviewV9,
    CorePathindInternalized1dReviewV9Error,
    validateCorePathindInternalized1dReviewV9
} from '../src/v3_2/pathind_internalized_review_v9';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV9 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V9
    )) as CorePathindInternalized1dReviewV9;

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
    mutate: (review: CorePathindInternalized1dReviewV9) => void,
    expected: CorePathindInternalized1dReviewV9Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV9(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV9Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v9 separate review', () => {
    it('approves only checkpoint a735c40 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV9();
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
                'a735c40',
                'a216b88d16fbd28bae647a294e8026b1a7b1b650ce32301992d66c8652331cbd',
                'f26d340',
                '1de3c95',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v9 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V9;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9.exactImplementation
        );
    });

    it('authorizes the corrected five-support boundary', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V9.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.exactFiveMathematicalProjectionsAuthorized,
                authorization.exactFiveDerivedSupportRulesAuthorized
            ],
            [4, 10, 5, 5, 0, 10, true, true]
        );
        assert.equal(
            authorization.postSigmaSourceFibreFusionRuleId,
            'pathind.internalized.' +
                'path-ind-source-fibre-post-sigma-projection-fusion'
        );
    });

    it('requires e560551 and denies boundary widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V9.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites
                    .sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.postSigmaSourceFibreFusionUsesOnlyEarlierDeclarations,
                authorization.v8PreDeltaPathIndSrcGlobalRuleRejected
            ],
            ['e560551', true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.laterLibraryGlobalReferenceAuthorized,
                authorization.declarationRepartitionAuthorized,
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
            'PATHIND_INTERNALIZED_REVIEW_V9_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V9_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V9_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_review_v9|REVIEW_V9/u,
                path
            );
        }
    });
});
