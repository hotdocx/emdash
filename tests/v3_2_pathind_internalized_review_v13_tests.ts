/**
 * Focused separate-review tests for corrected internalized PathInd v13.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13
} from '../src/v3_2/pathind_internalized_proposal_v13';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13,
    CorePathindInternalized1dReviewV13,
    CorePathindInternalized1dReviewV13Error,
    validateCorePathindInternalized1dReviewV13
} from '../src/v3_2/pathind_internalized_review_v13';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV13 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13
    )) as CorePathindInternalized1dReviewV13;

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
    mutate: (review: CorePathindInternalized1dReviewV13) => void,
    expected: CorePathindInternalized1dReviewV13Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV13(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV13Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v13 separate review', () => {
    it('approves only checkpoint d77f0d7 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV13();
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
                'd77f0d7',
                '555b3d3f656a52d89ddbbd1a76f030d522b673b07918d2b0ed9bf708b313f2e1',
                '39abb02',
                '8833f8f',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v13 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13.exactImplementation
        );
    });

    it('authorizes the one-for-one post-delta boundary only', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.baseRuntimeRuleCount,
                authorization.extensionRuntimeRuleCount,
                authorization.semanticCountDeltaFromV12,
                authorization.v12PreDeltaFusionRetained
            ],
            [4, 12, 5, 7, 0, 10, 9, 3, 0, false]
        );
        assert.equal(
            authorization.pathoutPiTransportPostDeltaFusionRuleId,
            'pathind.internalized.' +
                'pathout-pi-transport-post-delta-presentation-fusion'
        );
    });

    it('requires the stable parent and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites.sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.pathoutPiTransportFusionUsesStablePostDeltaType,
                authorization
                    .pathoutPiTransportFusionClosesCompleteFunctorParent,
                authorization
                    .pathoutPiTransportFusionUsesActiveSectionFacadeOnly,
                authorization
                    .pathoutPiTransportFusionUsesActiveSectionPullbackOnly
            ],
            ['e560551', true, true, true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.additionalRuntimeRuleAuthorized,
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
            Array.from({ length: 20 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V13_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V13_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V13_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_review_v13|REVIEW_V13/u,
                path
            );
        }
    });
});
