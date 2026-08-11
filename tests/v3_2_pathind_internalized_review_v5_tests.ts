/**
 * Focused separate-review tests for corrected internalized PathInd v5.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5
} from '../src/v3_2/pathind_internalized_proposal_v5';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5,
    CorePathindInternalized1dReviewV5,
    CorePathindInternalized1dReviewV5Error,
    validateCorePathindInternalized1dReviewV5
} from '../src/v3_2/pathind_internalized_review_v5';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV5 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5
    )) as CorePathindInternalized1dReviewV5;

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
    mutate: (review: CorePathindInternalized1dReviewV5) => void,
    expected: CorePathindInternalized1dReviewV5Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV5(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV5Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v5 separate review', () => {
    it('approves only checkpoint fe0306d under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV5();
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
                'fe0306d',
                '9a9adef53c4d682def1528ff194fce11838bb4899de94169fa7fbe21f67eccda',
                '001a899',
                '7984efb',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v5 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5.exactImplementation
        );
    });

    it('authorizes five projections plus two supports at 4/7/0/10', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.exactFiveMathematicalProjectionsAuthorized,
                authorization.exactTwoDerivedSupportRulesAuthorized
            ],
            [4, 7, 5, 2, 0, 10, true, true]
        );
        assert.equal(
            authorization.piPullbackComponentProjectionRuleId,
            'pathind.internalized.pi-pullback-component'
        );
    });

    it('requires generic closure and denies every semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5.authorization;
        assert.equal(
            authorization.genericComparisonPrerequisite
                .semanticCheckpointRequiredBeforePathIndCheckpoint,
            true
        );
        assert.deepEqual(
            [
                authorization.newRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.pathIndSpecificOuterCommutingRuleAuthorized,
                authorization.overSpecifiedInferredFamilySlotsAuthorized,
                authorization.genericCategoryCollapseAuthorized,
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
            'PATHIND_INTERNALIZED_REVIEW_V5_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V5_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V5_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_review_v5|REVIEW_V5/u,
                    path
                );
            }
        });
});
