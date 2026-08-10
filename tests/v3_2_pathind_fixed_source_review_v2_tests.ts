/**
 * Focused separate-review tests for corrected PATHIND proposal v2.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
} from '../src/v3_2/pathind_fixed_source_proposal_v2';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V2,
    CorePathindFixedSource1cReviewV2,
    CorePathindFixedSource1cReviewV2Error,
    validateCorePathindFixedSource1cReviewV2
} from '../src/v3_2/pathind_fixed_source_review_v2';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV2 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V2
    )) as CorePathindFixedSource1cReviewV2;

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
    mutate: (review: CorePathindFixedSource1cReviewV2) => void,
    expected: CorePathindFixedSource1cReviewV2Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV2(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV2Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v2 review', () => {
    it('approves only checkpointed v2 and supersedes v1 review', () => {
        const review = validateCorePathindFixedSource1cReviewV2();
        assertDeepFrozen(review);
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
                '7413dd6',
                'cc639fc',
                '2deae91',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-2',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
        );
    });

    it('authorizes exactly the root-only 5/7/0/6 correction', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V2.authorization;
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
                authorization.genericEnginesOnly,
                authorization.rootOnlyQualification,
                authorization.homConObjectProjectionAuthorized
            ],
            [true, 5, 7, 0, 6, 1, 8, 4, 8, true, true, true]
        );
    });

    it('preserves checker, alternate-body, and later/public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V2.authorization;
        assert.deepEqual(
            [
                authorization.genericCheckerChangeAuthorized,
                authorization.alternateFibCovBodyAuthorized,
                authorization.duplicateHomConDeclarationAuthorized,
                authorization.PathIndFuncAuthorized,
                authorization.PathIndTransfdAuthorized,
                authorization.internalizedPathInductionAuthorized,
                authorization.transitivityDefinitionsAuthorized,
                authorization.pathCategoryProofBridgeAuthorized,
                authorization.newCoreOrCheckerPrimitiveAuthorized,
                authorization.ordinarySafeLibraryRuleRegistrationAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            [false, false, false, false, false, false, false, false, false,
                false, false, false, false]
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V2_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V2_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V2_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v2/u,
                path
            );
        }
    });
});
