/**
 * Focused separate-review tests for corrected PATHIND proposal v3.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3
} from '../src/v3_2/pathind_fixed_source_proposal_v3';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V3,
    CorePathindFixedSource1cReviewV3,
    CorePathindFixedSource1cReviewV3Error,
    validateCorePathindFixedSource1cReviewV3
} from '../src/v3_2/pathind_fixed_source_review_v3';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV3 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V3
    )) as CorePathindFixedSource1cReviewV3;

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
    mutate: (review: CorePathindFixedSource1cReviewV3) => void,
    expected: CorePathindFixedSource1cReviewV3Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV3(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV3Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v3 review', () => {
    it('approves only checkpointed v3 and supersedes v2 review', () => {
        const review = validateCorePathindFixedSource1cReviewV3();
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
                'bfe09e3',
                '7413dd6',
                '3421647',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-3',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3
        );
    });

    it('authorizes exactly the root-only 5/8/0/6 correction', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V3.authorization;
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
                authorization.exactActiveFibreSignaturesRequired,
                authorization.homConObjectProjectionAuthorized,
                authorization.displayedFunctorObjectProjectionAuthorized
            ],
            [true, 5, 8, 0, 6, 1, 8, 5, 9, true, true, true]
        );
    });

    it('preserves signature, checker, and later/public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V3.authorization;
        assert.deepEqual(
            [
                authorization.genericCheckerChangeAuthorized,
                authorization.alternateFibCovBodyAuthorized,
                authorization.canonicalSignatureSubstitutionAuthorized,
                authorization.duplicateClassifierDeclarationAuthorized,
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
                false, false, false, false, false]
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V3_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V3_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    canonicalSignatureSubstitutionAuthorized: boolean;
                }).canonicalSignatureSubstitutionAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V3_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v3/u,
                path
            );
        }
    });
});
