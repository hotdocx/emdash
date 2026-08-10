/**
 * Focused separate-review tests for corrected PATHIND proposal v4.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4
} from '../src/v3_2/pathind_fixed_source_proposal_v4';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V4,
    CorePathindFixedSource1cReviewV4,
    CorePathindFixedSource1cReviewV4Error,
    validateCorePathindFixedSource1cReviewV4
} from '../src/v3_2/pathind_fixed_source_review_v4';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV4 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V4
    )) as CorePathindFixedSource1cReviewV4;

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
    mutate: (review: CorePathindFixedSource1cReviewV4) => void,
    expected: CorePathindFixedSource1cReviewV4Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV4(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV4Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v4 review', () => {
    it('approves only checkpointed v4 and supersedes v3 review', () => {
        const review = validateCorePathindFixedSource1cReviewV4();
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
                'f4101e2',
                'bfe09e3',
                '880593e',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-4',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4
        );
    });

    it('authorizes exactly the root-only 5/9/0/6 correction', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V4.authorization;
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
                authorization.displayedFunctorObjectProjectionAuthorized,
                authorization.displayedHomObjectFusionAuthorized,
                authorization.displayedHomObjectFusionAuthorityLines
            ],
            [
                true, 5, 9, 0, 6, 1, 8, 5, 9, true, true, true, true,
                [5481, 9177]
            ]
        );
    });

    it('preserves normalization, checker, and later/public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V4.authorization;
        assert.deepEqual(
            [
                authorization.genericNestedRuntimeNormalizationAuthorized,
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
            [
                false, false, false, false, false, false, false, false,
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
            'PATHIND_FIXED_SOURCE_REVIEW_V4_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V4_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericNestedRuntimeNormalizationAuthorized: boolean;
                }).genericNestedRuntimeNormalizationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V4_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v4/u,
                path
            );
        }
    });
});
