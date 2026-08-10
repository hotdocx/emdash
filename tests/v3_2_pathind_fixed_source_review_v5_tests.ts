/**
 * Focused separate-review tests for corrected PATHIND proposal v5.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5
} from '../src/v3_2/pathind_fixed_source_proposal_v5';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V5,
    CorePathindFixedSource1cReviewV5,
    CorePathindFixedSource1cReviewV5Error,
    validateCorePathindFixedSource1cReviewV5
} from '../src/v3_2/pathind_fixed_source_review_v5';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV5 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V5
    )) as CorePathindFixedSource1cReviewV5;

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
    mutate: (review: CorePathindFixedSource1cReviewV5) => void,
    expected: CorePathindFixedSource1cReviewV5Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV5(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV5Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v5 review', () => {
    it('approves only checkpointed v5 and supersedes v4 review', () => {
        const review = validateCorePathindFixedSource1cReviewV5();
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
                '7219828',
                'f4101e2',
                '397472f',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-5',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5
        );
    });

    it('authorizes exactly the root-only 5/10/0/6 correction', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V5.authorization;
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
                authorization.transforClassifierDeltaAuthorized,
                authorization.transforClassifierDeltaAuthorityLines
            ],
            [true, 5, 10, 0, 6, 1, 8, 5, 9, true, [9150, 9151]]
        );
    });

    it('preserves engine, reduction, and later/public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V5.authorization;
        assert.deepEqual(
            [
                authorization.genericNestedRuntimeNormalizationAuthorized,
                authorization.wholeFibredProductRuntimeImportAuthorized,
                authorization.reversedTransforDeltaAuthorized,
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
                false, false, false, false, false, false, false, false,
                false
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
            'PATHIND_FIXED_SOURCE_REVIEW_V5_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V5_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    wholeFibredProductRuntimeImportAuthorized: boolean;
                }).wholeFibredProductRuntimeImportAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V5_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v5/u,
                path
            );
        }
    });
});
