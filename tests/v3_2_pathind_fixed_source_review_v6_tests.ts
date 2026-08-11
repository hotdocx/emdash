/**
 * Focused separate-review tests for corrected PATHIND proposal v6.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6
} from '../src/v3_2/pathind_fixed_source_proposal_v6';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V6,
    CorePathindFixedSource1cReviewV6,
    CorePathindFixedSource1cReviewV6Error,
    validateCorePathindFixedSource1cReviewV6
} from '../src/v3_2/pathind_fixed_source_review_v6';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cReviewV6 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V6
    )) as CorePathindFixedSource1cReviewV6;

const assertReviewError = (
    mutate: (review: CorePathindFixedSource1cReviewV6) => void,
    expected: CorePathindFixedSource1cReviewV6Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindFixedSource1cReviewV6(review),
        error =>
            error instanceof CorePathindFixedSource1cReviewV6Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected v6 review', () => {
    it('approves only checkpointed v6 and supersedes v5 review', () => {
        const review = validateCorePathindFixedSource1cReviewV6();
        assert.equal(Object.isFrozen(review), true);
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
                'b41c3b0',
                '7219828',
                '3f95e7c',
                'user-delegated-unattended-approval',
                true,
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-6',
                false
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6
        );
    });

    it('authorizes exactly the root-only 5/11/0/6 correction', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V6.authorization;
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
                authorization.fibreCovariantTargetSectionFusionAuthorized,
                authorization
                    .fibreCovariantTargetSectionFusionAuthorityLines
            ],
            [
                true, 5, 11, 0, 6, 1, 8, 5, 9, true,
                [
                    5481, 7865, 8419, 9177, 13765,
                    13767, 13773, 13775, 13923, 13928
                ]
            ]
        );
    });

    it('preserves diagnostic, engine, and later/public denials', () => {
        const authorization =
            CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V6.authorization;
        assert.deepEqual(
            [
                authorization.genericDeclarationUnfoldingAuthorized,
                authorization.retainedCheckerDiagnosticAuthorized,
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
                false, false, false
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
            'PATHIND_FIXED_SOURCE_REVIEW_V6_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V6_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericDeclarationUnfoldingAuthorized: boolean;
                }).genericDeclarationUnfoldingAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_REVIEW_V6_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_review_v6/u,
                path
            );
        }
    });
});
