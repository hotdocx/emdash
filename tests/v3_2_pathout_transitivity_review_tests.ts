/**
 * Focused separate-review tests for PathOut transitivity.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
} from '../src/v3_2/pathout_transitivity_proposal';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW,
    CorePathoutTransitivity1eReview,
    CorePathoutTransitivity1eReviewError,
    cloneCorePathoutTransitivity1eReview,
    validateCorePathoutTransitivity1eReview
} from '../src/v3_2/pathout_transitivity_review';

const repositoryRoot = resolve(__dirname, '..');

const assertReviewError = (
    mutate: (review: CorePathoutTransitivity1eReview) => void,
    expected: CorePathoutTransitivity1eReviewError['code']
): void => {
    const review = cloneCorePathoutTransitivity1eReview();
    mutate(review);
    assert.throws(
        () => validateCorePathoutTransitivity1eReview(review),
        error =>
            error instanceof CorePathoutTransitivity1eReviewError &&
            error.code === expected
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E separate review', () => {
    it('approves only checkpoint 50b9a56 under delegated authority', () => {
        const review = validateCorePathoutTransitivity1eReview();
        assertDeepFrozen(review);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.authority,
                review.approval.humanDecisionSupersedes
            ],
            [
                '50b9a56',
                '1951ff30d42ab95dfa9d77fadb747be9e' +
                    'ca3c4bf760a99ab283da07fc1351bfb',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing proposal', () => {
        const review = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL.exactImplementation
        );
    });

    it('authorizes exactly five checked transparent definitions', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.requiredExistingProviderCount,
                authorization.typedLibraryConsumerCount,
                authorization.selectedDefinitionalObservationCount,
                authorization.negativeConsumerCount,
                authorization.boundedOracleAssertionCount
            ],
            [0, 0, 0, 5, 11, 2, 8, 8, 8]
        );
        assert.equal(
            authorization.sourceInjectiveModifierIsMetadataOnly,
            true
        );
    });

    it('denies every semantic and presentation widening', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.typescriptInjectivityOrUnificationAuthorized,
                authorization.intrinsicCoreOwnerAuthorized,
                authorization.genericCheckerChangeAuthorized,
                authorization.genericEvaluatorChangeAuthorized,
                authorization.runtimeRuleAuthorized,
                authorization.proofRuleAuthorized,
                authorization.pathCategoryBridgeAuthorized,
                authorization.rawCompositionRuntimeCollapseAuthorized,
                authorization.textSyntaxAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            Array.from({ length: 12 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .transparentDefinitions as unknown as unknown[]
                ).pop();
            },
            'PATHOUT_TRANSITIVITY_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    runtimeRuleAuthorized: boolean;
                }).runtimeRuleAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
        () => {
            for (const path of [
                'src/v3_2/index.ts',
                'src/v3_2/package_core.ts',
                'src/v3_2/package_authoring.ts',
                'src/v3_2/package_workspace.ts',
                'src/v3_2/browser.ts'
            ]) {
                assert.doesNotMatch(
                    readFileSync(resolve(repositoryRoot, path), 'utf8'),
                    /pathout_transitivity_review|TRANSITIVITY_1E_REVIEW/u,
                    path
                );
            }
        });
});
