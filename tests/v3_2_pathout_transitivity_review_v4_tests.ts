/**
 * Focused separate-review tests for corrected PathOut transitivity v4.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID
} from '../src/v3_2/pathout_transitivity_proposal_v3';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4
} from '../src/v3_2/pathout_transitivity_proposal_v4';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4,
    CorePathoutTransitivity1eReviewV4,
    CorePathoutTransitivity1eReviewV4Error,
    cloneCorePathoutTransitivity1eReviewV4,
    validateCorePathoutTransitivity1eReviewV4
} from '../src/v3_2/pathout_transitivity_review_v4';

const repositoryRoot = resolve(__dirname, '..');

const assertReviewError = (
    mutate: (review: CorePathoutTransitivity1eReviewV4) => void,
    expected: CorePathoutTransitivity1eReviewV4Error['code']
): void => {
    const review = cloneCorePathoutTransitivity1eReviewV4();
    mutate(review);
    assert.throws(
        () => validateCorePathoutTransitivity1eReviewV4(review),
        error =>
            error instanceof CorePathoutTransitivity1eReviewV4Error &&
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

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E corrected v4 review', () => {
    it('approves only checkpoint 2498053 under delegated authority', () => {
        const review = validateCorePathoutTransitivity1eReviewV4();
        assertDeepFrozen(review);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.authority,
                review.approval.humanDecisionSupersedes,
                review.approval.supersededReviewCheckpoint
            ],
            [
                '2498053',
                '820df96e9a0b889172c2e74fbcdc77cd' +
                    '16329dcaf36105d3c53076807e76394b',
                'user-delegated-unattended-approval',
                true,
                '0834d00'
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v4 proposal', () => {
        const review = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4.exactImplementation
        );
    });

    it('authorizes one consumer-parent replacement at 0/1/0/5', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.localRuntimeSupportRuleCount,
                authorization.localProofRuleCount,
                authorization.transparentDefinitionCount,
                authorization
                    .exactConsumerParentRuntimeSupportRuleAuthorized,
                authorization.exactConsumerParentRuntimeSupportRuleId,
                authorization.exactSupersededPostDeltaRuleId,
                authorization.postDeltaRuntimeSupportRetained,
                authorization.secondLocalRuntimeSupportRuleAuthorized
            ],
            [
                0,
                1,
                0,
                5,
                true,
                CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
                CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
                false,
                false
            ]
        );
        assert.equal(
            authorization
                .localRuntimeSupportMustMatchOriginalConsumerParent,
            true
        );
        assert.equal(
            authorization
                .localRuntimeSupportMustBeConsultedBeforeDescendantDelta,
            true
        );
    });

    it('authorizes scoped proof reuse and predecessor-name repair', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4.authorization;
        assert.deepEqual(
            [
                authorization.inheritedProofProviderCount,
                authorization.inheritedProofProviderReuseAuthorized,
                authorization.inheritedProofProviderId,
                authorization
                    .inheritedProofProviderMustRecheckAgainstFinalEnvironment,
                authorization
                    .inheritedProofHelperExplicitDescendantEnvironmentAuthorized,
                authorization.canonicalPredecessorCoreNameTestRepairAuthorized,
                authorization.newProofRuleAuthorized
            ],
            [
                1,
                true,
                'stress.sigma-pi.uncurrying',
                true,
                true,
                true,
                false
            ]
        );
    });

    it('denies broad, generic, public, and external widening', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4.authorization;
        assert.deepEqual(
            [
                authorization.genericRuntimeRuleAuthorized,
                authorization.broadHomConRuntimeImportAuthorized,
                authorization.wholeDisplayedIdentityDeltaAuthorized,
                authorization.wholeRepresentableFamilyDeltaAuthorized,
                authorization.typescriptInjectivityOrUnificationAuthorized,
                authorization.intrinsicCoreOwnerAuthorized,
                authorization.genericRuntimeMatcherChangeAuthorized,
                authorization.genericCheckerChangeAuthorized,
                authorization.genericEvaluatorChangeAuthorized,
                authorization.genericComparisonChangeAuthorized,
                authorization.pathCategoryBridgeAuthorized,
                authorization.rawCompositionRuntimeCollapseAuthorized,
                authorization.textSyntaxAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            Array.from({ length: 16 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V4_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V4_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    secondLocalRuntimeSupportRuleAuthorized: boolean;
                }).secondLocalRuntimeSupportRuleAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V4_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels', () => {
        for (const path of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, path), 'utf8'),
                /pathout_transitivity_review_v4|TRANSITIVITY_1E_REVIEW_V4/u,
                path
            );
        }
    });
});
