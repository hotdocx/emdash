/**
 * Focused separate-review tests for corrected PathOut transitivity v3.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID
} from '../src/v3_2/pathout_transitivity_proposal_v2';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
} from '../src/v3_2/pathout_transitivity_proposal_v3';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3,
    CorePathoutTransitivity1eReviewV3,
    CorePathoutTransitivity1eReviewV3Error,
    cloneCorePathoutTransitivity1eReviewV3,
    validateCorePathoutTransitivity1eReviewV3
} from '../src/v3_2/pathout_transitivity_review_v3';

const repositoryRoot = resolve(__dirname, '..');

const assertReviewError = (
    mutate: (review: CorePathoutTransitivity1eReviewV3) => void,
    expected: CorePathoutTransitivity1eReviewV3Error['code']
): void => {
    const review = cloneCorePathoutTransitivity1eReviewV3();
    mutate(review);
    assert.throws(
        () => validateCorePathoutTransitivity1eReviewV3(review),
        error =>
            error instanceof CorePathoutTransitivity1eReviewV3Error &&
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

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E corrected v3 review', () => {
    it('approves only checkpoint fe1a9b7 under delegated authority', () => {
        const review = validateCorePathoutTransitivity1eReviewV3();
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
                'fe1a9b7',
                '0d7448ae68d9aa6ae3bf91b9010a676f' +
                    '8ca3c9101976e1de2c88816a94e68dd9',
                'user-delegated-unattended-approval',
                true,
                '31f23db'
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v3 proposal', () => {
        const review = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3.exactImplementation
        );
    });

    it('authorizes one post-delta replacement at unchanged 0/1/0/5', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.localRuntimeSupportRuleCount,
                authorization.localProofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.exactPostDeltaRuntimeSupportRuleAuthorized,
                authorization.exactPostDeltaRuntimeSupportRuleId,
                authorization.exactSupersededPreDeltaRuleId,
                authorization.preDeltaRuntimeSupportRetained,
                authorization.secondLocalRuntimeSupportRuleAuthorized
            ],
            [
                0,
                1,
                0,
                5,
                true,
                CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
                CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
                false,
                false
            ]
        );
    });

    it('authorizes explicit descendant-scope inherited proof reuse', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3.authorization;
        assert.deepEqual(
            [
                authorization.inheritedProofProviderCount,
                authorization.inheritedProofProviderReuseAuthorized,
                authorization.inheritedProofProviderId,
                authorization
                    .inheritedProofProviderMustRecheckAgainstFinalEnvironment,
                authorization
                    .inheritedProofHelperExplicitDescendantEnvironmentAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.genericPiToFunctordRuntimeCollapseAuthorized
            ],
            [
                1,
                true,
                'stress.sigma-pi.uncurrying',
                true,
                true,
                false,
                false
            ]
        );
    });

    it('denies broad, generic, public, and external widening', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3.authorization;
        assert.deepEqual(
            [
                authorization.genericRuntimeRuleAuthorized,
                authorization.broadHomConRuntimeImportAuthorized,
                authorization.wholeDisplayedIdentityDeltaAuthorized,
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
            Array.from({ length: 15 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V3_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V3_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    secondLocalRuntimeSupportRuleAuthorized: boolean;
                }).secondLocalRuntimeSupportRuleAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V3_AUTHORIZATION_DRIFT'
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
                /pathout_transitivity_review_v3|TRANSITIVITY_1E_REVIEW_V3/u,
                path
            );
        }
    });
});
