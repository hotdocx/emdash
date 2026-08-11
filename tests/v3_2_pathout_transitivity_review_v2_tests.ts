/**
 * Focused separate-review tests for corrected PathOut transitivity v2.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
} from '../src/v3_2/pathout_transitivity_proposal_v2';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2,
    CorePathoutTransitivity1eReviewV2,
    CorePathoutTransitivity1eReviewV2Error,
    cloneCorePathoutTransitivity1eReviewV2,
    validateCorePathoutTransitivity1eReviewV2
} from '../src/v3_2/pathout_transitivity_review_v2';

const repositoryRoot = resolve(__dirname, '..');

const assertReviewError = (
    mutate: (review: CorePathoutTransitivity1eReviewV2) => void,
    expected: CorePathoutTransitivity1eReviewV2Error['code']
): void => {
    const review = cloneCorePathoutTransitivity1eReviewV2();
    mutate(review);
    assert.throws(
        () => validateCorePathoutTransitivity1eReviewV2(review),
        error =>
            error instanceof CorePathoutTransitivity1eReviewV2Error &&
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

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E corrected v2 review', () => {
    it('approves only checkpoint b1e6f0f under delegated authority', () => {
        const review = validateCorePathoutTransitivity1eReviewV2();
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
                'b1e6f0f',
                '139dbc75984f229e879ac93ee01e2dafc' +
                    '8b39982ca19f5ea9120836b0f9c2b1c',
                'user-delegated-unattended-approval',
                true,
                'f60b36a'
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v2 proposal', () => {
        const review = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2.exactImplementation
        );
    });

    it('authorizes exactly one local support and five definitions', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.localRuntimeSupportRuleCount,
                authorization.localProofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.exactLocalRuntimeSupportRuleAuthorized,
                authorization.exactLocalRuntimeSupportRuleId,
                authorization.localRuntimeSupportMustRemainDerived,
                authorization.localRuntimeSupportMustRemainCompleteParent,
                authorization.localRuntimeSupportMustSubjectCheck,
                authorization
                    .localRuntimeSupportMustCompileAfterFiveDefinitions
            ],
            [
                0,
                1,
                0,
                5,
                true,
                CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
                true,
                true,
                true,
                true
            ]
        );
    });

    it('authorizes inherited proof reuse without a new proof rule', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2.authorization;
        assert.deepEqual(
            [
                authorization.inheritedProofProviderCount,
                authorization.inheritedProofProviderReuseAuthorized,
                authorization.inheritedProofProviderId,
                authorization
                    .inheritedProofProviderMustRecheckAgainstFinalEnvironment,
                authorization.newProofRuleAuthorized,
                authorization.genericPiToFunctordRuntimeCollapseAuthorized
            ],
            [
                1,
                true,
                'stress.sigma-pi.uncurrying',
                true,
                false,
                false
            ]
        );
    });

    it('denies broad, generic, public, and external widening', () => {
        const authorization =
            CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2.authorization;
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
            'PATHOUT_TRANSITIVITY_REVIEW_V2_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V2_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericRuntimeRuleAuthorized: boolean;
                }).genericRuntimeRuleAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_REVIEW_V2_AUTHORIZATION_DRIFT'
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
                /pathout_transitivity_review_v2|TRANSITIVITY_1E_REVIEW_V2/u,
                path
            );
        }
    });
});
