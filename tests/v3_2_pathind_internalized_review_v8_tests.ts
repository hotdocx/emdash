/**
 * Focused separate-review tests for corrected internalized PathInd v8.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8
} from '../src/v3_2/pathind_internalized_proposal_v8';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V8,
    CorePathindInternalized1dReviewV8,
    CorePathindInternalized1dReviewV8Error,
    validateCorePathindInternalized1dReviewV8
} from '../src/v3_2/pathind_internalized_review_v8';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV8 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V8
    )) as CorePathindInternalized1dReviewV8;

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
    mutate: (review: CorePathindInternalized1dReviewV8) => void,
    expected: CorePathindInternalized1dReviewV8Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV8(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV8Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v8 separate review', () => {
    it('approves only checkpoint f26d340 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV8();
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
                'f26d340',
                '680f0cd0ec6ae7927843f1c0038ce552e2b3fa55aead71ccdec7b9b8ae4fe5af',
                'ef761e4',
                '8cdff35',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v8 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V8;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8.exactImplementation
        );
    });

    it('authorizes five projections plus five supports at 4/10/0/10', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V8.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.exactFiveMathematicalProjectionsAuthorized,
                authorization.exactFiveDerivedSupportRulesAuthorized
            ],
            [4, 10, 5, 5, 0, 10, true, true]
        );
        assert.equal(
            authorization
                .pathInductionSourceFibrePresentationFusionRuleId,
            'pathind.internalized.' +
                'path-ind-source-fibre-at-sigma-pair-presentation-fusion'
        );
    });

    it('requires e560551 and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V8.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites
                    .sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.genericPrerequisites
                    .originalSourceRootReplayRequired,
                authorization.genericPrerequisites
                    .exactRequestedBudgetPropagationRequired
            ],
            ['e560551', true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.underlyingCategoryEqualityAuthorized,
                authorization.genericSigmaFibreRuleAuthorized,
                authorization.genericComparisonChangeAuthorized,
                authorization.genericDeclarationProofIntegrationAuthorized,
                authorization.genericRuntimeMatcherChangeAuthorized,
                authorization.genericCheckerChangeAuthorized,
                authorization.pathIndSpecificComparisonBudgetAuthorized,
                authorization.retainedTemporaryObserverAuthorized,
                authorization.wholeScaleStress2b3ImportAuthorized,
                authorization.transitivityDefinitionsAuthorized,
                authorization.newCoreOrCheckerPrimitiveAuthorized,
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
            'PATHIND_INTERNALIZED_REVIEW_V8_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V8_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V8_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels', () => {
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
                /pathind_internalized_review_v8|REVIEW_V8/u,
                path
            );
        }
    });
});
