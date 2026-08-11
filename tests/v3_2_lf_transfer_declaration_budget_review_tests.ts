/**
 * Focused separate-review tests for declaration budget propagation.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL
} from '../src/v3_2/lf_transfer_declaration_budget_proposal';
import {
    CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW,
    CoreLfTransferDeclarationBudgetReview,
    CoreLfTransferDeclarationBudgetReviewError,
    validateCoreLfTransferDeclarationBudgetReview
} from '../src/v3_2/lf_transfer_declaration_budget_review';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CoreLfTransferDeclarationBudgetReview =>
    JSON.parse(JSON.stringify(
        CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW
    )) as CoreLfTransferDeclarationBudgetReview;

const expectError = (
    mutate: (review: CoreLfTransferDeclarationBudgetReview) => void,
    code: CoreLfTransferDeclarationBudgetReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCoreLfTransferDeclarationBudgetReview(review),
        error =>
            error instanceof CoreLfTransferDeclarationBudgetReviewError &&
            error.code === code
    );
};

describe('Core LF transfer declaration budget separate review', () => {
    it('approves only checkpoint 9238104 under delegated authority', () => {
        const review = validateCoreLfTransferDeclarationBudgetReview();
        assert.equal(Object.isFrozen(review), true);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.authority,
                review.approval.humanDecisionSupersedes
            ],
            [
                '9238104',
                'b8903a21e8b66f49f498d81257399d502edf4d1278a709db3bba73fea78a5544',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing proposal', () => {
        const review = CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW;
        assert.deepEqual(
            review.recommendation,
            CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
    });

    it('authorizes exact wiring while preserving the public contract', () => {
        const authorization =
            CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.resolveAndValidateBeforeFactoryRequired,
                authorization.privateLimitAwareFactoryRequired,
                authorization.checkerConstraintLimitOverrideRequired,
                authorization.exactCallerSelectedLimitRequired,
                authorization.publicOptionNameMustRemainUnchanged,
                authorization.publicFactorySignatureMustRemainUnchanged,
                authorization.exportedDefaultMustRemain256,
                authorization.compiledModuleLimitContractMustRemainUnchanged
            ],
            Array.from({ length: 8 }, () => true)
        );
    });

    it('denies unbounded, semantic, public, and external widening', () => {
        const authorization =
            CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.unboundedBudgetAuthorized,
                authorization.adaptiveBudgetAuthorized,
                authorization.globalDefaultChangeAuthorized,
                authorization.pathIndSpecificBudgetAuthorized,
                authorization.newRuntimeRuleAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.proofProgramIntegrationAuthorized,
                authorization.newCoreNodeAuthorized,
                authorization.newCheckerBranchAuthorized,
                authorization.newEvaluatorBranchAuthorized,
                authorization.publicBarrelChangeAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            Array.from({ length: 13 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        expectError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_DECISION_DRIFT'
        );
        expectError(
            review => {
                (review.recommendation.exactCorrection as {
                    exportedDefaultUnchanged: boolean;
                }).exportedDefaultUnchanged = false;
            },
            'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_PROPOSAL_DRIFT'
        );
        expectError(
            review => {
                (review.authorization as {
                    globalDefaultChangeAuthorized: boolean;
                }).globalDefaultChangeAuthorized = true;
            },
            'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, package, workspace, or browser barrels',
        () => {
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
                    /lf_transfer_declaration_budget_review/u,
                    path
                );
            }
        });
});
