/**
 * Focused explicit-human review tests for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/D-DTTLF-USABILITY-012.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW,
    CoreCategoricalDisplayedChainReviewError,
    validateCoreCategoricalDisplayedChainReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertReviewError = (
    mutate: (review: any) => void,
    expected: CoreCategoricalDisplayedChainReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalDisplayedChainReview(review),
        error =>
            error instanceof CoreCategoricalDisplayedChainReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed displayed dependent chain', () => {
    it('records the explicit D-012 decision separately and exactly', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW.approval,
            {
                gate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-01',
                decisionId: 'D-DTTLF-USABILITY-012',
                decision: 'approved-as-proposed',
                authority: 'explicit-human-decision',
                recordedOn: '2026-07-28',
                decisionEvidence:
                    'Approve H-DTTLF-USABILITY-DISPLAYED-CHAIN-01/' +
                    'D-DTTLF-USABILITY-012 as proposed.'
            }
        );
    });

    it('retains an immutable snapshot of the pending proposal', () => {
        const review = CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL
        );
        assert.equal(
            review.recommendation.status,
            'proposal-awaiting-h-dttlf-usability-displayed-chain-01'
        );
    });

    it('authorizes exactly one owner and six runtime rules', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW.authorization;
        assert.deepEqual(
            authorization.exactKernelOwners,
            ['sigma_functord_sec']
        );
        assert.equal(authorization.exactKernelOwnerCount, 1);
        assert.deepEqual(
            authorization.exactRuntimeRuleIds,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL
                .selectedClosure.runtimeRules.map(rule => rule.id)
        );
        assert.equal(authorization.exactRuntimeRuleCount, 6);
    });

    it('authorizes the exact generic transfer prerequisites', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW.authorization;
        assert.deepEqual(
            authorization.existingDeclarationPrerequisites,
            ['sigma_map_func', 'fdapp1_int_cell', 'fdapp1_int_hom_fapp0']
        );
        assert.deepEqual(
            authorization.existingRuntimeRulePrerequisites,
            [
                'sigma_map_func-object-action',
                'sigma_map_func-structured-arrow-action'
            ]
        );
        assert.equal(
            authorization.genericDeclarationAndRuntimeTransferAuthorized,
            true
        );
        assert.equal(authorization.intrinsicCoreOwnerAuthorized, false);
    });

    it('selects only the existing recursive root pipeline', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW.authorization;
        assert.equal(
            authorization.selectedArchitecture,
            'hybrid-sequential-recursive-direct'
        );
        assert.equal(
            authorization.profile,
            'fibred-displayed-chain-1'
        );
        assert.equal(
            authorization.method,
            'displayedDependentContextLambda'
        );
        assert.equal(authorization.visibility, 'root-only');
        assert.equal(authorization.existingRecursiveContextualCompilerRequired, true);
        assert.equal(authorization.existingGenericCheckerAndEvaluatorRequired, true);
    });

    it('retains the measured warning evidence as diagnostic', () => {
        const review = CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW;
        assert.equal(
            review.retainedBoundaries.warningEvidence.delta
                .unjoinableCriticalPairs,
            8
        );
        assert.equal(
            review.retainedBoundaries.warningEvidence.delta
                .replaceablePatternVariables,
            0
        );
        assert.equal(
            review.authorization.warningDeltaIsDiagnosticNotVeto,
            true
        );
    });

    it('keeps parser, second-checker, total-equivalence, nd, and browser scope closed', () => {
        const review = CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW;
        assert.equal(
            review.authorization.rawExprOrSecondCheckerAuthorized,
            false
        );
        assert.equal(
            review.authorization.parserOrBulkAcquisitionAuthorized,
            false
        );
        assert.equal(
            review.authorization.genericTotalPullbackOrEquivalenceAuthorized,
            false
        );
        assert.equal(
            review.authorization.generalNdCoherenceAuthorized,
            false
        );
        assert.equal(
            review.authorization.browserOrDeployedPromotionAuthorized,
            false
        );
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /categorical_displayed_chain|DISPLAYED-CHAIN/u
        );
    });

    it('preserves the checkpoint-only Git boundary', () => {
        const git = CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW.gitBoundary;
        assert.equal(git.localCheckpointRequired, true);
        assert.equal(git.exactStagedDiffReviewRequired, true);
        assert.equal(git.pushMergePublishAuthorized, false);
        assert.equal(git.historyRewriteAuthorized, false);
        assert.equal(git.cleanupAuthorized, false);
        assert.equal(git.preservedTimeoutArtifactsUntouched, true);
    });

    it('is deeply frozen and rejects decision, proposal, and scope drift', () => {
        assertDeepFrozen(CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW);
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedChainReview()
        );
        assertReviewError(
            review => {
                review.approval.authority =
                    'user-delegated-unattended-approval';
            },
            'DISPLAYED_CHAIN_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.selectedClosure.runtimeRules.pop();
            },
            'DISPLAYED_CHAIN_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.generalNdCoherenceAuthorized = true;
            },
            'DISPLAYED_CHAIN_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_CHAIN_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
