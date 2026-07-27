/**
 * Executable FIBRED-PRODUCT-0B proposal boundary.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL,
    CoreCategoricalFibredProductProposalError,
    CoreCategoricalFibredProductProposalInput,
    validateCoreCategoricalFibredProductProposal
} from '../src/v3_2';

const clone = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('FIBRED-PRODUCT-0B exact owner-position proposal', () => {
    it('selects the zero-warning-delta existing-owner route', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL;
        assert.equal(
            proposal.recommendation.selected,
            'narrow-shared-base-existing-owner'
        );
        assert.equal(
            proposal.recommendation
                .activeProductCatdDeclarationRequired,
            false
        );
        assert.equal(
            proposal.recommendation.newMathematicalOwnerRequired,
            false
        );
        assert.equal(
            proposal.recommendation.authorityAuthorized,
            false
        );
        assert.deepEqual(
            proposal.alternatives.map(alternative => [
                alternative.id,
                alternative.warningInventory.criticalPairDelta
            ]),
            [
                ['broad-generic-product-off-diagonal', 3],
                ['stable-product-catd-head', 5],
                ['narrow-shared-base-existing-owner', 0]
            ]
        );
        validateCoreCategoricalFibredProductProposal();
    });

    it('proposes exactly two runtime rules and no owner', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL;
        assert.deepEqual(
            proposal.proposedRuntimeRules.map(rule => [
                rule.order,
                rule.id,
                rule.activeOwner,
                rule.sameBaseArrowRequired
            ]),
            [
                [
                    0,
                    'cat-valued-postcomposition-capped-action',
                    'hom_postcomp_fapp0',
                    false
                ],
                [
                    1,
                    'shared-base-product-action-projection',
                    'Product_cat_fapp1_fapp0_functord',
                    true
                ]
            ]
        );
        assert.equal(
            proposal.proposedRuntimeRules[1].lhs,
            'tapp1_fapp0(' +
            'Product_cat_fapp1_fapp0_functord(B[p]),C[p])'
        );
        assert.equal(
            proposal.proposedRuntimeRules[1].rhs,
            'Product_map_func(B[p],C[p])'
        );
        assert.equal(
            proposal.proposedRuntimeRules.every(
                rule => !rule.introducesOwner
            ),
            true
        );
    });

    it('retains the exact higher and comparison boundaries', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL;
        assert.equal(
            proposal.higherActionBoundary.returnedTransport,
            'stable-Product_map_func-with-existing-full-and-capped-hom-action'
        );
        assert.equal(
            proposal.higherActionBoundary.baseTwoCellAction,
            'not-yet-qualified'
        );
        assert.equal(
            proposal.comparisonPolicy.familyLevelFunctordProduct,
            'derive-from-projection-and-pairing-functors-not-global-runtime-collapse'
        );
        assert.equal(
            proposal.firstConsumer.genericTotalCategoryPullbackAssumed,
            false
        );
        assert.deepEqual(
            proposal.measuredEvidence.negativeConversions,
            [
                'opaque-family-does-not-collapse',
                'functord-category-does-not-runtime-collapse-to-product',
                'pullback-stability-does-not-runtime-convert'
            ]
        );
    });

    it('is deeply frozen and self-identifies the human gate', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL;
        assert.equal(
            proposal.decisionId,
            'D-DTTLF-USABILITY-004'
        );
        assert.match(
            proposal.decisionQuestion,
            /Approve H-DTTLF-USABILITY-02\/D-DTTLF-USABILITY-004/u
        );
        assertDeepFrozen(proposal);
    });

    it('rejects recommendation and warning-evidence drift', () => {
        const broadened = clone(
            CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL
        ) as unknown as {
            recommendation: {
                authorityAuthorized: boolean;
            };
        };
        broadened.recommendation.authorityAuthorized = true;
        assert.throws(
            () => validateCoreCategoricalFibredProductProposal(
                broadened as unknown as
                    CoreCategoricalFibredProductProposalInput
            ),
            error =>
                error instanceof
                    CoreCategoricalFibredProductProposalError &&
                error.code ===
                    'FIBRED_PRODUCT_RECOMMENDATION_DRIFT'
        );

        const evidenceChanged = clone(
            CORE_CATEGORICAL_FIBRED_PRODUCT_PROPOSAL
        ) as unknown as {
            measuredEvidence: {
                recommendedWarningInventory: {
                    criticalPairs: number;
                };
            };
        };
        evidenceChanged.measuredEvidence
            .recommendedWarningInventory.criticalPairs = 1011;
        assert.throws(
            () => validateCoreCategoricalFibredProductProposal(
                evidenceChanged as unknown as
                    CoreCategoricalFibredProductProposalInput
            ),
            error =>
                error instanceof
                    CoreCategoricalFibredProductProposalError &&
                error.code ===
                    'FIBRED_PRODUCT_EVIDENCE_DRIFT'
        );
    });
});
