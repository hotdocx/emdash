/**
 * Executable FIBRED-STRUCTURE-0A proposal boundary.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL,
    CoreCategoricalFibredStructureProposalError,
    CoreCategoricalFibredStructureProposalInput,
    validateCoreCategoricalFibredStructureProposal
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

describe('FIBRED-STRUCTURE-0A exact structural proposal', () => {
    it('selects the complete fixed-base package', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL;
        assert.equal(
            proposal.recommendation.selected,
            'fixed-base-displayed-universal-property'
        );
        assert.equal(
            proposal.recommendation.newMathematicalOwnersRequired,
            3
        );
        assert.equal(
            proposal.recommendation.newRuntimeRulesRequired,
            11
        );
        assert.equal(
            proposal.recommendation.activeProductCatdOwnerRequired,
            false
        );
        assert.equal(
            proposal.recommendation.authorityAuthorized,
            false
        );
        validateCoreCategoricalFibredStructureProposal();
    });

    it('freezes exactly three owners and eleven ordered rules', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL;
        assert.deepEqual(
            proposal.proposedOwners.map(owner => [
                owner.order,
                owner.name
            ]),
            [
                [0, 'Product_projL_funcd'],
                [1, 'Product_projR_funcd'],
                [2, 'Product_pair_funcd']
            ]
        );
        assert.deepEqual(
            proposal.proposedRuntimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        );
        assert.deepEqual(
            proposal.proposedRuntimeRules
                .filter(rule => rule.higherIterable)
                .map(rule => rule.id),
            [
                'left-projection-full-action',
                'left-projection-capped-action',
                'right-projection-full-action',
                'right-projection-capped-action',
                'pairing-full-action',
                'pairing-capped-action',
                'left-projection-pairing-beta',
                'right-projection-pairing-beta'
            ]
        );
    });

    it('derives swap and diagonal without two more owners', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL;
        assert.equal(
            proposal.derivedOperations.swap,
            'Product_pair_funcd(Product_projR_funcd,Product_projL_funcd)'
        );
        assert.equal(
            proposal.derivedOperations.diagonal,
            'Product_pair_funcd(id_funcd,id_funcd)'
        );
        assert.equal(
            proposal.derivedOperations.primitiveSwapOwnerRequired,
            false
        );
        assert.equal(
            proposal.derivedOperations.primitiveDiagonalOwnerRequired,
            false
        );
    });

    it('keeps reindexing canonicalization in the frontend boundary', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL;
        assert.equal(
            proposal.reindexingPolicy.emittedCanonicalCore,
            'P(Pullback_catd(B,F),Pullback_catd(C,F))'
        );
        assert.equal(
            proposal.reindexingPolicy.nonCanonicalCore,
            'Pullback_catd(P(B,C),F)'
        );
        assert.equal(
            proposal.reindexingPolicy
                .dependencyGraphSelectsCanonicalForm,
            true
        );
        assert.equal(
            proposal.reindexingPolicy.kernelRuntimeConversionClaimed,
            false
        );
        assert.equal(
            proposal.reindexingPolicy.kernelProofTimeEqualityClaimed,
            false
        );
        assert.equal(
            proposal.reindexingPolicy.kernelReindexingRuleAdded,
            false
        );
    });

    it('records positive, negative, higher, and alternative evidence', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL;
        assert.deepEqual(
            proposal.alternatives.map(alternative => [
                alternative.id,
                alternative.warningInventory.criticalPairDelta,
                alternative.warningInventory.replaceablePatternDelta
            ]),
            [
                ['fixed-base-displayed-universal-property', 0, 0],
                ['universe-level-projection-prewhiskering', 2, 6],
                ['semantic-composition-reindex-rule', 6, 0],
                ['stable-pullback-reindex-rule', 9, 0],
                ['stable-product-family-head', 5, 0]
            ]
        );
        assert.equal(
            proposal.measuredEvidence.higherEvidence.includes(
                'projection-action-accepts-a-genuine-next-cell'
            ),
            true
        );
        assert.equal(
            proposal.measuredEvidence.negativeConversions.includes(
                'raw-pullback-of-transparent-product-does-not-convert-to-canonical-reindexed-product'
            ),
            true
        );
    });

    it('is deeply frozen and rejects authority or reindexing drift', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL;
        assert.match(
            proposal.decisionQuestion,
            /Approve H-DTTLF-USABILITY-02\/D-DTTLF-USABILITY-006/u
        );
        assertDeepFrozen(proposal);

        const authorized = clone(proposal) as unknown as {
            recommendation: {
                authorityAuthorized: boolean;
            };
        };
        authorized.recommendation.authorityAuthorized = true;
        assert.throws(
            () => validateCoreCategoricalFibredStructureProposal(
                authorized as unknown as
                    CoreCategoricalFibredStructureProposalInput
            ),
            error =>
                error instanceof
                    CoreCategoricalFibredStructureProposalError &&
                error.code ===
                    'FIBRED_STRUCTURE_RECOMMENDATION_DRIFT'
        );

        const broadened = clone(proposal) as unknown as {
            reindexingPolicy: {
                kernelRuntimeConversionClaimed: boolean;
            };
        };
        broadened.reindexingPolicy.kernelRuntimeConversionClaimed =
            true;
        assert.throws(
            () => validateCoreCategoricalFibredStructureProposal(
                broadened as unknown as
                    CoreCategoricalFibredStructureProposalInput
            ),
            error =>
                error instanceof
                    CoreCategoricalFibredStructureProposalError &&
                error.code ===
                    'FIBRED_STRUCTURE_REINDEXING_DRIFT'
        );
    });
});
