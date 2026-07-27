/**
 * Executable FIBRED-COMPREHENSION-0B proposal boundary.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_COMPREHENSION_PROPOSAL,
    CoreCategoricalComprehensionProposalError,
    CoreCategoricalComprehensionProposalInput,
    validateCoreCategoricalComprehensionProposal
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

describe(
    'FIBRED-COMPREHENSION-0B exact owner-position proposal',
    () => {
        it('selects the reusable zero-warning-delta owner', () => {
            const proposal =
                CORE_CATEGORICAL_COMPREHENSION_PROPOSAL;
            assert.equal(
                proposal.recommendation.selected,
                'asymmetric-pullback-total-owner'
            );
            assert.deepEqual(
                proposal.alternatives.map(alternative => [
                    alternative.id,
                    alternative.newDeclarations,
                    alternative.newRuntimeRules,
                    alternative.warningInventory.criticalPairDelta
                ]),
                [
                    [
                        'semantic-sigma-intro-composite',
                        0,
                        0,
                        0
                    ],
                    [
                        'direct-contextual-pair-owner',
                        1,
                        3,
                        2
                    ],
                    [
                        'asymmetric-pullback-total-owner',
                        1,
                        2,
                        0
                    ]
                ]
            );
            assert.equal(
                proposal.recommendation.authorityAuthorized,
                false
            );
            validateCoreCategoricalComprehensionProposal();
        });

        it('proposes one owner with exactly two projections', () => {
            const proposal =
                CORE_CATEGORICAL_COMPREHENSION_PROPOSAL;
            assert.equal(
                proposal.proposedOwner.name,
                'sigma_pullback_total_func'
            );
            assert.equal(
                proposal.proposedOwner.arbitraryTotalFunctorPullback,
                false
            );
            assert.deepEqual(
                proposal.proposedRuntimeRules.map(rule => [
                    rule.order,
                    rule.id,
                    rule.ownerPosition,
                    rule.structuredSigmaInputRequired
                ]),
                [
                    [
                        0,
                        'pullback-total-object-action',
                        '9b-sigma-total-maps',
                        true
                    ],
                    [
                        1,
                        'pullback-total-structured-arrow-action',
                        '17-pullback-capped-transport-cut',
                        true
                    ]
                ]
            );
            assert.equal(
                proposal.recommendation.newProofTimeRulesRequired,
                0
            );
        });

        it('keeps contextual pairing transparent and directed', () => {
            const proposal =
                CORE_CATEGORICAL_COMPREHENSION_PROPOSAL;
            assert.equal(
                proposal.transparentContextualPair
                    .dedicatedPairOwnerIntroduced,
                false
            );
            assert.equal(
                proposal.measuredEvidence.positiveConversions.includes(
                    'further-family-base-arrow-substitution'
                ),
                true
            );
            assert.equal(
                proposal.interactionPolicy.firstProjection,
                'pointwise-computation-only-whole-functor-beta-deferred'
            );
            assert.equal(
                proposal.interactionPolicy.displayedProduct,
                'independent-d-004-gate-composes-later-without-being-assumed'
            );
        });

        it('separates the broad Sigma-introduction action', () => {
            const proposal =
                CORE_CATEGORICAL_COMPREHENSION_PROPOSAL;
            assert.equal(
                proposal.directSigmaIntroductionAudit
                    .neededForRecommendedContextualPair,
                false
            );
            assert.equal(
                proposal.directSigmaIntroductionAudit
                    .criticalPairDelta,
                10
            );
            assert.equal(
                proposal.recommendation
                    .directSigmaIntroArrowRuleRequired,
                false
            );
            assert.equal(
                proposal.nonEffects.includes(
                    'does-not-add-a-generic-total-category-pullback'
                ),
                true
            );
        });

        it('is deeply frozen and rejects proposal drift', () => {
            const proposal =
                CORE_CATEGORICAL_COMPREHENSION_PROPOSAL;
            assert.equal(
                proposal.decisionId,
                'D-DTTLF-USABILITY-005'
            );
            assert.match(
                proposal.decisionQuestion,
                /Approve H-DTTLF-USABILITY-02\/D-DTTLF-USABILITY-005/u
            );
            assertDeepFrozen(proposal);

            const broadened = clone(proposal) as unknown as {
                recommendation: {
                    authorityAuthorized: boolean;
                };
            };
            broadened.recommendation.authorityAuthorized = true;
            assert.throws(
                () => validateCoreCategoricalComprehensionProposal(
                    broadened as unknown as
                        CoreCategoricalComprehensionProposalInput
                ),
                error =>
                    error instanceof
                        CoreCategoricalComprehensionProposalError &&
                    error.code ===
                        'FIBRED_COMPREHENSION_RECOMMENDATION_DRIFT'
            );

            const evidenceChanged = clone(proposal) as unknown as {
                measuredEvidence: {
                    recommendedWarningInventory: {
                        criticalPairs: number;
                    };
                };
            };
            evidenceChanged.measuredEvidence
                .recommendedWarningInventory.criticalPairs = 1011;
            assert.throws(
                () => validateCoreCategoricalComprehensionProposal(
                    evidenceChanged as unknown as
                        CoreCategoricalComprehensionProposalInput
                ),
                error =>
                    error instanceof
                        CoreCategoricalComprehensionProposalError &&
                    error.code ===
                        'FIBRED_COMPREHENSION_EVIDENCE_DRIFT'
            );
        });
    }
);
