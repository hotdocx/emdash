/**
 * Exact proposal/review boundary for D-DTTLF-USABILITY-003.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL,
    CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW,
    CoreCategoricalDependentUsabilityProposalError,
    CoreCategoricalDependentUsabilityProposalInput,
    CoreCategoricalDependentUsabilityReviewError,
    CoreCategoricalDependentUsabilityReviewInput,
    validateCoreCategoricalDependentUsabilityProposal,
    validateCoreCategoricalDependentUsabilityReview
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

describe('TypeScript v3.2 dependent usability D-003 review', () => {
    it('keeps the pre-review proposal non-self-authorizing', () => {
        const proposal =
            CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL;
        assert.equal(
            proposal.recommendation.authorityAuthorized,
            false
        );
        assert.equal(
            proposal.recommendation
                .implementationUniformityRequired,
            false
        );
        assert.equal(
            proposal.recommendation
                .implementationSeparationRequired,
            false
        );
        assert.equal(
            proposal.solutionCriterion.algorithmNeutrality,
            'shared-or-distinct-lowering-is-evidence-driven'
        );
        assert.deepEqual(
            proposal.architectureAlternativesRetained.map(
                alternative => alternative.id
            ),
            [
                'progressively-shared-contextual-compiler',
                'one-frontend-with-authority-specific-lowerers',
                'data-driven-semantic-contextual-rule-table'
            ]
        );
        validateCoreCategoricalDependentUsabilityProposal();
        assertDeepFrozen(proposal);
    });

    it('records the exact user approval separately', () => {
        const review =
            CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW;
        assert.equal(review.status, 'reviewed-approved');
        assert.equal(
            review.approval.decisionEvidence,
            'Approve H-DTTLF-USABILITY-DEPENDENT/' +
            'D-DTTLF-USABILITY-003 as proposed.'
        );
        assert.equal(
            review.proposal.recommendation.authorityAuthorized,
            false
        );
        assert.equal(
            review.authorization.authorizedSlice,
            'USABILITY-DEPENDENT-1A'
        );
        assert.equal(
            review.authorization.authorizedWitness,
            'λ k :^n K. FF[k](s[k])'
        );
        assert.equal(
            review.successCriterion.sharedImplementationShape,
            'not-a-gate'
        );
        validateCoreCategoricalDependentUsabilityReview();
        assertDeepFrozen(review);
    });

    it('withholds every unapproved follow-on', () => {
        const authorization =
            CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW
                .authorization;
        assert.equal(
            authorization
                .newLambdapiOwnerOrMathematicalRuleAuthorized,
            false
        );
        assert.equal(
            authorization.generalDependentBracketAuthorized,
            false
        );
        assert.equal(
            authorization
                .browserOrProductProfilePromotionAuthorized,
            false
        );
        assert.equal(
            authorization.parserOrAcquisitionSelectionAuthorized,
            false
        );
        assert.equal(
            authorization.bulkTransferResumptionAuthorized,
            false
        );
        assert.equal(
            authorization.implementationUniformityRequired,
            false
        );
        assert.equal(
            authorization.implementationSeparationRequired,
            false
        );
    });

    it('rejects proposal algorithm-policy drift', () => {
        const changed = clone(
            CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL
        ) as unknown as {
            recommendation: {
                implementationUniformityRequired: boolean;
            };
        };
        changed.recommendation
            .implementationUniformityRequired = true;
        assert.throws(
            () =>
                validateCoreCategoricalDependentUsabilityProposal(
                    changed as unknown as
                        CoreCategoricalDependentUsabilityProposalInput
                ),
            error =>
                error instanceof
                    CoreCategoricalDependentUsabilityProposalError &&
                error.code ===
                    'DEPENDENT_USABILITY_ARCHITECTURE_DRIFT'
        );
    });

    it('rejects approval evidence and authorization drift', () => {
        const evidenceChanged = clone(
            CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW
        ) as unknown as {
            approval: {
                decisionEvidence: string;
            };
        };
        evidenceChanged.approval.decisionEvidence =
            'approved approximately';
        assert.throws(
            () =>
                validateCoreCategoricalDependentUsabilityReview(
                    evidenceChanged as unknown as
                        CoreCategoricalDependentUsabilityReviewInput
                ),
            error =>
                error instanceof
                    CoreCategoricalDependentUsabilityReviewError &&
                error.code ===
                    'DEPENDENT_USABILITY_REVIEW_DECISION_DRIFT'
        );

        const broadened = clone(
            CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW
        ) as unknown as {
            authorization: {
                generalDependentBracketAuthorized: boolean;
            };
        };
        broadened.authorization
            .generalDependentBracketAuthorized = true;
        assert.throws(
            () =>
                validateCoreCategoricalDependentUsabilityReview(
                    broadened as unknown as
                        CoreCategoricalDependentUsabilityReviewInput
                ),
            error =>
                error instanceof
                    CoreCategoricalDependentUsabilityReviewError &&
                error.code ===
                    'DEPENDENT_USABILITY_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
