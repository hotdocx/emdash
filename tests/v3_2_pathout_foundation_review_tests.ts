/**
 * Focused delegated review tests for corrected PathOut foundation proposal.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL
} from '../src/v3_2/pathout_foundation_proposal';
import {
    CORE_PATHOUT_FOUNDATION_1B0_REVIEW,
    CorePathoutFoundation1b0Review,
    CorePathoutFoundation1b0ReviewError,
    validateCorePathoutFoundation1b0Review
} from '../src/v3_2/pathout_foundation_review';

const clone = (): CorePathoutFoundation1b0Review =>
    JSON.parse(JSON.stringify(
        CORE_PATHOUT_FOUNDATION_1B0_REVIEW
    )) as CorePathoutFoundation1b0Review;

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
    mutate: (review: CorePathoutFoundation1b0Review) => void,
    expected: CorePathoutFoundation1b0ReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathoutFoundation1b0Review(review),
        error =>
            error instanceof CorePathoutFoundation1b0ReviewError &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-FOUNDATION-1B0 delegated v5 review', () => {
    it('approves only checkpointed v5 with human supersession', () => {
        const approval = CORE_PATHOUT_FOUNDATION_1B0_REVIEW.approval;
        assert.deepEqual(
            [
                approval.decision,
                approval.authority,
                approval.rejectedProposalCheckpoint,
                approval.supersededProposalCheckpoint,
                approval.supersededReviewCheckpoint,
                approval.supersededV3ProposalCheckpoint,
                approval.supersededV3ReviewCheckpoint,
                approval.supersededV4ProposalCheckpoint,
                approval.supersededV4ReviewCheckpoint,
                approval.approvedProposalCheckpoint,
                approval.humanDecisionSupersedes
            ],
            [
                'corrected-proposal-v5-approved-as-proposed',
                'user-delegated-unattended-approval',
                'dd69325',
                'b3d6d71',
                '38ef8ae',
                '640d5ec',
                '36c368e',
                '681d954',
                'ab556a9',
                '622a496',
                true
            ]
        );
    });

    it('retains an immutable copy of exact non-authorizing v5', () => {
        const recommendation =
            CORE_PATHOUT_FOUNDATION_1B0_REVIEW.recommendation;
        assert.notEqual(
            recommendation,
            CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL
        );
        assert.deepEqual(
            recommendation,
            CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL
        );
        assert.equal(
            recommendation.revision,
            'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-5'
        );
    });

    it('authorizes exact root-only 4/9/1/9 over corrected predecessor',
        () => {
        const authorization =
            CORE_PATHOUT_FOUNDATION_1B0_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.implementationRow,
                authorization.prerequisiteDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.proofRuleCount,
                authorization.transparentLibraryDefinitionCount,
                authorization.exactSelectedPredecessor.compileFunction,
                authorization.implementationAuthorized
            ],
            [
                'PATHOUT-LIBRARY-FOUNDATION-1B',
                4,
                9,
                1,
                9,
                'compileCoreCategoricalDirectMixedSourceActionTransfer',
                true
            ]
        );
    });

    it('denies every later semantic and product layer', () => {
        const authorization =
            CORE_PATHOUT_FOUNDATION_1B0_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.fixedSourcePathInductionAuthorized,
                authorization.internalizedPathInductionAuthorized,
                authorization.transitivityAuthorized,
                authorization.sigmaMapHigherActionAuthorized,
                authorization.newCoreOrCheckerPrimitiveAuthorized,
                authorization
                    .ordinarySafeLibraryRuleRegistrationAuthorized,
                authorization.browserOrPublicPackageExportAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            [false, false, false, false, false, false, false, false, false]
        );
    });

    it('is deeply frozen, validates, and rejects review drift', () => {
        assertDeepFrozen(CORE_PATHOUT_FOUNDATION_1B0_REVIEW);
        assert.doesNotThrow(
            () => validateCorePathoutFoundation1b0Review()
        );
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHOUT_FOUNDATION_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHOUT_FOUNDATION_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    browserOrPublicPackageExportAuthorized: boolean;
                }).browserOrPublicPackageExportAuthorized = true;
            },
            'PATHOUT_FOUNDATION_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('stays outside contributor, npm, and browser barrels', () => {
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
                readFileSync(path, 'utf8'),
                /pathout_foundation_review|PATHOUT_FOUNDATION_1B0_REVIEW/u,
                path
            );
        }
    });
});
