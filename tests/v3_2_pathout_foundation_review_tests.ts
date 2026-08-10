/**
 * Focused v8 supersession tests for corrected PathOut foundation proposal.
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

describe('PATHOUT-LIBRARY-FOUNDATION-1B0 v8 review supersession', () => {
    it('withdraws v8 after the identity-incoming runtime gap', () => {
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
                approval.supersededV5ProposalCheckpoint,
                approval.supersededV5ReviewCheckpoint,
                approval.supersededV6ProposalCheckpoint,
                approval.supersededV6ReviewCheckpoint,
                approval.supersededV7ProposalCheckpoint,
                approval.supersededV7ReviewCheckpoint,
                approval.supersededV8ProposalCheckpoint,
                approval.supersededV8ReviewCheckpoint,
                approval.replacementProposalCheckpoint,
                approval.humanDecisionSupersedes
            ],
            [
                'corrected-proposal-v8-superseded-after-measured-' +
                    'precomposition-identity-incoming-gap',
                'measured-implementation-forward-correction',
                'dd69325',
                'b3d6d71',
                '38ef8ae',
                '640d5ec',
                '36c368e',
                '681d954',
                'ab556a9',
                '622a496',
                'c4dd293',
                'f006ccb',
                'bdcef29',
                '2460ae9',
                '7035922',
                '6e4bb82',
                'edda832',
                'pending-separate-checkpoint',
                true
            ]
        );
    });

    it('retains an immutable copy of exact non-authorizing v9', () => {
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
            'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-9'
        );
    });

    it('freezes root-only 5/13/2/9 without implementation authority',
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
                5,
                13,
                2,
                9,
                'compileCoreCategoricalDirectMixedSourceActionTransfer',
                false
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
                    replacementProposalCheckpoint: string;
                }).replacementProposalCheckpoint = 'wrong';
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
