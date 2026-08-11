/**
 * Focused separate review tests for corrected internalized PathInd v2.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2
} from '../src/v3_2/pathind_internalized_proposal_v2';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2,
    CorePathindInternalized1dReviewV2,
    CorePathindInternalized1dReviewV2Error,
    validateCorePathindInternalized1dReviewV2
} from '../src/v3_2/pathind_internalized_review_v2';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV2 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2
    )) as CorePathindInternalized1dReviewV2;

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
    mutate: (review: CorePathindInternalized1dReviewV2) => void,
    expected: CorePathindInternalized1dReviewV2Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV2(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV2Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v2 separate review', () => {
    it('approves only checkpoint fbfc4dd under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV2();
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
                'fbfc4dd',
                '9a4b6e9f863af1068518920c050f5cbfdaeddb5fcf2fccb2d58a9e8ef7dfb85e',
                '188b8e5',
                'd3a0f31',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v2 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2.exactImplementation
        );
    });

    it('authorizes exactly 4/5/0/10 and one non-mathematical support rule',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2.authorization;
            assert.deepEqual(
                [
                    authorization.trustedDeclarationCount,
                    authorization.runtimeRuleCount,
                    authorization.mathematicalRuntimeProjectionCount,
                    authorization.derivedRuntimeSupportRuleCount,
                    authorization.proofRuleCount,
                    authorization.transparentDefinitionCount,
                    authorization
                        .componentSubjectPresentationFusionAuthorized,
                    authorization
                        .componentSubjectPresentationFusionIsMathematicalRule
                ],
                [4, 5, 4, 1, 0, 10, true, false]
            );
            assert.equal(
                authorization.componentSubjectPresentationFusionRuleId,
                'pathind.internalized.' +
                    'path-ind-functor-component-subject-fusion'
            );
        });

    it('denies failed substitutes, generic widening, and later effects',
        () => {
            const authorization =
                CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2.authorization;
            assert.deepEqual(
                [
                    authorization.genericRuntimeMatcherChangeAuthorized,
                    authorization.genericCheckerChangeAuthorized,
                    authorization.inheritedProofProgramDependencyAuthorized,
                    authorization
                        .genericFixedEvaluationRuntimeImportAuthorized,
                    authorization.alternatePathIndTypeAuthorized,
                    authorization.alternatePathIndComponentBodyAuthorized,
                    authorization.retainedTemporaryExperimentAuthorized,
                    authorization.wholeScaleStress2b3ImportAuthorized,
                    authorization.externalNaturalitySquareAuthorized,
                    authorization.transitivityDefinitionsAuthorized,
                    authorization.newCoreOrCheckerPrimitiveAuthorized,
                    authorization.browserOrPublicPackageExportAuthorized,
                    authorization.activeLambdapiSourceChangeAuthorized,
                    authorization.externalIntegrationOrReleaseAuthorized
                ],
                Array.from({ length: 14 }, () => false)
            );
            assert.equal(
                CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2
                    .gitBoundary.pushMergePublishAuthorized,
                false
            );
        });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V2_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .transparentDefinitions as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V2_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V2_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
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
                    /pathind_internalized_review_v2|REVIEW_V2/u,
                    path
                );
            }
        });
});
