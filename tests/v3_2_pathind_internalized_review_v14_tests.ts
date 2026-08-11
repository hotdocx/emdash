/**
 * Focused separate-review tests for corrected internalized PathInd v14.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14
} from '../src/v3_2/pathind_internalized_proposal_v14';
import {
    CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14,
    CorePathindInternalized1dReviewV14,
    CorePathindInternalized1dReviewV14Error,
    validateCorePathindInternalized1dReviewV14
} from '../src/v3_2/pathind_internalized_review_v14';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dReviewV14 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14
    )) as CorePathindInternalized1dReviewV14;

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
    mutate: (review: CorePathindInternalized1dReviewV14) => void,
    expected: CorePathindInternalized1dReviewV14Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCorePathindInternalized1dReviewV14(review),
        error =>
            error instanceof CorePathindInternalized1dReviewV14Error &&
            error.code === expected
    );
};

describe('corrected internalized PathInd v14 separate review', () => {
    it('approves only checkpoint 4244b54 under delegated authority', () => {
        const review = validateCorePathindInternalized1dReviewV14();
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
                '4244b54',
                '6ddf101160ab62b5209eb6c416e732c00b69025cfba8ffa562f7fffc43140e34',
                'd77f0d7',
                'a8aff88',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v14 proposal', () => {
        const review = CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14;
        assert.deepEqual(
            review.recommendation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
        assert.deepEqual(
            review.authorization.exactImplementation,
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14.exactImplementation
        );
    });

    it('authorizes exactly the staged eight-support boundary', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14.authorization;
        assert.deepEqual(
            [
                authorization.trustedDeclarationCount,
                authorization.runtimeRuleCount,
                authorization.mathematicalRuntimeProjectionCount,
                authorization.derivedRuntimeSupportRuleCount,
                authorization.proofRuleCount,
                authorization.transparentDefinitionCount,
                authorization.baseRuntimeRuleCount,
                authorization.prefixTransparentDefinitionCount,
                authorization.extensionRuntimeRuleCount,
                authorization.suffixTransparentDefinitionCount
            ],
            [4, 13, 5, 8, 0, 10, 9, 3, 4, 4]
        );
        assert.equal(
            authorization.pathInductionTargetFibreFusionRuleId,
            'pathind.internalized.' +
                'path-ind-target-fibre-at-sigma-pair-' +
                'presentation-fusion'
        );
    });

    it('requires existing authority and denies semantic widening', () => {
        const authorization =
            CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14.authorization;
        assert.deepEqual(
            [
                authorization.genericPrerequisites.sharedSemanticCheckpoint,
                authorization.genericPrerequisites.bothComplete,
                authorization.pathoutPiTransportCompiledBeforeTargetAlias,
                authorization.targetFibreFusionCoversBothAliasEndpoints,
                authorization.targetFibreFusionUsesActivePathIndTgtOnly,
                authorization.targetFibreFusionUsesActiveSectionFacadeOnly
            ],
            ['e560551', true, true, true, true, true]
        );
        assert.deepEqual(
            [
                authorization.newMathematicalRuntimeEquationAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.declarationBodyOrTypeChangeAuthorized,
                authorization.declarationSourceOrderChangeAuthorized,
                authorization.underlyingCategoryEqualityAuthorized,
                authorization.genericSigmaFibreRuntimeRuleAuthorized,
                authorization.genericSectionCategoryRuntimeRuleAuthorized,
                authorization.genericPullbackRuleChangeAuthorized,
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
            Array.from({ length: 20 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_REVIEW_V14_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (
                    review.recommendation.exactImplementation
                        .runtimeRules as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_REVIEW_V14_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    genericCheckerChangeAuthorized: boolean;
                }).genericCheckerChangeAuthorized = true;
            },
            'PATHIND_INTERNALIZED_REVIEW_V14_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_review_v14|REVIEW_V14/u,
                path
            );
        }
    });
});
