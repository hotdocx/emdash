/** Focused tests for the separate PathOut library graduation review. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL
} from '../src/v3_2/pathout_library_graduation_proposal';
import {
    CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW,
    CorePathoutLibraryGraduation0gReviewError,
    cloneCorePathoutLibraryGraduation0gReview,
    validateCorePathoutLibraryGraduation0gReview
} from '../src/v3_2/pathout_library_graduation_review';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G review', () => {
    it('approves only checkpoint 85b560e and its exact proposal bytes', () => {
        const review = validateCorePathoutLibraryGraduation0gReview();
        assertDeepFrozen(review);
        assert.equal(
            review.revision,
            'PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G-REVIEW-1'
        );
        assert.equal(
            review.approval.approvedProposalCheckpoint,
            '85b560e'
        );
        assert.equal(
            review.approval.approvedProposalSha256,
            'fc35b53dd151694069974b4df6ad3c04ee55cd5d8bacad34f9f21c47c8cee572'
        );
        assert.equal(
            review.recommendation,
            CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL
        );
    });

    it('approves the exact trust and transparent-library partition', () => {
        const scope =
            CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW.authorization;
        assert.equal(scope.mathematicalOpaqueOwnerCount, 5);
        assert.equal(scope.sealedSupportingOwnerCount, 9);
        assert.equal(scope.totalLocalSealedDeclarationCount, 14);
        assert.equal(scope.runtimeRuleCount, 39);
        assert.equal(scope.proofRuleCount, 2);
        assert.equal(scope.transparentDefinitionCount, 30);
        assert.deepEqual(scope.localSliceBoundaries, [
            '5/13/2/9',
            '5/12/0/6',
            '4/13/0/10',
            '0/1/0/5'
        ]);
    });

    it('approves only measured computation and honest evidence classes',
        () => {
            const scope =
                CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW.authorization;
            assert.equal(scope.fixedSourcePointAndArrowComputationQualified,
                true);
            assert.equal(scope.internallyVaryingSourceActionQualified, true);
            assert.equal(scope.selectedHigherActionQualified, true);
            assert.equal(scope.compositionNormalFormQualified, true);
            assert.equal(
                scope.compositionNormalFormTarget,
                'stable-representable-precomposition'
            );
            assert.equal(scope.finitePresentationFormCount, 4);
            assert.equal(scope.browserEvidenceMustRemainPinnedAndNonFresh,
                true);
            assert.equal(
                scope.onlyExplicitNodeCheckMayClaimFreshTypeScriptEvidence,
                true
            );
            assert.equal(scope.pathCategoryBridgeQualified, false);
            assert.equal(scope.wholeTheoryMetatheoryQualified, false);
        });

    it('completes STDLIB-8B without export, release, or implementation', () => {
        const review = CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW;
        assert.deepEqual(review.decision, {
            status: 'approved',
            graduatedProfileId: 'emdash-v3.2-pathout-pathind-root-1',
            graduatedScope: 'root-only-source-qualified',
            pathoutTrustedLibraryGraduate0gComplete: true,
            stdlib8bComplete: true,
            semanticImplementationDelta: 0,
            publicDistributionApproved: false,
            humanDecisionSupersedes: true
        });
        assert.equal(review.authorization.contributorBarrelExportAuthorized,
            false);
        assert.equal(review.authorization.npmBarrelExportAuthorized, false);
        assert.equal(review.authorization.packageVersionOrReleaseAuthorized,
            false);
        assert.equal(review.authorization.integrationOrDeploymentAuthorized,
            false);
        assert.equal(review.authorization.semanticImplementationRequired,
            false);
        assert.equal(
            review.nextDependencyState,
            'post-stdlib-8b-readiness-audit'
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        const decision = cloneCorePathoutLibraryGraduation0gReview();
        (decision.decision as { publicDistributionApproved: boolean })
            .publicDistributionApproved = true;
        assert.throws(
            () => validateCorePathoutLibraryGraduation0gReview(decision),
            error =>
                error instanceof CorePathoutLibraryGraduation0gReviewError &&
                error.code === 'PATHOUT_GRADUATION_REVIEW_DECISION_DRIFT'
        );

        const proposal = cloneCorePathoutLibraryGraduation0gReview();
        (proposal.recommendation.productProfile as {
            productionBackend: string;
        }).productionBackend = 'other';
        assert.throws(
            () => validateCorePathoutLibraryGraduation0gReview(proposal),
            error =>
                error instanceof CorePathoutLibraryGraduation0gReviewError &&
                error.code === 'PATHOUT_GRADUATION_REVIEW_PROPOSAL_DRIFT'
        );

        const authorization = cloneCorePathoutLibraryGraduation0gReview();
        (authorization.authorization as {
            npmBarrelExportAuthorized: boolean;
        }).npmBarrelExportAuthorized = true;
        assert.throws(
            () => validateCorePathoutLibraryGraduation0gReview(authorization),
            error =>
                error instanceof CorePathoutLibraryGraduation0gReviewError &&
                error.code ===
                    'PATHOUT_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('is absent from semantic, browser, and public package barrels', () => {
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts',
            'emdash-template/src/emdash_api.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_library_graduation/u,
                relative
            );
        }
        const source = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/pathout_library_graduation_review.ts'
        ), 'utf8');
        assert.doesNotMatch(source, /compileCorePath/u);
        assert.doesNotMatch(source, /createCoreLfChecker/u);
    });
});
