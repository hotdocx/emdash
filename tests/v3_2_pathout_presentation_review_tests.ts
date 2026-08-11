/**
 * Focused tests for the separate PathOut presentation review.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_PRESENTATION_1F_PROPOSAL
} from '../src/v3_2/pathout_presentation_proposal';
import {
    CORE_PATHOUT_PRESENTATION_1F_REVIEW,
    CorePathoutPresentation1fReview,
    CorePathoutPresentation1fReviewError,
    cloneCorePathoutPresentation1fReview,
    validateCorePathoutPresentation1fReview
} from '../src/v3_2/pathout_presentation_review';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

const assertReviewError = (
    mutate: (review: CorePathoutPresentation1fReview) => void,
    expected: CorePathoutPresentation1fReviewError['code']
): void => {
    const review = cloneCorePathoutPresentation1fReview();
    mutate(review);
    assert.throws(
        () => validateCorePathoutPresentation1fReview(review),
        error =>
            error instanceof CorePathoutPresentation1fReviewError &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-PRESENTATION-1F review', () => {
    it('approves only proposal checkpoint 6ad0812 and its digest', () => {
        const review = validateCorePathoutPresentation1fReview();
        assertDeepFrozen(review);
        assert.deepEqual(
            [
                review.approval.approvedProposalRevision,
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.authority,
                review.approval.humanDecisionSupersedes
            ],
            [
                'PATHOUT-LIBRARY-PRESENTATION-1F-PROPOSAL-1',
                '6ad0812',
                'b7b85c34af390a5b1489b0fdd0d015cd' +
                    '2a4ca554c38533bf4459b7ec26029be3',
                'user-delegated-unattended-approval',
                true
            ]
        );
        assert.deepEqual(
            review.recommendation,
            CORE_PATHOUT_PRESENTATION_1F_PROPOSAL
        );
    });

    it('authorizes exactly four expression forms and four stages', () => {
        const authorization =
            CORE_PATHOUT_PRESENTATION_1F_REVIEW.authorization;
        assert.deepEqual(authorization.exactImplementationStages, [
            'PATHOUT-LIBRARY-PRESENTATION-1F1',
            'PATHOUT-LIBRARY-PRESENTATION-1F2',
            'PATHOUT-LIBRARY-PRESENTATION-1F3',
            'PATHOUT-LIBRARY-PRESENTATION-1F4'
        ]);
        assert.deepEqual(authorization.expressionForms, [
            'pathout-category',
            'canonical-rho',
            'fixed-source-induction',
            'composition-normal-form'
        ]);
        assert.equal(authorization.finiteExpressionParserAuthorized, true);
        assert.equal(authorization.parserReturnsInertRequest, true);
        assert.equal(authorization.declarationOrBinderSyntaxAuthorized, false);
        assert.equal(authorization.categoricalParserWideningAuthorized, false);
    });

    it('freezes the browser-safe and Node semantic APIs separately', () => {
        const authorization =
            CORE_PATHOUT_PRESENTATION_1F_REVIEW.authorization;
        assert.deepEqual(authorization.browserSafeApi, [
            'CORE_PATHOUT_PRESENTATION_1F_MANIFEST',
            'parseCorePathoutPresentationText',
            'serializeCorePathoutPresentationRequest',
            'createCorePathoutQualificationReport',
            'formatCorePathoutQualificationReport'
        ]);
        assert.deepEqual(authorization.nodeSemanticApi, [
            'checkCorePathoutPresentationRequest',
            'formatCorePathoutFreshCheck'
        ]);
        assert.equal(
            authorization.staticManifestMustSayNotRerunInBrowser,
            true
        );
        assert.equal(authorization.nodeFreshSemanticCheckAuthorized, true);
        assert.equal(
            authorization.nodeFreshCheckMustDelegateToExistingTransfer,
            true
        );
        assert.equal(authorization.browserFreshSemanticCheckAuthorized, false);
        assert.equal(
            authorization.semanticTransferInBrowserClosureAuthorized,
            false
        );
    });

    it('authorizes only the CLI and owned-book presentation effects', () => {
        const authorization =
            CORE_PATHOUT_PRESENTATION_1F_REVIEW.authorization;
        assert.equal(authorization.cliApi[0],
            'runCorePathoutPresentationCli');
        assert.equal(authorization.cliCatalogAndParseMustRemainStatic, true);
        assert.equal(
            authorization.cliCheckMayDynamicallyLoadNodeAdapter,
            true
        );
        assert.equal(authorization.cliColdCompilationNoticeRequired, true);
        assert.equal(
            authorization.bookSource,
            'emdash2/book/chapters/05-induction-and-universal-properties.md'
        );
        assert.equal(authorization.generatedBookMarkdownEditAuthorized, false);
        assert.equal(authorization.newMathematicalClaimAuthorized, false);
    });

    it('requires proportional semantic, browser, CLI, and book evidence', () => {
        const evidence =
            CORE_PATHOUT_PRESENTATION_1F_REVIEW.requiredEvidence;
        assert.equal(evidence.focusedParserManifestFormatterTests, true);
        assert.equal(evidence.oneColdAllFourFormsSemanticCheck, true);
        assert.equal(evidence.malformedAndRoleEndpointNegatives, true);
        assert.equal(evidence.cliStaticAndSemanticContractTests, true);
        assert.equal(evidence.browserReviewerAndClosureTests, true);
        assert.equal(evidence.browserTemplateProductionBuild, true);
        assert.equal(evidence.bookTypographyCheckAndRender, true);
        assert.equal(evidence.testRunnerRegistration, true);
        assert.equal(evidence.checkAllRequired, false);
        assert.equal(evidence.activeLambdapiRerunRequired, false);
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'PATHOUT_PRESENTATION_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.audit as {
                    existingLfExpressionParserLocated: boolean;
                }).existingLfExpressionParserLocated = true;
            },
            'PATHOUT_PRESENTATION_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    browserFreshSemanticCheckAuthorized: boolean;
                }).browserFreshSemanticCheckAuthorized = true;
            },
            'PATHOUT_PRESENTATION_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('remains root-only and denies semantic, package, and hosted widening',
        () => {
            const review = CORE_PATHOUT_PRESENTATION_1F_REVIEW;
            assert.equal(review.decision.status, 'approved');
            assert.equal(review.decision.implementationAuthorized, true);
            assert.equal(
                review.authorization.genericEngineOrCoreChangeAuthorized,
                false
            );
            assert.equal(
                review.authorization.newRuntimeOrProofRuleAuthorized,
                false
            );
            assert.equal(
                review.authorization.packageVersionOrReleaseAuthorized,
                false
            );
            assert.equal(
                review.authorization.integrationOrDeploymentAuthorized,
                false
            );
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
                    /pathout_presentation_review/u,
                    relative
                );
            }
        });
});
