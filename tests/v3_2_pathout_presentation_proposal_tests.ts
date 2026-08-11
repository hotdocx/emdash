/**
 * Focused tests for the non-authorizing PathOut presentation proposal.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY
} from '../src/v3_2/pathout_transitivity_transfer';
import {
    CORE_PATHOUT_PRESENTATION_1F_PROPOSAL,
    CorePathoutPresentation1fProposal,
    CorePathoutPresentation1fProposalError,
    cloneCorePathoutPresentation1fProposal,
    validateCorePathoutPresentation1fProposal
} from '../src/v3_2/pathout_presentation_proposal';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

const assertProposalError = (
    mutate: (proposal: CorePathoutPresentation1fProposal) => void,
    expected: CorePathoutPresentation1fProposalError['code']
): void => {
    const proposal = cloneCorePathoutPresentation1fProposal();
    mutate(proposal);
    assert.throws(
        () => validateCorePathoutPresentation1fProposal(proposal),
        error =>
            error instanceof CorePathoutPresentation1fProposalError &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-PRESENTATION-1F proposal', () => {
    it('pins the completed semantic and public-package parents', () => {
        const proposal = validateCorePathoutPresentation1fProposal();
        assertDeepFrozen(proposal);
        assert.deepEqual(
            [
                proposal.parent.pathoutFoundationSemanticCheckpoint,
                proposal.parent.pathindFixedSourceSemanticCheckpoint,
                proposal.parent.genericComparisonAndBudgetCheckpoint,
                proposal.parent.pathindInternalizedSemanticCheckpoint,
                proposal.parent.pathoutTransitivitySemanticCheckpoint,
                proposal.parent.pathoutTransitivityLedgerCheckpoint
            ],
            [
                '550316a',
                'a361dc3',
                'e560551',
                'b6005b3',
                '3b113ad',
                '10432ba'
            ]
        );
        assert.equal(
            proposal.parent.pathoutTransitivityTransferSha256,
            'dd9484a58c6196fe5cc9c6c1ac941bea0a148c449855d011fc61fbcf3dc3fe9d'
        );
        assert.equal(
            proposal.parent.pathoutTransitivityFocusedTestSha256,
            'dda1a5436dabc02065aa02e30b1a14000c015783a866a894aa7884d40cae7dbf'
        );
        assert.deepEqual(
            [
                proposal.parent.publicPackage.name,
                proposal.parent.publicPackage.version,
                proposal.parent.publicPackage.releaseCandidateCheckpoint,
                proposal.parent.publicPackage.releaseCompletionCheckpoint
            ],
            ['@hotdocx/emdash', '0.2.0', 'ab513f7', 'e35d5ae']
        );
        assert.equal(
            CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.proposalCheckpoint,
            proposal.parent.pathoutTransitivityProposalCheckpoint
        );
        assert.equal(
            CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.reviewCheckpoint,
            proposal.parent.pathoutTransitivityReviewCheckpoint
        );
        assert.equal(
            JSON.parse(readFileSync(
                resolve(repositoryRoot, 'packages/emdash/package.json'),
                'utf8'
            )).version,
            proposal.parent.publicPackage.version
        );
    });

    it('freezes four expression-only forms and no declaration grammar', () => {
        const syntax = CORE_PATHOUT_PRESENTATION_1F_PROPOSAL.textSyntax;
        assert.deepEqual(
            syntax.forms.map(form => [
                form.id,
                form.head,
                form.canonicalSource,
                form.arity,
                form.semanticTarget
            ]),
            [
                [
                    'pathout-category',
                    'PathOut',
                    'PathOut(Z, x)',
                    2,
                    'PathOut_cat'
                ],
                [
                    'canonical-rho',
                    'rho',
                    'rho(Z, x, y, p)',
                    4,
                    'pathout_refl_arrow'
                ],
                [
                    'fixed-source-induction',
                    'Ind',
                    'Ind(Z, x, E, u)',
                    4,
                    'path_ind_sec'
                ],
                [
                    'composition-normal-form',
                    'compose',
                    'compose(Z, x, y, z, p, q)',
                    6,
                    'path_comp_func-applied-at-q'
                ]
            ]
        );
        assert.equal(syntax.expressionOnly, true);
        assert.equal(syntax.declarationSyntax, false);
        assert.equal(syntax.binderSyntax, false);
        assert.equal(syntax.parserOutput,
            'inert-CorePathoutPresentationRequest');
        assert.equal(syntax.parsingImpliesTyping, false);
        assert.equal(syntax.parsingImpliesQualification, false);
    });

    it('separates fast qualification from explicit semantic replay', () => {
        const proposal = CORE_PATHOUT_PRESENTATION_1F_PROPOSAL;
        assert.equal(proposal.implementationStages.length, 4);
        assert.deepEqual(
            proposal.implementationStages.map(stage => [
                stage.id,
                stage.importsSemanticTransfer,
                stage.canClaimFreshSemanticCheck
            ]),
            [
                ['PATHOUT-LIBRARY-PRESENTATION-1F1', false, false],
                ['PATHOUT-LIBRARY-PRESENTATION-1F2', true, true],
                ['PATHOUT-LIBRARY-PRESENTATION-1F3', false, false],
                ['PATHOUT-LIBRARY-PRESENTATION-1F4', false, false]
            ]
        );
        assert.equal(
            proposal.audit.measuredColdTransitivityCompilationMs,
            195_346
        );
        assert.equal(
            proposal.browserContract.freshSemanticCheckAvailable,
            false
        );
        assert.equal(
            proposal.browserContract.semanticTransferExcludedFromBrowserClosure,
            true
        );
        assert.equal(
            proposal.semanticDelegation.compiler,
            'compileCorePathoutTransitivity1eTransfer'
        );
        assert.equal(proposal.semanticDelegation.localRuleOrDefinitionDelta, 0);
        assert.equal(proposal.semanticDelegation.genericEngineDelta, 0);
        assert.equal(proposal.semanticDelegation.CoreNodeDelta, 0);
    });

    it('freezes explicit CLI, browser, book, and validation boundaries', () => {
        const proposal = CORE_PATHOUT_PRESENTATION_1F_PROPOSAL;
        assert.deepEqual(proposal.cliContract.commands, [
            'catalog [--format text|json]',
            'parse EXAMPLE [--source EXPRESSION] [--format text|json]',
            'check EXAMPLE [--source EXPRESSION] [--format text|json]'
        ]);
        assert.equal(
            proposal.cliContract.catalogAndParseMustNotLoadSemanticTransfer,
            true
        );
        assert.equal(
            proposal.bookContract.sourceChapter,
            'emdash2/book/chapters/05-induction-and-universal-properties.md'
        );
        assert.equal(
            proposal.bookContract.generatedMarkdownMayBeHandEdited,
            false
        );
        assert.equal(proposal.validation.checkAllRequired, false);
        assert.equal(proposal.validation.activeLambdapiRerunRequired, false);
        assert.equal(
            proposal.validation.testRunnerRegistrationRequiredForBehavior,
            true
        );
    });

    it('denies package, semantic, deployment, and parser widening', () => {
        const proposal = CORE_PATHOUT_PRESENTATION_1F_PROPOSAL;
        assert.deepEqual(
            Object.values(proposal.integration),
            Array.from({ length: 8 }, () => false)
        );
        for (const denial of [
            'generic-Lambdapi-or-declaration-parser',
            'widening-the-existing-categorical-text-parser',
            'browser-side-fresh-PathOut-transfer-compilation',
            'static-parse-or-checkpoint-report-claimed-as-a-fresh-check',
            'new-Core-checker-evaluator-comparison-runtime-or-proof-semantics',
            'public-package-entry-version-release-or-publication',
            'active-Lambdapi-source-or-mathematics-edit',
            'generated-book-Markdown-hand-edit',
            'external-integration-push-merge-deployment-or-cleanup'
        ]) {
            assert.ok(proposal.doesNotAuthorize.includes(
                denial as typeof proposal.doesNotAuthorize[number]
            ));
        }
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    pathoutTransitivityLedgerCheckpoint: string;
                }).pathoutTransitivityLedgerCheckpoint = 'wrong';
            },
            'PATHOUT_PRESENTATION_PROPOSAL_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.browserContract as {
                    freshSemanticCheckAvailable: boolean;
                }).freshSemanticCheckAvailable = true;
            },
            'PATHOUT_PRESENTATION_PROPOSAL_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHOUT_PRESENTATION_PROPOSAL_AUTHORIZATION_DRIFT'
        );
    });

    it('is behavior-free, non-exported, and non-self-authorizing', () => {
        const proposal = CORE_PATHOUT_PRESENTATION_1F_PROPOSAL;
        assert.equal(proposal.decision.status, 'proposal-only');
        assert.equal(proposal.decision.implementationAuthorized, false);
        const source = readFileSync(
            resolve(
                repositoryRoot,
                'src/v3_2/pathout_presentation_proposal.ts'
            ),
            'utf8'
        );
        assert.doesNotMatch(source, /from ['"].*transfer/u);
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
                /pathout_presentation_proposal/u,
                relative
            );
        }
    });
});
