/**
 * Non-authorizing PATHOUT-LIBRARY-PRESENTATION-1F proposal.
 *
 * The completed PathOut/PathInd transfers are deliberately expensive to
 * construct from a cold process. This proposal separates a fast,
 * browser-safe qualification view from an explicit Node-owned fresh check.
 * Both routes describe the same finite expression vocabulary; only the
 * Node route may claim that it reran the existing TypeScript semantics.
 */

export const CORE_PATHOUT_PRESENTATION_1F_PROPOSAL_REVISION =
    'PATHOUT-LIBRARY-PRESENTATION-1F-PROPOSAL-1' as const;

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const parent = {
    pathoutFoundationSemanticCheckpoint: '550316a',
    pathindFixedSourceSemanticCheckpoint: 'a361dc3',
    genericComparisonAndBudgetCheckpoint: 'e560551',
    pathindInternalizedSemanticCheckpoint: 'b6005b3',
    pathoutTransitivityProposalCheckpoint: '2498053',
    pathoutTransitivityReviewCheckpoint: 'fc9a323',
    pathoutTransitivitySemanticCheckpoint: '3b113ad',
    pathoutTransitivityLedgerCheckpoint: '10432ba',
    pathoutTransitivityTransferSha256:
        'dd9484a58c6196fe5cc9c6c1ac941bea0a148c449855d011fc61fbcf3dc3fe9d',
    pathoutTransitivityFocusedTestSha256:
        'dda1a5436dabc02065aa02e30b1a14000c015783a866a894aa7884d40cae7dbf',
    publicPackage: {
        name: '@hotdocx/emdash',
        version: '0.2.0',
        releaseCandidateCheckpoint: 'ab513f7',
        releaseCompletionCheckpoint: 'e35d5ae',
        newExportAuthorized: false,
        versionChangeAuthorized: false,
        releaseAuthorized: false
    }
} as const;

const textForms = [
    {
        id: 'pathout-category',
        head: 'PathOut',
        canonicalSource: 'PathOut(Z, x)',
        argumentRoles: ['category', 'object-in-category'],
        arity: 2,
        semanticTarget: 'PathOut_cat',
        resultKind: 'category',
        qualificationClaim:
            'the outgoing-arrow category is the Sigma total of the ' +
            'fixed-source representable'
    },
    {
        id: 'canonical-rho',
        head: 'rho',
        canonicalSource: 'rho(Z, x, y, p)',
        argumentRoles: [
            'category',
            'source-object',
            'target-object',
            'source-to-target-arrow'
        ],
        arity: 4,
        semanticTarget: 'pathout_refl_arrow',
        resultKind: 'arrow-in-pathout',
        qualificationClaim:
            'the canonical Sigma arrow runs from the reflexive outgoing ' +
            'arrow to the selected outgoing arrow'
    },
    {
        id: 'fixed-source-induction',
        head: 'Ind',
        canonicalSource: 'Ind(Z, x, E, u)',
        argumentRoles: [
            'category',
            'source-object',
            'motive-over-pathout',
            'datum-at-reflexive-object'
        ],
        arity: 4,
        semanticTarget: 'path_ind_sec',
        resultKind: 'dependent-section',
        qualificationClaim:
            'transport of the base datum along rho gives a section over ' +
            'all outgoing arrows'
    },
    {
        id: 'composition-normal-form',
        head: 'compose',
        canonicalSource: 'compose(Z, x, y, z, p, q)',
        argumentRoles: [
            'category',
            'source-object',
            'middle-object',
            'target-object',
            'source-to-middle-arrow',
            'middle-to-target-arrow'
        ],
        arity: 6,
        semanticTarget: 'path_comp_func-applied-at-q',
        resultKind: 'source-to-target-arrow',
        qualificationClaim:
            'the selected component of arrow-induced composition reduces ' +
            'to stable representable precomposition q after p'
    }
] as const;

const implementationStages = [
    {
        id: 'PATHOUT-LIBRARY-PRESENTATION-1F1',
        owner: 'src/v3_2/pathout_presentation.ts',
        purpose:
            'browser-safe immutable qualification manifest, finite ' +
            'expression parser, canonical serializer, and report formatter',
        executionClass: 'fast-static-browser-safe',
        importsSemanticTransfer: false,
        canClaimFreshSemanticCheck: false
    },
    {
        id: 'PATHOUT-LIBRARY-PRESENTATION-1F2',
        owner: 'src/v3_2/pathout_presentation_check.ts',
        purpose:
            'explicit Node-owned adapter from parsed requests to the ' +
            'existing compiled PathOut transfer and ordinary LF checker',
        executionClass: 'explicit-cold-or-process-cached-semantic-check',
        importsSemanticTransfer: true,
        canClaimFreshSemanticCheck: true
    },
    {
        id: 'PATHOUT-LIBRARY-PRESENTATION-1F3',
        owner:
            'examples/v3_2_pathout_cli.ts and emdash-template reviewer',
        purpose:
            'one CLI command family and one lazy browser panel over the two ' +
            'preceding owners',
        executionClass: 'static-by-default-explicit-check-only-in-node',
        importsSemanticTransfer: false,
        canClaimFreshSemanticCheck: false
    },
    {
        id: 'PATHOUT-LIBRARY-PRESENTATION-1F4',
        owner:
            'emdash2/book/chapters/05-induction-and-universal-properties.md',
        purpose:
            'short implementation bridge beside the existing mathematical ' +
            'exposition, edited at the owned source rather than generated MD',
        executionClass: 'book-source-prose',
        importsSemanticTransfer: false,
        canClaimFreshSemanticCheck: false
    }
] as const;

const cliContract = {
    dispatcher: './scripts/emdash pathout',
    commands: [
        'catalog [--format text|json]',
        'parse EXAMPLE [--source EXPRESSION] [--format text|json]',
        'check EXAMPLE [--source EXPRESSION] [--format text|json]'
    ],
    catalogAndParseMustNotLoadSemanticTransfer: true,
    checkMustLoadSemanticAdapterExplicitly: true,
    checkMustWarnBeforeColdCompilation: true,
    processLocalCompilationCachePermitted: true,
    hiddenMutableServerPermitted: false,
    mcpRequired: false
} as const;

const browserContract = {
    lazyEntry: 'loadCorePathoutPresentation',
    defaultAction: 'parse-and-show-qualified-checkpoint-report',
    freshSemanticCheckAvailable: false,
    qualifiedCheckpointMustBeVisible: true,
    semanticTransferExcludedFromBrowserClosure: true,
    nodeOrFilesystemDependencyPermitted: false,
    claimLanguage: {
        static: 'qualified-at-pinned-checkpoint-not-rerun-in-browser',
        semantic: 'fresh-TypeScript-check-only-after-explicit-Node-command'
    }
} as const;

const bookContract = {
    sourceChapter: 'emdash2/book/chapters/05-induction-and-universal-properties.md',
    placement: 'after-composition-diagnostic-before-return-to-literal-equality',
    mathematicalClaimsRemainOwnedBy: [
        'IND-PATHOUT',
        'IND-ARROW',
        'IND-COMPOSITION'
    ],
    explain: [
        'sealed-trusted-profile-versus-transparent-derived-library',
        'expression-only-presentation-over-the-same-explicit-Core',
        'browser-qualified-manifest-versus-explicit-Node-fresh-check',
        'Lambdapi-as-bounded-conformance-oracle-not-production-runtime'
    ],
    generatedMarkdownMayBeHandEdited: false,
    newMathematicalTheoremClaimAuthorized: false
} as const;

const validation = {
    proposal: [
        'focused-proposal-tests',
        'root-typecheck',
        'focused-eslint',
        'non-export-and-diff-hygiene'
    ],
    implementation: [
        'focused-parser-manifest-and-formatter-tests',
        'one-cold-all-four-forms-TypeScript-semantic-check',
        'wrong-head-arity-variable-role-and-endpoint-negatives',
        'CLI-catalog-parse-and-in-process-check-contract-tests',
        'browser-reviewer-tests-and-static-closure-check',
        'browser-template-production-build',
        'book-typography-check-render',
        'root-typecheck-and-focused-eslint',
        'workspace-check-and-exact-diff-hygiene'
    ],
    testRunnerRegistrationRequiredForBehavior: true,
    rootCheckTsDisposition:
        'run-once-at-completed-shared-behavior-boundary-unless-an-exact-' +
        'human-waiver-is-recorded',
    checkAllRequired: false,
    activeLambdapiRerunRequired: false,
    reasonLambdapiRerunOmitted:
        'the presentation delegates to unchanged already-oracled transfers',
    longAggregatePolicy:
        'never-rerun-for-reassurance-and-never-misreport-carried-evidence'
} as const;

const rawProposal = {
    revision: CORE_PATHOUT_PRESENTATION_1F_PROPOSAL_REVISION,
    status: 'proposal-awaiting-separate-immutable-review',
    parent,
    audit: {
        existingLfExpressionParserLocated: false,
        existingCategoricalExpressionParserMayBeWidened: false,
        declarationParserRequired: false,
        existingBrowserReviewerPresetCount: 12,
        existingBookMathematicsSufficient: true,
        measuredColdTransitivityCompilationMs: 195_346,
        defaultBrowserFreshCompilationAppropriate: false,
        selectedArchitecture:
            'one-finite-expression-vocabulary-two-honest-execution-modes'
    },
    textSyntax: {
        grammar:
            'Expression := Head "(" Identifier ("," Identifier)* ")"',
        expressionOnly: true,
        declarationSyntax: false,
        binderSyntax: false,
        nestedApplicationSyntax: false,
        parserOutput: 'inert-CorePathoutPresentationRequest',
        parsingImpliesTyping: false,
        parsingImpliesQualification: false,
        variableRenamingSupported: true,
        canonicalSerializationRequired: true,
        forms: textForms
    },
    implementationStages,
    cliContract,
    browserContract,
    bookContract,
    semanticDelegation: {
        compiler: 'compileCorePathoutTransitivity1eTransfer',
        checker: 'createCoreLfChecker',
        comparator: 'coreLfDefinitionalCompare',
        localRuleOrDefinitionDelta: 0,
        genericEngineDelta: 0,
        CoreNodeDelta: 0,
        activeLambdapiSourceDelta: 0,
        semanticTransferMustRemainOutsideBrowserClosure: true
    },
    validation,
    integration: {
        contributorBarrelChangeAuthorized: false,
        npmBarrelChangeAuthorized: false,
        packageVersionChangeAuthorized: false,
        npmPublicationAuthorized: false,
        githubReleaseAuthorized: false,
        pagesDeploymentAuthorized: false,
        siblingRepositoryEditAuthorized: false,
        mergeOrPushAuthorized: false
    },
    decision: {
        question:
            'Approve the four-stage PathOut presentation boundary without ' +
            'adding a second semantic engine?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize: [
        'generic-Lambdapi-or-declaration-parser',
        'widening-the-existing-categorical-text-parser',
        'browser-side-fresh-PathOut-transfer-compilation',
        'static-parse-or-checkpoint-report-claimed-as-a-fresh-check',
        'new-Core-checker-evaluator-comparison-runtime-or-proof-semantics',
        'new-PathOut-PathInd-owner-rule-equation-or-normal-form',
        'ordinary-user-installed-runtime-or-proof-rules',
        'public-package-entry-version-release-or-publication',
        'active-Lambdapi-source-or-mathematics-edit',
        'generated-book-Markdown-hand-edit',
        'external-integration-push-merge-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-presentation-1f-awaiting-separate-immutable-review'
} as const;

export type CorePathoutPresentation1fProposal = typeof rawProposal;

export type CorePathoutPresentation1fProposalErrorCode =
    | 'PATHOUT_PRESENTATION_PROPOSAL_AUTHORITY_DRIFT'
    | 'PATHOUT_PRESENTATION_PROPOSAL_SCOPE_DRIFT'
    | 'PATHOUT_PRESENTATION_PROPOSAL_AUTHORIZATION_DRIFT';

export class CorePathoutPresentation1fProposalError extends Error {
    constructor(
        public readonly code: CorePathoutPresentation1fProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutPresentation1fProposalError';
    }
}

export const CORE_PATHOUT_PRESENTATION_1F_PROPOSAL =
    deepFreeze(rawProposal);

export function cloneCorePathoutPresentation1fProposal():
CorePathoutPresentation1fProposal {
    return JSON.parse(JSON.stringify(rawProposal)) as
        CorePathoutPresentation1fProposal;
}

export function validateCorePathoutPresentation1fProposal(
    proposal: CorePathoutPresentation1fProposal =
        CORE_PATHOUT_PRESENTATION_1F_PROPOSAL
): CorePathoutPresentation1fProposal {
    if (!sameData(proposal.parent, parent)) {
        throw new CorePathoutPresentation1fProposalError(
            'PATHOUT_PRESENTATION_PROPOSAL_AUTHORITY_DRIFT',
            'PathOut presentation proposal parent authority drifted'
        );
    }
    if (!sameData(proposal.decision, rawProposal.decision)) {
        throw new CorePathoutPresentation1fProposalError(
            'PATHOUT_PRESENTATION_PROPOSAL_AUTHORIZATION_DRIFT',
            'PathOut presentation proposal authorization drifted'
        );
    }
    const proposalScope = {
        revision: proposal.revision,
        status: proposal.status,
        audit: proposal.audit,
        textSyntax: proposal.textSyntax,
        implementationStages: proposal.implementationStages,
        cliContract: proposal.cliContract,
        browserContract: proposal.browserContract,
        bookContract: proposal.bookContract,
        semanticDelegation: proposal.semanticDelegation,
        validation: proposal.validation,
        integration: proposal.integration,
        doesNotAuthorize: proposal.doesNotAuthorize,
        nextDependencyState: proposal.nextDependencyState
    };
    const expectedScope = {
        revision: rawProposal.revision,
        status: rawProposal.status,
        audit: rawProposal.audit,
        textSyntax: rawProposal.textSyntax,
        implementationStages: rawProposal.implementationStages,
        cliContract: rawProposal.cliContract,
        browserContract: rawProposal.browserContract,
        bookContract: rawProposal.bookContract,
        semanticDelegation: rawProposal.semanticDelegation,
        validation: rawProposal.validation,
        integration: rawProposal.integration,
        doesNotAuthorize: rawProposal.doesNotAuthorize,
        nextDependencyState: rawProposal.nextDependencyState
    };
    if (!sameData(proposalScope, expectedScope)) {
        throw new CorePathoutPresentation1fProposalError(
            'PATHOUT_PRESENTATION_PROPOSAL_SCOPE_DRIFT',
            'PathOut presentation proposal scope drifted'
        );
    }
    return deepFreeze(proposal);
}
