/**
 * Separate immutable review of PATHOUT-LIBRARY-PRESENTATION-1F proposal 1.
 *
 * This review approves only proposal checkpoint 6ad0812 and its exact
 * digest. It preserves the split between browser-safe qualification and an
 * explicit Node-owned fresh semantic check.
 */

import {
    CORE_PATHOUT_PRESENTATION_1F_PROPOSAL,
    validateCorePathoutPresentation1fProposal
} from './pathout_presentation_proposal';

export const CORE_PATHOUT_PRESENTATION_1F_REVIEW_REVISION =
    'PATHOUT-LIBRARY-PRESENTATION-1F-REVIEW-1' as const;

const APPROVED_PROPOSAL_CHECKPOINT = '6ad0812';
const APPROVED_PROPOSAL_SHA256 =
    'b7b85c34af390a5b1489b0fdd0d015cd2a4ca554c38533bf4459b7ec26029be3';

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

const authorization = {
    exactImplementationStages: [
        'PATHOUT-LIBRARY-PRESENTATION-1F1',
        'PATHOUT-LIBRARY-PRESENTATION-1F2',
        'PATHOUT-LIBRARY-PRESENTATION-1F3',
        'PATHOUT-LIBRARY-PRESENTATION-1F4'
    ],
    expressionForms: [
        'pathout-category',
        'canonical-rho',
        'fixed-source-induction',
        'composition-normal-form'
    ],
    browserSafeApi: [
        'CORE_PATHOUT_PRESENTATION_1F_MANIFEST',
        'parseCorePathoutPresentationText',
        'serializeCorePathoutPresentationRequest',
        'createCorePathoutQualificationReport',
        'formatCorePathoutQualificationReport'
    ],
    nodeSemanticApi: [
        'checkCorePathoutPresentationRequest',
        'formatCorePathoutFreshCheck'
    ],
    cliApi: ['runCorePathoutPresentationCli'],
    browserLoader: 'loadCorePathoutPresentation',
    browserPanel: 'lazy-static-PathOut-qualification-panel',
    bookSource:
        'emdash2/book/chapters/05-induction-and-universal-properties.md',
    bookPlacement:
        'after-composition-diagnostic-before-return-to-literal-equality',
    finiteExpressionParserAuthorized: true,
    variableRenamingAuthorized: true,
    sourceLocatedDiagnosticsRequired: true,
    canonicalSerializationRequired: true,
    parserReturnsInertRequest: true,
    parserMayClaimTyping: false,
    parserMayClaimQualification: false,
    declarationOrBinderSyntaxAuthorized: false,
    categoricalParserWideningAuthorized: false,
    staticQualificationManifestAuthorized: true,
    staticManifestMustPinSemanticCheckpoints: true,
    staticManifestMustSayNotRerunInBrowser: true,
    nodeFreshSemanticCheckAuthorized: true,
    nodeFreshCheckMustDelegateToExistingTransfer: true,
    nodeFreshCheckMustUseOrdinaryLfChecker: true,
    nodeFreshCheckMayUseExistingComparator: true,
    processLocalCompilationCacheAuthorized: true,
    hiddenServerOrMutableSessionAuthorized: false,
    browserFreshSemanticCheckAuthorized: false,
    semanticTransferInBrowserClosureAuthorized: false,
    cliCatalogAndParseMustRemainStatic: true,
    cliCheckMayDynamicallyLoadNodeAdapter: true,
    cliColdCompilationNoticeRequired: true,
    contributorBarrelChangeAuthorized: false,
    npmBarrelChangeAuthorized: false,
    packageVersionOrReleaseAuthorized: false,
    activeLambdapiSourceChangeAuthorized: false,
    generatedBookMarkdownEditAuthorized: false,
    newMathematicalClaimAuthorized: false,
    genericEngineOrCoreChangeAuthorized: false,
    newRuntimeOrProofRuleAuthorized: false,
    integrationOrDeploymentAuthorized: false
} as const;

const requiredEvidence = {
    focusedParserManifestFormatterTests: true,
    oneColdAllFourFormsSemanticCheck: true,
    malformedAndRoleEndpointNegatives: true,
    cliStaticAndSemanticContractTests: true,
    browserReviewerAndClosureTests: true,
    browserTemplateProductionBuild: true,
    bookTypographyCheckAndRender: true,
    rootTypecheckAndFocusedLint: true,
    workspaceCheck: true,
    testRunnerRegistration: true,
    checkTsDisposition:
        'one-completed-shared-boundary-run-unless-exact-human-waiver',
    checkAllRequired: false,
    activeLambdapiRerunRequired: false,
    exactDiffAndWhitespaceReview: true
} as const;

const rawReview = {
    revision: CORE_PATHOUT_PRESENTATION_1F_REVIEW_REVISION,
    status: 'approved-exact-proposal-for-bounded-implementation',
    approval: {
        approvedProposalRevision:
            CORE_PATHOUT_PRESENTATION_1F_PROPOSAL.revision,
        approvedProposalCheckpoint: APPROVED_PROPOSAL_CHECKPOINT,
        approvedProposalSha256: APPROVED_PROPOSAL_SHA256,
        authority: 'user-delegated-unattended-approval',
        humanDecisionSupersedes: true
    },
    recommendation: CORE_PATHOUT_PRESENTATION_1F_PROPOSAL,
    authorization,
    requiredEvidence,
    findings: [
        {
            id: 'PRESENTATION-REVIEW-FINDING-1',
            disposition: 'approve',
            statement:
                'The completed semantic transfer is sufficient; ' +
                'presentation must not add another equation or checker.'
        },
        {
            id: 'PRESENTATION-REVIEW-FINDING-2',
            disposition: 'approve-with-visible-evidence-class',
            statement:
                'A pinned browser qualification report is useful only when ' +
                'it visibly distinguishes itself from a fresh Node check.'
        },
        {
            id: 'PRESENTATION-REVIEW-FINDING-3',
            disposition: 'approve-expression-only',
            statement:
                'The four finite forms cover the mathematical story without ' +
                'a declaration parser or categorical-parser widening.'
        },
        {
            id: 'PRESENTATION-REVIEW-FINDING-4',
            disposition: 'approve-owned-book-bridge',
            statement:
                'Chapter 5 needs implementation provenance, not another ' +
                'derivation of its already checked mathematics.'
        }
    ],
    decision: {
        status: 'approved',
        implementationAuthorized: true,
        exactProposalOnly: true,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize:
        CORE_PATHOUT_PRESENTATION_1F_PROPOSAL.doesNotAuthorize,
    nextDependencyState:
        'pathout-presentation-1f-reviewed-implementation-ready'
} as const;

export type CorePathoutPresentation1fReview = typeof rawReview;

export type CorePathoutPresentation1fReviewErrorCode =
    | 'PATHOUT_PRESENTATION_REVIEW_DECISION_DRIFT'
    | 'PATHOUT_PRESENTATION_REVIEW_PROPOSAL_DRIFT'
    | 'PATHOUT_PRESENTATION_REVIEW_AUTHORIZATION_DRIFT';

export class CorePathoutPresentation1fReviewError extends Error {
    constructor(
        public readonly code: CorePathoutPresentation1fReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutPresentation1fReviewError';
    }
}

export const CORE_PATHOUT_PRESENTATION_1F_REVIEW = deepFreeze(rawReview);

export function cloneCorePathoutPresentation1fReview():
CorePathoutPresentation1fReview {
    return JSON.parse(JSON.stringify(rawReview)) as
        CorePathoutPresentation1fReview;
}

export function validateCorePathoutPresentation1fReview(
    review: CorePathoutPresentation1fReview =
        CORE_PATHOUT_PRESENTATION_1F_REVIEW
): CorePathoutPresentation1fReview {
    validateCorePathoutPresentation1fProposal();
    if (
        review.approval.approvedProposalCheckpoint !==
            APPROVED_PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !==
            APPROVED_PROPOSAL_SHA256 ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        !sameData(review.decision, rawReview.decision)
    ) {
        throw new CorePathoutPresentation1fReviewError(
            'PATHOUT_PRESENTATION_REVIEW_DECISION_DRIFT',
            'PathOut presentation review decision drifted'
        );
    }
    if (!sameData(
        review.recommendation,
        CORE_PATHOUT_PRESENTATION_1F_PROPOSAL
    )) {
        throw new CorePathoutPresentation1fReviewError(
            'PATHOUT_PRESENTATION_REVIEW_PROPOSAL_DRIFT',
            'PathOut presentation review proposal drifted'
        );
    }
    const reviewScope = {
        revision: review.revision,
        status: review.status,
        authorization: review.authorization,
        requiredEvidence: review.requiredEvidence,
        findings: review.findings,
        doesNotAuthorize: review.doesNotAuthorize,
        nextDependencyState: review.nextDependencyState
    };
    const expectedScope = {
        revision: rawReview.revision,
        status: rawReview.status,
        authorization: rawReview.authorization,
        requiredEvidence: rawReview.requiredEvidence,
        findings: rawReview.findings,
        doesNotAuthorize: rawReview.doesNotAuthorize,
        nextDependencyState: rawReview.nextDependencyState
    };
    if (!sameData(reviewScope, expectedScope)) {
        throw new CorePathoutPresentation1fReviewError(
            'PATHOUT_PRESENTATION_REVIEW_AUTHORIZATION_DRIFT',
            'PathOut presentation review authorization drifted'
        );
    }
    return deepFreeze(review);
}
