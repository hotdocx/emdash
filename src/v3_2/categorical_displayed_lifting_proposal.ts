/**
 * Executable DISPLAYED-LIFTING-0A proposal and owner/action audit.
 *
 * This artifact records the post-DISPLAYED-BRACKET-1A correction that
 * contextual abstraction is recursive compilation over the existing typed
 * construction IR. It does not introduce a second raw language, checker, or
 * parser. The matrix distinguishes frontend coverage from missing coherent
 * displayed mathematics before any DISPLAYED-LIFTING-1A implementation.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT,
    CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT_REVISION,
    validateCoreCategoricalDisplayedBracketContract
} from './categorical_displayed_bracket_contract';

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const rawProposal = {
    revision: 'DISPLAYED-LIFTING-0A-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-lifting-01',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01',
    decisionId: 'D-DTTLF-USABILITY-010',
    prerequisite: {
        displayedBracketDecision: 'D-DTTLF-USABILITY-009',
        displayedBracketContractRevision:
            CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT_REVISION,
        displayedBracketImplementationCheckpoint:
            'd4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab',
        displayedBracketLedgerCheckpoint: '6746d7b',
        implementationComplete: true,
        successorAutomaticallyAuthorized: false,
        measuredRootGate: {
            tests: 841,
            passed: 795,
            skipped: 46,
            failed: 0
        }
    },
    clarifiedGoal: {
        endUserUsability:
            'bound-variables-may-occur-recursively-under-supported-' +
            'typed-subexpressions',
        bracketMeaning:
            'internal-syntax-directed-contextual-lifting-operation',
        explicitBracketPunctuationRequired: false,
        stringParsingRequired: false,
        superficialConvenienceLayer: false,
        categoricalApplicationSelectionRequired: [
            'fapp0-or-fapp1',
            'tapp0-or-tapp1',
            'displayed-and-reindexed-counterparts',
            'variance-sensitive-precomposition-or-postcomposition'
        ]
    },
    architectureCorrection: {
        sourceBoundary: 'existing-typed-typescript-construction-ir',
        explicitTarget: 'backend-neutral-explicit-emdash-core',
        genericCheckerReused: true,
        rawExprLayerAdded: false,
        bidirectionalCheckerAdded: false,
        parserSelected: false,
        wholeBodyRecognizerExtended: false,
        recursion:
            'typed-node-by-typed-node-with-contextual-occurrence-evidence',
        unsupportedNodePolicy: 'fail-closed-with-source-provenance',
        sharedOrdinaryDisplayedAlgorithmRequired: false,
        separateOrdinaryDisplayedAlgorithmsRequired: false,
        selectionCriterion:
            'natural-scalable-non-hacky-solution-for-each-typed-judgment'
    },
    migrationAssessment: {
        migrationRow: 'MIGRATE-2',
        legacyGenericLfFrontendPhysicallyDeleted: true,
        legacyMechanismsRecoverableFromMainAndHistory: true,
        priorRecursiveCategoricalBracketSolutionDeleted: false,
        staleCategorySpecificApiRestorationSelected: false,
        conclusion:
            'the-current-gap-is-unimplemented-displayed-lifting-coverage-' +
            'and-authority-not-a-discarded-categorical-bracket'
    },
    matrixAxes: [
        'typed-constructor-or-application-judgment',
        'subject-closed-or-context-varying',
        'argument-closed-or-context-varying',
        'binder-mode-and-cell-level',
        'covariant-or-contravariant-position',
        'ordinary-or-displayed-dependent-family',
        'active-owner-derived-composite-or-exact-gap'
    ],
    ordinaryMatrix: [
        {
            id: 'ordinary-slot',
            occurrence: 'open',
            status: 'implemented-recursively',
            lowering: 'identity-functor'
        },
        {
            id: 'ordinary-closed-term',
            occurrence: 'closed',
            status: 'implemented-recursively',
            lowering: 'constant-functor-abstraction'
        },
        {
            id: 'ordinary-closed-subject-open-argument',
            subject: 'closed',
            argument: 'open',
            status: 'implemented-recursively',
            lowering: 'functor-composition'
        },
        {
            id: 'ordinary-open-subject-closed-argument',
            subject: 'open',
            argument: 'closed',
            status: 'implemented-and-permanent-regression',
            example: 'lambda x :^f A. F x y0',
            lowering:
                'Eval_func-after-Product_pair-of-F-after-id-and-Const-y0',
            specializedActiveOwner: 'fapp0_func'
        },
        {
            id: 'ordinary-open-subject-open-argument',
            subject: 'open',
            argument: 'open',
            status: 'implemented-recursively',
            lowering: 'Eval_func-after-Product_pair'
        },
        {
            id: 'ordinary-nested-abstraction',
            occurrence: 'open-under-abstraction',
            status: 'implemented-recursively',
            lowering: 'curry-package'
        }
    ],
    displayedMatrix: [
        {
            id: 'displayed-slot',
            subject: 'not-applicable',
            argument: 'open',
            status: 'implemented',
            activeAuthority: [
                'id_funcd',
                'Product_projL_funcd',
                'Product_projR_funcd'
            ],
            frontendRoute: 'displayed-slot-compilation'
        },
        {
            id: 'displayed-closed-subject-open-argument',
            subject: 'closed-coherent-displayed-functor',
            argument: 'open',
            status: 'implemented',
            activeAuthority: ['comp_fapp0'],
            frontendRoute: 'closed-displayed-functor-application'
        },
        {
            id: 'displayed-fibre-pair',
            subject: 'not-applicable',
            argument: 'two-recursively-compiled-branches',
            status: 'implemented',
            activeAuthority: ['Product_pair_funcd'],
            frontendRoute: 'fibrePair'
        },
        {
            id: 'displayed-closed-section-weakening',
            subject: 'closed-section',
            argument: 'unused-bound-slot',
            status: 'implemented-qualified',
            activeAuthority: ['section_pullback_func'],
            qualification: 'exact-supported-weakening-shape'
        },
        {
            id: 'displayed-open-subject-closed-argument',
            subject: 'context-varying-fibre-functor',
            argument: 'closed-or-coherent-section',
            status: 'authority-or-derived-construction-unresolved',
            activeIngredients: [
                'Functor_catd',
                'Functor_catd_func',
                'Eval_func',
                'fapp0_func'
            ],
            exactGap:
                'coherent-displayed-evaluation-from-Functor_catd-' +
                'times-source-family',
            frontendConsequence:
                'do-not-add-an-owner-specific-application-case-yet'
        },
        {
            id: 'displayed-open-subject-open-argument',
            subject: 'context-varying-fibre-functor',
            argument: 'context-varying-fibre-object',
            status: 'authority-or-derived-construction-unresolved',
            activeIngredients: [
                'Functor_catd',
                'Eval_func',
                'Product_pair_funcd'
            ],
            exactGap:
                'coherent-displayed-evaluation-and-its-reindexing-laws',
            frontendConsequence:
                'pairing-is-present-but-does-not-by-itself-supply-evaluation'
        },
        {
            id: 'displayed-nested-abstraction',
            subject: 'context-varying',
            argument: 'open-under-displayed-abstraction',
            status: 'architecture-comparison-required',
            alternatives: [
                'direct-displayed-curry',
                'sequential-totalization',
                'repeated-pullback-or-sigma'
            ],
            exactGap:
                'typed-source-target-and-coherence-for-one-nested-case'
        },
        {
            id: 'displayed-genuine-dependent-chain',
            subject: 'later-family-depends-on-earlier-slot',
            argument: 'open',
            status: 'separate-displayed-chain-0a',
            exactGap:
                'one-dependency-edge-comparison-and-sigma-arrow-action-audit'
        },
        {
            id: 'displayed-contravariant-action',
            subject: 'context-varying-in-negative-position',
            argument: 'open',
            status: 'frontend-route-unselected',
            activeIngredients: [
                'Functor_catd',
                'Functor_catd_func',
                'Op_catd',
                'precomposition-and-postcomposition-actions'
            ],
            exactGap:
                'typed-polarity-directed-contextual-lowering'
        },
        {
            id: 'displayed-higher-transformation-action',
            subject: 'transformation-valued',
            argument: 'object-or-arrow-level',
            status: 'separate-displayed-nd-0a',
            activeIngredients: [
                'tapp0-family',
                'tapp1-family',
                'tdapp-family',
                'fdapp-family'
            ],
            exactGap:
                'general-coherence-synthesis-and-cell-level-selection'
        },
        {
            id: 'displayed-profile-composition',
            subject: 'dependent-target-profile',
            argument: 'direct-displayed-bracket-profile',
            status: 'measured-transfer-presentation-mismatch',
            diagnostic: 'TYPE_MISMATCH',
            semanticPatchAuthorized: false,
            exactGap:
                'isolate-profile-join-before-attributing-to-mathematics'
        }
    ],
    ownerAuditConclusion: {
        ordinaryFixedEvaluationProven: true,
        closedDisplayedCompositionProven: true,
        displayedPairingProven: true,
        genericCoherentDisplayedEvaluationOwnerSelected: false,
        genericCoherentDisplayedEvaluationLexicallyPresent: false,
        absenceProvesMathematicalImpossibility: false,
        requiredNextEvidence:
            'owner-position-probe-and-derived-construction-comparison',
        newOwnerRequiresSeparateGate: true
    },
    recommendedNextRow: {
        id: 'DISPLAYED-EVAL-0B',
        kind: 'read-only-owner-position-and-derived-construction-probe',
        implementationAuthorizedByThisProposal: false,
        questions: [
            'can-existing-Functor_catd-and-evaluation-authority-derive-' +
                'coherent-displayed-evaluation',
            'if-not-what-is-the-minimal-owner-signature-and-law-set',
            'which-fixed-argument-and-both-open-frontend-judgments-would-' +
                'the-result-license',
            'is-the-profile-join-mismatch-transfer-only-or-semantic'
        ],
        successBranches: [
            'freeze-existing-authority-DISPLAYED-LIFTING-1A',
            'open-separate-minimal-owner-proposal-before-lifting'
        ]
    },
    withheldRows: [
        'semantic-DISPLAYED-LIFTING-1A',
        'genuine-dependent-chain-lowering',
        'general-nd-coherence',
        'sigma-arrow-action',
        'generic-total-category-pullback-or-equivalence',
        'parser-or-bulk-transfer',
        'browser-or-deployed-profile'
    ],
    semanticDelta: {
        newLambdapiOwners: 0,
        newLambdapiRuntimeRules: 0,
        newLambdapiProofRules: 0,
        newIntrinsicCoreOwners: 0,
        newSurfaceAstLayers: 0,
        newCheckerLayers: 0,
        browserProfilePromotion: false
    },
    decisionEffects: {
        freezesRecursiveLiftingArchitecture: true,
        freezesOwnerActionMatrix: true,
        authorizesDisplayedEval0B: true,
        authorizesSemanticDisplayedLifting1A: false,
        authorizesNewKernelOwnerOrRule: false,
        authorizesDisplayedChainImplementation: false,
        authorizesGeneralNdCoherence: false,
        authorizesParserOrBulkTransfer: false,
        authorizesBrowserPromotion: false,
        broadensGitAuthority: false
    },
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/' +
        'D-DTTLF-USABILITY-010 as proposed: preserve the existing typed ' +
        'TypeScript IR, recursive contextual compiler, explicit Core, and ' +
        'generic checker without adding RawExpr, a second bidirectional ' +
        'checker, parser, or bracket punctuation; accept the executable ' +
        'owner/action matrix and its exact coherent displayed-evaluation ' +
        'gap; authorize only root/active-authority DISPLAYED-EVAL-0B ' +
        'owner-position and derived-construction probes; and keep semantic ' +
        'DISPLAYED-LIFTING-1A, any new kernel owner/rule, genuine-chain ' +
        'lowering, general :^nd coherence, Sigma arrow action, parsing/' +
        'bulk transfer, browser promotion, and broader Git authority ' +
        'withheld pending separate exact proposals?'
} as const;

export type CoreCategoricalDisplayedLiftingProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedLiftingProposalErrorCode =
    | 'DISPLAYED_LIFTING_PREREQUISITE_DRIFT'
    | 'DISPLAYED_LIFTING_ARCHITECTURE_DRIFT'
    | 'DISPLAYED_LIFTING_MATRIX_DRIFT'
    | 'DISPLAYED_LIFTING_AUTHORITY_DRIFT'
    | 'DISPLAYED_LIFTING_PROPOSAL_DRIFT';

export class CoreCategoricalDisplayedLiftingProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedLiftingProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedLiftingProposalError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL =
    deepFreeze(rawProposal);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreCategoricalDisplayedLiftingProposal(
    proposal: CoreCategoricalDisplayedLiftingProposalInput =
        CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL
): void {
    try {
        validateCoreCategoricalDisplayedBracketContract();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedLiftingProposalError(
            'DISPLAYED_LIFTING_PREREQUISITE_DRIFT',
            'The implemented displayed-bracket contract drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        proposal.prerequisite.displayedBracketDecision !==
            'D-DTTLF-USABILITY-009' ||
        proposal.prerequisite.displayedBracketContractRevision !==
            CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT.revision ||
        !proposal.prerequisite.implementationComplete ||
        proposal.prerequisite.successorAutomaticallyAuthorized ||
        proposal.prerequisite.measuredRootGate.failed !== 0 ||
        proposal.prerequisite.measuredRootGate.tests !== 841
    ) {
        throw new CoreCategoricalDisplayedLiftingProposalError(
            'DISPLAYED_LIFTING_PREREQUISITE_DRIFT',
            'The DISPLAYED-BRACKET-1A implementation evidence drifted'
        );
    }

    const architecture = proposal.architectureCorrection;
    if (
        architecture.sourceBoundary !==
            'existing-typed-typescript-construction-ir' ||
        !architecture.genericCheckerReused ||
        architecture.rawExprLayerAdded ||
        architecture.bidirectionalCheckerAdded ||
        architecture.parserSelected ||
        architecture.wholeBodyRecognizerExtended ||
        proposal.clarifiedGoal.explicitBracketPunctuationRequired ||
        proposal.clarifiedGoal.stringParsingRequired ||
        proposal.migrationAssessment.priorRecursiveCategoricalBracketSolutionDeleted ||
        proposal.migrationAssessment.staleCategorySpecificApiRestorationSelected
    ) {
        throw new CoreCategoricalDisplayedLiftingProposalError(
            'DISPLAYED_LIFTING_ARCHITECTURE_DRIFT',
            'The recursive typed-IR architecture correction drifted'
        );
    }

    const ordinaryFixed = proposal.ordinaryMatrix.find(
        row => row.id ===
            'ordinary-open-subject-closed-argument'
    );
    const displayedFixed = proposal.displayedMatrix.find(
        row => row.id ===
            'displayed-open-subject-closed-argument'
    );
    const displayedBoth = proposal.displayedMatrix.find(
        row => row.id ===
            'displayed-open-subject-open-argument'
    );
    const profileJoin = proposal.displayedMatrix.find(
        row => row.id === 'displayed-profile-composition'
    );
    if (
        proposal.matrixAxes.length !== 7 ||
        proposal.ordinaryMatrix.length !== 6 ||
        proposal.displayedMatrix.length !== 11 ||
        ordinaryFixed?.status !==
            'implemented-and-permanent-regression' ||
        ordinaryFixed.example !== 'lambda x :^f A. F x y0' ||
        displayedFixed?.status !==
            'authority-or-derived-construction-unresolved' ||
        displayedBoth?.status !==
            'authority-or-derived-construction-unresolved' ||
        profileJoin?.status !==
            'measured-transfer-presentation-mismatch' ||
        profileJoin.semanticPatchAuthorized
    ) {
        throw new CoreCategoricalDisplayedLiftingProposalError(
            'DISPLAYED_LIFTING_MATRIX_DRIFT',
            'The typed occurrence/variance owner matrix drifted'
        );
    }

    if (
        !proposal.ownerAuditConclusion.ordinaryFixedEvaluationProven ||
        !proposal.ownerAuditConclusion.closedDisplayedCompositionProven ||
        !proposal.ownerAuditConclusion.displayedPairingProven ||
        proposal.ownerAuditConclusion
            .genericCoherentDisplayedEvaluationOwnerSelected ||
        proposal.ownerAuditConclusion
            .genericCoherentDisplayedEvaluationLexicallyPresent ||
        proposal.ownerAuditConclusion
            .absenceProvesMathematicalImpossibility ||
        !proposal.ownerAuditConclusion.newOwnerRequiresSeparateGate ||
        proposal.recommendedNextRow.id !== 'DISPLAYED-EVAL-0B' ||
        proposal.recommendedNextRow.implementationAuthorizedByThisProposal ||
        Object.values(proposal.semanticDelta).some(Boolean) ||
        proposal.decisionEffects.authorizesSemanticDisplayedLifting1A ||
        proposal.decisionEffects.authorizesNewKernelOwnerOrRule ||
        proposal.decisionEffects.authorizesDisplayedChainImplementation ||
        proposal.decisionEffects.authorizesGeneralNdCoherence ||
        proposal.decisionEffects.authorizesParserOrBulkTransfer ||
        proposal.decisionEffects.authorizesBrowserPromotion ||
        proposal.decisionEffects.broadensGitAuthority
    ) {
        throw new CoreCategoricalDisplayedLiftingProposalError(
            'DISPLAYED_LIFTING_AUTHORITY_DRIFT',
            'The proposal would hide an authority gap or broaden scope'
        );
    }

    if (
        proposal.revision !==
            'DISPLAYED-LIFTING-0A-PROPOSAL-1' ||
        proposal.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-lifting-01' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-010' ||
        !proposal.decisionEffects.freezesRecursiveLiftingArchitecture ||
        !proposal.decisionEffects.freezesOwnerActionMatrix ||
        !proposal.decisionEffects.authorizesDisplayedEval0B ||
        !sameData(proposal, rawProposal)
    ) {
        throw new CoreCategoricalDisplayedLiftingProposalError(
            'DISPLAYED_LIFTING_PROPOSAL_DRIFT',
            'The exact DISPLAYED-LIFTING-0A proposal or decision drifted'
        );
    }
}

validateCoreCategoricalDisplayedLiftingProposal();
