/**
 * PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal.
 *
 * This freezes the smallest internally natural and Sigma-total PathInd slice
 * above the qualified fixed-source profile. It installs no declaration or
 * rule; a separate immutable review is required before implementation.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVISION,
    CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
} from './pathind_fixed_source_transfer';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT,
    validateCorePathoutTrustBoundary0aAudit
} from './pathout_trust_boundary_audit';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-1' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-01/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-001 as proposed.';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

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

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const auditedInternalizedProfile =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.smallestProfiles
        .internalizedInduction;
const sigmaTotalUncurryingClosure =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.prerequisiteClosures[3];

const trustedDeclarations = [
    {
        order: 0,
        name: 'Sigma_transfd_funcd',
        authorityLine: 13360,
        sourceKind: 'constant-symbol',
        policy: 'opaque-signature',
        role: 'sigma-total-uncurrying-prerequisite',
        coreName:
            'emdash_v3_2_pathind_internalized_Sigma_transfd_funcd'
    },
    {
        order: 1,
        name: 'PathOutReflEval_funcd',
        authorityLine: 19080,
        sourceKind: 'constant-symbol',
        policy: 'opaque-signature',
        role: 'internally-natural-source-owner',
        coreName:
            'emdash_v3_2_pathind_internalized_' +
            'PathOutReflEval_funcd'
    },
    {
        order: 2,
        name: 'PathInd_func',
        authorityLine: 19242,
        sourceKind: 'constant-symbol',
        policy: 'opaque-signature',
        role: 'fixed-source-displayed-functor-owner',
        coreName: 'emdash_v3_2_pathind_internalized_PathInd_func'
    },
    {
        order: 3,
        name: 'PathInd_transfd',
        authorityLine: 19281,
        sourceKind: 'constant-symbol',
        policy: 'opaque-signature',
        role: 'primary-internally-natural-theorem-owner',
        coreName: 'emdash_v3_2_pathind_internalized_PathInd_transfd'
    }
] as const;

const runtimeRules = [
    {
        order: 0,
        id: 'pathind.internalized.sigma-transfd-object-component',
        authorityLine: 14516,
        sourceOwner: 'tapp0_fapp0',
        resultOwner: 'tdapp0_fapp0',
        policy: 'runtime-rewrite'
    },
    {
        order: 1,
        id: 'pathind.internalized.pathout-refl-eval-component',
        authorityLine: 19084,
        sourceOwner: 'tapp0_fapp0',
        resultOwner: 'pathout_refl_eval_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 2,
        id: 'pathind.internalized.path-ind-functor-component',
        authorityLine: 19248,
        sourceOwner: 'tapp0_fapp0',
        resultOwner: 'path_ind_func_fapp0',
        policy: 'runtime-rewrite'
    },
    {
        order: 3,
        id: 'pathind.internalized.path-ind-transfd-component',
        authorityLine: 19409,
        sourceOwner: 'tdapp0_fapp0',
        resultOwner: 'PathInd_func',
        policy: 'runtime-rewrite'
    }
] as const;

const transparentDefinitions = [
    {
        order: 0,
        name: 'PathOutMotives_catd',
        authorityLine: 19002,
        stage: 'internalized-prelude',
        coreName:
            'emdash_v3_2_pathind_internalized_PathOutMotives_catd'
    },
    {
        order: 1,
        name: 'PathOutPi_funcd',
        authorityLine: 19018,
        stage: 'internalized-prelude',
        coreName: 'emdash_v3_2_pathind_internalized_PathOutPi_funcd'
    },
    {
        order: 2,
        name: 'PathIndTgt_catd',
        authorityLine: 19036,
        stage: 'internalized-prelude',
        coreName: 'emdash_v3_2_pathind_internalized_PathIndTgt_catd'
    },
    {
        order: 3,
        name: 'pathout_motive_transport_obj',
        authorityLine: 19139,
        stage: 'derived-internalized-library',
        coreName:
            'emdash_v3_2_pathind_internalized_' +
            'pathout_motive_transport_obj'
    },
    {
        order: 4,
        name: 'pathout_motive_transport_arrow',
        authorityLine: 19160,
        stage: 'derived-internalized-library',
        coreName:
            'emdash_v3_2_pathind_internalized_' +
            'pathout_motive_transport_arrow'
    },
    {
        order: 5,
        name: 'PathIndSrc_catd',
        authorityLine: 19296,
        stage: 'derived-internalized-library',
        coreName: 'emdash_v3_2_pathind_internalized_PathIndSrc_catd'
    },
    {
        order: 6,
        name: 'PathIndSrc_transport_func',
        authorityLine: 19309,
        stage: 'derived-internalized-library',
        coreName:
            'emdash_v3_2_pathind_internalized_' +
            'PathIndSrc_transport_func'
    },
    {
        order: 7,
        name: 'PathInd_funcd',
        authorityLine: 19332,
        stage: 'derived-internalized-library',
        coreName: 'emdash_v3_2_pathind_internalized_PathInd_funcd'
    },
    {
        order: 8,
        name: 'pathout_pi_transport_func',
        authorityLine: 19734,
        stage: 'derived-internalized-library',
        coreName:
            'emdash_v3_2_pathind_internalized_' +
            'pathout_pi_transport_func'
    },
    {
        order: 9,
        name: 'PathIndTgt_transport_func',
        authorityLine: 19751,
        stage: 'derived-internalized-library',
        coreName:
            'emdash_v3_2_pathind_internalized_' +
            'PathIndTgt_transport_func'
    }
] as const;

const requiredExistingProviders = [
    {
        name: 'Sigma_catd_functord_catd',
        provider: 'CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE',
        role: 'sigma-total-family'
    },
    {
        name: 'Transfd',
        provider: 'CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE',
        role: 'displayed-transformation-classifier'
    },
    {
        name: 'tdapp0_fapp0',
        provider: 'CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE',
        role: 'displayed-transformation-component'
    },
    {
        name: 'Fibre_func',
        provider: 'CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE',
        role: 'displayed-functor-fibre'
    },
    {
        name: 'Pullback_catd_func',
        provider:
            'CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE',
        role: 'moving-motive-family'
    },
    {
        name: 'Pi_int_funcd',
        provider:
            'CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE',
        role: 'moving-section-family'
    },
    {
        name: 'section_pullback_func',
        provider: 'CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE',
        role: 'target-transport'
    },
    {
        name: 'section_pullback_sec',
        provider: 'CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE',
        role: 'target-transport-point-action'
    },
    {
        name: 'fdapp1_int_cell',
        provider: 'CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE',
        role: 'internally-owned-higher-action'
    }
] as const;

const implementationStages = [
    {
        order: 0,
        id: 'sigma-uncurrying-trusted-prerequisite',
        declarations: ['Sigma_transfd_funcd']
    },
    {
        order: 1,
        id: 'internalized-transparent-prelude',
        declarations: [
            'PathOutMotives_catd',
            'PathOutPi_funcd',
            'PathIndTgt_catd'
        ]
    },
    {
        order: 2,
        id: 'internalized-trusted-theorem-package',
        declarations: [
            'PathOutReflEval_funcd',
            'PathInd_func',
            'PathInd_transfd'
        ]
    },
    {
        order: 3,
        id: 'internalized-runtime-projections',
        rules: runtimeRules.map(rule => rule.id)
    },
    {
        order: 4,
        id: 'derived-internalized-library',
        declarations: transparentDefinitions
            .filter(entry => entry.stage === 'derived-internalized-library')
            .map(entry => entry.name)
    }
] as const;

const rawProposal = {
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_REVISION,
    row: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
    status: 'proposal-frozen-awaiting-separate-review',
    parent: {
        auditRevision: CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision,
        authoritySourceSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256,
        authorityChecksSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256,
        fixedSourceRevision: CORE_PATHIND_FIXED_SOURCE_1C_REVISION,
        fixedSourceSemanticCheckpoint: 'a361dc3',
        fixedSourceLedgerCheckpoint: '033dbb8',
        fixedSourceBoundary: {
            trustedDeclarationCount:
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .trustedDeclarationCount,
            runtimeRuleCount:
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
            proofRuleCount:
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .proofRuleCount,
            transparentDefinitionCount:
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .transparentDefinitionCount
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-01',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-001',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        trustedDeclarations,
        runtimeRules,
        proofRules: [] as const,
        transparentDefinitions,
        implementationStages,
        exactBoundary: '4/4/0/10',
        genericEnginesOnly: true,
        intrinsicCoreOwnerDelta: 0,
        checkerBranchDelta: 0,
        evaluatorBranchDelta: 0,
        activeLambdapiOwnerDelta: 0,
        activeLambdapiRuleDelta: 0
    },
    selectedPredecessor: {
        revision: CORE_PATHIND_FIXED_SOURCE_1C_REVISION,
        compileFunction: 'compileCorePathindFixedSource1cTransfer',
        semanticCheckpoint: 'a361dc3',
        reuseWholeQualifiedFixedSourceProfile: true,
        duplicateFixedSourceOwnerOrRule: false,
        localImplementationDeltaIsFourFourZeroTen: true
    },
    dependencyClosure: {
        auditedInternalized: cloneData(auditedInternalizedProfile),
        sigmaTotalUncurrying: cloneData(sigmaTotalUncurryingClosure),
        requiredExistingProviders,
        sigmaUncurryingOwnerRequiresSelectedTransfer: true,
        importWholeScaleStress2b3Profile: false,
        externalHandWrittenNaturalitySquareIncluded: false,
        arbitraryNonCartesianSigmaNaturalityIncluded: false,
        sourceArrowCollapsedToExternalEquation: false,
        higherActionCollapsedToExternalEquation: false,
        transitivityDefinitionsIncluded: false,
        pathCategoryProofBridgeIncluded: false
    },
    typedLibraryConsumers: [
        {
            name: 'PathInd_transfd',
            role: 'primary-internally-natural-varying-source-theorem',
            expectedType:
                'Transfd(PathOutReflEval_funcd,PathOutPi_funcd)',
            expectedComponent: 'PathInd_transfd(Z)[x]=PathInd_func(Z,x)',
            externalNaturalitySquareRequired: false
        },
        {
            name: 'PathInd_funcd',
            role: 'derived-Sigma-total-presentation',
            expectedType:
                'Functord(PathIndSrc_catd,PathIndTgt_catd)',
            expectedComponent:
                'PathInd_funcd(Z)[(x,E)]=path_ind_func_fapp0(Z,x,E)',
            primitiveTheorem: false
        }
    ],
    selectedRuntimeObservations: [
        'PathOutReflEval_funcd[x]-reduces-to-pathout_refl_eval_func(x)',
        'PathInd_func(x)[E]-reduces-to-path_ind_func_fapp0(x,E)',
        'PathInd_transfd[x]-reduces-to-PathInd_func(x)',
        'PathInd_transfd[x][E][u]-reduces-to-path_ind_sec(x,E,u)',
        'Sigma_transfd_funcd(eta)[(k,r)]-reduces-to-eta[k][r]',
        'PathInd_funcd[(x,E)]-reduces-to-path_ind_func_fapp0(x,E)',
        'PathIndSrc_transport(p,E)-retains-E-along-rho-source-action',
        'PathIndTgt_transport(p,E)-retains-section-pullback-target-action',
        'PathOutPi_funcd-higher-action-retains-fdapp1_int_cell-owner'
    ],
    negativeConsumers: [
        'PathInd-transfd-component-at-an-object-from-the-wrong-base',
        'PathInd-func-component-at-a-motive-over-the-wrong-PathOut',
        'PathInd-funcd-component-at-a-non-Sigma-total-object',
        'source-transport-with-a-motive-over-the-wrong-source',
        'target-transport-applied-to-a-foreign-section',
        'claiming-arbitrary-non-cartesian-Sigma-arrow-naturality',
        'replacing-internal-naturality-by-an-external-square',
        'foreign-session-or-scoped-term',
        'ordinary-safe-library-runtime-rule-attempt',
        'ordinary-safe-library-opaque-signature-attempt'
    ],
    boundedOracle: {
        packageRoot: 'emdash2',
        timeoutMs: 20_000,
        assertions: [
            'PathOutReflEval-component-is-fixed-evaluation',
            'PathInd-func-component-is-fixed-source-component',
            'PathInd-transfd-component-is-PathInd-func',
            'PathInd-transfd-component-motive-is-fixed-source-component',
            'PathInd-transfd-component-object-is-path-ind-section',
            'generic-Sigma-transfd-component-is-fibrewise-component',
            'PathInd-funcd-component-is-fixed-source-component',
            'PathInd-funcd-component-object-is-path-ind-section',
            'PathInd-source-transport-is-rho-action',
            'PathInd-target-transport-is-section-pullback',
            'PathOutPi-higher-action-is-PathInd-target-transport'
        ],
        requiredForImplementationAcceptance: true,
        requiredForProposalAcceptance: false
    },
    profileSealing: {
        rootOnlyDuringQualification: true,
        publicSafeLibraryCanAddTransparentDefinitions: true,
        publicSafeLibraryCanAddOpaqueOwners: false,
        publicSafeLibraryCanAddRuntimeRules: false,
        publicSafeLibraryCanAddProofRules: false,
        lowLevelAuthoringApiRemainsExplicitlyTrustBearing: true,
        packageOrBrowserExportAuthorized: false
    },
    deferred: {
        transitivityDefinitions: [
            'CompTarget_catd',
            'CompTarget_fapp1_func',
            'CompMotive_catd',
            'path_comp_sec',
            'path_comp_func'
        ],
        proofRules: ['path-category-reflexive-component-join'],
        presentation: [
            'text-syntax',
            'CLI-reviewer-preset',
            'browser-reviewer-preset',
            'public-package-export'
        ]
    },
    validation: {
        focusedProposalTestsRequired: true,
        rootTypecheckRequired: true,
        focusedLintRequired: true,
        implementationFocusedTestsRequired: true,
        boundedLambdapiOracleRequiredForImplementation: true,
        longAggregateRequired: false,
        reasonLongAggregateOmitted:
            'proposal-is-immutable-data-only-and-direct-gates-cover-it'
    },
    gitBoundary: {
        proposalCheckpointRequiredBeforeReview: true,
        reviewCheckpointRequiredBeforeImplementation: true,
        exactStagedDiffReviewRequired: true,
        localCheckpointAuthorized: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-implementation',
        'whole-scale-stress-2b3-profile-import',
        'external-hand-written-naturality-square',
        'arbitrary-non-cartesian-Sigma-arrow-naturality',
        'collapse-of-internally-owned-source-arrow-or-higher-action',
        'transitivity-library',
        'path-category-proof-bridge',
        'new-Core-owner-or-checker-branch',
        'ordinary-safe-library-rule-registration',
        'text-parser-or-declaration-syntax',
        'browser-or-public-package-export',
        'active-Lambdapi-source-change',
        'push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathind-internalized-1d-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposal = typeof rawProposal;

export type CorePathindInternalized1dProposalErrorCode =
    | 'PATHIND_INTERNALIZED_PROPOSAL_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_PROPOSAL_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_PROPOSAL_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalError extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalError';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposal(
    proposal: CorePathindInternalized1dProposal =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL
): CorePathindInternalized1dProposal {
    validateCorePathoutTrustBoundary0aAudit();
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-1' ||
        proposal.parent.auditRevision !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision ||
        proposal.parent.authoritySourceSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256 ||
        proposal.parent.authorityChecksSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256 ||
        proposal.parent.fixedSourceRevision !==
            CORE_PATHIND_FIXED_SOURCE_1C_REVISION ||
        proposal.parent.fixedSourceSemanticCheckpoint !== 'a361dc3' ||
        proposal.parent.fixedSourceLedgerCheckpoint !== '033dbb8' ||
        !sameData(proposal.parent.fixedSourceBoundary, {
            trustedDeclarationCount: 5,
            runtimeRuleCount: 12,
            proofRuleCount: 0,
            transparentDefinitionCount: 6
        })
    ) {
        throw new CorePathindInternalized1dProposalError(
            'PATHIND_INTERNALIZED_PROPOSAL_AUTHORITY_DRIFT',
            'The audited authority or fixed-source predecessor drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    if (
        !sameData(implementation.trustedDeclarations, trustedDeclarations) ||
        !sameData(implementation.runtimeRules, runtimeRules) ||
        implementation.proofRules.length !== 0 ||
        !sameData(
            implementation.transparentDefinitions,
            transparentDefinitions
        ) ||
        !sameData(implementation.implementationStages, implementationStages) ||
        implementation.exactBoundary !== '4/4/0/10' ||
        !implementation.genericEnginesOnly ||
        implementation.intrinsicCoreOwnerDelta !== 0 ||
        implementation.checkerBranchDelta !== 0 ||
        implementation.evaluatorBranchDelta !== 0 ||
        implementation.activeLambdapiOwnerDelta !== 0 ||
        implementation.activeLambdapiRuleDelta !== 0 ||
        !sameData(
            proposal.dependencyClosure.auditedInternalized,
            auditedInternalizedProfile
        ) ||
        !sameData(
            proposal.dependencyClosure.sigmaTotalUncurrying,
            sigmaTotalUncurryingClosure
        ) ||
        !sameData(
            proposal.dependencyClosure.requiredExistingProviders,
            requiredExistingProviders
        ) ||
        !proposal.dependencyClosure
            .sigmaUncurryingOwnerRequiresSelectedTransfer ||
        proposal.dependencyClosure.importWholeScaleStress2b3Profile ||
        proposal.dependencyClosure
            .externalHandWrittenNaturalitySquareIncluded ||
        proposal.dependencyClosure
            .arbitraryNonCartesianSigmaNaturalityIncluded ||
        proposal.dependencyClosure.sourceArrowCollapsedToExternalEquation ||
        proposal.dependencyClosure.higherActionCollapsedToExternalEquation ||
        proposal.dependencyClosure.transitivityDefinitionsIncluded ||
        proposal.dependencyClosure.pathCategoryProofBridgeIncluded ||
        proposal.selectedPredecessor.revision !==
            CORE_PATHIND_FIXED_SOURCE_1C_REVISION ||
        proposal.selectedPredecessor.semanticCheckpoint !== 'a361dc3' ||
        !proposal.selectedPredecessor
            .reuseWholeQualifiedFixedSourceProfile ||
        proposal.selectedPredecessor.duplicateFixedSourceOwnerOrRule ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourFourZeroTen ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 9 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 11
    ) {
        throw new CorePathindInternalized1dProposalError(
            'PATHIND_INTERNALIZED_PROPOSAL_SCOPE_DRIFT',
            'The exact 4/4/0/10 internalized PathInd scope drifted'
        );
    }

    if (
        proposal.decision.question !== DECISION_QUESTION ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.profileSealing.packageOrBrowserExportAuthorized ||
        proposal.profileSealing.publicSafeLibraryCanAddOpaqueOwners ||
        proposal.profileSealing.publicSafeLibraryCanAddRuntimeRules ||
        proposal.profileSealing.publicSafeLibraryCanAddProofRules ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathind-internalized-1d-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalError(
            'PATHIND_INTERNALIZED_PROPOSAL_AUTHORIZATION_DRIFT',
            'The internalized proposal became self-authorizing or widened'
        );
    }
    return proposal;
}
