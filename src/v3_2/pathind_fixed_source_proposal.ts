/**
 * PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal.
 *
 * This freezes the smallest fixed-source PathInd slice above the qualified
 * PathOut foundation.  It installs no declarations or rules; a separate
 * immutable review is required before implementation.
 */

import {
    CORE_PATHOUT_FOUNDATION_1B_REVISION,
    CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
} from './pathout_foundation_transfer';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT,
    validateCorePathoutTrustBoundary0aAudit
} from './pathout_trust_boundary_audit';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-1' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-01/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-001 as proposed.';

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

const covariantFibreClosure =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.prerequisiteClosures[2];
const auditedFixedSourceProfile =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.smallestProfiles
        .fixedSourceInduction;

const trustedDeclarations = [
    {
        order: 0,
        name: 'fib_cov_int',
        authorityLine: 13948,
        sourceKind: 'constant-symbol',
        policy: 'opaque-signature',
        coreName: 'emdash_v3_2_pathind_fixed_source_fib_cov_int'
    },
    {
        order: 1,
        name: 'fib_cov_src_func',
        authorityLine: 13952,
        sourceKind: 'symbol',
        policy: 'opaque-signature',
        coreName: 'emdash_v3_2_pathind_fixed_source_fib_cov_src_func'
    },
    {
        order: 2,
        name: 'fib_cov_transf',
        authorityLine: 13959,
        sourceKind: 'injective-symbol',
        policy: 'opaque-signature',
        coreName: 'emdash_v3_2_pathind_fixed_source_fib_cov_transf'
    },
    {
        order: 3,
        name: 'path_ind_sec',
        authorityLine: 19181,
        sourceKind: 'symbol',
        policy: 'opaque-signature',
        coreName: 'emdash_v3_2_pathind_fixed_source_path_ind_sec'
    },
    {
        order: 4,
        name: 'path_ind_func_fapp0',
        authorityLine: 19227,
        sourceKind: 'symbol',
        policy: 'opaque-signature',
        coreName:
            'emdash_v3_2_pathind_fixed_source_path_ind_func_fapp0'
    }
] as const;

const runtimeRules = [
    {
        order: 0,
        id: 'pathind.fixed-source.fib-cov-package-component',
        authorityLine: 13965,
        sourceOwner: 'tapp0_fapp0',
        resultOwner: 'fib_cov_src_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 1,
        id: 'pathind.fixed-source.fib-cov-component-object',
        authorityLine: 13975,
        sourceOwner: 'fapp0',
        resultOwner: 'fib_cov_transf',
        policy: 'runtime-rewrite'
    },
    {
        order: 2,
        id: 'pathind.fixed-source.fib-cov-section-point',
        authorityLine: 13979,
        sourceOwner: 'tapp0_fapp0',
        resultOwner: 'fib_cov_tapp0_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 3,
        id: 'pathind.fixed-source.path-ind-section-object-action',
        authorityLine: 19234,
        sourceOwner: 'fapp0',
        resultOwner: 'path_ind_sec',
        policy: 'runtime-rewrite'
    },
    {
        order: 4,
        id: 'pathind.fixed-source.path-ind-point-computation',
        authorityLine: 19418,
        sourceOwner: 'tapp0_fapp0',
        resultOwner: 'Obj_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 5,
        id: 'pathind.fixed-source.path-ind-sigma-pullback-computation',
        authorityLine: 19441,
        sourceOwner: 'path_ind_sec',
        resultOwner: 'fib_cov_transf',
        policy: 'runtime-rewrite'
    }
] as const;

const transparentDefinitions = [
    {
        order: 0,
        name: 'FibCov_target_catd',
        authorityLine: 13923,
        coreName: 'emdash_v3_2_pathind_fixed_source_FibCov_target_catd'
    },
    {
        order: 1,
        name: 'pathout_refl_eval_func',
        authorityLine: 19067,
        coreName:
            'emdash_v3_2_pathind_fixed_source_pathout_refl_eval_func'
    },
    {
        order: 2,
        name: 'pathout_refl_eval_base_func',
        authorityLine: 19118,
        coreName:
            'emdash_v3_2_pathind_fixed_source_' +
            'pathout_refl_eval_base_func'
    },
    {
        order: 3,
        name: 'pathout_refl_arrow_sec',
        authorityLine: 19193,
        coreName:
            'emdash_v3_2_pathind_fixed_source_pathout_refl_arrow_sec'
    },
    {
        order: 4,
        name: 'PathInd_src_catd',
        authorityLine: 19210,
        coreName: 'emdash_v3_2_pathind_fixed_source_PathInd_src_catd'
    },
    {
        order: 5,
        name: 'PathInd_tgt_catd',
        authorityLine: 19218,
        coreName: 'emdash_v3_2_pathind_fixed_source_PathInd_tgt_catd'
    }
] as const;

const selectedFixedSourceOwnerNames = [
    'pathout_refl_eval_func',
    'pathout_refl_eval_base_func',
    'path_ind_sec',
    'pathout_refl_arrow_sec',
    'PathInd_src_catd',
    'PathInd_tgt_catd',
    'path_ind_func_fapp0'
] as const;

const selectedFixedSourceRuleIds = [
    'path-ind-section-object-action',
    'path-ind-point-computation',
    'path-ind-sigma-pullback-computation'
] as const;

const rawProposal = {
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_REVISION,
    row: 'PATHIND-TRUSTED-PROFILE-1C',
    status: 'proposal-frozen-awaiting-separate-review',
    parent: {
        auditRevision: CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision,
        authoritySourceSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256,
        authorityChecksSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256,
        foundationRevision: CORE_PATHOUT_FOUNDATION_1B_REVISION,
        foundationSemanticCheckpoint: '550316a',
        foundationLedgerCheckpoint: '349b6d4',
        foundationBoundary: {
            prerequisiteDeclarationCount:
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .prerequisiteDeclarationCount,
            runtimeRuleCount:
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
            proofRuleCount:
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .proofRuleCount,
            transparentLibraryDefinitionCount:
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .transparentLibraryDefinitionCount
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-01',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-001',
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
        exactBoundary: '5/6/0/6',
        genericEnginesOnly: true,
        intrinsicCoreOwnerDelta: 0,
        checkerBranchDelta: 0,
        evaluatorBranchDelta: 0,
        activeLambdapiOwnerDelta: 0,
        activeLambdapiRuleDelta: 0
    },
    selectedPredecessor: {
        revision: CORE_PATHOUT_FOUNDATION_1B_REVISION,
        compileFunction: 'compileCorePathoutFoundation1bTransfer',
        semanticCheckpoint: '550316a',
        reuseWholeQualifiedFoundation: true,
        duplicateFoundationOwnerOrRule: false,
        localImplementationDeltaIsFiveSixZeroSix: true
    },
    dependencyClosure: {
        covariantFibre: cloneData(covariantFibreClosure),
        auditedFixedSource: cloneData(auditedFixedSourceProfile),
        selectedFixedSource: {
            ownerNames: selectedFixedSourceOwnerNames,
            ruleIds: selectedFixedSourceRuleIds,
            deferredOwnerNames: ['PathInd_func'],
            deferredRuleIds: ['path-ind-functor-component'],
            reason:
                'PathInd_func starts coherent fixed-source packaging and is ' +
                'selected with PathInd_transfd by internalized row 1D'
        },
        excludedReadableAlias: 'FibCov_source_catd',
        pathCategoryProofBridgeIncluded: false,
        internalizedInductionIncluded: false,
        transitivityDefinitionsIncluded: false
    },
    typedLibraryConsumer: {
        count: 1,
        name: 'pathout_refl_arrow_sec',
        construction:
            'path_ind_sec(Rep_PathOut(reflout_x),id_reflout_x)',
        expectedType:
            'Pi(q:PathOut_Z(x),Hom_PathOut_Z(x)(reflout_x,q))',
        nontrivialPointComputation:
            'pathout_refl_arrow_sec(x)[(y,p)]=pathout_refl_arrow(x,y,p)',
        usesDirectTypedCore: true,
        publicFacadeAuthorized: false
    },
    selectedRuntimeObservations: [
        'path_ind_func_fapp0(E)[u]-reduces-to-path_ind_sec(E,u)',
        'path_ind_sec(E,u)[(y,p)]-reduces-to-E[rho_xyp](u)',
        'path_ind_sec(Sigma_proj1_pullback(Rep_x,D),u)-reduces-to-' +
            'fib_cov_transf(D,x,u)'
    ],
    negativeConsumers: [
        'wrong-PathOut-source-category',
        'motive-over-the-wrong-PathOut-base',
        'base-datum-from-the-wrong-reflexive-fibre',
        'section-evaluated-at-a-foreign-PathOut-object',
        'Sigma-pullback-computation-with-the-wrong-representable-source',
        'foreign-session-or-scoped-term',
        'ordinary-safe-library-runtime-rule-attempt',
        'ordinary-safe-library-opaque-signature-attempt'
    ],
    boundedOracle: {
        packageRoot: 'emdash2',
        timeoutMs: 20_000,
        assertions: [
            'FibCov-target-is-hom-con',
            'fib-cov-package-component-is-fib-cov-src-func',
            'fib-cov-component-object-is-fib-cov-transf',
            'fib-cov-section-point-is-fib-cov-tapp0-func',
            'path-ind-component-object-is-path-ind-sec',
            'path-ind-Sigma-pullback-fold-is-fib-cov-transf',
            'pathout-refl-arrow-section-point-is-rho'
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
        internalizedOwners: [
            'PathOutReflEval_funcd',
            'PathInd_func',
            'PathInd_transfd'
        ],
        internalizedTransparentDefinitions: [
            'PathOutMotives_catd',
            'PathOutPi_funcd',
            'PathIndTgt_catd',
            'pathout_motive_transport_obj',
            'pathout_motive_transport_arrow',
            'PathIndSrc_catd',
            'PathIndSrc_transport_func',
            'PathInd_funcd',
            'pathout_pi_transport_func',
            'PathIndTgt_transport_func'
        ],
        transitivityDefinitions: [
            'CompTarget_catd',
            'CompTarget_fapp1_func',
            'CompMotive_catd',
            'path_comp_sec',
            'path_comp_func'
        ],
        proofRules: ['path-category-reflexive-component-join']
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
        'PATHIND-TRUSTED-PROFILE-1C-implementation',
        'PathInd_func-or-PathInd_transfd',
        'internalized-or-varying-source-path-induction',
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
        'pathind-fixed-source-1c-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposal = typeof rawProposal;

export type CorePathindFixedSource1cProposalErrorCode =
    | 'PATHIND_FIXED_SOURCE_PROPOSAL_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_PROPOSAL_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_PROPOSAL_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalError extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalError';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposal(
    proposal: CorePathindFixedSource1cProposal =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
): CorePathindFixedSource1cProposal {
    validateCorePathoutTrustBoundary0aAudit();
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-1' ||
        proposal.parent.auditRevision !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision ||
        proposal.parent.authoritySourceSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256 ||
        proposal.parent.authorityChecksSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256 ||
        proposal.parent.foundationRevision !==
            CORE_PATHOUT_FOUNDATION_1B_REVISION ||
        proposal.parent.foundationSemanticCheckpoint !== '550316a' ||
        proposal.parent.foundationLedgerCheckpoint !== '349b6d4' ||
        !sameData(proposal.parent.foundationBoundary, {
            prerequisiteDeclarationCount: 5,
            runtimeRuleCount: 13,
            proofRuleCount: 2,
            transparentLibraryDefinitionCount: 9
        })
    ) {
        throw new CorePathindFixedSource1cProposalError(
            'PATHIND_FIXED_SOURCE_PROPOSAL_AUTHORITY_DRIFT',
            'The audited authority or qualified PathOut predecessor drifted'
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
        implementation.exactBoundary !== '5/6/0/6' ||
        !implementation.genericEnginesOnly ||
        implementation.intrinsicCoreOwnerDelta !== 0 ||
        implementation.checkerBranchDelta !== 0 ||
        implementation.evaluatorBranchDelta !== 0 ||
        implementation.activeLambdapiOwnerDelta !== 0 ||
        implementation.activeLambdapiRuleDelta !== 0 ||
        !sameData(
            proposal.dependencyClosure.covariantFibre,
            covariantFibreClosure
        ) ||
        !sameData(
            proposal.dependencyClosure.auditedFixedSource,
            auditedFixedSourceProfile
        ) ||
        !sameData(
            proposal.dependencyClosure.selectedFixedSource.ownerNames,
            selectedFixedSourceOwnerNames
        ) ||
        !sameData(
            proposal.dependencyClosure.selectedFixedSource.ruleIds,
            selectedFixedSourceRuleIds
        ) ||
        proposal.dependencyClosure.selectedFixedSource
            .deferredOwnerNames.join(',') !== 'PathInd_func' ||
        proposal.dependencyClosure.selectedFixedSource
            .deferredRuleIds.join(',') !== 'path-ind-functor-component' ||
        proposal.selectedPredecessor.revision !==
            CORE_PATHOUT_FOUNDATION_1B_REVISION ||
        proposal.selectedPredecessor.semanticCheckpoint !== '550316a' ||
        !proposal.selectedPredecessor.reuseWholeQualifiedFoundation ||
        proposal.selectedPredecessor.duplicateFoundationOwnerOrRule ||
        !proposal.selectedPredecessor.localImplementationDeltaIsFiveSixZeroSix ||
        proposal.typedLibraryConsumer.count !== 1 ||
        proposal.typedLibraryConsumer.name !== 'pathout_refl_arrow_sec' ||
        proposal.typedLibraryConsumer.publicFacadeAuthorized ||
        proposal.selectedRuntimeObservations.length !== 3 ||
        proposal.negativeConsumers.length !== 8 ||
        proposal.boundedOracle.assertions.length !== 7 ||
        proposal.dependencyClosure.pathCategoryProofBridgeIncluded ||
        proposal.dependencyClosure.internalizedInductionIncluded ||
        proposal.dependencyClosure.transitivityDefinitionsIncluded
    ) {
        throw new CorePathindFixedSource1cProposalError(
            'PATHIND_FIXED_SOURCE_PROPOSAL_SCOPE_DRIFT',
            'The exact 5/6/0/6 fixed-source PathInd scope drifted'
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
            'pathind-fixed-source-1c-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalError(
            'PATHIND_FIXED_SOURCE_PROPOSAL_AUTHORIZATION_DRIFT',
            'The fixed-source proposal became self-authorizing or widened'
        );
    }
    return proposal;
}
