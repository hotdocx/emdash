/**
 * PATHOUT-LIBRARY-FOUNDATION-1B0 non-authorizing proposal.
 *
 * The proposal freezes the exact two prerequisite closures and nine
 * transparent definitions selected by the corrected 0A audit. It compiles
 * or installs nothing; a separate immutable review must authorize 1B.
 */

import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT,
    validateCorePathoutTrustBoundary0aAudit
} from './pathout_trust_boundary_audit';

export const CORE_PATHOUT_FOUNDATION_1B0_REVISION =
    'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-2' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHOUT-FOUNDATION-01/' +
    'D-TS-EMDASH-PATHOUT-FOUNDATION-001 as proposed.';

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

const representedSourceClosure =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.prerequisiteClosures[0];
const sigmaTotalizationClosure =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.prerequisiteClosures[1];
const foundationProfile =
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.smallestProfiles.foundation;

const prerequisiteDeclarations = [
    {
        order: 0,
        name: 'hom_int_precomp_tele_func',
        authorityLine: 8427,
        sourceKind: 'symbol',
        policy: 'opaque-signature',
        coreName:
            'emdash_v3_2_pathout_foundation_hom_int_precomp_tele_func'
    },
    {
        order: 1,
        name: 'hom_int_precomp_func',
        authorityLine: 8438,
        sourceKind: 'symbol',
        policy: 'opaque-signature',
        coreName:
            'emdash_v3_2_pathout_foundation_hom_int_precomp_func'
    },
    {
        order: 2,
        name: 'Sigma_func',
        authorityLine: 12801,
        sourceKind: 'injective-symbol',
        policy: 'opaque-signature',
        coreName: 'emdash_v3_2_pathout_foundation_Sigma_func'
    }
] as const;

const runtimeRules = [
    {
        order: 0,
        id: 'pathout.foundation.hom-int-precomp-full-action',
        authorityLine: 8445,
        sourceOwner: 'fapp1_func',
        resultOwner: 'hom_int_precomp_tele_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 1,
        id: 'pathout.foundation.hom-int-precomp-capped-action',
        authorityLine: 8449,
        sourceOwner: 'fapp1_fapp0',
        resultOwner: 'hom_int_precomp_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 2,
        id: 'pathout.foundation.hom-int-precomp-tele-application',
        authorityLine: 8453,
        sourceOwner: 'fapp0',
        resultOwner: 'hom_int_precomp_func',
        policy: 'runtime-rewrite'
    },
    {
        order: 3,
        id: 'pathout.foundation.sigma-func-object',
        authorityLine: 12803,
        sourceOwner: 'fapp0',
        resultOwner: 'Sigma_cat',
        policy: 'runtime-rewrite'
    },
    {
        order: 4,
        id: 'pathout.foundation.sigma-func-capped-action',
        authorityLine: 13148,
        sourceOwner: 'fapp1_fapp0',
        resultOwner: 'sigma_map_func',
        policy: 'runtime-rewrite'
    }
] as const;

const proofRules = [
    {
        order: 0,
        id: 'pathout.foundation.hom-int-precomp-projection-order',
        authorityLine: 8463,
        rigidHeads: [
            'hom_precomp_along_fapp0',
            'hom_int_precomp_func'
        ],
        generatedConstraintCount: 3,
        policy: 'proof-unification'
    }
] as const;

const libraryDefinitions = [
    {
        order: 0,
        name: 'Rep_catd_func',
        authorityLine: 13765,
        coreName: 'emdash_v3_2_pathout_foundation_Rep_catd_func'
    },
    {
        order: 1,
        name: 'Rep_catd',
        authorityLine: 13773,
        coreName: 'emdash_v3_2_pathout_foundation_Rep_catd'
    },
    {
        order: 2,
        name: 'Rep_transport_func',
        authorityLine: 13785,
        coreName:
            'emdash_v3_2_pathout_foundation_Rep_transport_func'
    },
    {
        order: 3,
        name: 'PathOut_cat',
        authorityLine: 18960,
        coreName: 'emdash_v3_2_pathout_foundation_PathOut_cat'
    },
    {
        order: 4,
        name: 'PathOut_cat_func',
        authorityLine: 18969,
        coreName: 'emdash_v3_2_pathout_foundation_PathOut_cat_func'
    },
    {
        order: 5,
        name: 'PathOut_transport_func',
        authorityLine: 18984,
        coreName:
            'emdash_v3_2_pathout_foundation_PathOut_transport_func'
    },
    {
        order: 6,
        name: 'pathout_obj',
        authorityLine: 19047,
        coreName: 'emdash_v3_2_pathout_foundation_pathout_obj'
    },
    {
        order: 7,
        name: 'pathout_refl_obj',
        authorityLine: 19056,
        coreName: 'emdash_v3_2_pathout_foundation_pathout_refl_obj'
    },
    {
        order: 8,
        name: 'pathout_refl_arrow',
        authorityLine: 19100,
        coreName:
            'emdash_v3_2_pathout_foundation_pathout_refl_arrow'
    }
] as const;

const rawProposal = {
    revision: CORE_PATHOUT_FOUNDATION_1B0_REVISION,
    row: 'PATHOUT-LIBRARY-FOUNDATION-1B0',
    status: 'proposal-awaiting-separate-review',
    parent: {
        auditRevision: CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision,
        initialAuditCheckpoint: 'a05493b',
        correctedAuditCheckpoint: '5a1ea75',
        correctedLedgerCheckpoint: '828b0d7',
        supersededProposalCheckpoint: 'dd69325',
        supersededProposalLedgerCheckpoint: '3226a6a',
        correctionReason:
            'independent-review-found-hom_-only-in-the-reviewed-' +
            'mixed-action-descendant',
        authoritySourceSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256,
        authorityChecksSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHOUT-FOUNDATION-01',
        id: 'D-TS-EMDASH-PATHOUT-FOUNDATION-001',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedesDelegatedReview: true
    },
    selectedPredecessor: {
        compileFunction:
            'compileCoreCategoricalMixedActionTransfer',
        boundaryRevision:
            'MIXED-NEST-ACTION-0B-GENERIC-TRANSFER-1',
        reason:
            'smallest-current-reviewed-descendant-containing-hom_int-' +
            'and-hom_-with-their-object-projections-plus-displayed-chain-' +
            'sigma-map-and-directed-sigma-primitives',
        requiredExistingOwners: [
            'id',
            'hom_int',
            'hom_',
            'hom_precomp_along_fapp0',
            'comp_fapp0',
            'comp_cat_fapp0',
            'Sigma_cat',
            'sigma_map_func',
            'Struct_sigma',
            'sigma_transport_arrow'
        ],
        importWholeScaleProfile: false,
        reuseReviewedMixedActionDescendant: true,
        extractOrDuplicateRepresentedHomSubset: false,
        reusedMixedActionDeclarations: ['hom_'],
        reusedMixedActionRuntimeRules: [
            'categorical.mixed-action.internal-hom-object-projection',
            'categorical.mixed-action.represented-hom-object-projection'
        ]
    },
    exactImplementation: {
        prerequisiteDeclarations,
        runtimeRules,
        proofRules,
        libraryDefinitions: libraryDefinitions.map(entry => ({
            ...entry,
            sourceKind: 'symbol',
            policy: 'checked-transparent-definition'
        })),
        phaseOrder: [
            'compile-opaque-prerequisite-declarations',
            'compose-five-authority-runtime-rules',
            'compile-one-authority-proof-rule',
            'compile-nine-transparent-library-definitions',
            'recheck-proof-rule-against-final-declaration-context'
        ],
        genericEnginesOnly: true,
        intrinsicCoreOwnerDelta: 0,
        checkerBranchDelta: 0,
        evaluatorBranchDelta: 0,
        activeLambdapiOwnerDelta: 0,
        activeLambdapiRuleDelta: 0
    },
    dependencyClosure: {
        representedSource:
            cloneData(representedSourceClosure),
        sigmaTotalization:
            cloneData(sigmaTotalizationClosure),
        selectedFoundation:
            cloneData(foundationProfile),
        representedHomReuse: {
            owner: 'hom_',
            sourceLine: 7223,
            internalHomObjectProjectionLine: 8419,
            representedHomObjectProjectionLine: 7226,
            sourceProfile: 'MIXED-NEST-ACTION-0B-GENERIC-TRANSFER-1',
            duplicateTransferAuthorized: false
        },
        laterCovariantFibreClosureIncluded: false,
        laterSigmaTransfdUncurryingIncluded: false,
        deferredSigmaHigherActionIncluded: false,
        wholeSourcePrefixIncluded: false
    },
    profileSealing: {
        trustedProfileContains: [
            'three-opaque-authority-declarations',
            'five-runtime-rules',
            'one-proof-unification-rule'
        ],
        derivedLibraryContains: [
            'nine-checked-transparent-definitions'
        ],
        rootOnlyDuringQualification: true,
        publicSafeLibraryCanAddTransparentDefinitions: true,
        publicSafeLibraryCanAddOpaqueOwners: false,
        publicSafeLibraryCanAddRuntimeRules: false,
        publicSafeLibraryCanAddProofRules: false,
        lowLevelAuthoringApiRemainsExplicitlyTrustBearing: true,
        packageOrBrowserExportAuthorized: false,
        deterministicLambdapiEmission:
            'optional-backend-conformance-output-only'
    },
    positiveConsumers: [
        {
            id: 'representable-fibre',
            observation: 'Rep_catd(x)[y]-reduces-to-Hom(Z,x,y)'
        },
        {
            id: 'representable-precomposition',
            observation:
                'Rep_transport_func(p)-is-hom_int-precomposition'
        },
        {
            id: 'pathout-total',
            observation: 'PathOut_cat(x)-reduces-to-Sigma_cat(Rep_catd(x))'
        },
        {
            id: 'pathout-functor-object',
            observation: 'PathOut_cat_func[x]-reduces-to-PathOut_cat(x)'
        },
        {
            id: 'pathout-source-action',
            observation:
                'PathOut_transport_func(p)-maps-(z,q)-to-(z,q-after-p)'
        },
        {
            id: 'pathout-reflexive-action',
            observation:
                'PathOut_transport_func(p)[(y,id_y)]-reduces-to-(y,p)'
        },
        {
            id: 'canonical-reflexive-arrow',
            observation:
                'pathout_refl_arrow(p)-has-source-(x,id_x)-and-target-(y,p)'
        }
    ],
    negativeConsumers: [
        'wrong-representable-source-object',
        'wrong-precomposition-endpoint',
        'wrong-pathout-source-object',
        'dependent-pair-with-wrong-fibre-component',
        'pathout-transport-with-wrong-endpoint',
        'foreign-session-or-scoped-term',
        'ordinary-safe-library-runtime-rule-attempt',
        'ordinary-safe-library-proof-rule-attempt'
    ],
    boundedOracle: {
        packageRoot: 'emdash2',
        timeoutMs: 20_000,
        assertions: [
            'Rep_transport_func-is-hom_int_precomp_func',
            'Sigma_func-object-is-Sigma_cat',
            'Sigma_func-capped-action-is-sigma_map_func',
            'PathOut_cat_func-object-is-PathOut_cat',
            'PathOut-transport-on-refl-is-pathout_obj-of-p',
            'pathout_refl_arrow-has-canonical-Sigma-endpoints'
        ],
        requiredForImplementationAcceptance: true,
        requiredForProposalAcceptance: false
    },
    validation: {
        focusedProposalTestsRequired: true,
        rootTypecheckRequired: true,
        focusedLintRequired: true,
        workspaceContractRequired: true,
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
        'PATHOUT-LIBRARY-FOUNDATION-1B-implementation',
        'fixed-source-path-induction',
        'internalized-path-induction',
        'transitivity-library',
        'sigma-map-transf-higher-action',
        'new-Core-owner-or-checker-branch',
        'ordinary-safe-library-rule-registration',
        'text-parser-or-declaration-syntax',
        'browser-or-public-package-export',
        'active-Lambdapi-source-change',
        'push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'foundation-1b0-awaiting-separate-immutable-review'
} as const;

export type CorePathoutFoundation1b0Proposal = typeof rawProposal;

export type CorePathoutFoundation1b0ProposalErrorCode =
    | 'PATHOUT_FOUNDATION_PROPOSAL_AUTHORITY_DRIFT'
    | 'PATHOUT_FOUNDATION_PROPOSAL_SCOPE_DRIFT'
    | 'PATHOUT_FOUNDATION_PROPOSAL_AUTHORIZATION_DRIFT';

export class CorePathoutFoundation1b0ProposalError extends Error {
    constructor(
        public readonly code:
            CorePathoutFoundation1b0ProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutFoundation1b0ProposalError';
    }
}

export const CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCorePathoutFoundation1b0Proposal(
    proposal: CorePathoutFoundation1b0Proposal =
        CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL
): CorePathoutFoundation1b0Proposal {
    validateCorePathoutTrustBoundary0aAudit();
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-FOUNDATION-1B0-PROPOSAL-2' ||
        proposal.parent.auditRevision !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision ||
        proposal.parent.correctedAuditCheckpoint !== '5a1ea75' ||
        proposal.parent.correctedLedgerCheckpoint !== '828b0d7' ||
        proposal.parent.supersededProposalCheckpoint !== 'dd69325' ||
        proposal.parent.supersededProposalLedgerCheckpoint !== '3226a6a' ||
        proposal.parent.authoritySourceSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256 ||
        proposal.parent.authorityChecksSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256
    ) {
        throw new CorePathoutFoundation1b0ProposalError(
            'PATHOUT_FOUNDATION_PROPOSAL_AUTHORITY_DRIFT',
            'The corrected 0A authority or checkpoint boundary drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    if (
        implementation.prerequisiteDeclarations.length !== 3 ||
        implementation.runtimeRules.length !== 5 ||
        implementation.proofRules.length !== 1 ||
        implementation.libraryDefinitions.length !== 9 ||
        !sameData(
            implementation.prerequisiteDeclarations,
            prerequisiteDeclarations
        ) ||
        !sameData(implementation.runtimeRules, runtimeRules) ||
        !sameData(implementation.proofRules, proofRules) ||
        !sameData(
            implementation.libraryDefinitions.map(entry => ({
                order: entry.order,
                name: entry.name,
                authorityLine: entry.authorityLine,
                coreName: entry.coreName
            })),
            libraryDefinitions
        ) ||
        !implementation.genericEnginesOnly ||
        implementation.intrinsicCoreOwnerDelta !== 0 ||
        implementation.checkerBranchDelta !== 0 ||
        implementation.evaluatorBranchDelta !== 0 ||
        implementation.activeLambdapiOwnerDelta !== 0 ||
        implementation.activeLambdapiRuleDelta !== 0 ||
        !sameData(
            proposal.dependencyClosure.representedSource,
            representedSourceClosure
        ) ||
        !sameData(
            proposal.dependencyClosure.sigmaTotalization,
            sigmaTotalizationClosure
        ) ||
        !sameData(
            proposal.dependencyClosure.selectedFoundation,
            foundationProfile
        ) ||
        proposal.selectedPredecessor.compileFunction !==
            'compileCoreCategoricalMixedActionTransfer' ||
        proposal.selectedPredecessor.boundaryRevision !==
            'MIXED-NEST-ACTION-0B-GENERIC-TRANSFER-1' ||
        !proposal.selectedPredecessor.reuseReviewedMixedActionDescendant ||
        proposal.selectedPredecessor
            .extractOrDuplicateRepresentedHomSubset ||
        proposal.dependencyClosure.representedHomReuse.owner !== 'hom_' ||
        proposal.dependencyClosure.representedHomReuse
            .duplicateTransferAuthorized
    ) {
        throw new CorePathoutFoundation1b0ProposalError(
            'PATHOUT_FOUNDATION_PROPOSAL_SCOPE_DRIFT',
            'The exact 3/5/1/9 foundation scope drifted'
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
            'foundation-1b0-awaiting-separate-immutable-review'
    ) {
        throw new CorePathoutFoundation1b0ProposalError(
            'PATHOUT_FOUNDATION_PROPOSAL_AUTHORIZATION_DRIFT',
            'The proposal became self-authorizing or widened its effects'
        );
    }
    return proposal;
}
