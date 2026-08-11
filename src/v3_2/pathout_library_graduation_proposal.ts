/**
 * Non-authorizing PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G proposal.
 *
 * This record classifies the completed root-only profile. It installs no
 * declaration, rule, parser, export, package entry, or release effect.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
} from './pathind_fixed_source_transfer';
import {
    CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY
} from './pathind_internalized_transfer';
import {
    CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
} from './pathout_foundation_transfer';
import {
    CORE_PATHOUT_PRESENTATION_1F_MANIFEST
} from './pathout_presentation';
import {
    CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE
} from './pathout_presentation_cli';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY
} from './pathout_transitivity_transfer';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT,
    validateCorePathoutTrustBoundary0aAudit
} from './pathout_trust_boundary_audit';

export const CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL_REVISION =
    'PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G-PROPOSAL-1' as const;

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const mathematicalOpaqueOwners = Object.freeze(
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.selectedOwners
        .filter(entry => entry.sourceOpacity === 'opaque')
        .map(entry => entry.name)
);

const sealedSupportingOwners = Object.freeze([
    ...CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
        .prerequisiteDeclarationNames,
    ...CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
        .trustedDeclarationNames,
    ...CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY
        .trustedDeclarationNames
].filter(name => !mathematicalOpaqueOwners.includes(name)));

const transparentDefinitions = Object.freeze([
    ...CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
        .transparentLibraryDefinitionNames,
    ...CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
        .transparentDefinitionNames,
    ...CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY
        .transparentDefinitionNames,
    ...CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.transparentDefinitionNames
]);

const runtimeRuleIds = Object.freeze([
    ...CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY.runtimeRuleIds,
    ...CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY.runtimeRuleIds,
    ...CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY.runtimeRuleIds,
    ...CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.runtimeRuleIds
]);

const proofRuleIds = Object.freeze([
    ...CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY.proofRuleIds,
    ...CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY.proofRuleIds,
    ...CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY.proofRuleIds,
    ...CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.proofRuleIds
]);

const rawProposal = {
    revision: CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL_REVISION,
    row: 'PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G',
    status: 'ready-for-separate-review',
    recommendation:
        'graduate-qualified-root-only-trusted-and-derived-profile',
    parent: {
        trustAuditRevision: CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision,
        trustAuditCheckpoint: 'a05493b',
        activeSourceSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256,
        activeChecksSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256,
        foundationSemanticCheckpoint: '550316a',
        foundationLedgerCheckpoint: '349b6d4',
        fixedSourceSemanticCheckpoint: 'a361dc3',
        fixedSourceLedgerCheckpoint: '033dbb8',
        genericClosureCheckpoint: 'e560551',
        internalizedSemanticCheckpoint: 'b6005b3',
        internalizedLedgerCheckpoint: '6225075',
        transitivitySemanticCheckpoint: '3b113ad',
        transitivityLedgerCheckpoint: '10432ba',
        presentationProposalCheckpoint: '6ad0812',
        presentationReviewCheckpoint: 'f03ef01',
        presentationSemanticCheckpoint: '8d226cc',
        presentationLedgerCheckpoint: 'be487c9'
    },
    productProfile: {
        id: 'emdash-v3.2-pathout-pathind-root-1',
        qualification: 'root-only-source-qualified',
        mathematicalAuthority: 'active-emdash-v3.2-lambdapi-source',
        productionBackend: 'typescript-emdash',
        lambdapiRole: 'bounded-conformance-oracle',
        genericKernel:
            'existing-backend-neutral-explicit-core-checker-and-rule-engines',
        intrinsicCoreOwnerDelta: 0,
        checkerBranchDelta: 0,
        evaluatorBranchDelta: 0,
        activeLambdapiOwnerDelta: 0,
        activeLambdapiRuleDelta: 0
    },
    sealedTrustedProfile: {
        policy:
            'provenance-pinned-opaque-owners-and-exact-rules-only',
        mathematicalOpaqueOwners,
        sealedSupportingOwners,
        mathematicalOpaqueOwnerCount: mathematicalOpaqueOwners.length,
        sealedSupportingOwnerCount: sealedSupportingOwners.length,
        totalLocalSealedDeclarationCount:
            mathematicalOpaqueOwners.length + sealedSupportingOwners.length,
        runtimeRuleIds,
        proofRuleIds,
        runtimeRuleCount: runtimeRuleIds.length,
        proofRuleCount: proofRuleIds.length,
        ordinaryUsersMayAddOpaqueOwners: false,
        ordinaryUsersMayAddRuntimeRules: false,
        ordinaryUsersMayAddProofRules: false
    },
    transparentDerivedLibrary: {
        policy: 'checked-transparent-definitions-and-proof-terms',
        definitionNames: transparentDefinitions,
        definitionCount: transparentDefinitions.length,
        ordinaryUsersMayAddCheckedTransparentDefinitions: true,
        includes: [
            'represented fixed-source outgoing-arrow category',
            'canonical arrow from the reflexive outgoing arrow',
            'fixed-source arrow-induction section',
            'functorial motive and source-varying induction packaging',
            'composition recovered from arrow induction'
        ]
    },
    localSliceBoundaries: [
        {
            id: 'PATHOUT-LIBRARY-FOUNDATION-1B',
            exact: '5/13/2/9',
            sealedDeclarations: 5,
            runtimeRules: 13,
            proofRules: 2,
            transparentDefinitions: 9
        },
        {
            id: 'PATHIND-TRUSTED-PROFILE-1C',
            exact: '5/12/0/6',
            sealedDeclarations: 5,
            runtimeRules: 12,
            proofRules: 0,
            transparentDefinitions: 6
        },
        {
            id: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
            exact: '4/13/0/10',
            sealedDeclarations: 4,
            runtimeRules: 13,
            proofRules: 0,
            transparentDefinitions: 10
        },
        {
            id: 'PATHOUT-LIBRARY-TRANSITIVITY-1E',
            exact: '0/1/0/5',
            sealedDeclarations: 0,
            runtimeRules: 1,
            proofRules: 0,
            transparentDefinitions: 5
        }
    ],
    computationEnvelope: {
        fixedSourcePointAndArrowComputation: true,
        internallyVaryingSourceAction: true,
        selectedHigherAction: true,
        compositionNormalForm: true,
        compositionNormalFormTarget: 'stable-representable-precomposition',
        pathCategoryComparisonLibraryIncluded: false,
        pathCategoryReflexiveJoinRuleIncluded: false,
        arbitraryExternalNaturalityIncluded: false,
        wholeTheoryNormalizationClaimed: false,
        confluenceClaimed: false,
        canonicityClaimed: false,
        consistencyClaimed: false
    },
    presentation: {
        manifestRevision: CORE_PATHOUT_PRESENTATION_1F_MANIFEST.revision,
        cliRevision: CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE.revision,
        formIds: CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.map(
            form => form.id
        ),
        formCount: CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.length,
        browserEvidence:
            'qualified-at-pinned-checkpoint-not-rerun-in-browser',
        nodeEvidence: 'explicit-fresh-TypeScript-semantic-check',
        browserLoadsSemanticTransfer: false,
        declarationOrBinderParserIncluded: false
    },
    distribution: {
        contributorSourceQualified: true,
        contributorBarrelExported: false,
        npmBarrelExported: false,
        npmVersionChanged: false,
        releaseOrRegistryEffect: false,
        browserUsesDirectLazyRootSource: true,
        publicExportNeedsConcreteConsumerAndSeparateReleaseDecision: true
    },
    decision: {
        proposalIsSelfAuthorizing: false,
        separateImmutableReviewRequired: true,
        implementationChangeRequiredForGraduation: false,
        recommendedAfterApproval:
            'complete-STDLIB-8B-and-audit-next-concrete-consumer'
    },
    doesNotAuthorize: [
        'new Core node or checker/evaluator branch',
        'new declaration, runtime rule, proof rule, or equation',
        'ordinary-user opaque declarations or rule installation',
        'general inductive, HIT, or categorical-HIT declarations',
        'general declaration or binder text parsing',
        'whole-library transfer graduation',
        'path-category comparison bridge',
        'metatheoretic normalization, confluence, canonicity, or consistency',
        'public or npm barrel export',
        'package version, publication, release, push, merge, or deployment',
        'active Lambdapi source edit',
        'sibling-repository mutation or worktree cleanup'
    ]
} as const;

export type CorePathoutLibraryGraduation0gProposal = typeof rawProposal;

export type CorePathoutLibraryGraduation0gProposalErrorCode =
    | 'PATHOUT_GRADUATION_PREREQUISITE_DRIFT'
    | 'PATHOUT_GRADUATION_CLASSIFICATION_DRIFT'
    | 'PATHOUT_GRADUATION_PROPOSAL_DRIFT';

export class CorePathoutLibraryGraduation0gProposalError extends Error {
    constructor(
        public readonly code:
            CorePathoutLibraryGraduation0gProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutLibraryGraduation0gProposalError';
    }
}

export const CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL =
    deepFreeze(rawProposal);

export function cloneCorePathoutLibraryGraduation0gProposal():
CorePathoutLibraryGraduation0gProposal {
    return JSON.parse(JSON.stringify(rawProposal)) as
        CorePathoutLibraryGraduation0gProposal;
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCorePathoutLibraryGraduation0gProposal(
    proposal: CorePathoutLibraryGraduation0gProposal =
        CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL
): CorePathoutLibraryGraduation0gProposal {
    validateCorePathoutTrustBoundary0aAudit();
    const boundaries = proposal.localSliceBoundaries;
    if (
        proposal.parent.presentationSemanticCheckpoint !== '8d226cc' ||
        proposal.parent.presentationLedgerCheckpoint !== 'be487c9' ||
        proposal.parent.activeSourceSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256 ||
        proposal.parent.activeChecksSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256 ||
        boundaries.length !== 4 ||
        !sameData(boundaries.map(boundary => boundary.exact), [
            '5/13/2/9',
            '5/12/0/6',
            '4/13/0/10',
            '0/1/0/5'
        ]) ||
        proposal.presentation.manifestRevision !==
            CORE_PATHOUT_PRESENTATION_1F_MANIFEST.revision ||
        proposal.presentation.cliRevision !==
            CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE.revision
    ) {
        throw new CorePathoutLibraryGraduation0gProposalError(
            'PATHOUT_GRADUATION_PREREQUISITE_DRIFT',
            'PathOut graduation prerequisites drifted'
        );
    }
    if (
        proposal.sealedTrustedProfile.mathematicalOpaqueOwnerCount !== 5 ||
        proposal.sealedTrustedProfile.sealedSupportingOwnerCount !== 9 ||
        proposal.sealedTrustedProfile.totalLocalSealedDeclarationCount !==
            14 ||
        proposal.sealedTrustedProfile.runtimeRuleCount !== 39 ||
        proposal.sealedTrustedProfile.proofRuleCount !== 2 ||
        proposal.transparentDerivedLibrary.definitionCount !== 30 ||
        new Set(proposal.sealedTrustedProfile.runtimeRuleIds).size !== 39 ||
        new Set(proposal.transparentDerivedLibrary.definitionNames).size !==
            30 ||
        proposal.distribution.contributorBarrelExported ||
        proposal.distribution.npmBarrelExported
    ) {
        throw new CorePathoutLibraryGraduation0gProposalError(
            'PATHOUT_GRADUATION_CLASSIFICATION_DRIFT',
            'PathOut graduation trust/library classification drifted'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        throw new CorePathoutLibraryGraduation0gProposalError(
            'PATHOUT_GRADUATION_PROPOSAL_DRIFT',
            'PathOut graduation proposal drifted'
        );
    }
    return deepFreeze(proposal);
}
