/**
 * Frozen, non-authorizing proposal for the root-only PathOut transitivity
 * library. This is immutable boundary data, not an implementation.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_REVISION,
    CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY
} from './pathind_internalized_transfer';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT,
    validateCorePathoutTrustBoundary0aAudit
} from './pathout_trust_boundary_audit';

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-1' as const;

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

const transparentDefinitions = [
    {
        order: 0,
        name: 'CompTarget_catd',
        authorityLine: 19363,
        sourceKind: 'injective-symbol',
        sourceOpacity: 'transparent',
        sourceRigidity: 'injective',
        policy: 'checked-transparent-definition',
        role: 'semantic-hom-con-alias'
    },
    {
        order: 1,
        name: 'CompTarget_fapp1_func',
        authorityLine: 19381,
        sourceKind: 'symbol',
        sourceOpacity: 'transparent',
        sourceRigidity: 'ordinary',
        policy: 'checked-transparent-definition',
        role: 'readable-capped-family-action-alias'
    },
    {
        order: 2,
        name: 'CompMotive_catd',
        authorityLine: 19401,
        sourceKind: 'symbol',
        sourceOpacity: 'transparent',
        sourceRigidity: 'ordinary',
        policy: 'checked-transparent-definition',
        role: 'sigma-projection-pullback-composition-motive'
    },
    {
        order: 3,
        name: 'path_comp_sec',
        authorityLine: 19687,
        sourceKind: 'symbol',
        sourceOpacity: 'transparent',
        sourceRigidity: 'ordinary',
        policy: 'checked-transparent-definition',
        role: 'fibre-covariant-transitivity-section'
    },
    {
        order: 4,
        name: 'path_comp_func',
        authorityLine: 19701,
        sourceKind: 'symbol',
        sourceOpacity: 'transparent',
        sourceRigidity: 'ordinary',
        policy: 'checked-transparent-definition',
        role: 'represented-source-precomposition'
    }
] as const;

const rawProposal = {
    revision: CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_REVISION,
    row: 'PATHOUT-LIBRARY-TRANSITIVITY-1E',
    status: 'proposal-only-awaiting-separate-immutable-review',
    parent: {
        auditRevision: CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision,
        authoritySourceSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256,
        authorityChecksSha256:
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256,
        internalizedRevision: CORE_PATHIND_INTERNALIZED_1D_REVISION,
        internalizedReviewedAuthorization:
            CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY
                .reviewedAuthorization,
        internalizedSemanticCheckpoint: 'b6005b3',
        internalizedLedgerCheckpoint: '6225075',
        internalizedBoundary: '4/13/0/10',
        activeLambdapiOwnerDelta: 0,
        activeLambdapiRuleDelta: 0
    },
    authority: {
        path: 'emdash2/emdash3_2.lp',
        selectedDeclarations: transparentDefinitions,
        selectedObservedRules: [] as const,
        excludedPathCategoryBridge: {
            proofRuleLines: [19455, 19475],
            transparentLibraryLines: [19488, 19673],
            reason:
                'not-required-by-selected-generic-transitivity-profile'
        }
    },
    exactImplementation: {
        exactBoundary: '0/0/0/5',
        trustedDeclarations: [] as const,
        runtimeRules: [] as const,
        proofRules: [] as const,
        transparentDefinitions,
        moduleStages: [
            {
                order: 0,
                id: 'derived-transitivity-library',
                declarations: transparentDefinitions.map(entry => entry.name)
            }
        ],
        allDefinitionsUseCheckedTransparentPolicy: true,
        allDefinitionsUseFreeDeclarationLinks: true,
        sourceInjectiveModifierRecordedAsMetadata: true,
        typescriptInjectivityBehaviorAdded: false,
        typescriptIntrinsicCoreOwnerAdded: false,
        genericCheckerBranchAdded: false,
        genericEvaluatorBranchAdded: false,
        genericRuntimeOrProofRuleAdded: false,
        comparisonStepLimit: 512,
        preserveSelectedSourceOrder: true
    },
    requiredExistingProviders: [
        'Catd_cat',
        'Functord_cat',
        'hom_con',
        'Rep_catd',
        'Op_cat',
        'Rep_catd_func',
        'fapp1_fapp0',
        'PathOut_cat',
        'Sigma_proj1_pullback_catd',
        'fib_cov_transf',
        'id_funcd'
    ],
    typedLibraryConsumers: [
        {
            name: 'path_comp_sec',
            expectedType:
                'Obj(Functord_cat(Z,Rep_catd(Z,x),CompTarget_catd(Z,x)))',
            role: 'fixed-source-transitivity-section'
        },
        {
            name: 'path_comp_func',
            expectedType: 'Functord(Rep_catd(Z,y),Rep_catd(Z,x))',
            role: 'represented-precomposition-by-a-path'
        }
    ],
    selectedDefinitionalObservations: [
        'CompTarget-fibre-is-representable-functor-category',
        'CompMotive-at-pathout-object-is-representable-functor-category',
        'CompMotive-sections-compare-with-CompTarget-representable-sections',
        'fixed-source-path-induction-on-CompMotive-is-path-comp-sec',
        'CompTarget-capped-action-is-CompTarget-fapp1-func',
        'path-comp-sec-component-is-path-comp-func',
        'path-comp-func-component-is-stable-representable-precomposition',
        'expanded-path-comp-component-retains-the-same-stable-normal-form'
    ],
    negativeConsumers: [
        'CompTarget-source-from-a-foreign-base',
        'CompMotive-point-from-a-foreign-PathOut',
        'path-comp-func-arrow-from-a-foreign-base',
        'path-comp-func-component-with-a-foreign-representable-arrow',
        'foreign-session-or-scoped-term',
        'using-source-injective-metadata-as-TypeScript-unification-authority',
        'ordinary-safe-library-runtime-or-proof-rule-attempt',
        'browser-or-public-package-import-before-presentation-review'
    ],
    boundedOracle: {
        packageRoot: 'emdash2',
        timeoutMs: 20_000,
        assertions: [
            'CompTarget-fibre-is-Functord-of-representables',
            'CompMotive-fibre-is-Functord-of-representables',
            'CompMotive-section-category-is-fixed-source-Functord',
            'path-induction-on-CompMotive-is-path-comp-sec',
            'CompTarget-action-is-readable-action-alias',
            'path-comp-sec-component-is-path-comp-func',
            'path-comp-func-component-is-stable-precomposition',
            'expanded-section-component-is-stable-precomposition'
        ],
        requiredForImplementationAcceptance: true,
        requiredForProposalAcceptance: false
    },
    profileSealing: {
        rootOnlyDuringQualification: true,
        ordinaryLibraryCanAddTransparentDefinitions: true,
        ordinaryLibraryCanAddOpaqueOwners: false,
        ordinaryLibraryCanAddRuntimeRules: false,
        ordinaryLibraryCanAddProofRules: false,
        browserOrPublicPackageExportAuthorized: false,
        pathCategoryBridgeAuthorized: false,
        textSyntaxAuthorized: false,
        transitivityClaimStopsAtStablePrecompositionNormalForm: true,
        rawCompositionComparisonRemainsProofTimeInActiveLambdapi: true
    },
    validation: {
        proposalTestsRequired: true,
        rootTypecheckRequired: true,
        focusedLintRequired: true,
        exactDiffAndWhitespaceReviewRequired: true,
        separateImmutableReviewRequired: true,
        implementationFocusedTestsRequired: true,
        namedBoundedOracleRequired: true,
        longAggregateRequired: false,
        carriedAggregateCheckpoint: 'e560551',
        carriedAggregateTests: 1923,
        reasonLongAggregateOmitted:
            'proposal-is-immutable-boundary-data-and-no-shared-runtime-' +
            'or-public-surface-changes'
    },
    gitBoundary: {
        proposalCheckpointRequiredBeforeReview: true,
        reviewCheckpointRequiredBeforeImplementation: true,
        localCheckpointAuthorized: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    decision: {
        question:
            'Approve only the exact root-only 0/0/0/5 transparent ' +
            'transitivity library over semantic checkpoint b6005b3?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-TRANSITIVITY-1E-implementation',
        'TypeScript-injectivity-or-unification-from-Lambdapi-metadata',
        'new-opaque-owner-runtime-rule-proof-rule-or-Core-node',
        'generic-checker-evaluator-or-comparison-change',
        'path-category-reflexive-component-join',
        'path-category-structured-versus-J-comparison-library',
        'public-browser-package-or-text-presentation',
        'active-Lambdapi-source-change',
        'integration-push-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-transitivity-1e-awaiting-separate-immutable-review'
} as const;

export type CorePathoutTransitivity1eProposal = typeof rawProposal;

export type CorePathoutTransitivity1eProposalErrorCode =
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_AUTHORITY_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_SCOPE_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eProposalError extends Error {
    constructor(
        public readonly code: CorePathoutTransitivity1eProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eProposalError';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL =
    deepFreeze(rawProposal);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCorePathoutTransitivity1eProposal(
    proposal: CorePathoutTransitivity1eProposal =
        CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
): CorePathoutTransitivity1eProposal {
    validateCorePathoutTrustBoundary0aAudit();
    const audited = CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.selectedOwners
        .filter(entry => entry.slice === 'transitivity')
        .map(entry => ({
            order: entry.order - 27,
            name: entry.name,
            authorityLine: entry.line,
            sourceKind: entry.sourceKind,
            sourceOpacity: entry.sourceOpacity
        }));
    const selected = proposal.authority.selectedDeclarations.map(entry => ({
        order: entry.order,
        name: entry.name,
        authorityLine: entry.authorityLine,
        sourceKind: entry.sourceKind,
        sourceOpacity: entry.sourceOpacity
    }));
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-1' ||
        proposal.parent.auditRevision !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision ||
        proposal.parent.authoritySourceSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.source.sha256 ||
        proposal.parent.authorityChecksSha256 !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.authority.checks.sha256 ||
        proposal.parent.internalizedRevision !==
            CORE_PATHIND_INTERNALIZED_1D_REVISION ||
        proposal.parent.internalizedReviewedAuthorization !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-14' ||
        proposal.parent.internalizedSemanticCheckpoint !== 'b6005b3' ||
        proposal.parent.internalizedLedgerCheckpoint !== '6225075' ||
        proposal.parent.internalizedBoundary !== '4/13/0/10' ||
        proposal.parent.activeLambdapiOwnerDelta !== 0 ||
        proposal.parent.activeLambdapiRuleDelta !== 0 ||
        !sameData(selected, audited)
    ) {
        throw new CorePathoutTransitivity1eProposalError(
            'PATHOUT_TRANSITIVITY_PROPOSAL_AUTHORITY_DRIFT',
            'The transitivity predecessor or active authority drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    if (
        implementation.exactBoundary !== '0/0/0/5' ||
        implementation.trustedDeclarations.length !== 0 ||
        implementation.runtimeRules.length !== 0 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 5 ||
        !implementation.allDefinitionsUseCheckedTransparentPolicy ||
        !implementation.allDefinitionsUseFreeDeclarationLinks ||
        !implementation.sourceInjectiveModifierRecordedAsMetadata ||
        implementation.typescriptInjectivityBehaviorAdded ||
        implementation.typescriptIntrinsicCoreOwnerAdded ||
        implementation.genericCheckerBranchAdded ||
        implementation.genericEvaluatorBranchAdded ||
        implementation.genericRuntimeOrProofRuleAdded ||
        implementation.comparisonStepLimit !== 512 ||
        !implementation.preserveSelectedSourceOrder ||
        proposal.requiredExistingProviders.length !== 11 ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedDefinitionalObservations.length !== 8 ||
        proposal.negativeConsumers.length !== 8 ||
        proposal.boundedOracle.assertions.length !== 8 ||
        !proposal.profileSealing
            .transitivityClaimStopsAtStablePrecompositionNormalForm ||
        !proposal.profileSealing
            .rawCompositionComparisonRemainsProofTimeInActiveLambdapi ||
        proposal.profileSealing.pathCategoryBridgeAuthorized ||
        proposal.profileSealing.browserOrPublicPackageExportAuthorized
    ) {
        throw new CorePathoutTransitivity1eProposalError(
            'PATHOUT_TRANSITIVITY_PROPOSAL_SCOPE_DRIFT',
            'The exact 0/0/0/5 transparent transitivity scope drifted'
        );
    }

    if (
        proposal.status !==
            'proposal-only-awaiting-separate-immutable-review' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathout-transitivity-1e-awaiting-separate-immutable-review'
    ) {
        throw new CorePathoutTransitivity1eProposalError(
            'PATHOUT_TRANSITIVITY_PROPOSAL_AUTHORIZATION_DRIFT',
            'The transitivity proposal became self-authorizing or widened'
        );
    }
    return proposal;
}

export const cloneCorePathoutTransitivity1eProposal = ():
CorePathoutTransitivity1eProposal => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
);
