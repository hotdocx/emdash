/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v9.
 *
 * V9 replaces v8's unavailable forward reference one-for-one with the
 * stable complete-parent form produced by the already-active generic Sigma
 * fibre projection. The local rule still adds no mathematical equation.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8,
    validateCorePathindInternalized1dProposalV8
} from './pathind_internalized_proposal_v8';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-9' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-09/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-009 as proposed.';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

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

const proposalV8 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8;

const pathInductionSourceFibrePostSigmaProjectionFusion = {
    order: 9,
    id:
        'pathind.internalized.' +
        'path-ind-source-fibre-post-sigma-projection-fusion',
    authority: 'derived-complete-parent-post-sigma-projection-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:13297-13314',
        'emdash2/emdash3_2.lp:19080-19091',
        'emdash2/emdash3_2.lp:19296-19317'
    ],
    sourceOwner: 'functor-object',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['Z', 'x', 'E'],
    left:
        'fapp0(Fibre_cat(PathOutMotives_catd(Z),x),Cat_cat,' +
        'PathOutReflEval_funcd(Z)[x],E)',
    right: 'Fibre_cat(E,pathout_refl_obj(Z,x))'
} as const;

const correctedRuntimeRules = Object.freeze(
    proposalV8.exactImplementation.runtimeRules.map((rule, index) =>
        index === 9
            ? pathInductionSourceFibrePostSigmaProjectionFusion
            : cloneData(rule)
    )
);

const correctedStages = proposalV8.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const {
    pathInductionSourceFibrePresentationFusion: _supersededV8Fusion,
    ...retainedDependencyClosure
} = cloneData(proposalV8.dependencyClosure);

void _supersededV8Fusion;

const rawProposal = {
    ...cloneData(proposalV8),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9_REVISION,
    status: 'corrected-proposal-v9-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV8.parent),
        supersededProposalRevision: proposalV8.revision,
        supersededProposalCheckpoint: 'f26d340',
        supersededReviewCheckpoint: '1de3c95',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV8.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v8-first-cold-module-load',
            v7AllNineLocalRuntimeRulesCompiled: true,
            v7CompiledTransparentDefinitionCount: 3,
            v8FailedBeforeRuntimeSubjectCheck: true,
            v8FailedBeforeSemanticCompilation: true,
            failingPhase: 'closed-runtime-module-construction',
            failingCode: 'UNRESOLVED_GLOBAL',
            failingPath: 'module.referencedSymbols',
            unresolvedGlobal: 'emdash.emdash3_2.PathIndSrc_catd',
            exactFailure:
                "Transfer fragment does not declare external global '" +
                "emdash.emdash3_2.PathIndSrc_catd'",
            runtimeFragmentCompiledBeforeDerivedLibrary: true,
            pathIndSrcDeclarationIsInLaterDerivedLibrary: true,
            v8PreDeltaRuleUnavailableAtRuntimeBoundary: true,
            stableGenericSigmaProjectionRhsAvailable: true,
            correctedCompleteParentLeft:
                pathInductionSourceFibrePostSigmaProjectionFusion.left,
            correctedCompleteParentRight:
                pathInductionSourceFibrePostSigmaProjectionFusion.right,
            declarationRepartitionRequired: false,
            forwardReferenceSupportRequired: false,
            underlyingCategoryEqualityRequired: false,
            genericSigmaFibreEquationRequired: false,
            genericComparisonChangeRequired: false,
            additionalActiveMathematicalRuleRequired: false,
            replacementDerivedSupportRuleRequired: true,
            proofRuleRequired: false,
            temporaryObserverRetained: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-09',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-009',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV8.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/10/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 5
    },
    selectedPredecessor: {
        ...cloneData(proposalV8.selectedPredecessor),
        v8PathInductionSourceFibrePresentationFusionSelected: false,
        v8PreDeltaPathIndSrcGlobalRuleRejected: true,
        v9PostSigmaProjectionSourceFibreFusionSelected: true
    },
    dependencyClosure: {
        ...retainedDependencyClosure,
        pathInductionSourceFibrePostSigmaProjectionFusion: {
            ruleId: pathInductionSourceFibrePostSigmaProjectionFusion.id,
            authorityPositions:
                pathInductionSourceFibrePostSigmaProjectionFusion
                    .authorityPositions,
            left: pathInductionSourceFibrePostSigmaProjectionFusion.left,
            right: pathInductionSourceFibrePostSigmaProjectionFusion.right,
            exactStablePostSigmaProjectionParentSelected: true,
            usesOnlyEarlierDeclaredSymbols: true,
            sourceFibrePresentationOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 0,
            replacedDerivedSupportRuleCount: 1,
            proofRuleDelta: 0,
            laterLibraryGlobalReferenceAuthorized: false,
            declarationRepartitionAuthorized: false,
            underlyingCategoryEqualityAuthorized: false,
            genericSigmaFibreRuleAuthorized: false,
            genericComparisonChangeAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV8.validation),
        v8ProposalCheckpointRequired: 'f26d340',
        v8ReviewCheckpointRequired: '1de3c95',
        reasonLongAggregateOmitted:
            'v9-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v9-implementation',
        ...cloneData(proposalV8.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v8-implementation'
        ),
        'a-runtime-reference-to-later-PathIndSrc_catd',
        'repartitioning-transparent-library-declarations'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v9-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV9 = typeof rawProposal;

export type CorePathindInternalized1dProposalV9ErrorCode =
    | 'PATHIND_INTERNALIZED_V9_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V9_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V9_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV9Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV9ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV9Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV9(
    proposal: CorePathindInternalized1dProposalV9 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9
): CorePathindInternalized1dProposalV9 {
    validateCorePathindInternalized1dProposalV8(proposalV8);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-9' ||
        proposal.parent.supersededProposalRevision !== proposalV8.revision ||
        proposal.parent.supersededProposalCheckpoint !== 'f26d340' ||
        proposal.parent.supersededReviewCheckpoint !== '1de3c95' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.v7AllNineLocalRuntimeRulesCompiled ||
        evidence.v7CompiledTransparentDefinitionCount !== 3 ||
        !evidence.v8FailedBeforeRuntimeSubjectCheck ||
        !evidence.v8FailedBeforeSemanticCompilation ||
        evidence.failingCode !== 'UNRESOLVED_GLOBAL' ||
        evidence.failingPath !== 'module.referencedSymbols' ||
        evidence.unresolvedGlobal !==
            'emdash.emdash3_2.PathIndSrc_catd' ||
        !evidence.runtimeFragmentCompiledBeforeDerivedLibrary ||
        !evidence.pathIndSrcDeclarationIsInLaterDerivedLibrary ||
        !evidence.v8PreDeltaRuleUnavailableAtRuntimeBoundary ||
        !evidence.stableGenericSigmaProjectionRhsAvailable ||
        evidence.declarationRepartitionRequired ||
        evidence.forwardReferenceSupportRequired ||
        evidence.underlyingCategoryEqualityRequired ||
        evidence.genericSigmaFibreEquationRequired ||
        evidence.genericComparisonChangeRequired ||
        evidence.additionalActiveMathematicalRuleRequired ||
        !evidence.replacementDerivedSupportRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained
    ) {
        throw new CorePathindInternalized1dProposalV9Error(
            'PATHIND_INTERNALIZED_V9_AUTHORITY_DRIFT',
            'The reviewed-v8 closed-module counterevidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion = proposal.dependencyClosure
        .pathInductionSourceFibrePostSigmaProjectionFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 10 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/10/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 5 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[9].id !==
            pathInductionSourceFibrePostSigmaProjectionFusion.id ||
        proposal.selectedPredecessor
            .v8PathInductionSourceFibrePresentationFusionSelected ||
        !proposal.selectedPredecessor
            .v8PreDeltaPathIndSrcGlobalRuleRejected ||
        !proposal.selectedPredecessor
            .v9PostSigmaProjectionSourceFibreFusionSelected ||
        fusion.ruleId !==
            pathInductionSourceFibrePostSigmaProjectionFusion.id ||
        !fusion.exactStablePostSigmaProjectionParentSelected ||
        !fusion.usesOnlyEarlierDeclaredSymbols ||
        !fusion.sourceFibrePresentationOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 0 ||
        fusion.replacedDerivedSupportRuleCount !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.laterLibraryGlobalReferenceAuthorized ||
        fusion.declarationRepartitionAuthorized ||
        fusion.underlyingCategoryEqualityAuthorized ||
        fusion.genericSigmaFibreRuleAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 10 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 12
    ) {
        throw new CorePathindInternalized1dProposalV9Error(
            'PATHIND_INTERNALIZED_V9_SCOPE_DRIFT',
            'The exact corrected 4/10/0/10 post-Sigma boundary drifted'
        );
    }

    if (
        proposal.decision.question !== DECISION_QUESTION ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.profileSealing.packageOrBrowserExportAuthorized ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathind-internalized-1d-v9-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV9Error(
            'PATHIND_INTERNALIZED_V9_AUTHORIZATION_DRIFT',
            'Corrected proposal v9 became self-authorizing or widened'
        );
    }
    return proposal;
}
