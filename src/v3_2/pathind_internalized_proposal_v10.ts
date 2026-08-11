/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v10.
 *
 * V10 retains the exact 4/10/0/10 semantic boundary but stages it around the
 * already-measured three-definition prefix. This makes PathIndSrc_catd an
 * earlier declared symbol for one direct complete-parent support rule.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9,
    validateCorePathindInternalized1dProposalV9
} from './pathind_internalized_proposal_v9';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-10' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-10/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-010 as proposed.';

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

const proposalV9 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9;

const pathInductionSourceFibreStagedParentFusion = {
    order: 9,
    id:
        'pathind.internalized.' +
        'path-ind-source-fibre-at-sigma-pair-presentation-fusion',
    authority: 'derived-staged-complete-parent-source-fibre-fusion',
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
        'Fibre_cat(PathIndSrc_catd(Z),Struct_sigma(x,E))',
    right: 'Fibre_cat(E,pathout_refl_obj(Z,x))'
} as const;

const baseRuntimeRules = Object.freeze(
    proposalV9.exactImplementation.runtimeRules
        .slice(0, 9)
        .map(rule => cloneData(rule))
);

const correctedRuntimeRules = Object.freeze([
    ...baseRuntimeRules,
    pathInductionSourceFibreStagedParentFusion
]);

const prefixTransparentDefinitions = Object.freeze([
    'pathout_motive_transport_obj',
    'pathout_motive_transport_arrow',
    'PathIndSrc_catd'
]);

const suffixTransparentDefinitions = Object.freeze([
    'PathIndSrc_transport_func',
    'PathInd_funcd',
    'pathout_pi_transport_func',
    'PathIndTgt_transport_func'
]);

const retainedInitialStages = proposalV9.exactImplementation
    .implementationStages.slice(0, 3).map(stage => cloneData(stage));

const correctedStages = Object.freeze([
    ...retainedInitialStages,
    {
        order: 3,
        id: 'internalized-runtime-base-projections',
        rules: baseRuntimeRules.map(rule => rule.id)
    },
    {
        order: 4,
        id: 'derived-internalized-prefix-library',
        declarations: prefixTransparentDefinitions
    },
    {
        order: 5,
        id: 'internalized-runtime-source-fibre-extension',
        rules: [pathInductionSourceFibreStagedParentFusion.id]
    },
    {
        order: 6,
        id: 'derived-internalized-suffix-library',
        declarations: suffixTransparentDefinitions
    }
]);

const {
    pathInductionSourceFibrePostSigmaProjectionFusion:
        _supersededV9Fusion,
    ...retainedDependencyClosure
} = cloneData(proposalV9.dependencyClosure);

void _supersededV9Fusion;

const rawProposal = {
    ...cloneData(proposalV9),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10_REVISION,
    status: 'corrected-proposal-v10-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV9.parent),
        supersededProposalRevision: proposalV9.revision,
        supersededProposalCheckpoint: 'a735c40',
        supersededReviewCheckpoint: '7b466d5',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV9.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v9-cold-semantic-replay-with-trace',
            allTenV9RuntimeRulesSubjectChecked: true,
            firstThreeTransparentDefinitionsCompiled: true,
            compiledTransparentDefinitions:
                cloneData(prefixTransparentDefinitions),
            failingDeclaration: 'PathIndSrc_transport_func',
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19309-19317',
            requestedComparisonStepLimit: 512,
            effectiveComparisonStepLimit: 512,
            comparisonStepLimitExceeded: false,
            comparisonStepsBeforeMismatch: 360,
            mismatchCode: 'TAG_MISMATCH',
            mismatchPath: [
                '$',
                'application:decode:argument:0',
                'application:object-classifier:argument:0',
                'call:argument:0',
                'application:functor-object:argument:0',
                'call:argument:1'
            ],
            v9PostSigmaSupportAppearedInTrace: false,
            genericSigmaTelescopeFibreRuleAppearedInTrace: false,
            anyPathIndRuntimeRuleAppearedInFailingTrace: false,
            sourceCategoryChildSelectedBeforeFamilyProjection: true,
            postSigmaParentCannotBecomeAvailable: true,
            baseNineRulesAlreadySufficientForPrefix: true,
            prefixCanBeCompiledBeforeTenthRule: true,
            stagedDirectParentRuleRequired: true,
            declarationBodyOrTypeChangeRequired: false,
            declarationSourceOrderChangeRequired: false,
            totalRuntimeRuleCountChangeRequired: false,
            totalTransparentDefinitionCountChangeRequired: false,
            underlyingCategoryEqualityRequired: false,
            genericComparisonChangeRequired: false,
            proofRuleRequired: false,
            temporaryObserverRetained: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-10',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-010',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV9.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/10/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 5,
        stagedModulePartition: {
            baseRuntimeRuleIds:
                baseRuntimeRules.map(rule => rule.id),
            prefixTransparentDefinitions,
            extensionRuntimeRuleIds: [
                pathInductionSourceFibreStagedParentFusion.id
            ],
            suffixTransparentDefinitions,
            declarationOrderPreserved: true,
            semanticCountDelta: 0
        }
    },
    selectedPredecessor: {
        ...cloneData(proposalV9.selectedPredecessor),
        v9PostSigmaProjectionSourceFibreFusionSelected: false,
        v9PostSigmaProjectionRuleRejectedByTrace: true,
        v10StagedDirectSourceFibreFusionSelected: true
    },
    dependencyClosure: {
        ...retainedDependencyClosure,
        pathInductionSourceFibreStagedParentFusion: {
            ruleId: pathInductionSourceFibreStagedParentFusion.id,
            authorityPositions:
                pathInductionSourceFibreStagedParentFusion
                    .authorityPositions,
            left: pathInductionSourceFibreStagedParentFusion.left,
            right: pathInductionSourceFibreStagedParentFusion.right,
            exactCompleteParentPairSelected: true,
            pathIndSrcDeclaredByPrefixBeforeRuleCompilation: true,
            baseRuntimeRetainsOnlyFirstNineRules: true,
            extensionRuntimeContainsOnlyThisRule: true,
            suffixUsesComposedBaseAndExtensionRuntime: true,
            sourceFibrePresentationOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 0,
            replacedDerivedSupportRuleCount: 1,
            proofRuleDelta: 0,
            declarationBodyOrTypeChangeAuthorized: false,
            declarationSourceOrderChangeAuthorized: false,
            underlyingCategoryEqualityAuthorized: false,
            genericSigmaFibreRuleAuthorized: false,
            genericComparisonChangeAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV9.validation),
        v9ProposalCheckpointRequired: 'a735c40',
        v9ReviewCheckpointRequired: '7b466d5',
        reasonLongAggregateOmitted:
            'v10-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v10-implementation',
        ...cloneData(proposalV9.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v9-implementation'
        ),
        'changing-any-selected-declaration-body-or-type',
        'changing-the-order-of-the-seven-derived-declarations',
        'adding-an-eleventh-runtime-rule'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v10-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV10 = typeof rawProposal;

export type CorePathindInternalized1dProposalV10ErrorCode =
    | 'PATHIND_INTERNALIZED_V10_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V10_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V10_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV10Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV10ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV10Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV10(
    proposal: CorePathindInternalized1dProposalV10 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10
): CorePathindInternalized1dProposalV10 {
    validateCorePathindInternalized1dProposalV9(proposalV9);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-10' ||
        proposal.parent.supersededProposalRevision !== proposalV9.revision ||
        proposal.parent.supersededProposalCheckpoint !== 'a735c40' ||
        proposal.parent.supersededReviewCheckpoint !== '7b466d5' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allTenV9RuntimeRulesSubjectChecked ||
        !evidence.firstThreeTransparentDefinitionsCompiled ||
        !sameData(
            evidence.compiledTransparentDefinitions,
            prefixTransparentDefinitions
        ) ||
        evidence.failingDeclaration !== 'PathIndSrc_transport_func' ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.effectiveComparisonStepLimit !== 512 ||
        evidence.comparisonStepLimitExceeded ||
        evidence.comparisonStepsBeforeMismatch !== 360 ||
        evidence.mismatchCode !== 'TAG_MISMATCH' ||
        evidence.v9PostSigmaSupportAppearedInTrace ||
        evidence.genericSigmaTelescopeFibreRuleAppearedInTrace ||
        evidence.anyPathIndRuntimeRuleAppearedInFailingTrace ||
        !evidence.sourceCategoryChildSelectedBeforeFamilyProjection ||
        !evidence.postSigmaParentCannotBecomeAvailable ||
        !evidence.baseNineRulesAlreadySufficientForPrefix ||
        !evidence.prefixCanBeCompiledBeforeTenthRule ||
        !evidence.stagedDirectParentRuleRequired ||
        evidence.declarationBodyOrTypeChangeRequired ||
        evidence.declarationSourceOrderChangeRequired ||
        evidence.totalRuntimeRuleCountChangeRequired ||
        evidence.totalTransparentDefinitionCountChangeRequired ||
        evidence.underlyingCategoryEqualityRequired ||
        evidence.genericComparisonChangeRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained
    ) {
        throw new CorePathindInternalized1dProposalV10Error(
            'PATHIND_INTERNALIZED_V10_AUTHORITY_DRIFT',
            'The reviewed-v9 trace or staged prerequisite drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const partition = implementation.stagedModulePartition;
    const fusion = proposal.dependencyClosure
        .pathInductionSourceFibreStagedParentFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 10 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/10/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 5 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        !sameData(partition.baseRuntimeRuleIds,
            baseRuntimeRules.map(rule => rule.id)) ||
        !sameData(partition.prefixTransparentDefinitions,
            prefixTransparentDefinitions) ||
        !sameData(partition.extensionRuntimeRuleIds,
            [pathInductionSourceFibreStagedParentFusion.id]) ||
        !sameData(partition.suffixTransparentDefinitions,
            suffixTransparentDefinitions) ||
        !partition.declarationOrderPreserved ||
        partition.semanticCountDelta !== 0 ||
        proposal.selectedPredecessor
            .v9PostSigmaProjectionSourceFibreFusionSelected ||
        !proposal.selectedPredecessor
            .v9PostSigmaProjectionRuleRejectedByTrace ||
        !proposal.selectedPredecessor
            .v10StagedDirectSourceFibreFusionSelected ||
        fusion.ruleId !== pathInductionSourceFibreStagedParentFusion.id ||
        !fusion.exactCompleteParentPairSelected ||
        !fusion.pathIndSrcDeclaredByPrefixBeforeRuleCompilation ||
        !fusion.baseRuntimeRetainsOnlyFirstNineRules ||
        !fusion.extensionRuntimeContainsOnlyThisRule ||
        !fusion.suffixUsesComposedBaseAndExtensionRuntime ||
        !fusion.sourceFibrePresentationOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 0 ||
        fusion.replacedDerivedSupportRuleCount !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.declarationBodyOrTypeChangeAuthorized ||
        fusion.declarationSourceOrderChangeAuthorized ||
        fusion.underlyingCategoryEqualityAuthorized ||
        fusion.genericSigmaFibreRuleAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized
    ) {
        throw new CorePathindInternalized1dProposalV10Error(
            'PATHIND_INTERNALIZED_V10_SCOPE_DRIFT',
            'The exact staged 4/10/0/10 boundary drifted'
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
            'pathind-internalized-1d-v10-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV10Error(
            'PATHIND_INTERNALIZED_V10_AUTHORIZATION_DRIFT',
            'Corrected proposal v10 became self-authorizing or widened'
        );
    }
    return proposal;
}
