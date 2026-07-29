/**
 * Executable DISPLAYED-CHAIN-2A-CLOSURE-0A proposal.
 *
 * D-016 authorized the exact four-binding mixed-telescope stress only while
 * its expected owner/rule/transfer delta remained zero. The implementation
 * audit falsified that expectation and stopped before promotion. This
 * deeply frozen proposal records the measured closure, selects an isolated
 * continuation profile, and authorizes nothing by itself.
 */

import {
    validateCoreCategoricalDisplayedGraduationReview
} from './categorical_displayed_graduation_review';

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

const existingDeclarations = [
    'sigma_Fst',
    'sigma_Snd',
    'Product_grpd'
] as const;

const exactExistingRuntimeRuleIds = [
    'categorical.displayed-chain-2a.product-groupoid-decode',
    'categorical.displayed-chain-2a.product-object',
    'categorical.displayed-chain-2a.product-left-projection.object',
    'categorical.displayed-chain-2a.product-right-projection.object',
    'categorical.displayed-chain-2a.product.general-hom',
    'categorical.displayed-chain-2a.product-map.object'
] as const;

const derivedRuntimeRuleIds = [
    'categorical.displayed-chain-2a.product-pair-left.delta-beta',
    'categorical.displayed-chain-2a.product-pair-right.delta-beta'
] as const;

const newRuntimeRuleIds = [
    'categorical.displayed-chain-2a.displayed-product-pair-internal-cell'
] as const;

const rawProposal = {
    revision: 'DISPLAYED-CHAIN-2A-CLOSURE-0A-PROPOSAL-1',
    row: 'DISPLAYED-CHAIN-2A-CLOSURE-0A',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-chain-2a-closure-01',
    reviewGate:
        'H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01',
    decisionId: 'D-DTTLF-USABILITY-017',
    prerequisite: {
        d016ReviewRevision:
            'DISPLAYED-BRACKET-GRADUATE-1-REVIEWED-1',
        d016ReviewCheckpoint:
            '24ce6ffede79e115bc5d387c65366598e56f5d3d',
        authorizedImplementationRow: 'DISPLAYED-CHAIN-2A',
        frozenShape:
            'k; a:A[k]; b:B[(k,a)], c:C[(k,a)]; ' +
            'd:D[((k,a),(b,c))]',
        expectedActiveOwnerDelta: 0,
        expectedActiveRuntimeRuleDelta: 0,
        expectedTransferEntryDelta: 0,
        closureDriftRequiresSeparateDecision: true,
        mandatoryStopHonored: true
    },
    auditVerdict: {
        loweringArchitectureSound: true,
        secondFrontendRequired: false,
        newBinderModeRequired: false,
        newMathematicalOwnerRequired: false,
        zeroDeltaAssumptionFalsified: true,
        firstStuckEvidence:
            'recursive-pair-b-c-internalized-arrow-cell',
        objectClosureBeforeNewRule: [
            'a',
            'b',
            'c',
            'd',
            'pair(b,c)'
        ],
        directInternalizedArrowClosureBeforeNewRule: [
            'a',
            'b',
            'c',
            'd'
        ],
        exactMissingMathematicalComputation:
            'fdapp1_int_cell(Product_pair_funcd(FF,GG),p,u) ' +
            'reduces to Product_pair(fdapp1_int_cell(FF,p,u),' +
            'fdapp1_int_cell(GG,p,u))',
        gapClass:
            'componentwise-internal-cell-action-for-existing-displayed-pair',
        architectureRedesignRequired: false
    },
    activeLambdapiCandidate: {
        newSymbolCount: 0,
        newRuntimeRuleCount: 1,
        newProofRuleCount: 0,
        owner: 'fdapp1_int_cell',
        pairedOwner: 'Product_pair_funcd',
        inferredTargetSlotRetainedAsWildcard: true,
        rhsConstructor: 'Product_pair',
        rhsComponentOwners: [
            'fdapp1_int_cell(FF)',
            'fdapp1_int_cell(GG)'
        ],
        ownerPositionProbe: {
            authorityCopy:
                'emdash2/tmp/probes/displayed_pair_internal_cell_2a.lp',
            positiveGenericConversion: 'passed',
            negativeOpaqueCellNoncollapse: 'passed',
            quietLog:
                'emdash2/logs/probes/' +
                'displayed_pair_internal_cell_2a-20260729-032242.log',
            warningLog:
                'emdash2/logs/probes/' +
                'displayed_pair_internal_cell_2a-20260729-032319.log',
            strictLhsAudit: 'passed-zero-unreviewed-candidates'
        },
        warningComparison: {
            baselineTotal: 1179,
            candidateTotal: 1179,
            baselineCriticalPairs: 1020,
            candidateCriticalPairs: 1020,
            baselineReplaceablePatternVariables: 159,
            candidateReplaceablePatternVariables: 159,
            warningDelta: 0,
            warningIsDiagnosticNotVeto: true
        }
    },
    typescriptClosure: {
        isolatedContinuationModule:
            'categorical_displayed_chain_2a_closure_transfer',
        isolatedProfile: 'fibred-displayed-chain-2a',
        completedChain1ProfileMutatedInPlace: false,
        existingDeclarations,
        existingDeclarationCount: existingDeclarations.length,
        exactExistingRuntimeRuleIds,
        exactExistingRuntimeRuleCount:
            exactExistingRuntimeRuleIds.length,
        derivedRuntimeRuleIds,
        derivedRuntimeRuleCount: derivedRuntimeRuleIds.length,
        newRuntimeRuleIds,
        newRuntimeRuleCount: newRuntimeRuleIds.length,
        totalContinuationRuntimeRuleCount:
            exactExistingRuntimeRuleIds.length +
            derivedRuntimeRuleIds.length +
            newRuntimeRuleIds.length,
        derivedRuleBasis:
            'active-transparent-Product_pair-plus-existing-' +
            'sigma-constructor-beta',
        broadSigmaConstructorBetasImported: false,
        typedPatternCorrections: [
            {
                id: 'sigma-pair-inferred-classifiers',
                slots: ['carrier', 'family-classifier'],
                change:
                    'rigid-computed-arguments-to-typed-wildcards',
                mathematicalNormalFormChanged: false
            },
            {
                id: 'displayed-projection-inferred-source-target',
                slots: ['source-family', 'target-family'],
                change:
                    'rigid-computed-arguments-to-typed-wildcards',
                mathematicalNormalFormChanged: false
            }
        ],
        typedPatternCorrectionCount: 2,
        checkerBudgetPlumbing: {
            generic: true,
            ownerSpecific: false,
            defaultCoreBudgetRemains: 256,
            selectedContinuationBudget: 512,
            existingLfSessionBudgetOptionHonoredByConstraints: true,
            newCheckerJudgment: false,
            newInferenceRule: false
        },
        subjectValidation: 'typescript-checked',
        externalSubjectReductionOracleCount: 0,
        intrinsicCoreOwnerCount: 0,
        ownerSpecificCheckerBranchCount: 0,
        ownerSpecificEvaluatorBranchCount: 0
    },
    prototypeEvidence: {
        objectComparisons: [
            { term: 'a', status: 'equal', steps: 99 },
            { term: 'b', status: 'equal', steps: 66 },
            { term: 'c', status: 'equal', steps: 66 },
            { term: 'd', status: 'equal', steps: 48 },
            { term: 'pair(b,c)', status: 'equal', steps: 164 }
        ],
        internalizedArrowIndependence: [
            { term: 'a', status: 'equal', steps: 96 },
            { term: 'b', status: 'equal', steps: 82 },
            { term: 'c', status: 'equal', steps: 82 },
            { term: 'd', status: 'equal', steps: 0 },
            { term: 'pair(b,c)', status: 'equal', steps: 986 }
        ],
        pairedInternalCellUsesNewRule: true,
        noncollapseComparisons: [
            { term: 'b', status: 'not-equal-to-opaque-rho' },
            { term: 'c', status: 'not-equal-to-opaque-rho' },
            {
                term: 'pair(b,c)',
                status: 'not-equal-to-opaque-rho',
                componentPairRetained: true
            }
        ],
        reindexingCorpusStillRequiredDuringImplementation: true,
        frontendNegativeCorpusStillRequiredDuringImplementation: true
    },
    alternatives: [
        {
            id: 'pretend-d016-zero-delta-still-holds',
            disposition: 'reject',
            reason:
                'The recursive paired internalized cell is measurably stuck'
        },
        {
            id: 'add-a-new-product-or-dependent-binder-owner',
            disposition: 'reject',
            reason:
                'All construction owners already exist; only one missing ' +
                'action rule and transfer closure are required'
        },
        {
            id: 'external-subject-reduction-oracle',
            disposition: 'reject',
            reason:
                'Importing Product_map object action and honoring the ' +
                'existing 512-step LF budget makes the rule TypeScript-checked'
        },
        {
            id: 'import-broad-sigma-constructor-betas',
            disposition: 'reject-for-this-slice',
            reason:
                'Two narrow checked Product_pair projection normal forms ' +
                'suffice and limit unrelated runtime effects'
        },
        {
            id: 'declaration-refinement-before-continuing',
            disposition: 'defer',
            reason:
                'The checked derived normal forms avoid reopening the ' +
                'optional DECL-REFINE-1A infrastructure question'
        },
        {
            id: 'isolated-canonical-closure-plus-one-owner-rule',
            disposition: 'recommend',
            reason:
                'It preserves chain-1, uses active owners and equations, ' +
                'and closes the full measured object/arrow corpus'
        }
    ],
    proposedImplementation: {
        activeLambdapiSymbolDelta: 0,
        activeLambdapiRuntimeRuleDelta: 1,
        activeLambdapiProofRuleDelta: 0,
        typescriptExistingDeclarationTransferCount: 3,
        typescriptRuntimeRuleCount: 9,
        typescriptExactExistingRuntimeRuleCount: 6,
        typescriptDerivedRuntimeRuleCount: 2,
        typescriptNewRuntimeRuleCount: 1,
        genericCheckerBudgetPlumbingCount: 1,
        intrinsicCoreOwnerDelta: 0,
        ownerSpecificCheckerEvaluatorDelta: 0,
        externalOracleDelta: 0,
        newProfileCount: 1,
        frontendMethod:
            'existing-displayedDependentContextLambda',
        frontendShapeRemainsExactly:
            'a; independent-siblings-b-c; d-dependent-on-pair',
        implementationRowAfterClosure:
            'DISPLAYED-CHAIN-2A'
    },
    validationPlan: {
        activeRulePositiveAndNoncollapseAssertionsRequired: true,
        boundedKernelCheckRequired: true,
        warningComparisonRequired: true,
        strictLhsAuditRequired: true,
        catalogAndHealthRefreshRequired: true,
        exactDeclarationAndRulePartitionRequired: true,
        everyTransferredRuleSubjectChecked: true,
        objectCorpusRequired: ['a', 'b', 'c', 'd', 'pair(b,c)'],
        internalizedArrowCorpusRequired: [
            'a',
            'b',
            'c',
            'd',
            'pair(b,c)'
        ],
        ordinaryReindexingCorpusRequired: true,
        profileBaseArityEscapeForeignDependencyNegativesRequired: true,
        rootTypecheckLintTestsRequired: true,
        completeRepositoryGateRequiredBeforeCheckpoint: true
    },
    nonEffects: [
        'does-not-rewrite-or-falsify-d016-history',
        'does-not-add-a-lambdapi-symbol',
        'does-not-add-a-proof-time-rule',
        'does-not-add-an-intrinsic-core-owner',
        'does-not-add-an-owner-specific-checker-or-evaluator-branch',
        'does-not-add-an-external-subject-reduction-oracle',
        'does-not-add-a-second-frontend-ast-or-checker',
        'does-not-add-a-parser-or-string-syntax',
        'does-not-authorize-general-nd',
        'does-not-authorize-arbitrary-telescope-depth-or-mixed-variance',
        'does-not-authorize-groupoidal-closure',
        'does-not-authorize-browser-promotion',
        'does-not-authorize-bulk-whole-library-transfer',
        'does-not-authorize-decl-refine-1a',
        'does-not-broaden-git-authority'
    ],
    decisionEffects: {
        authorityAuthorized: false,
        implementationAuthorized: false,
        nextIfApproved:
            'implement-displayed-chain-2a-closure-then-complete-' +
            'the-frozen-mixed-telescope',
        nextIfRejected:
            'displayed-chain-2a-remains-stopped-at-the-d016-closure-drift'
    }
} as const;

export type CoreCategoricalDisplayedChain2aClosureProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedChain2aClosureProposalErrorCode =
    | 'DISPLAYED_CHAIN_2A_CLOSURE_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_2A_CLOSURE_BOUNDARY_DRIFT'
    | 'DISPLAYED_CHAIN_2A_CLOSURE_AUTHORITY_DRIFT';

export class CoreCategoricalDisplayedChain2aClosureProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChain2aClosureProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChain2aClosureProposalError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreCategoricalDisplayedChain2aClosureProposal(
    proposal:
        CoreCategoricalDisplayedChain2aClosureProposalInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
): void {
    try {
        validateCoreCategoricalDisplayedGraduationReview();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedChain2aClosureProposalError(
            'DISPLAYED_CHAIN_2A_CLOSURE_PREREQUISITE_DRIFT',
            'The reviewed D-016 prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        proposal.revision !==
            'DISPLAYED-CHAIN-2A-CLOSURE-0A-PROPOSAL-1' ||
        proposal.row !== 'DISPLAYED-CHAIN-2A-CLOSURE-0A' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-017' ||
        proposal.prerequisite.authorizedImplementationRow !==
            'DISPLAYED-CHAIN-2A' ||
        !proposal.prerequisite.closureDriftRequiresSeparateDecision ||
        !proposal.prerequisite.mandatoryStopHonored ||
        !proposal.auditVerdict.zeroDeltaAssumptionFalsified ||
        !proposal.auditVerdict.loweringArchitectureSound ||
        proposal.auditVerdict.architectureRedesignRequired ||
        proposal.auditVerdict.newMathematicalOwnerRequired
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureProposalError(
            'DISPLAYED_CHAIN_2A_CLOSURE_PREREQUISITE_DRIFT',
            'The D-016 stop condition or measured closure diagnosis drifted'
        );
    }

    const lp = proposal.activeLambdapiCandidate;
    const ts = proposal.typescriptClosure;
    const implementation = proposal.proposedImplementation;
    if (
        lp.newSymbolCount !== 0 ||
        lp.newRuntimeRuleCount !== 1 ||
        lp.newProofRuleCount !== 0 ||
        lp.owner !== 'fdapp1_int_cell' ||
        !lp.inferredTargetSlotRetainedAsWildcard ||
        lp.warningComparison.warningDelta !== 0 ||
        lp.warningComparison.candidateTotal !== 1179 ||
        lp.warningComparison.candidateCriticalPairs !== 1020 ||
        lp.warningComparison.candidateReplaceablePatternVariables !== 159 ||
        ts.existingDeclarations.join(',') !==
            existingDeclarations.join(',') ||
        ts.exactExistingRuntimeRuleIds.join(',') !==
            exactExistingRuntimeRuleIds.join(',') ||
        ts.derivedRuntimeRuleIds.join(',') !==
            derivedRuntimeRuleIds.join(',') ||
        ts.newRuntimeRuleIds.join(',') !==
            newRuntimeRuleIds.join(',') ||
        ts.existingDeclarationCount !== 3 ||
        ts.exactExistingRuntimeRuleCount !== 6 ||
        ts.derivedRuntimeRuleCount !== 2 ||
        ts.newRuntimeRuleCount !== 1 ||
        ts.totalContinuationRuntimeRuleCount !== 9 ||
        ts.broadSigmaConstructorBetasImported ||
        ts.typedPatternCorrectionCount !== 2 ||
        ts.checkerBudgetPlumbing.defaultCoreBudgetRemains !== 256 ||
        ts.checkerBudgetPlumbing.selectedContinuationBudget !== 512 ||
        !ts.checkerBudgetPlumbing.generic ||
        ts.checkerBudgetPlumbing.ownerSpecific ||
        ts.subjectValidation !== 'typescript-checked' ||
        ts.externalSubjectReductionOracleCount !== 0 ||
        ts.intrinsicCoreOwnerCount !== 0 ||
        implementation.activeLambdapiRuntimeRuleDelta !== 1 ||
        implementation.typescriptExistingDeclarationTransferCount !== 3 ||
        implementation.typescriptRuntimeRuleCount !== 9 ||
        implementation.genericCheckerBudgetPlumbingCount !== 1 ||
        implementation.intrinsicCoreOwnerDelta !== 0 ||
        implementation.externalOracleDelta !== 0 ||
        proposal.alternatives.filter(
            alternative => alternative.disposition === 'recommend'
        ).map(alternative => alternative.id).join(',') !==
            'isolated-canonical-closure-plus-one-owner-rule'
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureProposalError(
            'DISPLAYED_CHAIN_2A_CLOSURE_BOUNDARY_DRIFT',
            'The exact one-rule/canonical-transfer closure drifted'
        );
    }

    if (
        proposal.decisionEffects.authorityAuthorized ||
        proposal.decisionEffects.implementationAuthorized ||
        proposal.nonEffects.length !== 15
    ) {
        throw new CoreCategoricalDisplayedChain2aClosureProposalError(
            'DISPLAYED_CHAIN_2A_CLOSURE_AUTHORITY_DRIFT',
            'The proposal must remain deeply frozen and non-self-authorizing'
        );
    }
}

validateCoreCategoricalDisplayedChain2aClosureProposal();
