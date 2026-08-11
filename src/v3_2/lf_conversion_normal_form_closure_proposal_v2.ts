/**
 * Corrected non-authorizing proposal v2 for terminal normal-form closure.
 *
 * V1 correctly selected deterministic same-budget closure, but incorrectly
 * selected the paired traversal's returned roots as its inputs. A paired
 * traversal can normalize past an intermediate parent redex; canonical
 * left-then-right replay must therefore start from the original source roots.
 */

import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL,
    validateCoreLfComparisonNormalFormClosureProposal
} from './lf_conversion_normal_form_closure_proposal';

export const CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2_REVISION =
    'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-PROPOSAL-2' as const;

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

const proposalV1 = CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL;

const correctedAlgorithm = Object.freeze([
    'retain-the-existing-paired-outcome-and-consumed-operation-count',
    'normalize-the-original-left-source-root',
    'normalize-the-original-right-source-root',
    'share-the-original-single-global-operation-budget-with-no-reset',
    'append-every-replayed-reduction-to-the-original-comparison-trace',
    'retry-structural-comparison-on-the-canonical-source-normal-forms',
    'return-equal-only-for-exact-kernel-expression-equality'
]);

const rawProposal = {
    ...cloneData(proposalV1),
    revision:
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2_REVISION,
    status: 'corrected-proposal-v2-awaiting-separate-review',
    parent: {
        supersededProposalRevision: proposalV1.revision,
        supersededProposalCheckpoint: 'cf8ed76',
        supersededReviewCheckpoint: '778da06',
        supersededLedgerCheckpoint: '2801a25',
        counterevidence: {
            measuredDuring:
                'reviewed-pathind-v5-cold-replay-with-in-process-wrapper',
            repositorySourceObserverAdded: false,
            retainedObserver: false,
            pairedComparisonStatus: 'not-equal',
            pairedComparisonSteps: 125,
            pairedMismatchCode: 'TAG_MISMATCH',
            pairedMismatchPath:
                '$/decode/Obj/Transf_cat/source-category',
            pairedMismatchLeftHead: 'displayed-category-category',
            pairedMismatchRightHead: 'call',
            pairedReturnedLeftNormalizationStatus: 'normal',
            pairedReturnedLeftAdditionalSteps: 0,
            pairedReturnedRightNormalizationStatus: 'normal',
            pairedReturnedRightAdditionalSteps: 0,
            pairedReturnedNormalFormsExactlyEqual: false,
            originalLeftNormalizationStatus: 'normal',
            originalLeftNormalizationSteps: 58,
            originalRightNormalizationStatus: 'normal',
            originalRightNormalizationSteps: 68,
            originalSourceNormalFormsExactlyEqual: true,
            exactCause:
                'paired-traversal-over-normalized-past-intermediate-' +
                'parent-redex',
            v1OutcomeRootClosureSufficient: false,
            v2OriginalRootReplayRequired: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-02',
        decisionId: 'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-002',
        question:
            'Approve terminal same-budget canonical replay from the ' +
            'original comparison roots after paired comparison returns ' +
            'not-equal?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactCorrection: {
        ...cloneData(proposalV1.exactCorrection),
        algorithm: correctedAlgorithm,
        closureInputs: 'original-comparison-source-roots',
        pairedOutcomeRootsUsedAsClosureInputs: false,
        pairedOutcomeRetainedForFallbackDiagnostic: true,
        replayedReductionsCountAgainstOriginalBudget: true,
        repeatedReductionWorkMayAppearInTrace: true,
        deterministicSideOrder: ['left', 'right'] as const
    },
    budgetAndFailureContract: {
        ...cloneData(proposalV1.budgetAndFailureContract),
        pairedPhaseConsumptionRetained: true,
        sourceReplayReceivesOnlyRemainingBudget: true,
        noMemoizationOrTraceDeduplication: true,
        directStructuralPlicityMismatchRemainsNotEqual: true
    },
    requiredEvidence: {
        ...cloneData(proposalV1.requiredEvidence),
        focusedGenericRegression: [
            ...cloneData(
                proposalV1.requiredEvidence.focusedGenericRegression
            ),
            'paired-over-normalization-loses-intermediate-parent-redex',
            'outcome-root-closure-remains-distinct-in-that-case',
            'original-root-replay-reaches-one-exact-normal-form',
            'direct-structural-plicity-mismatch-retains-full-roots'
        ],
        reviewedPathIndV5ConsumerMustCompile: true
    },
    implementationStages: [
        {
            order: 0,
            id: 'freeze-and-review-corrected-source-replay',
            mutation: false
        },
        {
            order: 1,
            id: 'add-over-normalization-focused-regression',
            mutation: true
        },
        {
            order: 2,
            id: 'switch-terminal-closure-inputs-to-original-roots',
            mutation: true
        },
        {
            order: 3,
            id: 'replay-reviewed-pathind-v5-consumer-once',
            mutation: true
        }
    ],
    doesNotAuthorize: [
        'implementation-before-separate-v2-review',
        ...cloneData(proposalV1.doesNotAuthorize).filter(entry =>
            entry !== 'implementation-before-separate-review'
        ),
        'resetting-the-budget-before-source-root-replay',
        'discarding-or-deduplicating-the-paired-phase-trace',
        'normalizing-only-the-distinct-paired-outcome-roots',
        'memoization-caching-or-a-new-reduction-strategy'
    ],
    nextDependencyState:
        'comparison-normal-form-closure-v2-awaiting-separate-review'
} as const;

export type CoreLfComparisonNormalFormClosureProposalV2 =
    typeof rawProposal;

export type CoreLfComparisonNormalFormClosureProposalV2ErrorCode =
    | 'COMPARISON_NORMAL_FORM_CLOSURE_V2_AUTHORITY_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_V2_SCOPE_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_V2_AUTHORIZATION_DRIFT';

export class CoreLfComparisonNormalFormClosureProposalV2Error
    extends Error {
    constructor(
        public readonly code:
            CoreLfComparisonNormalFormClosureProposalV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfComparisonNormalFormClosureProposalV2Error';
    }
}

export const CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2 =
    deepFreeze(rawProposal);

export function validateCoreLfComparisonNormalFormClosureProposalV2(
    proposal: CoreLfComparisonNormalFormClosureProposalV2 =
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2
): CoreLfComparisonNormalFormClosureProposalV2 {
    validateCoreLfComparisonNormalFormClosureProposal();
    const parent = proposal.parent;
    const evidence = parent.counterevidence;
    if (
        proposal.revision !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-PROPOSAL-2' ||
        parent.supersededProposalRevision !== proposalV1.revision ||
        parent.supersededProposalCheckpoint !== 'cf8ed76' ||
        parent.supersededReviewCheckpoint !== '778da06' ||
        parent.supersededLedgerCheckpoint !== '2801a25' ||
        evidence.repositorySourceObserverAdded ||
        evidence.retainedObserver ||
        evidence.pairedComparisonStatus !== 'not-equal' ||
        evidence.pairedComparisonSteps !== 125 ||
        evidence.pairedMismatchCode !== 'TAG_MISMATCH' ||
        evidence.pairedReturnedLeftAdditionalSteps !== 0 ||
        evidence.pairedReturnedRightAdditionalSteps !== 0 ||
        evidence.pairedReturnedNormalFormsExactlyEqual ||
        evidence.originalLeftNormalizationSteps !== 58 ||
        evidence.originalRightNormalizationSteps !== 68 ||
        !evidence.originalSourceNormalFormsExactlyEqual ||
        evidence.v1OutcomeRootClosureSufficient ||
        !evidence.v2OriginalRootReplayRequired
    ) {
        throw new CoreLfComparisonNormalFormClosureProposalV2Error(
            'COMPARISON_NORMAL_FORM_CLOSURE_V2_AUTHORITY_DRIFT',
            'The v1 checkpoint or measured source-replay evidence drifted'
        );
    }

    const correction = proposal.exactCorrection;
    const budget = proposal.budgetAndFailureContract;
    if (
        correction.owner !== 'coreLfDefinitionalCompare' ||
        correction.trigger !== 'existing-paired-outcome-is-not-equal' ||
        !sameData(correction.algorithm, correctedAlgorithm) ||
        correction.closureInputs !== 'original-comparison-source-roots' ||
        correction.pairedOutcomeRootsUsedAsClosureInputs ||
        !correction.pairedOutcomeRetainedForFallbackDiagnostic ||
        !correction.replayedReductionsCountAgainstOriginalBudget ||
        !correction.repeatedReductionWorkMayAppearInTrace ||
        correction.newCoreNodeCount !== 0 ||
        correction.newReductionRuleCount !== 0 ||
        correction.checkerBranchDelta !== 0 ||
        correction.comparisonClosureBranchDelta !== 1 ||
        !budget.oneGlobalBudgetAcrossPairedAndClosurePhases ||
        !budget.noBudgetResetBetweenSides ||
        !budget.pairedPhaseConsumptionRetained ||
        !budget.sourceReplayReceivesOnlyRemainingBudget ||
        !budget.noMemoizationOrTraceDeduplication ||
        !budget.directStructuralPlicityMismatchRemainsNotEqual ||
        proposal.requiredEvidence.focusedGenericRegression.length !== 9 ||
        !proposal.requiredEvidence.reviewedPathIndV5ConsumerMustCompile
    ) {
        throw new CoreLfComparisonNormalFormClosureProposalV2Error(
            'COMPARISON_NORMAL_FORM_CLOSURE_V2_SCOPE_DRIFT',
            'The exact same-budget source-root replay scope drifted'
        );
    }

    if (
        proposal.decision.gate !==
            'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-02' ||
        proposal.decision.decisionId !==
            'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-002' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.nextDependencyState !==
            'comparison-normal-form-closure-v2-awaiting-separate-review'
    ) {
        throw new CoreLfComparisonNormalFormClosureProposalV2Error(
            'COMPARISON_NORMAL_FORM_CLOSURE_V2_AUTHORIZATION_DRIFT',
            'Corrected comparison proposal v2 became self-authorizing'
        );
    }
    return proposal;
}
