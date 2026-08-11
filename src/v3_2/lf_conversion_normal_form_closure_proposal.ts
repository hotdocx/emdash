/**
 * Non-authorizing proposal for terminal normal-form closure in the generic
 * Core LF definitional comparison engine.
 *
 * The proposal adds no reduction equation. It repairs a completeness gap in
 * paired traversal: both sides can independently reach the same exact normal
 * form while the paired comparison still reports `not-equal`.
 */

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

export const CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_REVISION =
    'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-PROPOSAL-1' as const;

const rawProposal = {
    revision:
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_REVISION,
    status: 'proposal-awaiting-separate-review',
    row: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
    decision: {
        gate: 'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-01',
        decisionId: 'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-001',
        question:
            'Approve terminal same-budget normal-form closure only after ' +
            'the existing paired Core LF comparison returns not-equal?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    measuredCounterevidence: {
        consumerRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        consumerRule:
            'pathind.internalized.path-ind-transfd-component',
        measuredDuring:
            'reviewed-v4-runtime-compilation-with-in-memory-observers',
        earlierLocalRulesSubjectChecked: 6,
        candidatePiPullbackProjectionSubjectChecked: true,
        candidatePiPullbackProjectionProofRuleRequired: false,
        pairedComparisonStatus: 'not-equal',
        pairedComparisonSteps: 125,
        independentlyNormalizedLeftStatus: 'normal',
        independentlyNormalizedLeftSteps: 58,
        independentlyNormalizedRightStatus: 'normal',
        independentlyNormalizedRightSteps: 68,
        independentlyNormalizedFormsExactlyEqual: true,
        exactSharedNormalFormHead:
            'τ(Obj(Transf_cat(Functor_cat(PathOut,Cat),Cat,...)))',
        remainingDifferenceAfterIndependentNormalization: false,
        missingMathematicalTheorem: false,
        missingRuntimeEquationAfterCandidate: false,
        temporaryObserversRetained: false,
        genericSourceDiffEmpty: true
    },
    exactCorrection: {
        owner: 'coreLfDefinitionalCompare',
        file: 'src/v3_2/lf_conversion.ts',
        trigger: 'existing-paired-outcome-is-not-equal',
        algorithm: [
            'continue-normalizing-outcome-normalizedLeft',
            'continue-normalizing-outcome-normalizedRight',
            'share-the-original-single-global-operation-budget',
            'append-reductions-to-the-original-comparison-trace',
            'retry-structural-comparison-on-the-resulting-normal-forms',
            'return-equal-only-for-exact-kernel-expression-equality'
        ],
        deterministicSideOrder: ['left', 'right'],
        directEqualFastPathUnchanged: true,
        existingPairedTraversalRetained: true,
        standaloneNormalizerSemanticsUnchanged: true,
        weakHeadSemanticsUnchanged: true,
        runtimeRuleSetUnchanged: true,
        proofRuleSetUnchanged: true,
        unificationNotInvoked: true,
        newCoreNodeCount: 0,
        newReductionRuleCount: 0,
        checkerBranchDelta: 0,
        comparisonClosureBranchDelta: 1
    },
    budgetAndFailureContract: {
        oneGlobalBudgetAcrossPairedAndClosurePhases: true,
        noBudgetResetBetweenSides: true,
        exhaustedClosureReturnsStepLimitExceeded: true,
        stuckPlicityDoesNotBecomeEqual: true,
        distinctNormalFormsRemainNotEqual: true,
        finalNegativeReportsCoherentNormalizedFormsAndMismatch: true,
        traceRetainsSideAndPath: true
    },
    requiredEvidence: {
        focusedGenericRegression: [
            'nested-paired-miss-normalizes-to-one-exact-form',
            'same-case-with-operands-reversed',
            'distinct-normal-forms-remain-not-equal',
            'closure-budget-exhaustion-is-reported',
            'trace-is-deterministic-and-budget-accounted'
        ],
        affectedExistingConversionTestsRemainGreen: true,
        reviewedPathIndV5ConsumerMustCompile: true,
        rootTypecheckAndLintRequired: true,
        fullTypeScriptGateRequiredBeforeSemanticCheckpoint: true,
        repositoryWideCheckAllRequired: false,
        LambdapiSourceChangeRequired: false
    },
    implementationStages: [
        {
            order: 0,
            id: 'freeze-and-review-generic-closure',
            mutation: false
        },
        {
            order: 1,
            id: 'add-focused-synthetic-regression',
            mutation: true
        },
        {
            order: 2,
            id: 'implement-same-budget-terminal-closure',
            mutation: true
        },
        {
            order: 3,
            id: 'replay-reviewed-pathind-v5-consumer',
            mutation: true
        }
    ],
    doesNotAuthorize: [
        'implementation-before-separate-review',
        'a-new-runtime-rewrite-or-proof-rule',
        'a-new-Core-owner-checker-node-or-evaluator-node',
        'unbounded-normalization-or-a-budget-reset',
        'proof-search-unification-or-external-oracle-fallback',
        'changing-standalone-normalizer-or-weak-head-results',
        'accepting-distinct-normal-forms',
        'a-PathInd-specific-outer-commuting-rewrite',
        'text-browser-or-public-package-surface-change',
        'active-Lambdapi-source-change',
        'push-merge-publication-release-deployment-or-cleanup'
    ],
    nextDependencyState:
        'comparison-normal-form-closure-awaiting-separate-review'
} as const;

export type CoreLfComparisonNormalFormClosureProposal =
    typeof rawProposal;

export type CoreLfComparisonNormalFormClosureProposalErrorCode =
    | 'COMPARISON_NORMAL_FORM_CLOSURE_DECISION_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_EVIDENCE_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_SCOPE_DRIFT';

export class CoreLfComparisonNormalFormClosureProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfComparisonNormalFormClosureProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfComparisonNormalFormClosureProposalError';
    }
}

export const CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreLfComparisonNormalFormClosureProposal(
    proposal: CoreLfComparisonNormalFormClosureProposal =
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
): CoreLfComparisonNormalFormClosureProposal {
    if (
        proposal.revision !==
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_REVISION ||
        proposal.status !== 'proposal-awaiting-separate-review' ||
        proposal.decision.gate !==
            'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-01' ||
        proposal.decision.decisionId !==
            'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-001' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired
    ) {
        throw new CoreLfComparisonNormalFormClosureProposalError(
            'COMPARISON_NORMAL_FORM_CLOSURE_DECISION_DRIFT',
            'Comparison normal-form closure decision boundary drifted'
        );
    }

    const evidence = proposal.measuredCounterevidence;
    if (
        evidence.pairedComparisonStatus !== 'not-equal' ||
        evidence.pairedComparisonSteps !== 125 ||
        evidence.independentlyNormalizedLeftStatus !== 'normal' ||
        evidence.independentlyNormalizedLeftSteps !== 58 ||
        evidence.independentlyNormalizedRightStatus !== 'normal' ||
        evidence.independentlyNormalizedRightSteps !== 68 ||
        !evidence.independentlyNormalizedFormsExactlyEqual ||
        evidence.remainingDifferenceAfterIndependentNormalization ||
        evidence.missingMathematicalTheorem ||
        evidence.missingRuntimeEquationAfterCandidate ||
        evidence.temporaryObserversRetained ||
        !evidence.genericSourceDiffEmpty
    ) {
        throw new CoreLfComparisonNormalFormClosureProposalError(
            'COMPARISON_NORMAL_FORM_CLOSURE_EVIDENCE_DRIFT',
            'Measured paired-comparison counterevidence drifted'
        );
    }

    const correction = proposal.exactCorrection;
    const budget = proposal.budgetAndFailureContract;
    if (
        correction.owner !== 'coreLfDefinitionalCompare' ||
        correction.trigger !== 'existing-paired-outcome-is-not-equal' ||
        !correction.directEqualFastPathUnchanged ||
        !correction.existingPairedTraversalRetained ||
        !correction.standaloneNormalizerSemanticsUnchanged ||
        !correction.weakHeadSemanticsUnchanged ||
        !correction.runtimeRuleSetUnchanged ||
        !correction.proofRuleSetUnchanged ||
        correction.newCoreNodeCount !== 0 ||
        correction.newReductionRuleCount !== 0 ||
        correction.checkerBranchDelta !== 0 ||
        correction.comparisonClosureBranchDelta !== 1 ||
        !budget.oneGlobalBudgetAcrossPairedAndClosurePhases ||
        !budget.noBudgetResetBetweenSides ||
        !budget.exhaustedClosureReturnsStepLimitExceeded ||
        !budget.distinctNormalFormsRemainNotEqual ||
        !budget.finalNegativeReportsCoherentNormalizedFormsAndMismatch ||
        !budget.traceRetainsSideAndPath
    ) {
        throw new CoreLfComparisonNormalFormClosureProposalError(
            'COMPARISON_NORMAL_FORM_CLOSURE_SCOPE_DRIFT',
            'Comparison normal-form closure scope drifted'
        );
    }

    if (!sameData(proposal, cloneData(proposal))) {
        throw new CoreLfComparisonNormalFormClosureProposalError(
            'COMPARISON_NORMAL_FORM_CLOSURE_SCOPE_DRIFT',
            'Comparison normal-form closure proposal is not data-stable'
        );
    }
    return proposal;
}
