/**
 * Non-authorizing proposal for exact declaration-checker budget propagation.
 *
 * compileCoreLfDeclarations already accepts, validates, records, and later
 * exposes comparisonStepLimit. Its compilation-time checker factory silently
 * discards that value and therefore uses the frozen 256-step default. This
 * proposal wires the existing option to that internal checker without
 * changing the public factory signature or any global default.
 */

export const CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL_REVISION =
    'CORE-LF-TRANSFER-DECLARATION-BUDGET-PROPOSAL-1' as const;

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const EXACT_CORRECTION = Object.freeze([
    'resolve-and-validate-options-comparisonStepLimit-before-checker-factory',
    'pass-the-exact-resolved-limit-to-a-private-internal-factory',
    'retain-the-limit-in-CoreLfTransferDeclarationChecker',
    'return-that-limit-from-constraintComparisonStepLimit',
    'preserve-the-exported-factory-one-argument-signature-and-default',
    'preserve-the-compiled-module-recorded-limit-and-createChecker-behavior'
]);

const rawProposal = {
    revision: CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL_REVISION,
    status: 'proposal-awaiting-separate-review',
    row: 'CORE-LF-TRANSFER-DECLARATION-BUDGET-1',
    authority: {
        implementationOwner: 'src/v3_2/lf_transfer_compiler.ts',
        publicOption: 'CoreLfDeclarationCompilerOptions.comparisonStepLimit',
        defaultOwner: 'CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT',
        defaultValue: 256,
        publicFactory:
            'createCoreLfTransferDeclarationCheckerFactory(runtimeProgram?)',
        internalChecker: 'CoreLfTransferDeclarationChecker',
        hook: 'CoreChecker.constraintComparisonStepLimit'
    },
    parentCounterevidence: {
        measuredDuring:
            'reviewed-pathind-internalized-v6-cold-semantic-replay',
        pathIndProposalCheckpoint: '19eb941',
        pathIndReviewCheckpoint: '2112543',
        comparisonProposalCheckpoint: 'a42ffc9',
        comparisonReviewCheckpoint: '5277885',
        requestedComparisonStepLimit: 512,
        reportedComparisonStepLimit: 256,
        firstTransparentDefinitionCompiled:
            'pathout_motive_transport_obj',
        failingTransparentDefinition:
            'pathout_motive_transport_arrow',
        failureCode: 'CONVERSION_STEP_LIMIT',
        failurePath:
            '$/decode/Obj/Hom/target/call/argument:1/lambda/body/' +
            'decode/Obj/functor-object/functor',
        nextReduction: 'transfer-declaration-beta-step-implicit',
        pathIndV6PresentationFusionReachedAndUsed: true,
        declarationCompilerOptionValidated: true,
        declarationCompilerOptionRecordedOnResult: true,
        compilationFactoryCreatedBeforeOptionResolution: true,
        compilationFactoryReceivesResolvedLimit: false,
        internalCheckerOverridesConstraintLimitHook: false,
        mathematicalMismatchObserved: false,
        newRuntimeOrProofEquationRequired: false,
        temporaryObserverRetained: false
    },
    decision: {
        gate: 'H-TS-EMDASH-LF-DECLARATION-BUDGET-01',
        decisionId: 'D-TS-EMDASH-LF-DECLARATION-BUDGET-001',
        question:
            'Approve exact propagation of the existing declaration compiler ' +
            'comparisonStepLimit into compilation-time checking?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactCorrection: {
        owner: 'compileCoreLfDeclarations',
        algorithm: EXACT_CORRECTION,
        publicOptionNameUnchanged: true,
        publicFactorySignatureUnchanged: true,
        exportedDefaultUnchanged: true,
        perCompilationLimitAlreadyRequestedByCallers: true,
        boundedOnly: true,
        genericCheckerBranchDelta: 0,
        trustedCoreNodeDelta: 0,
        reductionEquationDelta: 0
    },
    requiredEvidence: {
        focusedRegression: [
            'one-delta-transparent-body-fails-with-explicit-zero-limit',
            'same-one-delta-transparent-body-passes-with-limit-one',
            'result-records-the-exact-selected-limit',
            'omitted-option-retains-the-256-step-default',
            'invalid-option-remains-rejected'
        ],
        existingCompilerFocusedSuiteRequired: true,
        rootTypecheckRequired: true,
        focusedLintRequired: true,
        reviewedPathIndV6ConsumerReplayRequired: true,
        requiredFullTypeScriptGateBeforeSemanticCheckpoint: true,
        repositoryWideAggregateRequired: false
    },
    doesNotAuthorize: [
        'implementation-before-separate-review',
        'changing-the-global-256-step-default',
        'an-unbounded-or-adaptive-comparison-budget',
        'a-PathInd-specific-budget-override',
        'proof-program-integration-into-declaration-checking',
        'a-new-runtime-or-proof-equation',
        'a-new-Core-node-checker-branch-or-evaluator-branch',
        'changing-the-exported-factory-signature',
        'changing-any-active-Lambdapi-source',
        'a-public-version-release-push-merge-or-deployment'
    ],
    validation: {
        focusedProposalGateRequired: true,
        rootTypecheckRequired: true,
        focusedLintRequired: true,
        reasonLongAggregateOmitted:
            'proposal-is-immutable-boundary-data-with-no-runtime-behavior'
    },
    gitBoundary: {
        localProposalCheckpointAuthorized: true,
        localSemanticCheckpointRequiresGreenFullTypeScriptGate: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nextDependencyState:
        'lf-transfer-declaration-budget-awaiting-separate-review'
} as const;

export type CoreLfTransferDeclarationBudgetProposal = typeof rawProposal;

export type CoreLfTransferDeclarationBudgetProposalErrorCode =
    | 'LF_TRANSFER_DECLARATION_BUDGET_AUTHORITY_DRIFT'
    | 'LF_TRANSFER_DECLARATION_BUDGET_SCOPE_DRIFT'
    | 'LF_TRANSFER_DECLARATION_BUDGET_AUTHORIZATION_DRIFT';

export class CoreLfTransferDeclarationBudgetProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfTransferDeclarationBudgetProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfTransferDeclarationBudgetProposalError';
    }
}

export const CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreLfTransferDeclarationBudgetProposal(
    proposal: CoreLfTransferDeclarationBudgetProposal =
        CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL
): CoreLfTransferDeclarationBudgetProposal {
    const evidence = proposal.parentCounterevidence;
    if (
        proposal.revision !==
            'CORE-LF-TRANSFER-DECLARATION-BUDGET-PROPOSAL-1' ||
        proposal.row !== 'CORE-LF-TRANSFER-DECLARATION-BUDGET-1' ||
        proposal.authority.defaultValue !== 256 ||
        evidence.pathIndProposalCheckpoint !== '19eb941' ||
        evidence.pathIndReviewCheckpoint !== '2112543' ||
        evidence.comparisonProposalCheckpoint !== 'a42ffc9' ||
        evidence.comparisonReviewCheckpoint !== '5277885' ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.reportedComparisonStepLimit !== 256 ||
        evidence.firstTransparentDefinitionCompiled !==
            'pathout_motive_transport_obj' ||
        evidence.failingTransparentDefinition !==
            'pathout_motive_transport_arrow' ||
        evidence.failureCode !== 'CONVERSION_STEP_LIMIT' ||
        !evidence.pathIndV6PresentationFusionReachedAndUsed ||
        !evidence.declarationCompilerOptionValidated ||
        !evidence.declarationCompilerOptionRecordedOnResult ||
        !evidence.compilationFactoryCreatedBeforeOptionResolution ||
        evidence.compilationFactoryReceivesResolvedLimit ||
        evidence.internalCheckerOverridesConstraintLimitHook ||
        evidence.mathematicalMismatchObserved ||
        evidence.newRuntimeOrProofEquationRequired ||
        evidence.temporaryObserverRetained
    ) {
        throw new CoreLfTransferDeclarationBudgetProposalError(
            'LF_TRANSFER_DECLARATION_BUDGET_AUTHORITY_DRIFT',
            'The measured ignored-budget counterevidence drifted'
        );
    }

    const correction = proposal.exactCorrection;
    if (
        correction.owner !== 'compileCoreLfDeclarations' ||
        JSON.stringify(correction.algorithm) !==
            JSON.stringify(EXACT_CORRECTION) ||
        !correction.publicOptionNameUnchanged ||
        !correction.publicFactorySignatureUnchanged ||
        !correction.exportedDefaultUnchanged ||
        !correction.perCompilationLimitAlreadyRequestedByCallers ||
        !correction.boundedOnly ||
        correction.genericCheckerBranchDelta !== 0 ||
        correction.trustedCoreNodeDelta !== 0 ||
        correction.reductionEquationDelta !== 0 ||
        proposal.requiredEvidence.focusedRegression.length !== 5 ||
        !proposal.requiredEvidence.requiredFullTypeScriptGateBeforeSemanticCheckpoint ||
        proposal.requiredEvidence.repositoryWideAggregateRequired
    ) {
        throw new CoreLfTransferDeclarationBudgetProposalError(
            'LF_TRANSFER_DECLARATION_BUDGET_SCOPE_DRIFT',
            'The exact default-preserving budget wiring drifted'
        );
    }

    if (
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'lf-transfer-declaration-budget-awaiting-separate-review'
    ) {
        throw new CoreLfTransferDeclarationBudgetProposalError(
            'LF_TRANSFER_DECLARATION_BUDGET_AUTHORIZATION_DRIFT',
            'The budget proposal became self-authorizing or widened'
        );
    }
    return proposal;
}
