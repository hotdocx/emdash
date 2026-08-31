/** Concise direct-TypeScript workflow over the separated delegation owners. */

import {
    AlgebraAlgorithmIdentity,
    AlgebraComputationLimits,
    AlgebraEngine
} from './algebra_engine';
import {
    AlgebraFormalCheckedAdoption,
    AlgebraFormalTrustedAdoption,
    AlgebraFormalTrustedAdoptionDecision,
    adoptAlgebraFormalCheckedPlan,
    adoptAlgebraFormalTrustedComputation,
    assertAlgebraFormalComputationResultCurrent
} from './algebra_formal_adoption';
import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationGoal,
    AlgebraFormalComputationRequest,
    AlgebraFormalDelegationError,
    createAlgebraFormalComputationRequest,
    defineAlgebraFormalComputationGoal,
    serializeAlgebraFormalComputationRequest
} from './algebra_formal_delegation';
import {
    AlgebraFormalComputationExecutionOptions,
    AlgebraFormalComputationResult,
    executeAlgebraFormalComputationRequest,
    serializeAlgebraFormalComputationResult
} from './algebra_formal_delegation_execution';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreProofDocumentInput
} from './proof_document';
import {
    CoreProofPlan
} from './proof_plan';

export const ALGEBRA_FORMAL_WORKFLOW_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-workflow-v1' as const,
    runRevision: 'emdash-algebra-formal-workflow-run-v1' as const,
    receiptRevision: 'emdash-algebra-formal-workflow-receipt-v1' as const,
    surface: 'direct-typescript' as const,
    runAndTrustSeparated: true as const,
    reusePolicy: 'exact-current-in-memory-result-only' as const,
    parsesStrings: false as const,
    addsCoreOwner: false as const,
    addsProofPlanTag: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export interface AlgebraFormalWorkflowInput<R, I, O> {
    readonly document: CoreProofDocumentInput;
    readonly goalId: string;
    readonly adapter: AlgebraFormalComputationAdapter<R, I, O>;
    readonly realization: unknown;
    readonly engine: AlgebraEngine;
    readonly algorithm?: AlgebraAlgorithmIdentity;
    readonly limits?: AlgebraComputationLimits;
    readonly execution?: AlgebraFormalComputationExecutionOptions;
}

export interface AlgebraFormalWorkflowRun<R, I, O> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_WORKFLOW_PROFILE.runRevision;
    readonly goal: AlgebraFormalComputationGoal;
    readonly request: AlgebraFormalComputationRequest<R, I, O>;
    readonly result: AlgebraFormalComputationResult<R, I, O>;
}

/** Run and observe only; adoption is intentionally a separate API call. */
export async function runAlgebraFormalWorkflow<R, I, O>(
    input: AlgebraFormalWorkflowInput<R, I, O>
): Promise<AlgebraFormalWorkflowRun<R, I, O>> {
    const goal = defineAlgebraFormalComputationGoal({
        document: input.document,
        goalId: input.goalId
    });
    const request = createAlgebraFormalComputationRequest({
        adapter: input.adapter,
        goal,
        realization: input.realization,
        engine: input.engine,
        ...(input.algorithm === undefined
            ? {}
            : { algorithm: input.algorithm }),
        ...(input.limits === undefined ? {} : { limits: input.limits })
    });
    const result = await executeAlgebraFormalComputationRequest(
        request,
        input.execution
    );
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_WORKFLOW_PROFILE.runRevision,
        goal,
        request,
        result
    });
}

export const trustAlgebraFormalWorkflow = <R, I, O>(input: {
    readonly run: AlgebraFormalWorkflowRun<R, I, O>;
    readonly assumptionName: string;
    readonly decision: AlgebraFormalTrustedAdoptionDecision;
}): AlgebraFormalTrustedAdoption<R, I, O> =>
    adoptAlgebraFormalTrustedComputation({
        result: input.run.result,
        assumptionName: input.assumptionName,
        decision: input.decision
    });

export const checkAlgebraFormalWorkflow = <R, I, O>(input: {
    readonly run: AlgebraFormalWorkflowRun<R, I, O>;
    readonly replacement: CoreProofPlan;
}): AlgebraFormalCheckedAdoption<R, I, O> => adoptAlgebraFormalCheckedPlan({
    result: input.run.result,
    replacement: input.replacement
});

export interface AlgebraFormalWorkflowReceipt {
    readonly revision:
        typeof ALGEBRA_FORMAL_WORKFLOW_PROFILE.receiptRevision;
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goalId: string;
    readonly outcome: 'claim' | 'observation';
    readonly requestData: string;
    readonly resultData: string;
}

export function createAlgebraFormalWorkflowReceipt<R, I, O>(
    run: AlgebraFormalWorkflowRun<R, I, O>
): AlgebraFormalWorkflowReceipt {
    assertAlgebraFormalComputationResultCurrent(run.result, run.request);
    return Object.freeze({
        revision: ALGEBRA_FORMAL_WORKFLOW_PROFILE.receiptRevision,
        moduleId: run.goal.moduleId,
        declarationId: run.goal.declarationId,
        goalId: run.goal.goalId,
        outcome: run.result.interpretation.kind,
        requestData: serializeAlgebraFormalComputationRequest(run.request),
        resultData: serializeAlgebraFormalComputationResult(run.result)
    });
}

export const serializeAlgebraFormalWorkflowReceipt = (
    receipt: AlgebraFormalWorkflowReceipt
): string => serializeCoreLfWorkspaceCanonicalJson(
    receipt,
    'algebraFormalWorkflowReceipt'
);

/**
 * Reuse an in-memory whole result only after exact current-request and result
 * validation. Serialized receipts alone are evidence, not executable values.
 */
export function reuseAlgebraFormalWorkflowResult<R, I, O>(input: {
    readonly stored: AlgebraFormalComputationResult<R, I, O>;
    readonly currentRequest: AlgebraFormalComputationRequest<R, I, O>;
}): AlgebraFormalComputationResult<R, I, O> {
    assertAlgebraFormalComputationResultCurrent(
        input.stored,
        input.currentRequest
    );
    if (
        serializeAlgebraFormalComputationRequest(input.currentRequest) !==
            input.stored.requestData
    ) {
        throw new AlgebraFormalDelegationError(
            'STALE_RESULT',
            'workflow.currentRequest',
            'Stored computation does not match the current request'
        );
    }
    return input.stored;
}
