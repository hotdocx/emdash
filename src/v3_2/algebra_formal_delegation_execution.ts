/** Exact execution and observation for inert goal-bound algebra requests. */

import {
    AlgebraComputed,
    AlgebraProgressEvent,
    computeAlgebraOperation
} from './algebra_engine';
import {
    ALGEBRA_FORMAL_DELEGATION_PROFILE,
    AlgebraFormalComputationInterpretation,
    AlgebraFormalComputationRequest,
    AlgebraFormalDelegationError,
    normalizeAlgebraFormalComputationInterpretation,
    serializeAlgebraFormalComputationInterpretation,
    serializeAlgebraFormalComputationOutput,
    serializeAlgebraFormalComputationRequest
} from './algebra_formal_delegation';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-delegation-execution-v1' as const,
    resultRevision: 'emdash-algebra-formal-result-v1' as const,
    acceptedQuality: 'exact' as const,
    hooks: 'runtime-only-cancellation-and-progress' as const,
    mutatesProofPlan: false as const,
    mutatesWorkspace: false as const,
    addsCoreOwner: false as const,
    addsProofPlanTag: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

const fail = (
    code: AlgebraFormalDelegationError['code'],
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraFormalDelegationError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export interface AlgebraFormalComputationExecutionOptions {
    readonly cancellation?: {
        readonly requested: () => boolean;
        readonly reason?: () => string | undefined;
    };
    readonly onProgress?: (event: AlgebraProgressEvent) => void;
}

export interface AlgebraFormalComputationResult<R, I, O> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.resultRevision;
    readonly request: AlgebraFormalComputationRequest<R, I, O>;
    readonly requestData: string;
    readonly computed: AlgebraComputed<O>;
    readonly outputData: string;
    readonly interpretation: AlgebraFormalComputationInterpretation;
    readonly interpretationData: string;
}

/**
 * Execute one already validated request and interpret its exact whole result.
 * No proof source or declaration environment changes in this operation.
 */
export async function executeAlgebraFormalComputationRequest<R, I, O>(
    request: AlgebraFormalComputationRequest<R, I, O>,
    options: AlgebraFormalComputationExecutionOptions = {}
): Promise<AlgebraFormalComputationResult<R, I, O>> {
    if (
        request.profileRevision !==
            ALGEBRA_FORMAL_DELEGATION_PROFILE.requestRevision
    ) {
        return fail(
            'STALE_REQUEST',
            'request.profileRevision',
            'Cannot execute a foreign formal-computation request revision'
        );
    }
    const requestData = serializeAlgebraFormalComputationRequest(request);
    let computed: AlgebraComputed<O>;
    try {
        computed = await computeAlgebraOperation({
            engine: request.engine,
            operation: request.operation,
            input: request.operationInput,
            ...(request.algorithm === undefined
                ? {}
                : { algorithm: request.algorithm }),
            context: {
                limits: request.limits,
                ...(options.cancellation === undefined
                    ? {}
                    : { cancellation: options.cancellation }),
                ...(options.onProgress === undefined
                    ? {}
                    : { onProgress: options.onProgress })
            }
        });
    } catch (error: unknown) {
        return fail(
            'EXECUTION_FAILED',
            'result.computed',
            'Algebra engine failed to execute the formal computation request',
            error
        );
    }
    if (computed.quality !== 'exact') {
        return fail(
            'UNSUPPORTED_RESULT_QUALITY',
            'result.computed.quality',
            `Formal computation v1 accepts exact results, received ` +
                `'${computed.quality}'`
        );
    }
    const outputData = serializeAlgebraFormalComputationOutput(
        request.adapter,
        computed.value
    );

    let first: AlgebraFormalComputationInterpretation;
    let second: AlgebraFormalComputationInterpretation;
    try {
        first = normalizeAlgebraFormalComputationInterpretation(
            request.goal,
            request.adapter.interpret({
                goal: request.goal,
                realization: request.realization,
                operationInput: request.operationInput,
                computed
            })
        );
        second = normalizeAlgebraFormalComputationInterpretation(
            request.goal,
            request.adapter.interpret({
                goal: request.goal,
                realization: request.realization,
                operationInput: request.operationInput,
                computed
            })
        );
    } catch (error: unknown) {
        if (error instanceof AlgebraFormalDelegationError) throw error;
        return fail(
            'INVALID_INTERPRETATION',
            'result.interpretation',
            'Adapter failed to interpret its computed output',
            error
        );
    }
    const firstInterpretationData =
        serializeAlgebraFormalComputationInterpretation(first);
    const secondInterpretationData =
        serializeAlgebraFormalComputationInterpretation(second);
    if (firstInterpretationData !== secondInterpretationData) {
        return fail(
            'NONDETERMINISTIC_INTERPRETATION',
            'result.interpretation',
            'Adapter returned different formal interpretations for one output'
        );
    }
    if (serializeAlgebraFormalComputationRequest(request) !== requestData) {
        return fail(
            'STALE_REQUEST',
            'result.request',
            'Formal computation request changed during execution'
        );
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.resultRevision,
        request,
        requestData,
        computed,
        outputData,
        interpretation: first,
        interpretationData: firstInterpretationData
    });
}

const identitySnapshot = (
    value: { readonly kind: string; readonly id: string; readonly revision: string }
) => ({ kind: value.kind, id: value.id, revision: value.revision });

export const serializeAlgebraFormalComputationResult = <R, I, O>(
    result: AlgebraFormalComputationResult<R, I, O>
): string => serializeCoreLfWorkspaceCanonicalJson({
    serializationRevision:
        ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.resultRevision,
    requestData: result.requestData,
    computation: {
        operation: identitySnapshot(result.computed.operation),
        engine: identitySnapshot(result.computed.engine),
        algorithm: identitySnapshot(result.computed.algorithm),
        quality: result.computed.quality,
        assumptions: result.computed.assumptions,
        diagnostics: result.computed.diagnostics,
        reusable: result.computed.reusable.map(artifact => ({
            id: artifact.id,
            kind: artifact.kind,
            portable: artifact.portable,
            schema: identitySnapshot(artifact.schema.identity)
        }))
    },
    outputData: result.outputData,
    interpretationData: result.interpretationData
}, 'algebraFormalComputationResult');
