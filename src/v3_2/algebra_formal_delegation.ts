/**
 * Goal-bound, backend-neutral delegation contracts for algebra computation.
 *
 * This module owns inert request and interpretation data only. Computation,
 * declaration adoption, and proof-plan replacement are separate layers.
 */

import {
    ALGEBRA_ENGINE_PROFILE,
    AlgebraAlgorithmIdentity,
    AlgebraComputationLimits,
    AlgebraComputed,
    AlgebraEngine,
    AlgebraOperation,
    normalizeAlgebraComputationContext
} from './algebra_engine';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    CoreProofArtifact,
    CoreProofDocumentInput,
    compileCoreProofDocument
} from './proof_document';
import {
    KernelExpression,
    kernelAssertScoped,
    kernelExpressionEquals
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-delegation-v1' as const,
    adapterRevision: 'emdash-algebra-formal-adapter-v1' as const,
    goalRevision: 'emdash-algebra-formal-goal-v1' as const,
    requestRevision: 'emdash-algebra-formal-request-v1' as const,
    interpretationRevision:
        'emdash-algebra-formal-interpretation-v1' as const,
    goalBoundary: 'closed-depth-zero-root-hole' as const,
    payloadPolicy: 'adapter-owned-canonical-bytes' as const,
    executionLayer: 'separate-authoring-workspace-action' as const,
    addsCoreOwner: false as const,
    addsProofPlanTag: false as const,
    performsComputation: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export interface AlgebraFormalComputationAdapterIdentity {
    readonly kind: 'algebra-formal-computation-adapter';
    readonly id: string;
    readonly revision: string;
}

export type AlgebraFormalDelegationErrorCode =
    | 'INVALID_ID'
    | 'INVALID_GOAL'
    | 'UNSUPPORTED_GOAL'
    | 'INVALID_ADAPTER'
    | 'INVALID_REALIZATION'
    | 'NONDETERMINISTIC_REALIZATION'
    | 'NONDETERMINISTIC_ACQUISITION'
    | 'NONDETERMINISTIC_ENCODING'
    | 'INVALID_ENCODING'
    | 'INVALID_ENGINE'
    | 'INVALID_ALGORITHM'
    | 'INVALID_INTERPRETATION'
    | 'CLAIM_TARGET_MISMATCH'
    | 'INVALID_CORE_DATA'
    | 'EXECUTION_FAILED'
    | 'UNSUPPORTED_RESULT_QUALITY'
    | 'STALE_REQUEST'
    | 'NONDETERMINISTIC_INTERPRETATION'
    | 'STALE_RESULT'
    | 'NO_ADOPTABLE_CLAIM'
    | 'UNACKNOWLEDGED_ASSUMPTIONS'
    | 'INVALID_APPROVAL'
    | 'ADOPTION_FAILED'
    | 'CHECKED_PLAN_FAILED';

export class AlgebraFormalDelegationError extends Error {
    constructor(
        public readonly code: AlgebraFormalDelegationErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalDelegationError';
    }
}

const fail = (
    code: AlgebraFormalDelegationErrorCode,
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

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const MAX_ENCODING_LENGTH = 16 * 1024 * 1024;

const stableId = (value: unknown, path: string, label: string): string => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return value;
    return fail('INVALID_ID', path, `${label} must be a stable portable ID`);
};

const stableRevision = (value: unknown, path: string): string => {
    if (
        typeof value === 'string' &&
        value.length > 0 &&
        value.length <= 256 &&
        !/[\u0000-\u001f\u007f]/u.test(value)
    ) return value;
    return fail(
        'INVALID_ID',
        path,
        'Revision must be nonempty, bounded, and contain no controls'
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const assertMetaFree = (expression: KernelExpression, path: string): void => {
    const visit = (current: KernelExpression): void => {
        switch (current.tag) {
            case 'universe':
            case 'reference':
            case 'bound':
                return;
            case 'meta':
                return fail(
                    'INVALID_CORE_DATA',
                    path,
                    'Formal computation data must not contain metavariables'
                );
            case 'application':
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'call':
                visit(current.callee);
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type);
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };
    try {
        kernelAssertScoped(expression);
        visit(expression);
    } catch (error: unknown) {
        if (error instanceof AlgebraFormalDelegationError) throw error;
        fail(
            'INVALID_CORE_DATA',
            path,
            'Formal computation data must be closed and well scoped',
            error
        );
    }
};

const canonicalCore = (
    expression: KernelExpression,
    path: string
): string => {
    assertMetaFree(expression, path);
    return serializeCoreExpression(expression);
};

const encoding = (
    value: unknown,
    path: string,
    label: string
): string => {
    if (
        typeof value !== 'string' ||
        value.length === 0 ||
        value.length > MAX_ENCODING_LENGTH
    ) {
        return fail(
            'INVALID_ENCODING',
            path,
            `${label} must be nonempty canonical text within ` +
                `${MAX_ENCODING_LENGTH} bytes`
        );
    }
    return value;
};

const deterministicEncoding = (
    encode: () => string,
    path: string,
    label: string
): string => {
    let first: string;
    let second: string;
    try {
        first = encoding(encode(), path, label);
        second = encoding(encode(), path, label);
    } catch (error: unknown) {
        if (error instanceof AlgebraFormalDelegationError) throw error;
        return fail(
            'INVALID_ENCODING',
            path,
            `${label} failed to produce canonical text`,
            error
        );
    }
    if (first !== second) {
        return fail(
            'NONDETERMINISTIC_ENCODING',
            path,
            `${label} returned different canonical bytes`
        );
    }
    return first;
};

const operationIdentity = (
    value: unknown,
    path: string
): void => {
    if (
        !record(value) ||
        value.kind !== 'algebra-operation' ||
        typeof value.id !== 'string' ||
        typeof value.revision !== 'string'
    ) {
        return fail(
            'INVALID_ADAPTER',
            path,
            'Expected an algebra-operation identity'
        );
    }
    stableId(value.id, `${path}.id`, 'Operation ID');
    stableRevision(value.revision, `${path}.revision`);
};

const engineIdentity = (value: unknown, path: string): void => {
    if (
        !record(value) ||
        value.kind !== 'algebra-engine' ||
        typeof value.id !== 'string' ||
        typeof value.revision !== 'string'
    ) {
        return fail(
            'INVALID_ENGINE',
            path,
            'Expected an algebra-engine identity'
        );
    }
    stableId(value.id, `${path}.id`, 'Engine ID');
    stableRevision(value.revision, `${path}.revision`);
};

const algorithmIdentity = (
    value: unknown,
    path: string
): AlgebraAlgorithmIdentity => {
    if (
        !record(value) ||
        value.kind !== 'algebra-algorithm' ||
        typeof value.id !== 'string' ||
        typeof value.revision !== 'string'
    ) {
        return fail(
            'INVALID_ALGORITHM',
            path,
            'Expected an algebra-algorithm identity'
        );
    }
    stableId(value.id, `${path}.id`, 'Algorithm ID');
    stableRevision(value.revision, `${path}.revision`);
    return value as unknown as AlgebraAlgorithmIdentity;
};

export interface AlgebraFormalComputationGoalInput {
    readonly document: CoreProofDocumentInput;
    readonly goalId: string;
}

export interface AlgebraFormalComputationGoal {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_DELEGATION_PROFILE.goalRevision;
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goalId: string;
    readonly contextDepth: 0;
    readonly target: KernelExpression;
    readonly targetCore: string;
    readonly sourceArtifact: CoreProofArtifact;
    readonly document: CoreProofDocumentInput;
}

/**
 * Select one exact closed root hole from a freshly checked proof document.
 */
export function defineAlgebraFormalComputationGoal(
    input: AlgebraFormalComputationGoalInput
): AlgebraFormalComputationGoal {
    if (!record(input) || !record(input.document)) {
        return fail('INVALID_GOAL', 'goal', 'Expected a proof document input');
    }
    const goalId = stableId(input.goalId, 'goal.goalId', 'Goal ID');
    const plan = input.document.plan;
    if (
        plan.tag !== 'hole' ||
        plan.goalId !== goalId ||
        plan.expectation?.contextDepth !== 0 ||
        plan.expectation.target === undefined ||
        !kernelExpressionEquals(plan.expectation.target, input.document.type)
    ) {
        return fail(
            'UNSUPPORTED_GOAL',
            'goal.document.plan',
            'Formal computation currently requires one depth-zero root hole ' +
                'whose exact expected target is the document type'
        );
    }
    const targetCore = canonicalCore(input.document.type, 'goal.target');
    let compilation: ReturnType<typeof compileCoreProofDocument>;
    try {
        compilation = compileCoreProofDocument(input.document);
    } catch (error: unknown) {
        return fail(
            'INVALID_GOAL',
            'goal.document',
            'Formal computation goal document did not check',
            error
        );
    }
    const goals = compilation.artifact.state.goals;
    if (
        compilation.artifact.state.status !== 'incomplete' ||
        goals.length !== 1 ||
        goals[0].id !== goalId ||
        goals[0].contextDepth !== 0
    ) {
        return fail(
            'INVALID_GOAL',
            'goal.document.plan',
            'Fresh proof replay did not retain exactly the selected root goal'
        );
    }
    const document = Object.freeze({ ...input.document });
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_DELEGATION_PROFILE.goalRevision,
        moduleId: input.document.moduleId,
        declarationId: input.document.declarationId,
        goalId,
        contextDepth: 0,
        target: input.document.type,
        targetCore,
        sourceArtifact: compilation.artifact,
        document
    });
}

export interface AlgebraFormalComputationDatumInput {
    readonly id: string;
    readonly type: KernelExpression;
    readonly term: KernelExpression;
}

export interface AlgebraFormalComputationDatum {
    readonly id: string;
    readonly type: KernelExpression;
    readonly typeCore: string;
    readonly term: KernelExpression;
    readonly termCore: string;
}

interface AlgebraFormalComputationInterpretationBaseInput {
    readonly summary: string;
    readonly data?: readonly AlgebraFormalComputationDatumInput[];
}

export type AlgebraFormalComputationInterpretationInput =
    | AlgebraFormalComputationInterpretationBaseInput & {
        readonly kind: 'observation';
    }
    | AlgebraFormalComputationInterpretationBaseInput & {
        readonly kind: 'claim';
        readonly claimType: KernelExpression;
    };

export interface AlgebraFormalComputationObservation {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_DELEGATION_PROFILE.interpretationRevision;
    readonly kind: 'observation';
    readonly summary: string;
    readonly data: readonly AlgebraFormalComputationDatum[];
}

export interface AlgebraFormalComputationClaim {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_DELEGATION_PROFILE.interpretationRevision;
    readonly kind: 'claim';
    readonly summary: string;
    readonly claimType: KernelExpression;
    readonly claimTypeCore: string;
    readonly data: readonly AlgebraFormalComputationDatum[];
}

export type AlgebraFormalComputationInterpretation =
    | AlgebraFormalComputationObservation
    | AlgebraFormalComputationClaim;

const summary = (value: unknown): string => {
    if (
        typeof value === 'string' &&
        value.trim().length > 0 &&
        value.length <= 4096 &&
        !/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f]/u.test(value)
    ) return value;
    return fail(
        'INVALID_INTERPRETATION',
        'interpretation.summary',
        'Interpretation summary must be nonempty, bounded portable text'
    );
};

const normalizeData = (
    values: readonly AlgebraFormalComputationDatumInput[] | undefined
): readonly AlgebraFormalComputationDatum[] => {
    if (values === undefined) return Object.freeze([]);
    if (!Array.isArray(values)) {
        return fail(
            'INVALID_INTERPRETATION',
            'interpretation.data',
            'Interpretation data must be an array'
        );
    }
    const seen = new Set<string>();
    return Object.freeze(values.map((value, index) => {
        if (!record(value)) {
            return fail(
                'INVALID_INTERPRETATION',
                `interpretation.data[${index}]`,
                'Formal datum must be a record'
            );
        }
        const datum = value as unknown as AlgebraFormalComputationDatumInput;
        const id = stableId(
            datum.id,
            `interpretation.data[${index}].id`,
            'Formal datum ID'
        );
        if (seen.has(id)) {
            return fail(
                'INVALID_INTERPRETATION',
                `interpretation.data[${index}].id`,
                `Duplicate formal datum '${id}'`
            );
        }
        seen.add(id);
        const typeCore = canonicalCore(
            datum.type,
            `interpretation.data[${index}].type`
        );
        const termCore = canonicalCore(
            datum.term,
            `interpretation.data[${index}].term`
        );
        return Object.freeze({
            id,
            type: datum.type,
            typeCore,
            term: datum.term,
            termCore
        });
    }));
};

export function normalizeAlgebraFormalComputationInterpretation(
    goal: AlgebraFormalComputationGoal,
    input: AlgebraFormalComputationInterpretationInput
): AlgebraFormalComputationInterpretation {
    if (!record(input)) {
        return fail(
            'INVALID_INTERPRETATION',
            'interpretation',
            'Formal interpretation must be a record'
        );
    }
    const selectedSummary = summary(input.summary);
    const data = normalizeData(input.data);
    if (input.kind === 'observation') {
        return Object.freeze({
            profileRevision:
                ALGEBRA_FORMAL_DELEGATION_PROFILE.interpretationRevision,
            kind: 'observation',
            summary: selectedSummary,
            data
        });
    }
    if (input.kind !== 'claim' || !('claimType' in input)) {
        return fail(
            'INVALID_INTERPRETATION',
            'interpretation.kind',
            'Interpretation kind must be observation or claim'
        );
    }
    const claimTypeCore = canonicalCore(
        input.claimType,
        'interpretation.claimType'
    );
    if (!kernelExpressionEquals(input.claimType, goal.target)) {
        return fail(
            'CLAIM_TARGET_MISMATCH',
            'interpretation.claimType',
            'Adapter claim is not the exact selected formal goal target'
        );
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_DELEGATION_PROFILE.interpretationRevision,
        kind: 'claim',
        summary: selectedSummary,
        claimType: input.claimType,
        claimTypeCore,
        data
    });
}

export const serializeAlgebraFormalComputationInterpretation = (
    interpretation: AlgebraFormalComputationInterpretation
): string => serializeCoreLfWorkspaceCanonicalJson({
    serializationRevision:
        ALGEBRA_FORMAL_DELEGATION_PROFILE.interpretationRevision,
    kind: interpretation.kind,
    summary: interpretation.summary,
    claimTypeCore: interpretation.kind === 'claim'
        ? interpretation.claimTypeCore
        : null,
    data: interpretation.data.map(datum => ({
        id: datum.id,
        typeCore: datum.typeCore,
        termCore: datum.termCore
    }))
}, 'algebraFormalComputationInterpretation');

export interface AlgebraFormalComputationAdapterInput<R, I, O> {
    readonly id: string;
    readonly revision: string;
    readonly operation: AlgebraOperation<I, O>;
    readonly normalizeRealization: (value: unknown, path: string) => R;
    readonly serializeRealization: (realization: R) => string;
    readonly acquire: (
        goal: AlgebraFormalComputationGoal,
        realization: R
    ) => unknown;
    readonly serializeInput: (input: I) => string;
    readonly serializeOutput: (output: O) => string;
    readonly interpret: (input: {
        readonly goal: AlgebraFormalComputationGoal;
        readonly realization: R;
        readonly operationInput: I;
        readonly computed: AlgebraComputed<O>;
    }) => AlgebraFormalComputationInterpretationInput;
}

export interface AlgebraFormalComputationAdapter<R, I, O> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_DELEGATION_PROFILE.adapterRevision;
    readonly identity: AlgebraFormalComputationAdapterIdentity;
    readonly operation: AlgebraOperation<I, O>;
    normalizeRealization(value: unknown, path: string): R;
    serializeRealization(realization: R): string;
    acquire(
        goal: AlgebraFormalComputationGoal,
        realization: R
    ): unknown;
    serializeInput(input: I): string;
    serializeOutput(output: O): string;
    interpret(input: {
        readonly goal: AlgebraFormalComputationGoal;
        readonly realization: R;
        readonly operationInput: I;
        readonly computed: AlgebraComputed<O>;
    }): AlgebraFormalComputationInterpretationInput;
}

export function defineAlgebraFormalComputationAdapter<R, I, O>(
    input: AlgebraFormalComputationAdapterInput<R, I, O>
): AlgebraFormalComputationAdapter<R, I, O> {
    if (
        !record(input) ||
        !record(input.operation) ||
        typeof input.normalizeRealization !== 'function' ||
        typeof input.serializeRealization !== 'function' ||
        typeof input.acquire !== 'function' ||
        typeof input.serializeInput !== 'function' ||
        typeof input.serializeOutput !== 'function' ||
        typeof input.interpret !== 'function'
    ) {
        return fail(
            'INVALID_ADAPTER',
            'adapter',
            'Adapter requires one current operation and all explicit callbacks'
        );
    }
    operationIdentity(input.operation.identity, 'adapter.operation.identity');
    if (
        input.operation.profileRevision !==
            ALGEBRA_ENGINE_PROFILE.operationRevision ||
        !record(input.operation.input) ||
        input.operation.input.profileRevision !==
            ALGEBRA_ENGINE_PROFILE.schemaRevision ||
        !record(input.operation.output) ||
        input.operation.output.profileRevision !==
            ALGEBRA_ENGINE_PROFILE.schemaRevision
    ) {
        return fail(
            'INVALID_ADAPTER',
            'adapter.operation',
            'Adapter operation requires current runtime schemas'
        );
    }
    const identity: AlgebraFormalComputationAdapterIdentity = Object.freeze({
        kind: 'algebra-formal-computation-adapter',
        id: stableId(input.id, 'adapter.id', 'Adapter ID'),
        revision: stableRevision(input.revision, 'adapter.revision')
    });
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_DELEGATION_PROFILE.adapterRevision,
        identity,
        operation: input.operation,
        normalizeRealization: input.normalizeRealization,
        serializeRealization: input.serializeRealization,
        acquire: input.acquire,
        serializeInput: input.serializeInput,
        serializeOutput: input.serializeOutput,
        interpret: input.interpret
    });
}

/** Validate that one adapter produces stable canonical bytes for an output. */
export const serializeAlgebraFormalComputationOutput = <R, I, O>(
    adapter: AlgebraFormalComputationAdapter<R, I, O>,
    output: O
): string => deterministicEncoding(
    () => adapter.serializeOutput(output),
    'result.outputData',
    'Operation-output serializer'
);

export interface AlgebraFormalComputationRequestInput<R, I, O> {
    readonly adapter: AlgebraFormalComputationAdapter<R, I, O>;
    readonly goal: AlgebraFormalComputationGoal;
    readonly realization: unknown;
    readonly engine: AlgebraEngine;
    readonly algorithm?: AlgebraAlgorithmIdentity;
    readonly limits?: AlgebraComputationLimits;
}

export interface AlgebraFormalComputationRequest<R, I, O> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_DELEGATION_PROFILE.requestRevision;
    readonly adapter: AlgebraFormalComputationAdapter<R, I, O>;
    readonly goal: AlgebraFormalComputationGoal;
    readonly realization: R;
    readonly realizationData: string;
    readonly operation: AlgebraOperation<I, O>;
    readonly operationInput: I;
    readonly operationInputData: string;
    readonly engine: AlgebraEngine;
    readonly algorithm?: AlgebraAlgorithmIdentity;
    readonly limits: AlgebraComputationLimits;
}

export function createAlgebraFormalComputationRequest<R, I, O>(
    input: AlgebraFormalComputationRequestInput<R, I, O>
): AlgebraFormalComputationRequest<R, I, O> {
    if (!record(input) || !record(input.adapter) || !record(input.goal)) {
        return fail(
            'INVALID_ADAPTER',
            'request',
            'Request requires one adapter, goal, realization, and engine'
        );
    }
    const adapter = input.adapter;
    if (
        adapter.profileRevision !==
            ALGEBRA_FORMAL_DELEGATION_PROFILE.adapterRevision
    ) {
        return fail(
            'INVALID_ADAPTER',
            'request.adapter.profileRevision',
            'Request adapter has a foreign profile revision'
        );
    }
    operationIdentity(adapter.operation.identity, 'request.adapter.operation');
    if (
        !record(adapter.identity) ||
        adapter.identity.kind !== 'algebra-formal-computation-adapter'
    ) {
        return fail(
            'INVALID_ADAPTER',
            'request.adapter.identity',
            'Request adapter has an invalid identity'
        );
    }
    stableId(adapter.identity.id, 'request.adapter.identity.id', 'Adapter ID');
    stableRevision(
        adapter.identity.revision,
        'request.adapter.identity.revision'
    );
    const goal = input.goal;
    if (
        goal.profileRevision !==
            ALGEBRA_FORMAL_DELEGATION_PROFILE.goalRevision
    ) {
        return fail(
            'INVALID_GOAL',
            'request.goal.profileRevision',
            'Request goal has a foreign profile revision'
        );
    }
    let firstRealization: R;
    let secondRealization: R;
    try {
        firstRealization = adapter.normalizeRealization(
            input.realization,
            'request.realization'
        );
        secondRealization = adapter.normalizeRealization(
            input.realization,
            'request.realization'
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_REALIZATION',
            'request.realization',
            'Adapter rejected the selected realization',
            error
        );
    }
    const firstRealizationData = deterministicEncoding(
        () => adapter.serializeRealization(firstRealization),
        'request.realizationData',
        'Realization serializer'
    );
    const secondRealizationData = deterministicEncoding(
        () => adapter.serializeRealization(secondRealization),
        'request.realizationData',
        'Realization serializer'
    );
    if (firstRealizationData !== secondRealizationData) {
        return fail(
            'NONDETERMINISTIC_REALIZATION',
            'request.realization',
            'Realization normalization returned different canonical values'
        );
    }

    let firstAcquired: unknown;
    let secondAcquired: unknown;
    try {
        firstAcquired = adapter.acquire(goal, firstRealization);
        secondAcquired = adapter.acquire(goal, secondRealization);
    } catch (error: unknown) {
        return fail(
            'INVALID_REALIZATION',
            'request.operationInput',
            'Adapter could not acquire its operation input',
            error
        );
    }
    let firstInput: I;
    let secondInput: I;
    try {
        firstInput = adapter.operation.input.normalize(
            firstAcquired,
            'request.operationInput'
        );
        secondInput = adapter.operation.input.normalize(
            secondAcquired,
            'request.operationInput'
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_REALIZATION',
            'request.operationInput',
            'Acquired value does not satisfy the operation input schema',
            error
        );
    }
    const firstInputData = deterministicEncoding(
        () => adapter.serializeInput(firstInput),
        'request.operationInputData',
        'Operation-input serializer'
    );
    const secondInputData = deterministicEncoding(
        () => adapter.serializeInput(secondInput),
        'request.operationInputData',
        'Operation-input serializer'
    );
    if (firstInputData !== secondInputData) {
        return fail(
            'NONDETERMINISTIC_ACQUISITION',
            'request.operationInput',
            'Input acquisition returned different canonical values'
        );
    }

    if (!record(input.engine)) {
        return fail('INVALID_ENGINE', 'request.engine', 'Expected one engine');
    }
    engineIdentity(input.engine.identity, 'request.engine.identity');
    const algorithm = input.algorithm === undefined
        ? undefined
        : algorithmIdentity(input.algorithm, 'request.algorithm');
    const limits = normalizeAlgebraComputationContext({
        limits: input.limits
    }).limits;
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_DELEGATION_PROFILE.requestRevision,
        adapter,
        goal,
        realization: firstRealization,
        realizationData: firstRealizationData,
        operation: adapter.operation,
        operationInput: firstInput,
        operationInputData: firstInputData,
        engine: input.engine,
        ...(algorithm === undefined ? {} : { algorithm }),
        limits
    });
}

const identitySnapshot = (
    value: { readonly kind: string; readonly id: string; readonly revision: string }
) => ({
    kind: value.kind,
    id: value.id,
    revision: value.revision
});

/** Stable request data including payload bytes, unlike graph topology JSON. */
export const serializeAlgebraFormalComputationRequest = <R, I, O>(
    request: AlgebraFormalComputationRequest<R, I, O>
): string => serializeCoreLfWorkspaceCanonicalJson({
    serializationRevision:
        ALGEBRA_FORMAL_DELEGATION_PROFILE.requestRevision,
    adapter: identitySnapshot(request.adapter.identity),
    goal: {
        moduleId: request.goal.moduleId,
        declarationId: request.goal.declarationId,
        goalId: request.goal.goalId,
        contextDepth: request.goal.contextDepth,
        targetCore: request.goal.targetCore,
        fingerprint: request.goal.sourceArtifact.fingerprint
    },
    operation: identitySnapshot(request.operation.identity),
    inputSchema: identitySnapshot(request.operation.input.identity),
    outputSchema: identitySnapshot(request.operation.output.identity),
    realizationData: request.realizationData,
    operationInputData: request.operationInputData,
    engine: identitySnapshot(request.engine.identity),
    algorithm: request.algorithm === undefined
        ? null
        : identitySnapshot(request.algorithm),
    limits: request.limits
}, 'algebraFormalComputationRequest');
