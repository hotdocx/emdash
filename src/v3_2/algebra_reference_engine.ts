/** Native in-process reference-engine registry for focused algebra. */

import {
    AlgebraAlgorithmIdentity,
    AlgebraComputationAssumptionInput,
    AlgebraComputationCandidate,
    AlgebraComputationContext,
    AlgebraComputationDiagnosticInput,
    AlgebraComputationQuality,
    AlgebraEngine,
    AlgebraIntermediateArtifactInput,
    AlgebraOperation,
    algebraAlgorithmIdentity,
    algebraEngineSupported,
    algebraEngineUnsupported,
    defineAlgebraEngine
} from './algebra_engine';

export const ALGEBRA_REFERENCE_ENGINE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-typescript-reference-engine-v1' as const,
    implementationRevision:
        'emdash-algebra-reference-implementation-v1' as const,
    selection: 'exact-operation-and-algorithm-identity' as const,
    execution: 'in-process-pure-function' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const,
    invokesExternalCas: false as const
});

export type AlgebraReferenceEngineErrorCode =
    | 'INVALID_IMPLEMENTATION'
    | 'DUPLICATE_IMPLEMENTATION'
    | 'UNKNOWN_IMPLEMENTATION'
    | 'CONTRACT_MISMATCH'
    | 'ALGORITHM_MISMATCH'
    | 'CANCELLED'
    | 'FUEL_EXHAUSTED'
    | 'IMPLEMENTATION_FAILURE';

export class AlgebraReferenceEngineError extends Error {
    constructor(
        public readonly code: AlgebraReferenceEngineErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraReferenceEngineError';
    }
}

const fail = (
    code: AlgebraReferenceEngineErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraReferenceEngineError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const sameIdentity = (
    left: { readonly id: string; readonly revision: string },
    right: { readonly id: string; readonly revision: string }
): boolean => left.id === right.id && left.revision === right.revision;

const operationKey = (operation: AlgebraOperation<unknown, unknown>): string =>
    `${operation.identity.id}\u0000${operation.identity.revision}`;

const algorithmKey = (algorithm: AlgebraAlgorithmIdentity): string =>
    `${algorithm.id}\u0000${algorithm.revision}`;

const compareAlgorithms = (
    left: AlgebraAlgorithmIdentity,
    right: AlgebraAlgorithmIdentity
): number => left.id < right.id ? -1 : left.id > right.id ? 1 :
    left.revision < right.revision ? -1 :
        left.revision > right.revision ? 1 : 0;

export interface AlgebraReferenceExecutionResult {
    readonly kind: 'algebra-reference-execution-result';
    readonly value: unknown;
    readonly quality?: AlgebraComputationQuality;
    readonly assumptions?: readonly AlgebraComputationAssumptionInput[];
    readonly diagnostics?: readonly AlgebraComputationDiagnosticInput[];
    readonly reusable?: readonly AlgebraIntermediateArtifactInput<unknown>[];
}

export interface AlgebraReferenceImplementation {
    readonly profileRevision:
        typeof ALGEBRA_REFERENCE_ENGINE_PROFILE.implementationRevision;
    readonly operation: AlgebraOperation<unknown, unknown>;
    readonly algorithm: AlgebraAlgorithmIdentity;
    readonly fuelCost: number;
    execute(
        input: unknown,
        context: AlgebraComputationContext
    ): AlgebraReferenceExecutionResult | Promise<AlgebraReferenceExecutionResult>;
}

export interface AlgebraReferenceImplementationInput<I, O> {
    readonly operation: AlgebraOperation<I, O>;
    readonly algorithm: AlgebraAlgorithmIdentity;
    readonly fuelCost?: number;
    readonly execute: (
        input: I,
        context: AlgebraComputationContext
    ) => O | AlgebraReferenceExecutionResult |
        Promise<O | AlgebraReferenceExecutionResult>;
}

const isExecutionResult = (
    value: unknown
): value is AlgebraReferenceExecutionResult => record(value) &&
    value.kind === 'algebra-reference-execution-result' &&
    'value' in value;

export const algebraReferenceExecutionResult = (
    input: Omit<AlgebraReferenceExecutionResult, 'kind'>
): AlgebraReferenceExecutionResult => Object.freeze({
    kind: 'algebra-reference-execution-result',
    ...input
});

export function defineAlgebraReferenceImplementation<I, O>(
    input: AlgebraReferenceImplementationInput<I, O>
): AlgebraReferenceImplementation {
    if (
        !record(input) ||
        !record(input.operation) ||
        !record(input.algorithm) ||
        typeof input.execute !== 'function'
    ) {
        return fail(
            'INVALID_IMPLEMENTATION',
            'implementation',
            'Reference implementation requires operation, algorithm, and execute'
        );
    }
    const fuelCost = input.fuelCost ?? 1;
    if (!Number.isSafeInteger(fuelCost) || fuelCost <= 0) {
        return fail(
            'INVALID_IMPLEMENTATION',
            'implementation.fuelCost',
            'Reference implementation fuel cost must be a positive safe integer'
        );
    }
    const operation = input.operation as unknown as AlgebraOperation<
        unknown,
        unknown
    >;
    const algorithm = algebraAlgorithmIdentity(
        input.algorithm.id,
        input.algorithm.revision
    );
    const execute = input.execute;
    return Object.freeze({
        profileRevision:
            ALGEBRA_REFERENCE_ENGINE_PROFILE.implementationRevision,
        operation,
        algorithm,
        fuelCost,
        async execute(value: unknown, context: AlgebraComputationContext) {
            const result = await execute(value as I, context);
            return isExecutionResult(result)
                ? result
                : algebraReferenceExecutionResult({ value: result });
        }
    });
}

export interface AlgebraReferenceEngineInput {
    readonly id?: string;
    readonly revision?: string;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const sameOperationContract = (
    left: AlgebraOperation<unknown, unknown>,
    right: AlgebraOperation<unknown, unknown>
): boolean => sameIdentity(left.identity, right.identity) &&
    sameIdentity(left.input.identity, right.input.identity) &&
    sameIdentity(left.output.identity, right.output.identity);

export function createAlgebraTypeScriptReferenceEngine(
    input: AlgebraReferenceEngineInput
): AlgebraEngine {
    if (!record(input) || !Array.isArray(input.implementations)) {
        return fail(
            'INVALID_IMPLEMENTATION',
            'engine.implementations',
            'Reference engine requires an implementation array'
        );
    }
    const implementations = new Map<string, {
        readonly operation: AlgebraOperation<unknown, unknown>;
        readonly algorithms: Map<string, AlgebraReferenceImplementation>;
    }>();
    input.implementations.forEach((implementation, index) => {
        if (
            !record(implementation) ||
            implementation.profileRevision !==
                ALGEBRA_REFERENCE_ENGINE_PROFILE.implementationRevision ||
            !record(implementation.operation) ||
            !record(implementation.algorithm) ||
            typeof implementation.execute !== 'function' ||
            !Number.isSafeInteger(implementation.fuelCost) ||
            (implementation.fuelCost as number) <= 0
        ) {
            fail(
                'INVALID_IMPLEMENTATION',
                `engine.implementations[${index}]`,
                'Reference implementation has an invalid contract'
            );
        }
        const key = operationKey(implementation.operation);
        const registered = implementations.get(key);
        if (
            registered !== undefined &&
            !sameOperationContract(
                registered.operation,
                implementation.operation
            )
        ) {
            fail(
                'CONTRACT_MISMATCH',
                `engine.implementations[${index}].operation`,
                `Implementations for '${implementation.operation.identity.id}' ` +
                    'do not share one operation contract'
            );
        }
        const algorithms = registered?.algorithms ?? new Map<
            string,
            AlgebraReferenceImplementation
        >();
        const selectedAlgorithmKey = algorithmKey(implementation.algorithm);
        if (algorithms.has(selectedAlgorithmKey)) {
            fail(
                'DUPLICATE_IMPLEMENTATION',
                `engine.implementations[${index}]`,
                `Duplicate '${implementation.algorithm.id}' implementation ` +
                    `for '${implementation.operation.identity.id}'`
            );
        }
        algorithms.set(selectedAlgorithmKey, implementation);
        if (registered === undefined) {
            implementations.set(key, {
                operation: implementation.operation,
                algorithms
            });
        }
    });

    const id = input.id ?? 'algebra.typescript-reference';
    const revision = input.revision ?? 'v1';

    return defineAlgebraEngine({
        id,
        revision,
        support(operation) {
            const registered = implementations.get(operationKey(
                operation as unknown as AlgebraOperation<unknown, unknown>
            ));
            if (registered === undefined) {
                return algebraEngineUnsupported({
                    operation: operation.identity,
                    engine: {
                        kind: 'algebra-engine',
                        id,
                        revision
                    },
                    diagnostics: [{
                        code: 'NO_REFERENCE_IMPLEMENTATION',
                        severity: 'info',
                        message: `No TypeScript reference implementation for ` +
                            `'${operation.identity.id}'`
                    }]
                });
            }
            if (!sameOperationContract(
                registered.operation,
                operation as unknown as AlgebraOperation<unknown, unknown>
            )) {
                return algebraEngineUnsupported({
                    operation: operation.identity,
                    engine: {
                        kind: 'algebra-engine',
                        id,
                        revision
                    },
                    diagnostics: [{
                        code: 'REFERENCE_CONTRACT_MISMATCH',
                        severity: 'error',
                        message: `Operation '${operation.identity.id}' uses ` +
                            'schemas different from the registered contract'
                    }]
                });
            }
            return algebraEngineSupported({
                operation: operation.identity,
                engine: {
                    kind: 'algebra-engine',
                    id,
                    revision
                },
                algorithms: [...registered.algorithms.values()]
                    .map(implementation => implementation.algorithm)
                    .sort(compareAlgorithms)
            });
        },
        async compute<I, O>(operation, value, algorithm, context) {
            const erasedOperation = operation as unknown as AlgebraOperation<
                unknown,
                unknown
            >;
            const registered = implementations.get(operationKey(
                erasedOperation
            ));
            if (registered === undefined) {
                return fail(
                    'UNKNOWN_IMPLEMENTATION',
                    'engine.compute.operation',
                    `No implementation for '${operation.identity.id}'`
                );
            }
            if (!sameOperationContract(registered.operation, erasedOperation)) {
                return fail(
                    'CONTRACT_MISMATCH',
                    'engine.compute.operation',
                    `Operation '${operation.identity.id}' has a foreign contract`
                );
            }
            const implementation = registered.algorithms.get(
                algorithmKey(algorithm)
            );
            if (implementation === undefined) {
                return fail(
                    'ALGORITHM_MISMATCH',
                    'engine.compute.algorithm',
                    `Algorithm '${algorithm.id}' is not registered for ` +
                        `'${operation.identity.id}'`
                );
            }
            if (context.cancellation?.requested()) {
                return fail(
                    'CANCELLED',
                    'engine.compute',
                    context.cancellation.reason?.() ??
                        `Computation '${operation.identity.id}' was cancelled`
                );
            }
            if (
                context.limits.fuel !== undefined &&
                context.limits.fuel < implementation.fuelCost
            ) {
                return fail(
                    'FUEL_EXHAUSTED',
                    'engine.compute.context.limits.fuel',
                    `Operation '${operation.identity.id}' requires fuel ` +
                        `${implementation.fuelCost}`
                );
            }
            context.onProgress?.({
                phase: operation.identity.id,
                completed: 0,
                total: 1,
                message: 'Starting TypeScript reference implementation'
            });
            let result: AlgebraReferenceExecutionResult;
            try {
                result = await implementation.execute(value, context);
            } catch (error: unknown) {
                if (error instanceof AlgebraReferenceEngineError) throw error;
                return fail(
                    'IMPLEMENTATION_FAILURE',
                    'engine.compute.implementation',
                    `Reference implementation '${implementation.algorithm.id}' ` +
                        'failed',
                    error
                );
            }
            context.onProgress?.({
                phase: operation.identity.id,
                completed: 1,
                total: 1,
                message: 'Completed TypeScript reference implementation'
            });
            return {
                operation: operation.identity,
                engine: {
                    kind: 'algebra-engine',
                    id,
                    revision
                },
                algorithm: implementation.algorithm,
                quality: result.quality ?? 'exact',
                value: result.value,
                assumptions: result.assumptions,
                diagnostics: result.diagnostics,
                reusable: result.reusable
            } as AlgebraComputationCandidate<O>;
        }
    });
}
