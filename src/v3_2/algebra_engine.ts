/**
 * Browser-safe contracts for focused algebra computation.
 *
 * This layer separates mathematical operations, implementation algorithms,
 * and execution engines. It owns validation and immutable computed results,
 * but no arithmetic algorithm, computation graph, process adapter, logical
 * Core constructor, or proof authority.
 */

export const ALGEBRA_ENGINE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-engine-v1' as const,
    operationRevision: 'emdash-algebra-operation-v1' as const,
    schemaRevision: 'emdash-algebra-runtime-schema-v1' as const,
    supportRevision: 'emdash-algebra-engine-support-v1' as const,
    resultRevision: 'emdash-algebra-computed-result-v1' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const,
    ownsAlgorithms: false as const,
    ownsComputationGraph: false as const,
    invokesLambdapi: false as const,
    productionExternalCasDependency: false as const
});

export type AlgebraEngineErrorCode =
    | 'INVALID_IDENTITY'
    | 'INVALID_SCHEMA'
    | 'INVALID_SCHEMA_VALUE'
    | 'INVALID_OPERATION'
    | 'INVALID_SUPPORT'
    | 'UNSUPPORTED_OPERATION'
    | 'INVALID_CONTEXT'
    | 'INVALID_METADATA'
    | 'INVALID_RESULT'
    | 'FOREIGN_OPERATION'
    | 'FOREIGN_ENGINE'
    | 'UNSUPPORTED_ALGORITHM'
    | 'ENGINE_FAILURE';

export class AlgebraEngineError extends Error {
    constructor(
        public readonly code: AlgebraEngineErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraEngineError';
    }
}

const fail = (
    code: AlgebraEngineErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraEngineError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SAFE_CODE = /^[A-Z][A-Z0-9_]*$/u;
const MAX_TEXT_LENGTH = 16_384;

const assertText = (
    value: unknown,
    path: string,
    label: string,
    allowEmpty = false
): string => {
    if (
        typeof value !== 'string' ||
        (!allowEmpty && value.length === 0) ||
        value.length > MAX_TEXT_LENGTH ||
        value.trim() !== value ||
        /[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f]/u.test(value)
    ) {
        return fail(
            'INVALID_METADATA',
            path,
            `Expected ${label} to be bounded portable text`
        );
    }
    return value;
};

const assertId = (
    value: unknown,
    path: string,
    label: string
): string => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return value;
    return fail(
        'INVALID_IDENTITY',
        path,
        `Expected one stable ${label} ID`
    );
};

const assertRevision = (value: unknown, path: string): string => {
    if (typeof value === 'string' && SAFE_REVISION.test(value)) return value;
    return fail(
        'INVALID_IDENTITY',
        path,
        'Expected one stable revision'
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const sameIdentity = (
    left: { readonly id: string; readonly revision: string },
    right: { readonly id: string; readonly revision: string }
): boolean => left.id === right.id && left.revision === right.revision;

const cloneFreezeArray = <T>(values: readonly T[]): readonly T[] =>
    Object.freeze([...values]);

export interface AlgebraOperationIdentity {
    readonly kind: 'algebra-operation';
    readonly id: string;
    readonly revision: string;
}

export interface AlgebraEngineIdentity {
    readonly kind: 'algebra-engine';
    readonly id: string;
    readonly revision: string;
}

export interface AlgebraAlgorithmIdentity {
    readonly kind: 'algebra-algorithm';
    readonly id: string;
    readonly revision: string;
}

export interface AlgebraSchemaIdentity {
    readonly kind: 'algebra-runtime-schema';
    readonly id: string;
    readonly revision: string;
}

type IdentityKind =
    | AlgebraOperationIdentity['kind']
    | AlgebraEngineIdentity['kind']
    | AlgebraAlgorithmIdentity['kind']
    | AlgebraSchemaIdentity['kind'];

const createIdentity = <Kind extends IdentityKind>(
    kind: Kind,
    id: string,
    revision: string,
    label: string
): Readonly<{ kind: Kind; id: string; revision: string }> => Object.freeze({
    kind,
    id: assertId(id, `${label}.id`, label),
    revision: assertRevision(revision, `${label}.revision`)
});

export const algebraOperationIdentity = (
    id: string,
    revision: string
): AlgebraOperationIdentity => createIdentity(
    'algebra-operation',
    id,
    revision,
    'operation'
);

export const algebraEngineIdentity = (
    id: string,
    revision: string
): AlgebraEngineIdentity => createIdentity(
    'algebra-engine',
    id,
    revision,
    'engine'
);

export const algebraAlgorithmIdentity = (
    id: string,
    revision: string
): AlgebraAlgorithmIdentity => createIdentity(
    'algebra-algorithm',
    id,
    revision,
    'algorithm'
);

export const algebraSchemaIdentity = (
    id: string,
    revision: string
): AlgebraSchemaIdentity => createIdentity(
    'algebra-runtime-schema',
    id,
    revision,
    'schema'
);

const normalizeOperationIdentity = (
    value: unknown,
    path: string
): AlgebraOperationIdentity => {
    if (!record(value) || value.kind !== 'algebra-operation') {
        return fail(
            'INVALID_IDENTITY',
            path,
            'Expected an algebra-operation identity'
        );
    }
    return algebraOperationIdentity(
        assertId(value.id, `${path}.id`, 'operation'),
        assertRevision(value.revision, `${path}.revision`)
    );
};

const normalizeEngineIdentity = (
    value: unknown,
    path: string
): AlgebraEngineIdentity => {
    if (!record(value) || value.kind !== 'algebra-engine') {
        return fail(
            'INVALID_IDENTITY',
            path,
            'Expected an algebra-engine identity'
        );
    }
    return algebraEngineIdentity(
        assertId(value.id, `${path}.id`, 'engine'),
        assertRevision(value.revision, `${path}.revision`)
    );
};

const normalizeAlgorithmIdentity = (
    value: unknown,
    path: string
): AlgebraAlgorithmIdentity => {
    if (!record(value) || value.kind !== 'algebra-algorithm') {
        return fail(
            'INVALID_IDENTITY',
            path,
            'Expected an algebra-algorithm identity'
        );
    }
    return algebraAlgorithmIdentity(
        assertId(value.id, `${path}.id`, 'algorithm'),
        assertRevision(value.revision, `${path}.revision`)
    );
};

const normalizeSchemaIdentity = (
    value: unknown,
    path: string
): AlgebraSchemaIdentity => {
    if (!record(value) || value.kind !== 'algebra-runtime-schema') {
        return fail(
            'INVALID_IDENTITY',
            path,
            'Expected an algebra-runtime-schema identity'
        );
    }
    return algebraSchemaIdentity(
        assertId(value.id, `${path}.id`, 'schema'),
        assertRevision(value.revision, `${path}.revision`)
    );
};

export interface AlgebraRuntimeSchema<T> {
    readonly profileRevision:
        typeof ALGEBRA_ENGINE_PROFILE.schemaRevision;
    readonly identity: AlgebraSchemaIdentity;
    /**
     * Validate, normalize, and detach one value from caller-owned mutable
     * input. Implementations own the value-specific immutability policy.
     */
    normalize(value: unknown, path: string): T;
}

export interface AlgebraRuntimeSchemaInput<T> {
    readonly id: string;
    readonly revision: string;
    readonly normalize: (value: unknown, path: string) => T;
}

const assertRuntimeSchema = <T>(
    value: unknown,
    path: string
): AlgebraRuntimeSchema<T> => {
    if (
        !record(value) ||
        value.profileRevision !== ALGEBRA_ENGINE_PROFILE.schemaRevision ||
        typeof value.normalize !== 'function'
    ) {
        return fail(
            'INVALID_SCHEMA',
            path,
            'Expected one current algebra runtime schema'
        );
    }
    normalizeSchemaIdentity(value.identity, `${path}.identity`);
    return value as unknown as AlgebraRuntimeSchema<T>;
};

export function defineAlgebraRuntimeSchema<T>(
    input: AlgebraRuntimeSchemaInput<T>
): AlgebraRuntimeSchema<T> {
    if (!record(input) || typeof input.normalize !== 'function') {
        return fail(
            'INVALID_SCHEMA',
            'schema',
            'Runtime schema requires one normalization function'
        );
    }
    const identity = algebraSchemaIdentity(input.id, input.revision);
    const normalize = input.normalize;
    return Object.freeze({
        profileRevision: ALGEBRA_ENGINE_PROFILE.schemaRevision,
        identity,
        normalize(value: unknown, path: string): T {
            try {
                return normalize(value, path);
            } catch (error: unknown) {
                if (error instanceof AlgebraEngineError) throw error;
                return fail(
                    'INVALID_SCHEMA_VALUE',
                    path,
                    `Value does not satisfy schema '${identity.id}'`,
                    error
                );
            }
        }
    });
}

export interface AlgebraOperation<I, O> {
    readonly profileRevision:
        typeof ALGEBRA_ENGINE_PROFILE.operationRevision;
    readonly identity: AlgebraOperationIdentity;
    readonly input: AlgebraRuntimeSchema<I>;
    readonly output: AlgebraRuntimeSchema<O>;
}

export interface AlgebraOperationInput<I, O> {
    readonly id: string;
    readonly revision: string;
    readonly input: AlgebraRuntimeSchema<I>;
    readonly output: AlgebraRuntimeSchema<O>;
}

export function defineAlgebraOperation<I, O>(
    input: AlgebraOperationInput<I, O>
): AlgebraOperation<I, O> {
    if (!record(input)) {
        return fail(
            'INVALID_OPERATION',
            'operation',
            'Operation requires current input and output runtime schemas'
        );
    }
    const inputSchema = assertRuntimeSchema<I>(
        input.input,
        'operation.input'
    );
    const outputSchema = assertRuntimeSchema<O>(
        input.output,
        'operation.output'
    );
    return Object.freeze({
        profileRevision: ALGEBRA_ENGINE_PROFILE.operationRevision,
        identity: algebraOperationIdentity(input.id, input.revision),
        input: inputSchema,
        output: outputSchema
    });
}

export type AlgebraDiagnosticSeverity = 'info' | 'warning' | 'error';

export interface AlgebraComputationDiagnostic {
    readonly code: string;
    readonly severity: AlgebraDiagnosticSeverity;
    readonly message: string;
    readonly path?: string;
}

export interface AlgebraComputationDiagnosticInput {
    readonly code: string;
    readonly severity: AlgebraDiagnosticSeverity;
    readonly message: string;
    readonly path?: string;
}

export const algebraComputationDiagnostic = (
    input: AlgebraComputationDiagnosticInput,
    path = 'diagnostic'
): AlgebraComputationDiagnostic => {
    if (!record(input) || !SAFE_CODE.test(input.code)) {
        return fail(
            'INVALID_METADATA',
            `${path}.code`,
            'Diagnostic code must use stable upper-snake-case spelling'
        );
    }
    if (!['info', 'warning', 'error'].includes(input.severity)) {
        return fail(
            'INVALID_METADATA',
            `${path}.severity`,
            'Diagnostic severity is not supported'
        );
    }
    return Object.freeze({
        code: input.code,
        severity: input.severity,
        message: assertText(
            input.message,
            `${path}.message`,
            'diagnostic message'
        ),
        ...(input.path === undefined
            ? {}
            : {
                path: assertText(
                    input.path,
                    `${path}.path`,
                    'diagnostic path'
                )
            })
    });
};

export interface AlgebraComputationAssumption {
    readonly id: string;
    readonly detail?: string;
}

export interface AlgebraComputationAssumptionInput {
    readonly id: string;
    readonly detail?: string;
}

export const algebraComputationAssumption = (
    input: AlgebraComputationAssumptionInput,
    path = 'assumption'
): AlgebraComputationAssumption => {
    if (!record(input)) {
        return fail(
            'INVALID_METADATA',
            path,
            'Assumption must be a record'
        );
    }
    return Object.freeze({
        id: assertId(input.id, `${path}.id`, 'assumption'),
        ...(input.detail === undefined
            ? {}
            : {
                detail: assertText(
                    input.detail,
                    `${path}.detail`,
                    'assumption detail'
                )
            })
    });
};

export interface AlgebraIntermediateArtifact<T = unknown> {
    readonly id: string;
    readonly kind: string;
    readonly portable: boolean;
    readonly schema: AlgebraRuntimeSchema<T>;
    readonly value: T;
}

export interface AlgebraIntermediateArtifactInput<T> {
    readonly id: string;
    readonly kind: string;
    readonly portable: boolean;
    readonly schema: AlgebraRuntimeSchema<T>;
    readonly value: unknown;
}

export function algebraIntermediateArtifact<T>(
    input: AlgebraIntermediateArtifactInput<T>,
    path = 'artifact'
): AlgebraIntermediateArtifact<T> {
    if (
        !record(input) ||
        typeof input.portable !== 'boolean' ||
        !record(input.schema)
    ) {
        return fail(
            'INVALID_METADATA',
            path,
            'Intermediate artifact has an invalid contract'
        );
    }
    const schema = assertRuntimeSchema<T>(
        input.schema,
        `${path}.schema`
    );
    return Object.freeze({
        id: assertId(input.id, `${path}.id`, 'artifact'),
        kind: assertId(input.kind, `${path}.kind`, 'artifact kind'),
        portable: input.portable,
        schema,
        value: schema.normalize(input.value, `${path}.value`)
    });
}

export interface AlgebraComputationLimits {
    readonly fuel?: number;
    readonly maximumOutputItems?: number;
    readonly maximumIntermediateItems?: number;
    readonly maximumBitLength?: number;
}

export interface AlgebraCancellationHook {
    readonly requested: () => boolean;
    readonly reason?: () => string | undefined;
}

export interface AlgebraProgressEvent {
    readonly phase: string;
    readonly completed: number;
    readonly total?: number;
    readonly message?: string;
}

export interface AlgebraComputationContextInput {
    readonly limits?: AlgebraComputationLimits;
    readonly cancellation?: AlgebraCancellationHook;
    readonly onProgress?: (event: AlgebraProgressEvent) => void;
}

export interface AlgebraComputationContext {
    readonly limits: AlgebraComputationLimits;
    readonly cancellation?: AlgebraCancellationHook;
    readonly onProgress?: (event: AlgebraProgressEvent) => void;
}

const optionalPositiveSafeInteger = (
    value: unknown,
    path: string
): number | undefined => {
    if (value === undefined) return undefined;
    if (Number.isSafeInteger(value) && (value as number) > 0) {
        return value as number;
    }
    return fail(
        'INVALID_CONTEXT',
        path,
        'Computation limit must be a positive safe integer'
    );
};

export const normalizeAlgebraComputationContext = (
    input: AlgebraComputationContextInput = {}
): AlgebraComputationContext => {
    if (!record(input)) {
        return fail(
            'INVALID_CONTEXT',
            'context',
            'Computation context must be a record'
        );
    }
    const limitsInput = input.limits ?? {};
    if (!record(limitsInput)) {
        return fail(
            'INVALID_CONTEXT',
            'context.limits',
            'Computation limits must be a record'
        );
    }
    const limits = Object.freeze({
        ...(limitsInput.fuel === undefined
            ? {}
            : {
                fuel: optionalPositiveSafeInteger(
                    limitsInput.fuel,
                    'context.limits.fuel'
                )!
            }),
        ...(limitsInput.maximumOutputItems === undefined
            ? {}
            : {
                maximumOutputItems: optionalPositiveSafeInteger(
                    limitsInput.maximumOutputItems,
                    'context.limits.maximumOutputItems'
                )!
            }),
        ...(limitsInput.maximumIntermediateItems === undefined
            ? {}
            : {
                maximumIntermediateItems: optionalPositiveSafeInteger(
                    limitsInput.maximumIntermediateItems,
                    'context.limits.maximumIntermediateItems'
                )!
            }),
        ...(limitsInput.maximumBitLength === undefined
            ? {}
            : {
                maximumBitLength: optionalPositiveSafeInteger(
                    limitsInput.maximumBitLength,
                    'context.limits.maximumBitLength'
                )!
            })
    });
    if (
        input.cancellation !== undefined &&
        (
            !record(input.cancellation) ||
            typeof input.cancellation.requested !== 'function' ||
            (
                input.cancellation.reason !== undefined &&
                typeof input.cancellation.reason !== 'function'
            )
        )
    ) {
        return fail(
            'INVALID_CONTEXT',
            'context.cancellation',
            'Cancellation hook requires a requested function'
        );
    }
    if (
        input.onProgress !== undefined &&
        typeof input.onProgress !== 'function'
    ) {
        return fail(
            'INVALID_CONTEXT',
            'context.onProgress',
            'Progress handler must be a function'
        );
    }
    const cancellation = input.cancellation as
        | AlgebraCancellationHook
        | undefined;
    const onProgress = input.onProgress as
        | ((event: AlgebraProgressEvent) => void)
        | undefined;
    return Object.freeze({
        limits,
        ...(cancellation === undefined
            ? {}
            : {
                cancellation: Object.freeze({
                    requested: cancellation.requested,
                    ...(cancellation.reason === undefined
                        ? {}
                        : { reason: cancellation.reason })
                })
            }),
        ...(onProgress === undefined
            ? {}
            : { onProgress })
    });
};

export type AlgebraEngineSupport =
    | AlgebraEngineSupported
    | AlgebraEngineUnsupported;

export interface AlgebraEngineSupported {
    readonly profileRevision:
        typeof ALGEBRA_ENGINE_PROFILE.supportRevision;
    readonly status: 'supported';
    readonly operation: AlgebraOperationIdentity;
    readonly engine: AlgebraEngineIdentity;
    readonly algorithms: readonly AlgebraAlgorithmIdentity[];
    readonly defaultAlgorithm: AlgebraAlgorithmIdentity;
    readonly diagnostics: readonly AlgebraComputationDiagnostic[];
}

export interface AlgebraEngineUnsupported {
    readonly profileRevision:
        typeof ALGEBRA_ENGINE_PROFILE.supportRevision;
    readonly status: 'unsupported';
    readonly operation: AlgebraOperationIdentity;
    readonly engine: AlgebraEngineIdentity;
    readonly diagnostics: readonly AlgebraComputationDiagnostic[];
}

export interface AlgebraEngineSupportedInput {
    readonly operation: AlgebraOperationIdentity;
    readonly engine: AlgebraEngineIdentity;
    readonly algorithms: readonly AlgebraAlgorithmIdentity[];
    readonly defaultAlgorithm?: AlgebraAlgorithmIdentity;
    readonly diagnostics?: readonly AlgebraComputationDiagnosticInput[];
}

export interface AlgebraEngineUnsupportedInput {
    readonly operation: AlgebraOperationIdentity;
    readonly engine: AlgebraEngineIdentity;
    readonly diagnostics?: readonly AlgebraComputationDiagnosticInput[];
}

const normalizeDiagnostics = (
    input: readonly AlgebraComputationDiagnosticInput[] | undefined,
    path: string
): readonly AlgebraComputationDiagnostic[] => {
    if (input === undefined) return Object.freeze([]);
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_METADATA',
            path,
            'Diagnostics must be an array'
        );
    }
    return cloneFreezeArray(input.map((entry, index) =>
        algebraComputationDiagnostic(entry, `${path}[${index}]`)
    ));
};

export const algebraEngineSupported = (
    input: AlgebraEngineSupportedInput
): AlgebraEngineSupported => {
    if (!record(input) || !Array.isArray(input.algorithms)) {
        return fail(
            'INVALID_SUPPORT',
            'support',
            'Supported result requires an algorithm array'
        );
    }
    const operation = normalizeOperationIdentity(
        input.operation,
        'support.operation'
    );
    const engine = normalizeEngineIdentity(input.engine, 'support.engine');
    if (input.algorithms.length === 0) {
        return fail(
            'INVALID_SUPPORT',
            'support.algorithms',
            'Supported result requires at least one algorithm'
        );
    }
    const algorithms = input.algorithms.map((identity, index) =>
        normalizeAlgorithmIdentity(identity, `support.algorithms[${index}]`)
    );
    const seen = new Set<string>();
    algorithms.forEach((algorithm, index) => {
        const key = `${algorithm.id}\u0000${algorithm.revision}`;
        if (seen.has(key)) {
            fail(
                'INVALID_SUPPORT',
                `support.algorithms[${index}]`,
                `Duplicate supported algorithm '${algorithm.id}'`
            );
        }
        seen.add(key);
    });
    const requestedDefault = input.defaultAlgorithm === undefined
        ? algorithms[0]
        : normalizeAlgorithmIdentity(
            input.defaultAlgorithm,
            'support.defaultAlgorithm'
        );
    const defaultAlgorithm = algorithms.find(algorithm =>
        sameIdentity(algorithm, requestedDefault)
    );
    if (!defaultAlgorithm) {
        return fail(
            'INVALID_SUPPORT',
            'support.defaultAlgorithm',
            'Default algorithm is not in the supported algorithm set'
        );
    }
    return Object.freeze({
        profileRevision: ALGEBRA_ENGINE_PROFILE.supportRevision,
        status: 'supported',
        operation,
        engine,
        algorithms: cloneFreezeArray(algorithms),
        defaultAlgorithm,
        diagnostics: normalizeDiagnostics(input.diagnostics, 'support.diagnostics')
    });
};

export const algebraEngineUnsupported = (
    input: AlgebraEngineUnsupportedInput
): AlgebraEngineUnsupported => {
    if (!record(input)) {
        return fail(
            'INVALID_SUPPORT',
            'support',
            'Unsupported result must be a record'
        );
    }
    const operation = normalizeOperationIdentity(
        input.operation,
        'support.operation'
    );
    const engine = normalizeEngineIdentity(input.engine, 'support.engine');
    return Object.freeze({
        profileRevision: ALGEBRA_ENGINE_PROFILE.supportRevision,
        status: 'unsupported',
        operation,
        engine,
        diagnostics: normalizeDiagnostics(input.diagnostics, 'support.diagnostics')
    });
};

export type AlgebraComputationQuality =
    | 'exact'
    | 'probabilistic'
    | 'heuristic'
    | 'partial';

export interface AlgebraComputationCandidate<T> {
    readonly operation: AlgebraOperationIdentity;
    readonly engine: AlgebraEngineIdentity;
    readonly algorithm: AlgebraAlgorithmIdentity;
    readonly quality: AlgebraComputationQuality;
    readonly value: unknown;
    readonly assumptions?: readonly AlgebraComputationAssumptionInput[];
    readonly diagnostics?: readonly AlgebraComputationDiagnosticInput[];
    readonly reusable?: readonly AlgebraIntermediateArtifactInput<unknown>[];
}

export interface AlgebraComputed<T> {
    readonly profileRevision:
        typeof ALGEBRA_ENGINE_PROFILE.resultRevision;
    readonly operation: AlgebraOperationIdentity;
    readonly engine: AlgebraEngineIdentity;
    readonly algorithm: AlgebraAlgorithmIdentity;
    readonly quality: AlgebraComputationQuality;
    readonly value: T;
    readonly assumptions: readonly AlgebraComputationAssumption[];
    readonly diagnostics: readonly AlgebraComputationDiagnostic[];
    readonly reusable: readonly AlgebraIntermediateArtifact<unknown>[];
}

export interface AlgebraEngine {
    readonly identity: AlgebraEngineIdentity;

    support<I, O>(
        operation: AlgebraOperation<I, O>,
        input: I
    ): AlgebraEngineSupport;

    compute<I, O>(
        operation: AlgebraOperation<I, O>,
        input: I,
        algorithm: AlgebraAlgorithmIdentity,
        context: AlgebraComputationContext
    ): Promise<AlgebraComputationCandidate<O>>;
}

export interface AlgebraEngineInput {
    readonly id: string;
    readonly revision: string;
    readonly support: AlgebraEngine['support'];
    readonly compute: AlgebraEngine['compute'];
}

export function defineAlgebraEngine(input: AlgebraEngineInput): AlgebraEngine {
    if (
        !record(input) ||
        typeof input.support !== 'function' ||
        typeof input.compute !== 'function'
    ) {
        return fail(
            'INVALID_IDENTITY',
            'engine',
            'Engine requires support and compute functions'
        );
    }
    return Object.freeze({
        identity: algebraEngineIdentity(input.id, input.revision),
        support: input.support,
        compute: input.compute
    });
}

const assertSupportFor = (
    support: AlgebraEngineSupport,
    operation: AlgebraOperationIdentity,
    engine: AlgebraEngineIdentity
): AlgebraEngineSupport => {
    if (
        !record(support) ||
        support.profileRevision !== ALGEBRA_ENGINE_PROFILE.supportRevision ||
        !['supported', 'unsupported'].includes(support.status)
    ) {
        return fail(
            'INVALID_SUPPORT',
            'support',
            'Engine returned a non-current support result'
        );
    }
    const supportOperation = normalizeOperationIdentity(
        support.operation,
        'support.operation'
    );
    const supportEngine = normalizeEngineIdentity(
        support.engine,
        'support.engine'
    );
    if (!sameIdentity(supportOperation, operation)) {
        return fail(
            'FOREIGN_OPERATION',
            'support.operation',
            'Engine support result targets a foreign operation'
        );
    }
    if (!sameIdentity(supportEngine, engine)) {
        return fail(
            'FOREIGN_ENGINE',
            'support.engine',
            'Engine support result names a foreign engine'
        );
    }
    return support;
};

const validateEngineAndOperation = <I, O>(
    engine: AlgebraEngine,
    operation: AlgebraOperation<I, O>
): {
    readonly engineIdentity: AlgebraEngineIdentity;
    readonly operationIdentity: AlgebraOperationIdentity;
} => {
    if (
        !record(engine) ||
        typeof engine.support !== 'function' ||
        typeof engine.compute !== 'function'
    ) {
        return fail(
            'INVALID_IDENTITY',
            'engine',
            'Expected one algebra engine'
        );
    }
    const engineIdentity = normalizeEngineIdentity(
        engine.identity,
        'engine.identity'
    );
    if (
        !record(operation) ||
        operation.profileRevision !== ALGEBRA_ENGINE_PROFILE.operationRevision
    ) {
        return fail(
            'INVALID_OPERATION',
            'operation',
            'Expected one current algebra operation'
        );
    }
    const operationIdentity = normalizeOperationIdentity(
        operation.identity,
        'operation.identity'
    );
    assertRuntimeSchema(operation.input, 'operation.input');
    assertRuntimeSchema(operation.output, 'operation.output');
    return { engineIdentity, operationIdentity };
};

const inspectNormalizedAlgebraEngineSupport = <I, O>(
    engine: AlgebraEngine,
    operation: AlgebraOperation<I, O>,
    normalizedInput: I,
    engineIdentity: AlgebraEngineIdentity,
    operationIdentity: AlgebraOperationIdentity
): AlgebraEngineSupport => {
    let support: AlgebraEngineSupport;
    try {
        support = engine.support(operation, normalizedInput);
    } catch (error: unknown) {
        return fail(
            'ENGINE_FAILURE',
            'engine.support',
            `Engine '${engineIdentity.id}' failed while inspecting support`,
            error
        );
    }
    return assertSupportFor(support, operationIdentity, engineIdentity);
};

export const inspectAlgebraEngineSupport = <I, O>(
    engine: AlgebraEngine,
    operation: AlgebraOperation<I, O>,
    input: unknown
): AlgebraEngineSupport => {
    const { engineIdentity, operationIdentity } =
        validateEngineAndOperation(engine, operation);
    const normalizedInput = operation.input.normalize(input, 'input');
    return inspectNormalizedAlgebraEngineSupport(
        engine,
        operation,
        normalizedInput,
        engineIdentity,
        operationIdentity
    );
};

const normalizeAssumptions = (
    input: readonly AlgebraComputationAssumptionInput[] | undefined
): readonly AlgebraComputationAssumption[] => {
    if (input === undefined) return Object.freeze([]);
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_RESULT',
            'result.assumptions',
            'Result assumptions must be an array'
        );
    }
    return cloneFreezeArray(input.map((entry, index) =>
        algebraComputationAssumption(entry, `result.assumptions[${index}]`)
    ));
};

const normalizeArtifacts = (
    input: readonly AlgebraIntermediateArtifactInput<unknown>[] | undefined
): readonly AlgebraIntermediateArtifact<unknown>[] => {
    if (input === undefined) return Object.freeze([]);
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_RESULT',
            'result.reusable',
            'Reusable artifacts must be an array'
        );
    }
    return cloneFreezeArray(input.map((entry, index) =>
        algebraIntermediateArtifact(entry, `result.reusable[${index}]`)
    ));
};

export const validateAlgebraComputed = <I, O>(
    operation: AlgebraOperation<I, O>,
    engine: AlgebraEngineIdentity,
    support: AlgebraEngineSupported,
    candidate: AlgebraComputationCandidate<O>
): AlgebraComputed<O> => {
    const engineIdentity = normalizeEngineIdentity(engine, 'engine');
    const operationIdentity = normalizeOperationIdentity(
        operation.identity,
        'operation.identity'
    );
    const checkedSupport = assertSupportFor(
        support,
        operationIdentity,
        engineIdentity
    );
    if (checkedSupport.status !== 'supported') {
        return fail(
            'INVALID_SUPPORT',
            'support',
            'Computed result validation requires supported engine evidence'
        );
    }
    if (!record(candidate)) {
        return fail(
            'INVALID_RESULT',
            'result',
            'Engine result must be a record'
        );
    }
    const candidateOperation = normalizeOperationIdentity(
        candidate.operation,
        'result.operation'
    );
    const candidateEngine = normalizeEngineIdentity(
        candidate.engine,
        'result.engine'
    );
    const candidateAlgorithm = normalizeAlgorithmIdentity(
        candidate.algorithm,
        'result.algorithm'
    );
    if (!sameIdentity(candidateOperation, operationIdentity)) {
        return fail(
            'FOREIGN_OPERATION',
            'result.operation',
            'Engine result targets a foreign operation'
        );
    }
    if (!sameIdentity(candidateEngine, engineIdentity)) {
        return fail(
            'FOREIGN_ENGINE',
            'result.engine',
            'Engine result names a foreign engine'
        );
    }
    const algorithm = checkedSupport.algorithms.find(value =>
        sameIdentity(value, candidateAlgorithm)
    );
    if (!algorithm) {
        return fail(
            'UNSUPPORTED_ALGORITHM',
            'result.algorithm',
            'Engine result names an algorithm absent from support inspection'
        );
    }
    if (!['exact', 'probabilistic', 'heuristic', 'partial'].includes(
        candidate.quality
    )) {
        return fail(
            'INVALID_RESULT',
            'result.quality',
            'Engine result has an unsupported computation quality'
        );
    }
    return Object.freeze({
        profileRevision: ALGEBRA_ENGINE_PROFILE.resultRevision,
        operation: operationIdentity,
        engine: engineIdentity,
        algorithm,
        quality: candidate.quality,
        value: operation.output.normalize(candidate.value, 'result.value'),
        assumptions: normalizeAssumptions(candidate.assumptions),
        diagnostics: normalizeDiagnostics(
            candidate.diagnostics,
            'result.diagnostics'
        ),
        reusable: normalizeArtifacts(candidate.reusable)
    });
};

export interface AlgebraComputeInput<I, O> {
    readonly engine: AlgebraEngine;
    readonly operation: AlgebraOperation<I, O>;
    readonly input: unknown;
    readonly algorithm?: AlgebraAlgorithmIdentity;
    readonly context?: AlgebraComputationContextInput;
}

export async function computeAlgebraOperation<I, O>(
    request: AlgebraComputeInput<I, O>
): Promise<AlgebraComputed<O>> {
    if (!record(request)) {
        return fail(
            'INVALID_OPERATION',
            'request',
            'Computation request must be a record'
        );
    }
    const { engineIdentity, operationIdentity } = validateEngineAndOperation(
        request.engine,
        request.operation
    );
    const normalizedInput = request.operation.input.normalize(
        request.input,
        'input'
    );
    const support = inspectNormalizedAlgebraEngineSupport(
        request.engine,
        request.operation,
        normalizedInput,
        engineIdentity,
        operationIdentity
    );
    if (support.status === 'unsupported') {
        return fail(
            'UNSUPPORTED_OPERATION',
            'support',
            `Engine '${engineIdentity.id}' does not support ` +
                `'${operationIdentity.id}'`
        );
    }
    const algorithm = request.algorithm === undefined
        ? support.defaultAlgorithm
        : support.algorithms.find(value =>
            sameIdentity(value, request.algorithm!)
        );
    if (!algorithm) {
        return fail(
            'UNSUPPORTED_ALGORITHM',
            'request.algorithm',
            'Requested algorithm is absent from support inspection'
        );
    }
    const context = normalizeAlgebraComputationContext(request.context);
    let candidate: AlgebraComputationCandidate<O>;
    try {
        candidate = await request.engine.compute(
            request.operation,
            normalizedInput,
            algorithm,
            context
        );
    } catch (error: unknown) {
        if (error instanceof AlgebraEngineError) throw error;
        return fail(
            'ENGINE_FAILURE',
            'engine.compute',
            `Engine '${engineIdentity.id}' failed during computation`,
            error
        );
    }
    return validateAlgebraComputed(
        request.operation,
        engineIdentity,
        support,
        candidate
    );
}
