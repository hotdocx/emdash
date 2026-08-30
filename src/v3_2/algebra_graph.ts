/**
 * Typed backend-neutral computation graphs over focused algebra operations.
 *
 * Graphs retain external inputs, ordered operation nodes, and named outputs.
 * This first profile validates and serializes graph topology and lowers it to
 * sequential calls through `computeAlgebraOperation`. It owns no arithmetic,
 * optimizer, cache, scheduler, process adapter, or logical proof behavior.
 */

import {
    ALGEBRA_ENGINE_PROFILE,
    AlgebraAlgorithmIdentity,
    AlgebraComputationContextInput,
    AlgebraComputed,
    AlgebraEngine,
    AlgebraEngineError,
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    algebraEngineIdentity,
    computeAlgebraOperation,
    normalizeAlgebraComputationContext
} from './algebra_engine';

export const ALGEBRA_GRAPH_PROFILE = Object.freeze({
    revision: 'emdash-algebra-computation-graph-v1' as const,
    valueRevision: 'emdash-algebra-graph-value-v1' as const,
    executionRevision: 'emdash-algebra-graph-execution-v1' as const,
    serializationRevision: 'emdash-algebra-graph-json-v1' as const,
    executionOrder: 'declared-topological-order' as const,
    optimizer: false as const,
    parallelScheduler: false as const,
    persistentCache: false as const,
    embedsLiteralValues: false as const,
    maximumInputs: 4_096,
    maximumNodes: 100_000,
    maximumOutputs: 4_096,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraGraphErrorCode =
    | 'INVALID_GRAPH_IDENTITY'
    | 'INVALID_GRAPH'
    | 'INVALID_GRAPH_VALUE'
    | 'INVALID_ENGINE'
    | 'FOREIGN_GRAPH_VALUE'
    | 'DUPLICATE_INPUT'
    | 'DUPLICATE_NODE'
    | 'DUPLICATE_OUTPUT'
    | 'GRAPH_LIMIT_EXCEEDED'
    | 'SCHEMA_MISMATCH'
    | 'UNKNOWN_REFERENCE'
    | 'NON_TOPOLOGICAL_REFERENCE'
    | 'INVALID_INPUT_VALUES'
    | 'MISSING_INPUT_VALUE'
    | 'UNKNOWN_INPUT_VALUE'
    | 'DUPLICATE_INPUT_VALUE'
    | 'CANCELLED'
    | 'NODE_EXECUTION_FAILED';

export class AlgebraGraphError extends Error {
    constructor(
        public readonly code: AlgebraGraphErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraGraphError';
    }
}

const fail = (
    code: AlgebraGraphErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraGraphError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const assertId = (
    value: unknown,
    path: string,
    label: string
): string => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return value;
    return fail(
        'INVALID_GRAPH_IDENTITY',
        path,
        `Expected one stable ${label} ID`
    );
};

const assertRevision = (value: unknown, path: string): string => {
    if (typeof value === 'string' && SAFE_REVISION.test(value)) return value;
    return fail(
        'INVALID_GRAPH_IDENTITY',
        path,
        'Expected one stable graph revision'
    );
};

const freezeArray = <T>(input: readonly T[]): readonly T[] =>
    Object.freeze([...input]);

const sameIdentity = (
    left: { readonly id: string; readonly revision: string },
    right: { readonly id: string; readonly revision: string }
): boolean => left.id === right.id && left.revision === right.revision;

const assertSchema = <T>(
    schema: unknown,
    path: string
): AlgebraRuntimeSchema<T> => {
    if (
        !record(schema) ||
        schema.profileRevision !== ALGEBRA_ENGINE_PROFILE.schemaRevision ||
        typeof schema.normalize !== 'function' ||
        !record(schema.identity) ||
        schema.identity.kind !== 'algebra-runtime-schema' ||
        typeof schema.identity.id !== 'string' ||
        typeof schema.identity.revision !== 'string'
    ) {
        return fail(
            'INVALID_GRAPH',
            path,
            'Expected one current runtime schema'
        );
    }
    assertId(schema.identity.id, `${path}.identity.id`, 'schema');
    assertRevision(
        schema.identity.revision,
        `${path}.identity.revision`
    );
    return schema as unknown as AlgebraRuntimeSchema<T>;
};

const assertOperation = <I, O>(
    operation: unknown,
    path: string
): AlgebraOperation<I, O> => {
    if (
        !record(operation) ||
        operation.profileRevision !== ALGEBRA_ENGINE_PROFILE.operationRevision ||
        !record(operation.identity) ||
        operation.identity.kind !== 'algebra-operation'
    ) {
        return fail(
            'INVALID_GRAPH',
            path,
            'Expected one current algebra operation'
        );
    }
    assertId(operation.identity.id, `${path}.identity.id`, 'operation');
    assertRevision(
        operation.identity.revision,
        `${path}.identity.revision`
    );
    assertSchema(operation.input, `${path}.input`);
    assertSchema(operation.output, `${path}.output`);
    return operation as unknown as AlgebraOperation<I, O>;
};

export interface AlgebraGraphIdentity {
    readonly kind: 'algebra-computation-graph';
    readonly id: string;
    readonly revision: string;
}

export const algebraGraphIdentity = (
    id: string,
    revision: string
): AlgebraGraphIdentity => Object.freeze({
    kind: 'algebra-computation-graph',
    id: assertId(id, 'graph.id', 'graph'),
    revision: assertRevision(revision, 'graph.revision')
});

const normalizeGraphIdentity = (
    value: unknown,
    path: string
): AlgebraGraphIdentity => {
    if (!record(value) || value.kind !== 'algebra-computation-graph') {
        return fail(
            'INVALID_GRAPH_IDENTITY',
            path,
            'Expected an algebra-computation-graph identity'
        );
    }
    return Object.freeze({
        kind: 'algebra-computation-graph',
        id: assertId(value.id, `${path}.id`, 'graph'),
        revision: assertRevision(value.revision, `${path}.revision`)
    });
};

export type AlgebraGraphReference =
    | AlgebraGraphInputReference
    | AlgebraGraphNodeReference;

export interface AlgebraGraphInputReference {
    readonly kind: 'graph-input';
    readonly id: string;
}

export interface AlgebraGraphNodeReference {
    readonly kind: 'node-output';
    readonly id: string;
}

const inputReference = (id: string): AlgebraGraphInputReference =>
    Object.freeze({ kind: 'graph-input', id });

const nodeReference = (id: string): AlgebraGraphNodeReference =>
    Object.freeze({ kind: 'node-output', id });

const referenceKey = (reference: AlgebraGraphReference): string =>
    `${reference.kind}\u0000${reference.id}`;

export interface AlgebraGraphValue<T> {
    readonly profileRevision:
        typeof ALGEBRA_GRAPH_PROFILE.valueRevision;
    readonly graph: AlgebraGraphIdentity;
    readonly reference: AlgebraGraphReference;
    readonly schema: AlgebraRuntimeSchema<T>;
}

const graphValue = <T>(
    graph: AlgebraGraphIdentity,
    reference: AlgebraGraphReference,
    schema: AlgebraRuntimeSchema<T>
): AlgebraGraphValue<T> => Object.freeze({
    profileRevision: ALGEBRA_GRAPH_PROFILE.valueRevision,
    graph,
    reference,
    schema
});

const assertGraphValue = <T>(
    value: unknown,
    graph: AlgebraGraphIdentity,
    path: string
): AlgebraGraphValue<T> => {
    if (
        !record(value) ||
        value.profileRevision !== ALGEBRA_GRAPH_PROFILE.valueRevision ||
        !record(value.reference) ||
        !['graph-input', 'node-output'].includes(
            value.reference.kind as string
        )
    ) {
        return fail(
            'INVALID_GRAPH_VALUE',
            path,
            'Expected one current algebra graph value'
        );
    }
    const valueGraph = normalizeGraphIdentity(value.graph, `${path}.graph`);
    if (!sameIdentity(valueGraph, graph)) {
        return fail(
            'FOREIGN_GRAPH_VALUE',
            `${path}.graph`,
            'Graph value belongs to a foreign computation graph'
        );
    }
    const reference = value.reference as unknown as AlgebraGraphReference;
    assertId(reference.id, `${path}.reference.id`, 'graph reference');
    return {
        profileRevision: ALGEBRA_GRAPH_PROFILE.valueRevision,
        graph: valueGraph,
        reference,
        schema: assertSchema<T>(value.schema, `${path}.schema`)
    };
};

export interface AlgebraGraphInput {
    readonly id: string;
    readonly schema: AlgebraRuntimeSchema<unknown>;
}

export interface AlgebraGraphNode {
    readonly id: string;
    readonly operation: AlgebraOperation<unknown, unknown>;
    readonly input: AlgebraGraphReference;
    readonly inputSchema: AlgebraRuntimeSchema<unknown>;
    readonly outputSchema: AlgebraRuntimeSchema<unknown>;
    readonly algorithm?: AlgebraAlgorithmIdentity;
}

export interface AlgebraGraphOutput {
    readonly id: string;
    readonly source: AlgebraGraphReference;
    readonly schema: AlgebraRuntimeSchema<unknown>;
}

export interface AlgebraComputationGraph {
    readonly profileRevision: typeof ALGEBRA_GRAPH_PROFILE.revision;
    readonly identity: AlgebraGraphIdentity;
    readonly inputs: readonly AlgebraGraphInput[];
    readonly nodes: readonly AlgebraGraphNode[];
    readonly outputs: readonly AlgebraGraphOutput[];
}

export interface AlgebraGraphNamedOutput<T> {
    readonly id: string;
    readonly value: AlgebraGraphValue<T>;
}

export interface AlgebraComputationGraphBuilder {
    readonly identity: AlgebraGraphIdentity;

    input<T>(id: string, schema: AlgebraRuntimeSchema<T>): AlgebraGraphValue<T>;

    operation<I, O>(
        id: string,
        operation: AlgebraOperation<I, O>,
        input: AlgebraGraphValue<I>,
        algorithm?: AlgebraAlgorithmIdentity
    ): AlgebraGraphValue<O>;

    build(
        outputs: readonly AlgebraGraphNamedOutput<unknown>[]
    ): AlgebraComputationGraph;
}

const algorithmIdentity = (
    value: unknown,
    path: string
): AlgebraAlgorithmIdentity => {
    if (!record(value) || value.kind !== 'algebra-algorithm') {
        return fail(
            'INVALID_GRAPH',
            path,
            'Expected one algebra algorithm identity'
        );
    }
    return algebraAlgorithmIdentity(
        assertId(value.id, `${path}.id`, 'algorithm'),
        assertRevision(value.revision, `${path}.revision`)
    );
};

export const createAlgebraComputationGraphBuilder = (
    id: string,
    revision: string
): AlgebraComputationGraphBuilder => {
    const identity = algebraGraphIdentity(id, revision);
    const inputs: AlgebraGraphInput[] = [];
    const nodes: AlgebraGraphNode[] = [];
    const valueIds = new Set<string>();
    let built = false;

    const assertOpen = (): void => {
        if (built) {
            fail(
                'INVALID_GRAPH',
                'builder',
                'Graph builder has already produced its immutable graph'
            );
        }
    };

    const reserveValueId = (
        valueId: string,
        path: string,
        duplicateCode: 'DUPLICATE_INPUT' | 'DUPLICATE_NODE'
    ): string => {
        const normalized = assertId(valueId, path, 'graph value');
        if (valueIds.has(normalized)) {
            fail(
                duplicateCode,
                path,
                `Duplicate graph value ID '${normalized}'`
            );
        }
        valueIds.add(normalized);
        return normalized;
    };

    const builder: AlgebraComputationGraphBuilder = {
        identity,

        input<T>(inputId: string, schemaInput: AlgebraRuntimeSchema<T>) {
            assertOpen();
            const normalizedId = reserveValueId(
                inputId,
                `inputs[${inputs.length}].id`,
                'DUPLICATE_INPUT'
            );
            const schema = assertSchema<T>(
                schemaInput,
                `inputs[${inputs.length}].schema`
            );
            inputs.push(Object.freeze({
                id: normalizedId,
                schema: schema as AlgebraRuntimeSchema<unknown>
            }));
            return graphValue(identity, inputReference(normalizedId), schema);
        },

        operation<I, O>(
            nodeId: string,
            operationInput: AlgebraOperation<I, O>,
            inputValue: AlgebraGraphValue<I>,
            preferredAlgorithm?: AlgebraAlgorithmIdentity
        ) {
            assertOpen();
            const normalizedId = reserveValueId(
                nodeId,
                `nodes[${nodes.length}].id`,
                'DUPLICATE_NODE'
            );
            const operation = assertOperation<I, O>(
                operationInput,
                `nodes[${nodes.length}].operation`
            );
            const source = assertGraphValue<I>(
                inputValue,
                identity,
                `nodes[${nodes.length}].input`
            );
            if (!sameIdentity(source.schema.identity, operation.input.identity)) {
                return fail(
                    'SCHEMA_MISMATCH',
                    `nodes[${nodes.length}].input`,
                    `Operation '${operation.identity.id}' does not accept ` +
                        `schema '${source.schema.identity.id}'`
                );
            }
            const algorithm = preferredAlgorithm === undefined
                ? undefined
                : algorithmIdentity(
                    preferredAlgorithm,
                    `nodes[${nodes.length}].algorithm`
                );
            nodes.push(Object.freeze({
                id: normalizedId,
                operation: operation as AlgebraOperation<unknown, unknown>,
                input: source.reference,
                inputSchema: source.schema as AlgebraRuntimeSchema<unknown>,
                outputSchema: operation.output as AlgebraRuntimeSchema<unknown>,
                ...(algorithm === undefined ? {} : { algorithm })
            }));
            return graphValue(
                identity,
                nodeReference(normalizedId),
                operation.output
            );
        },

        build(outputInputs: readonly AlgebraGraphNamedOutput<unknown>[]) {
            assertOpen();
            if (!Array.isArray(outputInputs) || outputInputs.length === 0) {
                return fail(
                    'INVALID_GRAPH',
                    'outputs',
                    'Graph requires at least one named output'
                );
            }
            const outputIds = new Set<string>();
            const outputs = outputInputs.map((entry, index) => {
                if (!record(entry)) {
                    return fail(
                        'INVALID_GRAPH',
                        `outputs[${index}]`,
                        'Named output must be a record'
                    );
                }
                const outputId = assertId(
                    entry.id,
                    `outputs[${index}].id`,
                    'graph output'
                );
                if (outputIds.has(outputId)) {
                    return fail(
                        'DUPLICATE_OUTPUT',
                        `outputs[${index}].id`,
                        `Duplicate graph output ID '${outputId}'`
                    );
                }
                outputIds.add(outputId);
                const value = assertGraphValue(
                    entry.value,
                    identity,
                    `outputs[${index}].value`
                );
                return Object.freeze({
                    id: outputId,
                    source: value.reference,
                    schema: value.schema as AlgebraRuntimeSchema<unknown>
                });
            });
            built = true;
            const graph = Object.freeze({
                profileRevision: ALGEBRA_GRAPH_PROFILE.revision,
                identity,
                inputs: freezeArray(inputs),
                nodes: freezeArray(nodes),
                outputs: freezeArray(outputs)
            });
            return validateAlgebraComputationGraph(graph);
        }
    };
    return Object.freeze(builder);
};

const assertReference = (
    value: unknown,
    path: string
): AlgebraGraphReference => {
    if (
        !record(value) ||
        !['graph-input', 'node-output'].includes(value.kind as string)
    ) {
        return fail(
            'INVALID_GRAPH',
            path,
            'Expected one graph reference'
        );
    }
    return Object.freeze({
        kind: value.kind as AlgebraGraphReference['kind'],
        id: assertId(value.id, `${path}.id`, 'graph reference')
    }) as AlgebraGraphReference;
};

export function validateAlgebraComputationGraph(
    input: AlgebraComputationGraph
): AlgebraComputationGraph {
    if (
        !record(input) ||
        input.profileRevision !== ALGEBRA_GRAPH_PROFILE.revision ||
        !Array.isArray(input.inputs) ||
        !Array.isArray(input.nodes) ||
        !Array.isArray(input.outputs)
    ) {
        return fail(
            'INVALID_GRAPH',
            'graph',
            'Expected one current computation graph'
        );
    }
    if (input.inputs.length > ALGEBRA_GRAPH_PROFILE.maximumInputs) {
        return fail(
            'GRAPH_LIMIT_EXCEEDED',
            'graph.inputs',
            `Graph exceeds ${ALGEBRA_GRAPH_PROFILE.maximumInputs} inputs`
        );
    }
    if (input.nodes.length > ALGEBRA_GRAPH_PROFILE.maximumNodes) {
        return fail(
            'GRAPH_LIMIT_EXCEEDED',
            'graph.nodes',
            `Graph exceeds ${ALGEBRA_GRAPH_PROFILE.maximumNodes} nodes`
        );
    }
    if (input.outputs.length > ALGEBRA_GRAPH_PROFILE.maximumOutputs) {
        return fail(
            'GRAPH_LIMIT_EXCEEDED',
            'graph.outputs',
            `Graph exceeds ${ALGEBRA_GRAPH_PROFILE.maximumOutputs} outputs`
        );
    }
    const identity = normalizeGraphIdentity(input.identity, 'graph.identity');
    const sources = new Map<string, AlgebraRuntimeSchema<unknown>>();
    const valueIds = new Set<string>();

    const normalizedInputs = input.inputs.map((entry, index) => {
        if (!record(entry)) {
            return fail(
                'INVALID_GRAPH',
                `graph.inputs[${index}]`,
                'Graph input must be a record'
            );
        }
        const inputId = assertId(
            entry.id,
            `graph.inputs[${index}].id`,
            'graph input'
        );
        if (valueIds.has(inputId)) {
            return fail(
                'DUPLICATE_INPUT',
                `graph.inputs[${index}].id`,
                `Duplicate graph input '${inputId}'`
            );
        }
        const schema = assertSchema(
            entry.schema,
            `graph.inputs[${index}].schema`
        );
        valueIds.add(inputId);
        sources.set(
            referenceKey(inputReference(inputId)),
            schema
        );
        return Object.freeze({ id: inputId, schema });
    });

    const normalizedNodes = input.nodes.map((entry, index) => {
        if (!record(entry)) {
            return fail(
                'INVALID_GRAPH',
                `graph.nodes[${index}]`,
                'Graph node must be a record'
            );
        }
        const nodeId = assertId(
            entry.id,
            `graph.nodes[${index}].id`,
            'graph node'
        );
        if (valueIds.has(nodeId)) {
            return fail(
                'DUPLICATE_NODE',
                `graph.nodes[${index}].id`,
                `Duplicate graph node '${nodeId}'`
            );
        }
        const operation = assertOperation(
            entry.operation,
            `graph.nodes[${index}].operation`
        );
        const reference = assertReference(
            entry.input,
            `graph.nodes[${index}].input`
        );
        const sourceSchema = sources.get(referenceKey(reference));
        if (!sourceSchema) {
            return fail(
                reference.kind === 'node-output'
                    ? 'NON_TOPOLOGICAL_REFERENCE'
                    : 'UNKNOWN_REFERENCE',
                `graph.nodes[${index}].input`,
                `Graph node '${nodeId}' refers to unavailable ` +
                    `'${reference.id}'`
            );
        }
        const inputSchema = assertSchema(
            entry.inputSchema,
            `graph.nodes[${index}].inputSchema`
        );
        const outputSchema = assertSchema(
            entry.outputSchema,
            `graph.nodes[${index}].outputSchema`
        );
        if (
            !sameIdentity(sourceSchema.identity, inputSchema.identity) ||
            !sameIdentity(inputSchema.identity, operation.input.identity) ||
            !sameIdentity(outputSchema.identity, operation.output.identity)
        ) {
            fail(
                'SCHEMA_MISMATCH',
                `graph.nodes[${index}]`,
                `Graph node '${nodeId}' has inconsistent schemas`
            );
        }
        const algorithm = entry.algorithm === undefined
            ? undefined
            : algorithmIdentity(
                entry.algorithm,
                `graph.nodes[${index}].algorithm`
            );
        valueIds.add(nodeId);
        sources.set(referenceKey(nodeReference(nodeId)), outputSchema);
        return Object.freeze({
            id: nodeId,
            operation,
            input: reference,
            inputSchema,
            outputSchema,
            ...(algorithm === undefined ? {} : { algorithm })
        });
    });

    if (input.outputs.length === 0) {
        return fail(
            'INVALID_GRAPH',
            'graph.outputs',
            'Graph requires at least one named output'
        );
    }
    const outputIds = new Set<string>();
    const normalizedOutputs = input.outputs.map((entry, index) => {
        if (!record(entry)) {
            return fail(
                'INVALID_GRAPH',
                `graph.outputs[${index}]`,
                'Graph output must be a record'
            );
        }
        const outputId = assertId(
            entry.id,
            `graph.outputs[${index}].id`,
            'graph output'
        );
        if (outputIds.has(outputId)) {
            return fail(
                'DUPLICATE_OUTPUT',
                `graph.outputs[${index}].id`,
                `Duplicate graph output '${outputId}'`
            );
        }
        outputIds.add(outputId);
        const reference = assertReference(
            entry.source,
            `graph.outputs[${index}].source`
        );
        const sourceSchema = sources.get(referenceKey(reference));
        if (!sourceSchema) {
            fail(
                'UNKNOWN_REFERENCE',
                `graph.outputs[${index}].source`,
                `Graph output '${outputId}' refers to unknown ` +
                    `'${reference.id}'`
            );
        }
        const schema = assertSchema(
            entry.schema,
            `graph.outputs[${index}].schema`
        );
        if (!sameIdentity(sourceSchema.identity, schema.identity)) {
            fail(
                'SCHEMA_MISMATCH',
                `graph.outputs[${index}].schema`,
                `Graph output '${outputId}' has a foreign schema`
            );
        }
        return Object.freeze({
            id: outputId,
            source: reference,
            schema
        });
    });

    return Object.freeze({
        profileRevision: ALGEBRA_GRAPH_PROFILE.revision,
        identity,
        inputs: freezeArray(normalizedInputs),
        nodes: freezeArray(normalizedNodes),
        outputs: freezeArray(normalizedOutputs)
    });
}

const identitySnapshot = (
    identity: { readonly kind: string; readonly id: string; readonly revision: string }
) => ({
    kind: identity.kind,
    id: identity.id,
    revision: identity.revision
});

const schemaSnapshot = (schema: AlgebraRuntimeSchema<unknown>) =>
    identitySnapshot(schema.identity);

const referenceSnapshot = (reference: AlgebraGraphReference) => ({
    kind: reference.kind,
    id: reference.id
});

/** Stable topology-only JSON. Runtime input values are intentionally absent. */
export const serializeAlgebraComputationGraph = (
    input: AlgebraComputationGraph
): string => {
    const graph = validateAlgebraComputationGraph(input);
    return `${JSON.stringify({
        serializationRevision: ALGEBRA_GRAPH_PROFILE.serializationRevision,
        profileRevision: graph.profileRevision,
        identity: identitySnapshot(graph.identity),
        inputs: graph.inputs.map(entry => ({
            id: entry.id,
            schema: schemaSnapshot(entry.schema)
        })),
        nodes: graph.nodes.map(entry => ({
            id: entry.id,
            operation: identitySnapshot(entry.operation.identity),
            input: referenceSnapshot(entry.input),
            inputSchema: schemaSnapshot(entry.inputSchema),
            outputSchema: schemaSnapshot(entry.outputSchema),
            algorithm: entry.algorithm === undefined
                ? null
                : identitySnapshot(entry.algorithm)
        })),
        outputs: graph.outputs.map(entry => ({
            id: entry.id,
            source: referenceSnapshot(entry.source),
            schema: schemaSnapshot(entry.schema)
        }))
    })}\n`;
};

export interface AlgebraGraphInputValue {
    readonly id: string;
    readonly value: unknown;
}

export interface AlgebraGraphNodeExecution {
    readonly id: string;
    readonly result: AlgebraComputed<unknown>;
}

export interface AlgebraGraphOutputValue {
    readonly id: string;
    readonly schema: AlgebraRuntimeSchema<unknown>;
    readonly value: unknown;
}

export interface AlgebraGraphExecution {
    readonly profileRevision:
        typeof ALGEBRA_GRAPH_PROFILE.executionRevision;
    readonly graph: AlgebraGraphIdentity;
    readonly engine: AlgebraEngine['identity'];
    readonly nodes: readonly AlgebraGraphNodeExecution[];
    readonly outputs: readonly AlgebraGraphOutputValue[];
}

export interface ExecuteAlgebraComputationGraphInput {
    readonly graph: AlgebraComputationGraph;
    readonly engine: AlgebraEngine;
    readonly inputs: readonly AlgebraGraphInputValue[];
    readonly context?: AlgebraComputationContextInput;
}

const assertEngine = (
    engine: unknown
): AlgebraEngine['identity'] => {
    if (
        !record(engine) ||
        typeof engine.support !== 'function' ||
        typeof engine.compute !== 'function' ||
        !record(engine.identity) ||
        engine.identity.kind !== 'algebra-engine'
    ) {
        return fail(
            'INVALID_ENGINE',
            'execution.engine',
            'Expected one algebra engine'
        );
    }
    try {
        return algebraEngineIdentity(
            engine.identity.id as string,
            engine.identity.revision as string
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_ENGINE',
            'execution.engine.identity',
            'Graph engine identity is invalid',
            error
        );
    }
};

const normalizeInputValues = (
    graph: AlgebraComputationGraph,
    input: readonly AlgebraGraphInputValue[]
): Map<string, unknown> => {
    if (!Array.isArray(input)) {
        return fail(
            'INVALID_INPUT_VALUES',
            'execution.inputs',
            'Graph input values must be an array'
        );
    }
    const byId = new Map<string, unknown>();
    input.forEach((entry, index) => {
        if (!record(entry)) {
            fail(
                'INVALID_INPUT_VALUES',
                `execution.inputs[${index}]`,
                'Graph input value must be a record'
            );
        }
        const id = assertId(
            entry.id,
            `execution.inputs[${index}].id`,
            'graph input value'
        );
        const key = referenceKey(inputReference(id));
        if (byId.has(key)) {
            fail(
                'DUPLICATE_INPUT_VALUE',
                `execution.inputs[${index}].id`,
                `Duplicate value for graph input '${id}'`
            );
        }
        const declaration = graph.inputs.find(value => value.id === id);
        if (!declaration) {
            fail(
                'UNKNOWN_INPUT_VALUE',
                `execution.inputs[${index}].id`,
                `Value supplied for unknown graph input '${id}'`
            );
        }
        byId.set(
            key,
            declaration.schema.normalize(
                entry.value,
                `execution.inputs[${index}].value`
            )
        );
    });
    graph.inputs.forEach((entry, index) => {
        if (!byId.has(referenceKey(inputReference(entry.id)))) {
            fail(
                'MISSING_INPUT_VALUE',
                `execution.graph.inputs[${index}]`,
                `Missing value for graph input '${entry.id}'`
            );
        }
    });
    return byId;
};

export async function executeAlgebraComputationGraph(
    request: ExecuteAlgebraComputationGraphInput
): Promise<AlgebraGraphExecution> {
    if (!record(request)) {
        return fail(
            'INVALID_GRAPH',
            'execution',
            'Graph execution request must be a record'
        );
    }
    const graph = validateAlgebraComputationGraph(request.graph);
    const engineIdentity = assertEngine(request.engine);
    const context = normalizeAlgebraComputationContext(request.context);
    const values = normalizeInputValues(graph, request.inputs);
    const nodes: AlgebraGraphNodeExecution[] = [];

    for (let index = 0; index < graph.nodes.length; index++) {
        const node = graph.nodes[index];
        if (context.cancellation?.requested()) {
            return fail(
                'CANCELLED',
                `execution.nodes[${index}]`,
                context.cancellation.reason?.() ??
                    `Execution cancelled before node '${node.id}'`
            );
        }
        const inputKey = referenceKey(node.input);
        if (!values.has(inputKey)) {
            return fail(
                'UNKNOWN_REFERENCE',
                `execution.nodes[${index}].input`,
                `Node '${node.id}' input is unavailable at execution`
            );
        }
        const value = values.get(inputKey);
        let result: AlgebraComputed<unknown>;
        try {
            result = await computeAlgebraOperation({
                engine: request.engine,
                operation: node.operation,
                input: value,
                ...(node.algorithm === undefined
                    ? {}
                    : { algorithm: node.algorithm }),
                context
            });
        } catch (error: unknown) {
            return fail(
                'NODE_EXECUTION_FAILED',
                `execution.nodes[${index}]`,
                `Execution failed at graph node '${node.id}'`,
                error
            );
        }
        values.set(referenceKey(nodeReference(node.id)), result.value);
        nodes.push(Object.freeze({ id: node.id, result }));
    }

    const outputs = graph.outputs.map((entry, index) => {
        const outputKey = referenceKey(entry.source);
        if (!values.has(outputKey)) {
            return fail(
                'UNKNOWN_REFERENCE',
                `execution.outputs[${index}]`,
                `Graph output '${entry.id}' is unavailable at execution`
            );
        }
        const value = values.get(outputKey);
        return Object.freeze({
            id: entry.id,
            schema: entry.schema,
            value
        });
    });

    return Object.freeze({
        profileRevision: ALGEBRA_GRAPH_PROFILE.executionRevision,
        graph: graph.identity,
        engine: engineIdentity,
        nodes: freezeArray(nodes),
        outputs: freezeArray(outputs)
    });
}
