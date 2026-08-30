/** Focused CAS-GRAPH-1B computation-graph tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraComputationCandidate,
    AlgebraEngine,
    AlgebraEngineError,
    AlgebraOperation,
    algebraAlgorithmIdentity,
    algebraEngineIdentity,
    algebraEngineSupported,
    algebraEngineUnsupported,
    defineAlgebraEngine,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from '../src/v3_2/algebra_engine';
import {
    ALGEBRA_GRAPH_PROFILE,
    AlgebraComputationGraph,
    AlgebraGraphError,
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph,
    serializeAlgebraComputationGraph,
    validateAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';

interface VectorValue {
    readonly values: readonly number[];
}

interface ScalarValue {
    readonly value: number;
}

const vectorSchema = defineAlgebraRuntimeSchema<VectorValue>({
    id: 'fixture.graph.vector',
    revision: 'v1',
    normalize(value: unknown, path: string): VectorValue {
        if (
            typeof value !== 'object' ||
            value === null ||
            !Array.isArray((value as { values?: unknown }).values) ||
            !(value as { values: unknown[] }).values.every(Number.isSafeInteger)
        ) {
            throw new Error(`invalid vector at ${path}`);
        }
        return Object.freeze({
            values: Object.freeze([
                ...(value as { values: number[] }).values
            ])
        });
    }
});

const scalarSchema = defineAlgebraRuntimeSchema<ScalarValue>({
    id: 'fixture.graph.scalar',
    revision: 'v1',
    normalize(value: unknown, path: string): ScalarValue {
        if (
            typeof value !== 'object' ||
            value === null ||
            !Number.isSafeInteger((value as { value?: unknown }).value)
        ) {
            throw new Error(`invalid scalar at ${path}`);
        }
        return Object.freeze({ value: (value as { value: number }).value });
    }
});

const double = defineAlgebraOperation<VectorValue, VectorValue>({
    id: 'fixture.graph.double',
    revision: 'v1',
    input: vectorSchema,
    output: vectorSchema
});

const scalarIdentity = defineAlgebraOperation<ScalarValue, ScalarValue>({
    id: 'fixture.graph.scalar-identity',
    revision: 'v1',
    input: scalarSchema,
    output: scalarSchema
});

const referenceAlgorithm = algebraAlgorithmIdentity(
    'fixture.graph.reference',
    'v1'
);
const alternateAlgorithm = algebraAlgorithmIdentity(
    'fixture.graph.alternate',
    'v1'
);

interface EngineOptions {
    readonly unsupported?: boolean;
    readonly throwOnCall?: number;
    readonly onCompute?: (algorithmId: string) => void;
}

const graphEngine = (options: EngineOptions = {}): AlgebraEngine => {
    const identity = algebraEngineIdentity('fixture.graph.engine', 'v1');
    let calls = 0;
    return defineAlgebraEngine({
        id: identity.id,
        revision: identity.revision,
        support<I, O>(operation: AlgebraOperation<I, O>) {
            if (options.unsupported) {
                return algebraEngineUnsupported({
                    operation: operation.identity,
                    engine: identity,
                    diagnostics: [{
                        code: 'UNSUPPORTED_FIXTURE',
                        severity: 'info',
                        message: 'Fixture engine is disabled'
                    }]
                });
            }
            return algebraEngineSupported({
                operation: operation.identity,
                engine: identity,
                algorithms: [referenceAlgorithm, alternateAlgorithm]
            });
        },
        async compute<I, O>(operation, input, algorithm) {
            calls++;
            if (options.throwOnCall === calls) {
                throw new Error(`failure on call ${calls}`);
            }
            options.onCompute?.(algorithm.id);
            if (operation.identity.id === double.identity.id) {
                const vector = input as unknown as VectorValue;
                return {
                    operation: operation.identity,
                    engine: identity,
                    algorithm,
                    quality: 'exact',
                    value: {
                        values: vector.values.map(value => value * 2)
                    }
                } as AlgebraComputationCandidate<O>;
            }
            return {
                operation: operation.identity,
                engine: identity,
                algorithm,
                quality: 'exact',
                value: input
            } as AlgebraComputationCandidate<O>;
        }
    });
};

const graphError = (
    expected: AlgebraGraphError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraGraphError);
    assert.equal(error.code, expected);
    return true;
};

const twoStepGraph = () => {
    const builder = createAlgebraComputationGraphBuilder(
        'fixture.graph.two-step',
        'v1'
    );
    const input = builder.input('source', vectorSchema);
    const twice = builder.operation('twice', double, input);
    const fourfold = builder.operation(
        'fourfold',
        double,
        twice,
        alternateAlgorithm
    );
    return builder.build([
        { id: 'result', value: fourfold },
        { id: 'original', value: input }
    ]);
};

describe('v3.2 focused algebra computation graphs', () => {
    it('builds an immutable typed two-step topology', () => {
        const graph = twoStepGraph();
        assert.equal(graph.profileRevision, ALGEBRA_GRAPH_PROFILE.revision);
        assert.deepEqual(graph.inputs.map(entry => entry.id), ['source']);
        assert.deepEqual(graph.nodes.map(entry => entry.id), [
            'twice',
            'fourfold'
        ]);
        assert.deepEqual(graph.outputs.map(entry => entry.id), [
            'result',
            'original'
        ]);
        assert.equal(graph.nodes[0].input.kind, 'graph-input');
        assert.equal(graph.nodes[1].input.kind, 'node-output');
        assert.equal(graph.nodes[1].algorithm?.id, alternateAlgorithm.id);
        assert.ok(Object.isFrozen(graph));
        assert.ok(Object.isFrozen(graph.inputs));
        assert.ok(Object.isFrozen(graph.nodes));
        assert.ok(Object.isFrozen(graph.outputs));
        assert.ok(Object.isFrozen(graph.nodes[0]));
    });

    it('serializes topology deterministically without runtime values', () => {
        const graph = twoStepGraph();
        const first = serializeAlgebraComputationGraph(graph);
        const second = serializeAlgebraComputationGraph(graph);
        assert.equal(first, second);
        assert.ok(first.endsWith('\n'));
        const parsed = JSON.parse(first) as {
            serializationRevision: string;
            identity: { id: string };
            inputs: unknown[];
            nodes: { id: string; algorithm: { id: string } | null }[];
            outputs: unknown[];
        };
        assert.equal(
            parsed.serializationRevision,
            ALGEBRA_GRAPH_PROFILE.serializationRevision
        );
        assert.equal(parsed.identity.id, 'fixture.graph.two-step');
        assert.equal(parsed.inputs.length, 1);
        assert.deepEqual(parsed.nodes.map(entry => entry.id), [
            'twice',
            'fourfold'
        ]);
        assert.equal(
            parsed.nodes[1].algorithm?.id,
            alternateAlgorithm.id
        );
        assert.equal(parsed.outputs.length, 2);
        assert.equal(first.includes('"values"'), false);
    });

    it('lowers ordered nodes through the engine and retains node results', async () => {
        const algorithms: string[] = [];
        const execution = await executeAlgebraComputationGraph({
            graph: twoStepGraph(),
            engine: graphEngine({
                onCompute: id => algorithms.push(id)
            }),
            inputs: [{ id: 'source', value: { values: [3, 5] } }],
            context: { limits: { fuel: 100 } }
        });
        assert.equal(
            execution.profileRevision,
            ALGEBRA_GRAPH_PROFILE.executionRevision
        );
        assert.deepEqual(algorithms, [
            referenceAlgorithm.id,
            alternateAlgorithm.id
        ]);
        assert.deepEqual(
            (execution.nodes[0].result.value as VectorValue).values,
            [6, 10]
        );
        assert.deepEqual(
            (execution.nodes[1].result.value as VectorValue).values,
            [12, 20]
        );
        assert.deepEqual(
            (execution.outputs[0].value as VectorValue).values,
            [12, 20]
        );
        assert.deepEqual(
            (execution.outputs[1].value as VectorValue).values,
            [3, 5]
        );
        assert.ok(Object.isFrozen(execution));
        assert.ok(Object.isFrozen(execution.nodes));
        assert.ok(Object.isFrozen(execution.outputs));
    });

    it('supports an input-only graph without invoking an engine operation', async () => {
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.graph.identity',
            'v1'
        );
        const input = builder.input('source', vectorSchema);
        const graph = builder.build([{ id: 'result', value: input }]);
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine: graphEngine({ throwOnCall: 1 }),
            inputs: [{ id: 'source', value: { values: [9] } }]
        });
        assert.equal(execution.nodes.length, 0);
        assert.deepEqual(
            (execution.outputs[0].value as VectorValue).values,
            [9]
        );
    });

    it('rejects values from foreign builders and mismatched schemas', () => {
        const left = createAlgebraComputationGraphBuilder(
            'fixture.graph.left',
            'v1'
        );
        const right = createAlgebraComputationGraphBuilder(
            'fixture.graph.right',
            'v1'
        );
        const leftInput = left.input('left-input', vectorSchema);
        assert.throws(
            () => right.operation('foreign', double, leftInput),
            graphError('FOREIGN_GRAPH_VALUE')
        );
        const scalarInput = right.input('scalar-input', scalarSchema);
        assert.throws(
            () => right.operation(
                'wrong-schema',
                double,
                scalarInput as never
            ),
            graphError('SCHEMA_MISMATCH')
        );
        assert.equal(scalarIdentity.input.identity.id, scalarSchema.identity.id);
    });

    it('rejects duplicate IDs and reuse after immutable build', () => {
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.graph.duplicates',
            'v1'
        );
        const input = builder.input('value', vectorSchema);
        assert.throws(
            () => builder.input('value', vectorSchema),
            graphError('DUPLICATE_INPUT')
        );
        assert.throws(
            () => builder.operation('value', double, input),
            graphError('DUPLICATE_NODE')
        );
        const node = builder.operation('node', double, input);
        assert.throws(
            () => builder.build([
                { id: 'same', value: node },
                { id: 'same', value: input }
            ]),
            graphError('DUPLICATE_OUTPUT')
        );

        const complete = createAlgebraComputationGraphBuilder(
            'fixture.graph.complete',
            'v1'
        );
        const completeInput = complete.input('source', vectorSchema);
        complete.build([{ id: 'result', value: completeInput }]);
        assert.throws(
            () => complete.input('later', vectorSchema),
            graphError('INVALID_GRAPH')
        );
    });

    it('rejects missing, unknown, and duplicate execution inputs', async () => {
        const graph = twoStepGraph();
        const engine = graphEngine();
        await assert.rejects(
            executeAlgebraComputationGraph({ graph, engine, inputs: [] }),
            graphError('MISSING_INPUT_VALUE')
        );
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph,
                engine,
                inputs: [{ id: 'unknown', value: { values: [1] } }]
            }),
            graphError('UNKNOWN_INPUT_VALUE')
        );
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph,
                engine,
                inputs: [
                    { id: 'source', value: { values: [1] } },
                    { id: 'source', value: { values: [2] } }
                ]
            }),
            graphError('DUPLICATE_INPUT_VALUE')
        );
    });

    it('rejects non-topological references in reconstructed graph data', () => {
        const graph = twoStepGraph();
        const malformed = {
            ...graph,
            nodes: [...graph.nodes].reverse()
        } as AlgebraComputationGraph;
        assert.throws(
            () => validateAlgebraComputationGraph(malformed),
            graphError('NON_TOPOLOGICAL_REFERENCE')
        );
    });

    it('bounds reconstructed topology and validates input-only engines', async () => {
        const graph = twoStepGraph();
        const oversized = {
            ...graph,
            inputs: Array.from(
                { length: ALGEBRA_GRAPH_PROFILE.maximumInputs + 1 },
                () => graph.inputs[0]
            )
        } as AlgebraComputationGraph;
        assert.throws(
            () => validateAlgebraComputationGraph(oversized),
            graphError('GRAPH_LIMIT_EXCEEDED')
        );

        const identityBuilder = createAlgebraComputationGraphBuilder(
            'fixture.graph.bad-engine',
            'v1'
        );
        const value = identityBuilder.input('source', vectorSchema);
        const identityGraph = identityBuilder.build([
            { id: 'result', value }
        ]);
        const malformedEngine = {
            ...graphEngine(),
            identity: {
                kind: 'algebra-engine',
                id: 'not valid',
                revision: 'v1'
            }
        } as AlgebraEngine;
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph: identityGraph,
                engine: malformedEngine,
                inputs: [{ id: 'source', value: { values: [1] } }]
            }),
            graphError('INVALID_ENGINE')
        );
    });

    it('wraps engine failures at the exact graph node', async () => {
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph: twoStepGraph(),
                engine: graphEngine({ throwOnCall: 2 }),
                inputs: [{ id: 'source', value: { values: [1] } }]
            }),
            error => {
                assert.ok(error instanceof AlgebraGraphError);
                assert.equal(error.code, 'NODE_EXECUTION_FAILED');
                assert.equal(error.path, 'execution.nodes[1]');
                assert.ok(error.underlying instanceof AlgebraEngineError);
                assert.equal(error.underlying.code, 'ENGINE_FAILURE');
                return true;
            }
        );
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph: twoStepGraph(),
                engine: graphEngine({ unsupported: true }),
                inputs: [{ id: 'source', value: { values: [1] } }]
            }),
            graphError('NODE_EXECUTION_FAILED')
        );
    });

    it('honors graph-level cancellation before executing a node', async () => {
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph: twoStepGraph(),
                engine: graphEngine(),
                inputs: [{ id: 'source', value: { values: [1] } }],
                context: {
                    cancellation: {
                        requested: () => true,
                        reason: () => 'cancelled by focused test'
                    }
                }
            }),
            graphError('CANCELLED')
        );
    });
});
