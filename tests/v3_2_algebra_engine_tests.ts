/** Focused CAS-CONTRACT-1A algebra-engine contract tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_ENGINE_PROFILE,
    AlgebraAlgorithmIdentity,
    AlgebraComputationCandidate,
    AlgebraEngine,
    AlgebraEngineError,
    AlgebraOperation,
    algebraAlgorithmIdentity,
    algebraComputationDiagnostic,
    algebraEngineIdentity,
    algebraEngineSupported,
    algebraEngineUnsupported,
    algebraIntermediateArtifact,
    algebraOperationIdentity,
    computeAlgebraOperation,
    defineAlgebraEngine,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema,
    inspectAlgebraEngineSupport,
    normalizeAlgebraComputationContext
} from '../src/v3_2/algebra_engine';

interface VectorValue {
    readonly values: readonly number[];
}

const vectorSchema = defineAlgebraRuntimeSchema<VectorValue>({
    id: 'fixture.vector',
    revision: 'v1',
    normalize(value: unknown, path: string): VectorValue {
        if (
            typeof value !== 'object' ||
            value === null ||
            !Array.isArray((value as { values?: unknown }).values) ||
            !(value as { values: unknown[] }).values.every(entry =>
                Number.isSafeInteger(entry)
            )
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

const operation = defineAlgebraOperation<VectorValue, VectorValue>({
    id: 'fixture.vector.double',
    revision: 'v1',
    input: vectorSchema,
    output: vectorSchema
});

const algorithm = algebraAlgorithmIdentity('fixture.double.reference', 'v1');

const errorCode = (
    expected: AlgebraEngineError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraEngineError);
    assert.equal(error.code, expected);
    return true;
};

interface EngineOptions {
    readonly supportOperation?: ReturnType<typeof algebraOperationIdentity>;
    readonly supportEngine?: ReturnType<typeof algebraEngineIdentity>;
    readonly candidateOperation?: ReturnType<typeof algebraOperationIdentity>;
    readonly candidateEngine?: ReturnType<typeof algebraEngineIdentity>;
    readonly candidateAlgorithm?: AlgebraAlgorithmIdentity;
    readonly quality?: AlgebraComputationCandidate<VectorValue>['quality'];
    readonly unsupported?: boolean;
    readonly output?: { values: number[] };
    readonly diagnostics?: AlgebraComputationCandidate<VectorValue>['diagnostics'];
    readonly throwFromCompute?: boolean;
    readonly onSupport?: (input: VectorValue) => void;
    readonly onCompute?: (
        input: VectorValue,
        selected: AlgebraAlgorithmIdentity,
        context: Parameters<AlgebraEngine['compute']>[3]
    ) => void;
}

const fixtureEngine = (options: EngineOptions = {}): AlgebraEngine => {
    const identity = algebraEngineIdentity('fixture.typescript', 'v1');
    return defineAlgebraEngine({
        id: identity.id,
        revision: identity.revision,
        support<I, O>(current: AlgebraOperation<I, O>, input: I) {
            options.onSupport?.(input as unknown as VectorValue);
            if (options.unsupported) {
                return algebraEngineUnsupported({
                    operation: options.supportOperation ?? current.identity,
                    engine: options.supportEngine ?? identity,
                    diagnostics: [{
                        code: 'NOT_IMPLEMENTED',
                        severity: 'info',
                        message: 'Fixture does not implement this operation'
                    }]
                });
            }
            return algebraEngineSupported({
                operation: options.supportOperation ?? current.identity,
                engine: options.supportEngine ?? identity,
                algorithms: [algorithm]
            });
        },
        async compute<I, O>(current, input, selected, context) {
            if (options.throwFromCompute) throw new Error('fixture failure');
            options.onCompute?.(
                input as unknown as VectorValue,
                selected,
                context
            );
            const vector = input as unknown as VectorValue;
            const output = options.output ?? {
                values: vector.values.map(value => value * 2)
            };
            return {
                operation: options.candidateOperation ?? current.identity,
                engine: options.candidateEngine ?? identity,
                algorithm: options.candidateAlgorithm ?? selected,
                quality: options.quality ?? 'exact',
                value: output,
                assumptions: [{
                    id: 'fixture.integer-input',
                    detail: 'Inputs use safe integers'
                }],
                diagnostics: options.diagnostics ?? [{
                    code: 'REFERENCE_PATH',
                    severity: 'info',
                    message: 'Used the fixture reference implementation'
                }],
                reusable: [{
                    id: 'fixture.original-vector',
                    kind: 'fixture.vector',
                    portable: true,
                    schema: vectorSchema,
                    value: vector
                }]
            } as AlgebraComputationCandidate<O>;
        }
    });
};

describe('v3.2 focused algebra-engine contracts', () => {
    it('constructs stable role-distinguished identities and rejects bad IDs', () => {
        assert.deepEqual(operation.identity, {
            kind: 'algebra-operation',
            id: 'fixture.vector.double',
            revision: 'v1'
        });
        assert.equal(
            algebraEngineIdentity('fixture.typescript', 'v1').kind,
            'algebra-engine'
        );
        assert.equal(algorithm.kind, 'algebra-algorithm');
        assert.throws(
            () => algebraOperationIdentity('not valid', 'v1'),
            errorCode('INVALID_IDENTITY')
        );
        assert.throws(
            () => algebraAlgorithmIdentity('fixture.algorithm', 'bad revision'),
            errorCode('INVALID_IDENTITY')
        );
    });

    it('keeps support inspection separate from computation', () => {
        let supportCalls = 0;
        let computeCalls = 0;
        const engine = fixtureEngine({
            onSupport(input) {
                supportCalls++;
                assert.ok(Object.isFrozen(input));
                assert.ok(Object.isFrozen(input.values));
            },
            onCompute() {
                computeCalls++;
            }
        });
        const support = inspectAlgebraEngineSupport(
            engine,
            operation,
            { values: [1, 2] }
        );
        assert.equal(support.status, 'supported');
        assert.equal(supportCalls, 1);
        assert.equal(computeCalls, 0);
        if (support.status === 'supported') {
            assert.deepEqual(support.algorithms, [algorithm]);
            assert.equal(support.defaultAlgorithm.id, algorithm.id);
            assert.ok(Object.isFrozen(support));
            assert.ok(Object.isFrozen(support.algorithms));
        }
    });

    it('validates and detaches immutable exact results and artifacts', async () => {
        const callerInput = { values: [2, 3] };
        const candidateOutput = { values: [4, 6] };
        const result = await computeAlgebraOperation({
            engine: fixtureEngine({ output: candidateOutput }),
            operation,
            input: callerInput,
            context: {
                limits: {
                    fuel: 100,
                    maximumOutputItems: 20,
                    maximumIntermediateItems: 10,
                    maximumBitLength: 256
                }
            }
        });

        callerInput.values[0] = 99;
        candidateOutput.values[0] = 88;

        assert.equal(
            result.profileRevision,
            ALGEBRA_ENGINE_PROFILE.resultRevision
        );
        assert.equal(result.quality, 'exact');
        assert.deepEqual(result.value.values, [4, 6]);
        assert.deepEqual(result.reusable[0].value, { values: [2, 3] });
        assert.equal(result.assumptions[0].id, 'fixture.integer-input');
        assert.equal(result.diagnostics[0].code, 'REFERENCE_PATH');
        assert.ok(Object.isFrozen(result));
        assert.ok(Object.isFrozen(result.value));
        assert.ok(Object.isFrozen(result.value.values));
        assert.ok(Object.isFrozen(result.assumptions));
        assert.ok(Object.isFrozen(result.diagnostics));
        assert.ok(Object.isFrozen(result.reusable));
        assert.ok(Object.isFrozen(result.reusable[0].value));
    });

    it('normalizes computation inputs exactly once before support and execution', async () => {
        let inputNormalizations = 0;
        let outputNormalizations = 0;
        const countedInput = defineAlgebraRuntimeSchema<VectorValue>({
            id: 'fixture.counted-input',
            revision: 'v1',
            normalize(value: unknown): VectorValue {
                inputNormalizations++;
                const values = (value as { values: number[] }).values;
                return Object.freeze({ values: Object.freeze([...values]) });
            }
        });
        const countedOutput = defineAlgebraRuntimeSchema<VectorValue>({
            id: 'fixture.counted-output',
            revision: 'v1',
            normalize(value: unknown): VectorValue {
                outputNormalizations++;
                const values = (value as { values: number[] }).values;
                return Object.freeze({ values: Object.freeze([...values]) });
            }
        });
        const countedOperation = defineAlgebraOperation({
            id: 'fixture.vector.counted-double',
            revision: 'v1',
            input: countedInput,
            output: countedOutput
        });
        const engine = defineAlgebraEngine({
            id: 'fixture.counted-engine',
            revision: 'v1',
            support(current) {
                return algebraEngineSupported({
                    operation: current.identity,
                    engine: algebraEngineIdentity(
                        'fixture.counted-engine',
                        'v1'
                    ),
                    algorithms: [algorithm]
                });
            },
            async compute<I, O>(current, input, selected) {
                const values = (input as unknown as VectorValue).values;
                return {
                    operation: current.identity,
                    engine: algebraEngineIdentity(
                        'fixture.counted-engine',
                        'v1'
                    ),
                    algorithm: selected,
                    quality: 'exact',
                    value: { values: values.map(value => value * 2) }
                } as AlgebraComputationCandidate<O>;
            }
        });
        const result = await computeAlgebraOperation({
            engine,
            operation: countedOperation,
            input: { values: [3] }
        });
        assert.deepEqual(result.value.values, [6]);
        assert.equal(inputNormalizations, 1);
        assert.equal(outputNormalizations, 1);
    });

    it('passes bounded cancellation and progress hooks as management data', async () => {
        let cancelled = false;
        const progress: string[] = [];
        const result = await computeAlgebraOperation({
            engine: fixtureEngine({
                onCompute(input, selected, context) {
                    assert.deepEqual(input.values, [5]);
                    assert.equal(selected.id, algorithm.id);
                    assert.equal(context.limits.fuel, 7);
                    assert.equal(context.cancellation?.requested(), false);
                    context.onProgress?.({
                        phase: 'fixture.compute',
                        completed: 1,
                        total: 1
                    });
                    cancelled = true;
                    assert.equal(context.cancellation?.requested(), true);
                    assert.equal(context.cancellation?.reason?.(), 'requested');
                }
            }),
            operation,
            input: { values: [5] },
            algorithm,
            context: {
                limits: { fuel: 7 },
                cancellation: {
                    requested: () => cancelled,
                    reason: () => cancelled ? 'requested' : undefined
                },
                onProgress: event => progress.push(event.phase)
            }
        });
        assert.deepEqual(result.value.values, [10]);
        assert.deepEqual(progress, ['fixture.compute']);
        assert.ok(Object.isFrozen(
            normalizeAlgebraComputationContext({ limits: { fuel: 1 } })
        ));
        assert.throws(
            () => normalizeAlgebraComputationContext({ limits: { fuel: 0 } }),
            errorCode('INVALID_CONTEXT')
        );
    });

    it('reports unsupported operations without invoking computation', async () => {
        let computeCalls = 0;
        const engine = fixtureEngine({
            unsupported: true,
            onCompute() {
                computeCalls++;
            }
        });
        const support = inspectAlgebraEngineSupport(
            engine,
            operation,
            { values: [1] }
        );
        assert.equal(support.status, 'unsupported');
        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation,
                input: { values: [1] }
            }),
            errorCode('UNSUPPORTED_OPERATION')
        );
        assert.equal(computeCalls, 0);
    });

    it('rejects foreign support and result identities', async () => {
        const foreignOperation = algebraOperationIdentity(
            'fixture.vector.foreign',
            'v1'
        );
        const foreignEngine = algebraEngineIdentity('fixture.foreign', 'v1');
        assert.throws(
            () => inspectAlgebraEngineSupport(
                fixtureEngine({ supportOperation: foreignOperation }),
                operation,
                { values: [1] }
            ),
            errorCode('FOREIGN_OPERATION')
        );
        assert.throws(
            () => inspectAlgebraEngineSupport(
                fixtureEngine({ supportEngine: foreignEngine }),
                operation,
                { values: [1] }
            ),
            errorCode('FOREIGN_ENGINE')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({
                    candidateOperation: foreignOperation
                }),
                operation,
                input: { values: [1] }
            }),
            errorCode('FOREIGN_OPERATION')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({ candidateEngine: foreignEngine }),
                operation,
                input: { values: [1] }
            }),
            errorCode('FOREIGN_ENGINE')
        );
    });

    it('rejects algorithms absent from inspected support', async () => {
        const foreignAlgorithm = algebraAlgorithmIdentity(
            'fixture.unadvertised',
            'v1'
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine(),
                operation,
                input: { values: [1] },
                algorithm: foreignAlgorithm
            }),
            errorCode('UNSUPPORTED_ALGORITHM')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({
                    candidateAlgorithm: foreignAlgorithm
                }),
                operation,
                input: { values: [1] }
            }),
            errorCode('UNSUPPORTED_ALGORITHM')
        );
    });

    it('rejects malformed result values, metadata, and engine failures', async () => {
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({ output: { values: [1.5] } }),
                operation,
                input: { values: [1] }
            }),
            errorCode('INVALID_SCHEMA_VALUE')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({
                    diagnostics: [{
                        code: 'not_uppercase',
                        severity: 'warning',
                        message: 'bad diagnostic'
                    }]
                }),
                operation,
                input: { values: [1] }
            }),
            errorCode('INVALID_METADATA')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({
                    quality: 'unknown' as AlgebraComputationCandidate<
                        VectorValue
                    >['quality']
                }),
                operation,
                input: { values: [1] }
            }),
            errorCode('INVALID_RESULT')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: fixtureEngine({ throwFromCompute: true }),
                operation,
                input: { values: [1] }
            }),
            errorCode('ENGINE_FAILURE')
        );
    });

    it('validates standalone diagnostics and reusable artifacts', () => {
        const diagnostic = algebraComputationDiagnostic({
            code: 'EXAMPLE_WARNING',
            severity: 'warning',
            message: 'Example warning'
        });
        const artifact = algebraIntermediateArtifact({
            id: 'fixture.artifact',
            kind: 'fixture.vector',
            portable: true,
            schema: vectorSchema,
            value: { values: [7, 8] }
        });
        assert.ok(Object.isFrozen(diagnostic));
        assert.ok(Object.isFrozen(artifact));
        assert.deepEqual(artifact.value.values, [7, 8]);
        assert.throws(
            () => algebraComputationDiagnostic({
                code: 'bad-code',
                severity: 'info',
                message: 'Bad code'
            }),
            errorCode('INVALID_METADATA')
        );
    });
});
