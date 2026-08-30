/** Focused CAS-ENGINE-2C native reference-engine tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraEngineError,
    algebraAlgorithmIdentity,
    computeAlgebraOperation,
    defineAlgebraOperation
} from '../src/v3_2/algebra_engine';
import {
    ALGEBRA_INTEGER_SCHEMA,
    ALGEBRA_RATIONAL_SCHEMA,
    RATIONAL_DOMAIN,
    algebraIntegerText,
    algebraRationalText
} from '../src/v3_2/algebra_exact';
import {
    AlgebraGraphError,
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import {
    algebraPolynomialAdd,
    algebraPolynomialEquals,
    algebraPolynomialMultiply,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialText,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    AlgebraReferenceEngineError,
    algebraReferenceExecutionResult,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from '../src/v3_2/algebra_reference_engine';
import {
    ALGEBRA_EXACT_REFERENCE_IMPLEMENTATIONS,
    ALGEBRA_INTEGER_ADD_OPERATION,
    ALGEBRA_INTEGER_MULTIPLY_OPERATION,
    ALGEBRA_INTEGER_NEGATE_OPERATION,
    ALGEBRA_RATIONAL_ADD_OPERATION,
    ALGEBRA_RATIONAL_NEGATE_OPERATION,
    algebraPolynomialReferenceOperations
} from '../src/v3_2/algebra_reference_operations';

const engineError = (
    code: AlgebraEngineError['code'],
    underlying?: AlgebraReferenceEngineError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraEngineError);
    assert.equal(error.code, code);
    if (underlying !== undefined) {
        assert.ok(error.underlying instanceof AlgebraReferenceEngineError);
        assert.equal(error.underlying.code, underlying);
    }
    return true;
};

const exactEngine = () => createAlgebraTypeScriptReferenceEngine({
    implementations: ALGEBRA_EXACT_REFERENCE_IMPLEMENTATIONS
});

describe('v3.2 native TypeScript algebra reference engine', () => {
    it('executes selected exact operations through normalized contracts', async () => {
        const engine = exactEngine();
        const integer = await computeAlgebraOperation({
            engine,
            operation: ALGEBRA_INTEGER_ADD_OPERATION,
            input: { left: '12', right: '-5' }
        });
        const rational = await computeAlgebraOperation({
            engine,
            operation: ALGEBRA_RATIONAL_ADD_OPERATION,
            input: { left: '1/6', right: '1/3' }
        });
        assert.equal(algebraIntegerText(integer.value), '7');
        assert.equal(algebraRationalText(rational.value), '1/2');
        assert.equal(integer.quality, 'exact');
        assert.equal(integer.engine.id, 'algebra.typescript-reference');
        assert.equal(integer.operation.id, ALGEBRA_INTEGER_ADD_OPERATION.identity.id);
    });

    it('reports unsupported operations and schema-contract collisions', async () => {
        const engine = exactEngine();
        const unsupported = defineAlgebraOperation({
            id: 'fixture.unimplemented',
            revision: 'v1',
            input: ALGEBRA_INTEGER_SCHEMA,
            output: ALGEBRA_INTEGER_SCHEMA
        });
        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation: unsupported,
                input: '1'
            }),
            engineError('UNSUPPORTED_OPERATION')
        );

        const collision = defineAlgebraOperation({
            id: ALGEBRA_INTEGER_ADD_OPERATION.identity.id,
            revision: ALGEBRA_INTEGER_ADD_OPERATION.identity.revision,
            input: ALGEBRA_INTEGER_SCHEMA,
            output: ALGEBRA_INTEGER_SCHEMA
        });
        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation: collision,
                input: '1'
            }),
            engineError('UNSUPPORTED_OPERATION')
        );
    });

    it('registers multiple algorithms deterministically and honors selection', async () => {
        const selected: string[] = [];
        const first = algebraAlgorithmIdentity('fixture.algorithm.a', 'v1');
        const second = algebraAlgorithmIdentity('fixture.algorithm.b', 'v1');
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: [
                defineAlgebraReferenceImplementation({
                    operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
                    algorithm: second,
                    execute: input => {
                        selected.push(second.id);
                        return {
                            kind: 'algebra-integer' as const,
                            parent: input.parent,
                            value: -input.value
                        };
                    }
                }),
                defineAlgebraReferenceImplementation({
                    operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
                    algorithm: first,
                    execute: input => {
                        selected.push(first.id);
                        return {
                            kind: 'algebra-integer' as const,
                            parent: input.parent,
                            value: -input.value
                        };
                    }
                })
            ]
        });
        const automatic = await computeAlgebraOperation({
            engine,
            operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
            input: '3'
        });
        const explicit = await computeAlgebraOperation({
            engine,
            operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
            input: '4',
            algorithm: second
        });
        assert.equal(automatic.algorithm.id, first.id);
        assert.equal(explicit.algorithm.id, second.id);
        assert.deepEqual(selected, [first.id, second.id]);
        assert.equal(algebraIntegerText(automatic.value), '-3');
        assert.equal(algebraIntegerText(explicit.value), '-4');
    });

    it('rejects duplicate algorithm registrations', () => {
        const algorithm = algebraAlgorithmIdentity('fixture.duplicate', 'v1');
        const implementation = defineAlgebraReferenceImplementation({
            operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
            algorithm,
            execute: input => ({
                kind: 'algebra-integer' as const,
                parent: input.parent,
                value: -input.value
            })
        });
        assert.throws(
            () => createAlgebraTypeScriptReferenceEngine({
                implementations: [implementation, implementation]
            }),
            error => {
                assert.ok(error instanceof AlgebraReferenceEngineError);
                assert.equal(error.code, 'DUPLICATE_IMPLEMENTATION');
                return true;
            }
        );
    });

    it('enforces cancellation and operation fuel before implementation work', async () => {
        await assert.rejects(
            computeAlgebraOperation({
                engine: exactEngine(),
                operation: ALGEBRA_INTEGER_MULTIPLY_OPERATION,
                input: { left: '6', right: '7' },
                context: { limits: { fuel: 1 } }
            }),
            engineError('ENGINE_FAILURE', 'FUEL_EXHAUSTED')
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine: exactEngine(),
                operation: ALGEBRA_INTEGER_ADD_OPERATION,
                input: { left: '1', right: '2' },
                context: {
                    cancellation: {
                        requested: () => true,
                        reason: () => 'focused cancellation'
                    }
                }
            }),
            engineError('ENGINE_FAILURE', 'CANCELLED')
        );
    });

    it('reports deterministic start/completion progress and metadata', async () => {
        const phases: string[] = [];
        const metadataAlgorithm = algebraAlgorithmIdentity(
            'fixture.metadata',
            'v1'
        );
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: [defineAlgebraReferenceImplementation({
                operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
                algorithm: metadataAlgorithm,
                execute: input => algebraReferenceExecutionResult({
                    value: {
                        kind: 'algebra-integer',
                        parent: input.parent,
                        value: -input.value
                    },
                    assumptions: [{ id: 'fixture.pure-bigint' }],
                    diagnostics: [{
                        code: 'METADATA_PATH',
                        severity: 'info',
                        message: 'Used metadata fixture'
                    }]
                })
            })]
        });
        const result = await computeAlgebraOperation({
            engine,
            operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
            input: '8',
            context: {
                onProgress: event => phases.push(
                    `${event.phase}:${event.completed}`
                )
            }
        });
        assert.deepEqual(phases, [
            `${ALGEBRA_INTEGER_NEGATE_OPERATION.identity.id}:0`,
            `${ALGEBRA_INTEGER_NEGATE_OPERATION.identity.id}:1`
        ]);
        assert.equal(result.assumptions[0].id, 'fixture.pure-bigint');
        assert.equal(result.diagnostics[0].code, 'METADATA_PATH');
    });

    it('executes a multi-node exact graph with retained results', async () => {
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.reference.double-negate',
            'v1'
        );
        const input = builder.input('value', ALGEBRA_RATIONAL_SCHEMA);
        const negative = builder.operation(
            'negative',
            ALGEBRA_RATIONAL_NEGATE_OPERATION,
            input
        );
        const restored = builder.operation(
            'restored',
            ALGEBRA_RATIONAL_NEGATE_OPERATION,
            negative
        );
        const graph = builder.build([{ id: 'result', value: restored }]);
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine: exactEngine(),
            inputs: [{ id: 'value', value: '-2/3' }]
        });
        assert.equal(execution.nodes.length, 2);
        assert.equal(
            algebraRationalText(execution.outputs[0].value as never),
            '-2/3'
        );
    });

    it('executes ring-specific polynomial operations and graph nodes', async () => {
        const ring = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grevlex'
        );
        const operations = algebraPolynomialReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: [
                ...ALGEBRA_EXACT_REFERENCE_IMPLEMENTATIONS,
                ...operations.implementations
            ]
        });
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const sum = await computeAlgebraOperation({
            engine,
            operation: operations.add,
            input: { left: x, right: y }
        });
        const product = await computeAlgebraOperation({
            engine,
            operation: operations.multiply,
            input: { left: sum.value, right: sum.value },
            context: { limits: { fuel: 2, maximumOutputItems: 3 } }
        });
        assert.equal(
            algebraPolynomialText(product.value),
            '1*x^2 + 2*x*y + 1*y^2'
        );

        const builder = createAlgebraComputationGraphBuilder(
            'fixture.reference.polynomial-double-negate',
            'v1'
        );
        const source = builder.input('value', operations.polynomialSchema);
        const negative = builder.operation('negative', operations.negate, source);
        const restored = builder.operation('restored', operations.negate, negative);
        const graph = builder.build([{ id: 'result', value: restored }]);
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine,
            inputs: [{ id: 'value', value: sum.value }]
        });
        assert.ok(algebraPolynomialEquals(
            execution.outputs[0].value as typeof sum.value,
            sum.value
        ));
    });

    it('executes polynomial power and division with bounded output', async () => {
        const ring = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'lex'
        );
        const operations = algebraPolynomialReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const sum = algebraPolynomialAdd(x, y);
        const square = await computeAlgebraOperation({
            engine,
            operation: operations.power,
            input: { base: sum, exponent: 2n },
            context: { limits: { fuel: 2, maximumOutputItems: 3 } }
        });
        assert.ok(algebraPolynomialEquals(
            square.value,
            algebraPolynomialPower(sum, 2n)
        ));
        const division = await computeAlgebraOperation({
            engine,
            operation: operations.divide,
            input: {
                dividend: square.value,
                divisors: [sum],
                maximumSteps: 10
            },
            context: { limits: { fuel: 10, maximumOutputItems: 2 } }
        });
        assert.equal(division.value.quotients.length, 1);
        assert.ok(algebraPolynomialEquals(division.value.quotients[0], sum));
        assert.equal(algebraPolynomialText(division.value.remainder), '0');
        assert.ok(algebraPolynomialEquals(
            algebraPolynomialMultiply(division.value.quotients[0], sum),
            square.value
        ));
    });

    it('wraps polynomial output-limit failures at engine and graph boundaries', async () => {
        const ring = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grevlex'
        );
        const operations = algebraPolynomialReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation: operations.multiply,
                input: {
                    left: algebraPolynomialAdd(x, y),
                    right: algebraPolynomialAdd(x, y)
                },
                context: { limits: { fuel: 2, maximumOutputItems: 2 } }
            }),
            engineError('ENGINE_FAILURE', 'IMPLEMENTATION_FAILURE')
        );

        const builder = createAlgebraComputationGraphBuilder(
            'fixture.reference.graph-failure',
            'v1'
        );
        const input = builder.input('value', operations.polynomialSchema);
        const node = builder.operation('negative', operations.negate, input);
        const graph = builder.build([{ id: 'result', value: node }]);
        await assert.rejects(
            executeAlgebraComputationGraph({
                graph,
                engine: createAlgebraTypeScriptReferenceEngine({
                    implementations: []
                }),
                inputs: [{ id: 'value', value: x }]
            }),
            error => {
                assert.ok(error instanceof AlgebraGraphError);
                assert.equal(error.code, 'NODE_EXECUTION_FAILED');
                assert.ok(error.underlying instanceof AlgebraEngineError);
                assert.equal(error.underlying.code, 'UNSUPPORTED_OPERATION');
                return true;
            }
        );
    });
});
