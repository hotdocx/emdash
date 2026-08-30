/** Focused CAS-EXACT-2A exact-domain tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraEngineError,
    algebraAlgorithmIdentity,
    algebraEngineIdentity,
    algebraEngineSupported,
    defineAlgebraEngine
} from '../src/v3_2/algebra_engine';
import {
    AlgebraParentError,
    assertAlgebraParent,
    defineAlgebraParent,
    sameAlgebraParent,
    validateAlgebraParent
} from '../src/v3_2/algebra_parent';
import {
    ALGEBRA_EXACT_PROFILE,
    ALGEBRA_INTEGER_SCHEMA,
    ALGEBRA_RATIONAL_SCHEMA,
    AlgebraExactError,
    AlgebraIntegerInput,
    AlgebraRational,
    INTEGER_RING,
    INTEGER_DOMAIN,
    RATIONAL_FIELD,
    RATIONAL_DOMAIN,
    algebraInteger,
    algebraIntegerAdd,
    algebraIntegerCompare,
    algebraIntegerDivRem,
    algebraIntegerEquals,
    algebraIntegerGcd,
    algebraIntegerMultiply,
    algebraIntegerNegate,
    algebraIntegerPower,
    algebraIntegerSubtract,
    algebraIntegerText,
    algebraIntegerToRational,
    algebraRational,
    algebraRationalAdd,
    algebraRationalCompare,
    algebraRationalDivide,
    algebraRationalEquals,
    algebraRationalFromIntegers,
    algebraRationalInverse,
    algebraRationalMultiply,
    algebraRationalNegate,
    algebraRationalPower,
    algebraRationalSubtract,
    algebraRationalText,
    serializeAlgebraInteger,
    serializeAlgebraRational
} from '../src/v3_2/algebra_exact';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph,
    serializeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';

const exactError = (
    expected: AlgebraExactError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraExactError);
    assert.equal(error.code, expected);
    return true;
};

describe('v3.2 focused exact algebra domains', () => {
    it('defines immutable role-distinct integer and rational parents', () => {
        assert.equal(INTEGER_RING.kind, 'integer-ring');
        assert.equal(RATIONAL_FIELD.kind, 'rational-field');
        assert.equal(
            sameAlgebraParent(INTEGER_RING, RATIONAL_FIELD),
            false
        );
        assert.ok(Object.isFrozen(INTEGER_RING));
        assert.ok(Object.isFrozen(INTEGER_RING.identity));
        assert.deepEqual(validateAlgebraParent(INTEGER_RING), INTEGER_RING);
        assert.equal(
            assertAlgebraParent(INTEGER_RING, INTEGER_RING),
            INTEGER_RING
        );
        assert.throws(
            () => assertAlgebraParent(RATIONAL_FIELD, INTEGER_RING),
            error => {
                assert.ok(error instanceof AlgebraParentError);
                assert.equal(error.code, 'FOREIGN_PARENT');
                return true;
            }
        );
        assert.throws(
            () => defineAlgebraParent('Not Valid', 'fixture.parent', 'v1'),
            error => {
                assert.ok(error instanceof AlgebraParentError);
                assert.equal(error.code, 'INVALID_PARENT');
                return true;
            }
        );
    });

    it('constructs canonical bigint-backed integers and rejects numbers', () => {
        assert.equal(algebraInteger(123n).value, 123n);
        assert.equal(algebraInteger('-45').value, -45n);
        assert.equal(algebraInteger('0').value, 0n);
        assert.equal(algebraIntegerText('-45'), '-45');
        assert.ok(Object.isFrozen(algebraInteger(1n)));
        for (const invalid of ['+1', '01', '-0', '1.0', ' 1']) {
            assert.throws(
                () => algebraInteger(invalid),
                exactError('INVALID_INTEGER')
            );
        }
        assert.throws(
            () => algebraInteger(1 as unknown as AlgebraIntegerInput),
            exactError('INVALID_INTEGER')
        );
        assert.equal(ALGEBRA_EXACT_PROFILE.acceptsJavascriptNumber, false);
    });

    it('computes exact integer arithmetic, order, gcd, and powers', () => {
        assert.equal(algebraIntegerAdd('12', '-5').value, 7n);
        assert.equal(algebraIntegerSubtract('12', '-5').value, 17n);
        assert.equal(algebraIntegerMultiply('-7', '6').value, -42n);
        assert.equal(algebraIntegerNegate('-8').value, 8n);
        assert.equal(algebraIntegerPower('-3', 5n).value, -243n);
        assert.equal(algebraIntegerPower('0', 0n).value, 1n);
        assert.equal(algebraIntegerGcd('-84', '30').value, 6n);
        assert.equal(algebraIntegerGcd('0', '0').value, 0n);
        assert.equal(algebraIntegerEquals('7', 7n), true);
        assert.equal(algebraIntegerCompare('-1', '0'), -1);
        assert.equal(algebraIntegerCompare('2', '2'), 0);
        assert.equal(algebraIntegerCompare('3', '2'), 1);
        assert.throws(
            () => algebraIntegerPower('2', -1n),
            exactError('NEGATIVE_EXPONENT')
        );
    });

    it('uses Euclidean integer division for every divisor sign', () => {
        const cases = [
            ['7', '3', 2n, 1n],
            ['-7', '3', -3n, 2n],
            ['7', '-3', -2n, 1n],
            ['-7', '-3', 3n, 2n]
        ] as const;
        for (const [dividend, divisor, quotient, remainder] of cases) {
            const result = algebraIntegerDivRem(dividend, divisor);
            assert.equal(result.quotient.value, quotient);
            assert.equal(result.remainder.value, remainder);
            assert.equal(
                BigInt(divisor) * result.quotient.value +
                    result.remainder.value,
                BigInt(dividend)
            );
            assert.ok(result.remainder.value >= 0n);
            assert.ok(result.remainder.value < (
                BigInt(divisor) < 0n ? -BigInt(divisor) : BigInt(divisor)
            ));
        }
        assert.throws(
            () => algebraIntegerDivRem('1', '0'),
            exactError('DIVISION_BY_ZERO')
        );
    });

    it('normalizes rational signs, gcds, zero, and integer coercions', () => {
        assert.deepEqual(
            algebraRationalFromIntegers('6', '-8'),
            {
                kind: 'algebra-rational',
                parent: RATIONAL_FIELD,
                numerator: -3n,
                denominator: 4n
            }
        );
        assert.equal(algebraRationalText('2/4'), '1/2');
        assert.equal(algebraRationalText('-10/15'), '-2/3');
        assert.equal(algebraRationalText('0/9'), '0');
        assert.equal(algebraRationalText(9n), '9');
        assert.equal(algebraIntegerToRational('-4').numerator, -4n);
        assert.equal(algebraIntegerToRational('-4').denominator, 1n);
        assert.ok(Object.isFrozen(algebraRational('1/2')));
    });

    it('computes exact rational field arithmetic and order', () => {
        assert.equal(algebraRationalText(
            algebraRationalAdd('1/6', '1/3')
        ), '1/2');
        assert.equal(algebraRationalText(
            algebraRationalSubtract('1/6', '1/3')
        ), '-1/6');
        assert.equal(algebraRationalText(
            algebraRationalMultiply('-2/3', '9/10')
        ), '-3/5');
        assert.equal(algebraRationalText(
            algebraRationalDivide('3/4', '-2/5')
        ), '-15/8');
        assert.equal(algebraRationalText(
            algebraRationalNegate('-7/9')
        ), '7/9');
        assert.equal(algebraRationalText(
            algebraRationalInverse('-7/9')
        ), '-9/7');
        assert.equal(algebraRationalText(
            algebraRationalPower('-2/3', 4n)
        ), '16/81');
        assert.equal(algebraRationalEquals('2/4', '1/2'), true);
        assert.equal(algebraRationalCompare('-1/2', '-1/3'), -1);
        assert.equal(algebraRationalCompare('2/6', '1/3'), 0);
        assert.equal(algebraRationalCompare('5/4', '1'), 1);
    });

    it('rejects zero denominators, zero inverse, numbers, and bad text', () => {
        assert.throws(
            () => algebraRationalFromIntegers('1', '0'),
            exactError('ZERO_DENOMINATOR')
        );
        assert.throws(
            () => algebraRationalInverse('0'),
            exactError('DIVISION_BY_ZERO')
        );
        assert.throws(
            () => algebraRationalPower('2', -1n),
            exactError('NEGATIVE_EXPONENT')
        );
        assert.throws(
            () => algebraRational('1/-2'),
            exactError('INVALID_RATIONAL')
        );
        assert.throws(
            () => algebraRational('01/2'),
            exactError('INVALID_RATIONAL')
        );
        assert.throws(
            () => algebraRational(1 as never),
            exactError('INVALID_RATIONAL')
        );
    });

    it('rejects structurally plausible values with foreign parents', () => {
        const foreignRational = Object.freeze({
            kind: 'algebra-rational',
            parent: INTEGER_RING,
            numerator: 1n,
            denominator: 2n
        }) as unknown as AlgebraRational;
        assert.throws(
            () => algebraRational(foreignRational),
            exactError('FOREIGN_PARENT')
        );
    });

    it('serializes exact values without JSON bigint ambiguity', () => {
        assert.deepEqual(JSON.parse(serializeAlgebraInteger('-123')), {
            serializationRevision:
                ALGEBRA_EXACT_PROFILE.serializationRevision,
            kind: 'algebra-integer',
            parent: {
                id: INTEGER_RING.identity.id,
                revision: INTEGER_RING.identity.revision
            },
            value: '-123'
        });
        assert.deepEqual(JSON.parse(serializeAlgebraRational('-6/8')), {
            serializationRevision:
                ALGEBRA_EXACT_PROFILE.serializationRevision,
            kind: 'algebra-rational',
            parent: {
                id: RATIONAL_FIELD.identity.id,
                revision: RATIONAL_FIELD.identity.revision
            },
            numerator: '-3',
            denominator: '4'
        });
        assert.ok(serializeAlgebraInteger('1').endsWith('\n'));
        assert.ok(serializeAlgebraRational('1/2').endsWith('\n'));
    });

    it('normalizes through runtime schemas and rejects inexact numbers', () => {
        assert.equal(ALGEBRA_INTEGER_SCHEMA.normalize('42', 'value').value, 42n);
        assert.equal(
            ALGEBRA_RATIONAL_SCHEMA.normalize(
                { numerator: '12', denominator: '18' },
                'value'
            ).numerator,
            2n
        );
        assert.throws(
            () => ALGEBRA_INTEGER_SCHEMA.normalize(42, 'value'),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.equal(error.code, 'INVALID_SCHEMA_VALUE');
                assert.ok(error.underlying instanceof AlgebraExactError);
                return true;
            }
        );
        assert.throws(
            () => ALGEBRA_RATIONAL_SCHEMA.normalize(0.5, 'value'),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.equal(error.code, 'INVALID_SCHEMA_VALUE');
                return true;
            }
        );
    });

    it('flows exact values through a topology-only graph without engine work', async () => {
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.exact.identity',
            'v1'
        );
        const value = builder.input('value', ALGEBRA_RATIONAL_SCHEMA);
        const graph = builder.build([{ id: 'result', value }]);
        const engineIdentity = algebraEngineIdentity(
            'fixture.exact.unused-engine',
            'v1'
        );
        const engine = defineAlgebraEngine({
            id: engineIdentity.id,
            revision: engineIdentity.revision,
            support(operation) {
                return algebraEngineSupported({
                    operation: operation.identity,
                    engine: engineIdentity,
                    algorithms: [algebraAlgorithmIdentity(
                        'fixture.exact.unused',
                        'v1'
                    )]
                });
            },
            async compute() {
                throw new Error('input-only graph must not compute');
            }
        });
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine,
            inputs: [{ id: 'value', value: '-10/15' }]
        });
        assert.equal(execution.nodes.length, 0);
        assert.equal(
            algebraRationalText(execution.outputs[0].value as AlgebraRational),
            '-2/3'
        );
        const topology = serializeAlgebraComputationGraph(graph);
        assert.ok(topology.includes('algebra.exact.rational'));
        assert.equal(topology.includes('-10/15'), false);
    });

    it('exposes immutable operational domains for later polynomial engines', () => {
        assert.equal(INTEGER_DOMAIN.parent, INTEGER_RING);
        assert.equal(INTEGER_DOMAIN.schema, ALGEBRA_INTEGER_SCHEMA);
        assert.equal(INTEGER_DOMAIN.zero.value, 0n);
        assert.equal(INTEGER_DOMAIN.one.value, 1n);
        assert.equal(INTEGER_DOMAIN.multiply('12', '-3').value, -36n);
        assert.equal(INTEGER_DOMAIN.isZero('0'), true);
        assert.equal(INTEGER_DOMAIN.isOne('1'), true);
        assert.equal(INTEGER_DOMAIN.text('-9'), '-9');

        assert.equal(RATIONAL_DOMAIN.parent, RATIONAL_FIELD);
        assert.equal(RATIONAL_DOMAIN.field, true);
        assert.equal(RATIONAL_DOMAIN.add('1/2', '1/3').numerator, 5n);
        assert.equal(RATIONAL_DOMAIN.add('1/2', '1/3').denominator, 6n);
        assert.equal(RATIONAL_DOMAIN.divide('2/3', '4/5').numerator, 5n);
        assert.equal(RATIONAL_DOMAIN.divide('2/3', '4/5').denominator, 6n);
        assert.equal(RATIONAL_DOMAIN.isZero('0/7'), true);
        assert.equal(RATIONAL_DOMAIN.isOne('9/9'), true);
        assert.ok(Object.isFrozen(INTEGER_DOMAIN));
        assert.ok(Object.isFrozen(RATIONAL_DOMAIN));
    });
});
