/** Focused AFFINE-QUOTIENT-1A canonical quotient-ring tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { AlgebraIdealError, algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialMultiply,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    ALGEBRA_QUOTIENT_PROFILE,
    AlgebraQuotientError,
    algebraPolynomialQuotientRing,
    algebraQuotientAdd,
    algebraQuotientElement,
    algebraQuotientElementSchema,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientOne,
    algebraQuotientPower,
    algebraQuotientReduce,
    algebraQuotientText,
    algebraQuotientZero,
    serializeAlgebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraQuotientReferenceOperations } from '../src/v3_2/algebra_quotient_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';

const quotientError = (code: AlgebraQuotientError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraQuotientError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const x2 = algebraPolynomialPower(x, 2n);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [x2])
    );
    return { ring, x, x2, quotient };
};

describe('v3.2 canonical polynomial quotient rings', () => {
    it('normalizes equivalent representatives through one reduced basis', () => {
        const { x, x2, quotient } = fixture();
        const first = algebraQuotientElement(quotient, x);
        const second = algebraQuotientElement(
            quotient,
            algebraPolynomialAdd(x, x2)
        );
        assert.ok(algebraQuotientEquals(first, second));
        assert.equal(algebraQuotientText(first), '[1*x]');
        const reduction = algebraQuotientReduce(
            quotient,
            algebraPolynomialAdd(x, x2)
        );
        assert.equal(reduction.membership.coefficients.length, 1);
        assert.equal(reduction.membership.member, false);
        assert.equal(ALGEBRA_QUOTIENT_PROFILE.normalForm,
            'reduced-groebner-remainder');
        assert.ok(Object.isFrozen(quotient));
        assert.ok(Object.isFrozen(reduction));
    });

    it('computes nilpotent arithmetic in Q[x]/(x^2)', () => {
        const { x, quotient } = fixture();
        const value = algebraQuotientElement(quotient, x);
        assert.ok(algebraQuotientEquals(
            algebraQuotientMultiply(value, value),
            algebraQuotientZero(quotient)
        ));
        assert.ok(algebraQuotientEquals(
            algebraQuotientPower(value, 2n),
            algebraQuotientZero(quotient)
        ));
        assert.equal(
            algebraQuotientText(algebraQuotientAdd(value, algebraQuotientOne(quotient))),
            '[1*x + 1]'
        );
    });

    it('identifies quotient parents by canonical reduced bases', () => {
        const { ring, x2, quotient } = fixture();
        const scaled = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, [
            algebraPolynomialMultiply(algebraPolynomialConstant(ring, '2'), x2)
        ]));
        assert.equal(scaled.identity.id, quotient.identity.id);
        assert.ok(algebraQuotientEquals(
            algebraQuotientElement(scaled, algebraPolynomialVariable(ring, 0)),
            algebraQuotientElement(quotient, algebraPolynomialVariable(ring, 0)) as never
        ));
    });

    it('handles zero and unit ideals without special-case representations', () => {
        const { ring, x } = fixture();
        const zeroQuotient = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(ring, [])
        );
        assert.equal(algebraQuotientText(algebraQuotientElement(zeroQuotient, x)),
            '[1*x]');
        const unitQuotient = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(ring, [algebraPolynomialConstant(ring, '1')])
        );
        assert.ok(algebraQuotientEquals(
            algebraQuotientOne(unitQuotient),
            algebraQuotientZero(unitQuotient)
        ));
    });

    it('normalizes schemas and serializes exact representatives', () => {
        const { x, quotient } = fixture();
        const schema = algebraQuotientElementSchema(quotient);
        const value = schema.normalize(x, 'value');
        const restored = schema.normalize(value, 'value');
        assert.ok(algebraQuotientEquals(value, restored));
        const parsed = JSON.parse(serializeAlgebraQuotientElement(value));
        assert.equal(parsed.serializationRevision,
            ALGEBRA_QUOTIENT_PROFILE.serializationRevision);
        assert.deepEqual(parsed.representative, [{
            coefficient: '1',
            exponents: ['1']
        }]);
    });

    it('rejects foreign quotient parents and negative powers', () => {
        const { ring, x, quotient } = fixture();
        const otherRing = algebraPolynomialRing(RATIONAL_DOMAIN, ['y'], 'lex');
        assert.throws(
            () => algebraQuotientElement(
                quotient,
                algebraPolynomialVariable(otherRing, 0) as never
            ),
            quotientError('FOREIGN_POLYNOMIAL_RING')
        );
        assert.throws(
            () => algebraQuotientPower(algebraQuotientElement(quotient, x), -1n),
            quotientError('NEGATIVE_EXPONENT')
        );
        const other = algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(ring, [x])
        );
        assert.throws(
            () => algebraQuotientAdd(
                algebraQuotientElement(quotient, x),
                algebraQuotientElement(other, x)
            ),
            quotientError('FOREIGN_QUOTIENT_RING')
        );
    });

    it('executes normalization and arithmetic in retained graphs', async () => {
        const { x, quotient } = fixture();
        const operations = algebraQuotientReferenceOperations(quotient);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const normalizeBuilder = createAlgebraComputationGraphBuilder(
            'fixture.quotient.double-negate',
            'v1'
        );
        const polynomial = normalizeBuilder.input(
            'polynomial',
            operations.normalize.input
        );
        const normalized = normalizeBuilder.operation(
            'normalized',
            operations.normalize,
            polynomial
        );
        const negative = normalizeBuilder.operation(
            'negative',
            operations.negate,
            normalized
        );
        const restored = normalizeBuilder.operation(
            'restored',
            operations.negate,
            negative
        );
        const execution = await executeAlgebraComputationGraph({
            graph: normalizeBuilder.build([{ id: 'result', value: restored }]),
            engine,
            inputs: [{ id: 'polynomial', value: x }]
        });
        assert.ok(algebraQuotientEquals(
            execution.outputs[0].value as ReturnType<typeof algebraQuotientElement>,
            algebraQuotientElement(quotient, x)
        ));

        const multiplyBuilder = createAlgebraComputationGraphBuilder(
            'fixture.quotient.multiply',
            'v1'
        );
        const pair = multiplyBuilder.input('pair', operations.binarySchema);
        const product = multiplyBuilder.operation(
            'product',
            operations.multiply,
            pair
        );
        const productExecution = await executeAlgebraComputationGraph({
            graph: multiplyBuilder.build([{ id: 'result', value: product }]),
            engine,
            inputs: [{
                id: 'pair',
                value: {
                    left: algebraQuotientElement(quotient, x),
                    right: algebraQuotientElement(quotient, x)
                }
            }]
        });
        assert.ok(algebraQuotientEquals(
            productExecution.outputs[0].value as ReturnType<typeof algebraQuotientElement>,
            algebraQuotientZero(quotient)
        ));
    });

    it('propagates bounded and cancelled Groebner construction', () => {
        const { ring, x } = fixture();
        const generators = algebraPolynomialIdeal(ring, [
            algebraPolynomialPower(x, 2n),
            algebraPolynomialAdd(x, algebraPolynomialConstant(ring, '1'))
        ]);
        assert.throws(
            () => algebraPolynomialQuotientRing(generators, {
                context: { cancellation: { requested: () => true } }
            }),
            (error: unknown) => {
                assert.ok(error instanceof AlgebraIdealError);
                assert.equal(error.code, 'CANCELLED');
                return true;
            }
        );
    });
});
