/** Focused CAS-POLY-2B sparse-polynomial tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { AlgebraEngineError } from '../src/v3_2/algebra_engine';
import {
    AlgebraExactError,
    AlgebraRationalInput,
    INTEGER_DOMAIN,
    RATIONAL_DOMAIN,
    algebraRationalText
} from '../src/v3_2/algebra_exact';
import {
    ALGEBRA_POLYNOMIAL_PROFILE,
    AlgebraPolynomial,
    AlgebraPolynomialError,
    algebraPolynomial,
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialDivide,
    algebraPolynomialEquals,
    algebraPolynomialFromMonomial,
    algebraPolynomialLeadingTerm,
    algebraPolynomialMultiply,
    algebraPolynomialNegate,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialSchema,
    algebraPolynomialSubstitute,
    algebraPolynomialSubtract,
    algebraPolynomialText,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    compareAlgebraMonomials,
    serializeAlgebraPolynomial,
    validateAlgebraPolynomial
} from '../src/v3_2/algebra_polynomial';

const polynomialError = (
    expected: AlgebraPolynomialError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraPolynomialError);
    assert.equal(error.code, expected);
    return true;
};

const Qxy = () => algebraPolynomialRing(
    RATIONAL_DOMAIN,
    ['x', 'y'],
    'grevlex'
);

describe('v3.2 focused sparse polynomial algebra', () => {
    it('defines immutable structural polynomial parents and monomial orders', () => {
        const lex = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const grlex = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grlex'
        );
        const grevlex = Qxy();
        assert.notEqual(lex.identity.id, grlex.identity.id);
        assert.notEqual(grlex.identity.id, grevlex.identity.id);
        assert.deepEqual(grevlex.variables, ['x', 'y']);
        assert.equal(grevlex.coefficientDomain, RATIONAL_DOMAIN);
        assert.ok(Object.isFrozen(grevlex));
        assert.ok(Object.isFrozen(grevlex.variables));
        assert.throws(
            () => algebraPolynomialRing(
                RATIONAL_DOMAIN,
                ['x', 'x'],
                'lex'
            ),
            polynomialError('DUPLICATE_VARIABLE')
        );
        assert.throws(
            () => algebraPolynomialRing(
                RATIONAL_DOMAIN,
                ['not-valid!'],
                'lex'
            ),
            polynomialError('INVALID_VARIABLE')
        );
        assert.throws(
            () => algebraPolynomialRing(
                RATIONAL_DOMAIN,
                Array.from(
                    { length: ALGEBRA_POLYNOMIAL_PROFILE.maximumVariables + 1 },
                    (_, index) => `x${index}`
                ),
                'lex'
            ),
            polynomialError('POLYNOMIAL_LIMIT_EXCEEDED')
        );
    });

    it('canonicalizes sparse terms, combines duplicates, removes zero, and sorts', () => {
        const ring = Qxy();
        const polynomial = algebraPolynomial(ring, [
            { coefficient: '1', exponents: [1n, 0n] },
            { coefficient: '2', exponents: ['1', '0'] },
            { coefficient: '-3', exponents: [1n, 0n] },
            { coefficient: '0', exponents: [0n, 9n] },
            { coefficient: '5/2', exponents: [0n, 2n] },
            { coefficient: '1', exponents: [2n, 0n] }
        ]);
        assert.equal(polynomial.terms.length, 2);
        assert.deepEqual(polynomial.terms[0].monomial.exponents, [2n, 0n]);
        assert.deepEqual(polynomial.terms[1].monomial.exponents, [0n, 2n]);
        assert.equal(
            algebraRationalText(polynomial.terms[1].coefficient),
            '5/2'
        );
        assert.equal(algebraPolynomialText(polynomial), '1*x^2 + 5/2*y^2');
        assert.ok(Object.isFrozen(polynomial));
        assert.ok(Object.isFrozen(polynomial.terms));
        assert.ok(Object.isFrozen(polynomial.terms[0].monomial.exponents));
    });

    it('implements lexicographic and graded order distinctions', () => {
        const lex = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const grlex = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grlex'
        );
        const x2Lex = algebraPolynomialFromMonomial(lex, '1', [2n, 0n]);
        const y3Lex = algebraPolynomialFromMonomial(lex, '1', [0n, 3n]);
        const x2Grlex = algebraPolynomialFromMonomial(grlex, '1', [2n, 0n]);
        const y3Grlex = algebraPolynomialFromMonomial(grlex, '1', [0n, 3n]);
        assert.equal(compareAlgebraMonomials(
            'lex',
            algebraPolynomialLeadingTerm(x2Lex)!.monomial,
            algebraPolynomialLeadingTerm(y3Lex)!.monomial
        ), 1);
        assert.equal(compareAlgebraMonomials(
            'grlex',
            algebraPolynomialLeadingTerm(x2Grlex)!.monomial,
            algebraPolynomialLeadingTerm(y3Grlex)!.monomial
        ), -1);

        const three = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y', 'z'],
            'grlex'
        );
        const xy2 = algebraPolynomialFromMonomial(three, '1', [1n, 2n, 0n]);
        const x2z = algebraPolynomialFromMonomial(three, '1', [2n, 0n, 1n]);
        assert.equal(compareAlgebraMonomials(
            'grlex',
            algebraPolynomialLeadingTerm(xy2)!.monomial,
            algebraPolynomialLeadingTerm(x2z)!.monomial
        ), -1);
        assert.equal(compareAlgebraMonomials(
            'grevlex',
            algebraPolynomialLeadingTerm(xy2)!.monomial,
            algebraPolynomialLeadingTerm(x2z)!.monomial
        ), 1);
    });

    it('constructs zero, one, constants, and variables with strict bounds', () => {
        const ring = Qxy();
        assert.equal(algebraPolynomialText(algebraPolynomialZero(ring)), '0');
        assert.equal(algebraPolynomialText(algebraPolynomialOne(ring)), '1');
        assert.equal(
            algebraPolynomialText(algebraPolynomialConstant(ring, '-3/2')),
            '-3/2'
        );
        assert.equal(
            algebraPolynomialText(algebraPolynomialVariable(ring, 0)),
            '1*x'
        );
        assert.equal(
            algebraPolynomialText(algebraPolynomialVariable(ring, 1)),
            '1*y'
        );
        assert.throws(
            () => algebraPolynomialVariable(ring, 2),
            polynomialError('VARIABLE_OUT_OF_RANGE')
        );
        assert.throws(
            () => algebraPolynomialFromMonomial(ring, '1', [1n]),
            polynomialError('INVALID_EXPONENT')
        );
        assert.throws(
            () => algebraPolynomialFromMonomial(ring, '1', [-1n, 0n]),
            polynomialError('INVALID_EXPONENT')
        );
        assert.throws(
            () => algebraPolynomialFromMonomial(
                ring,
                '1',
                [1 as never, 0n]
            ),
            polynomialError('INVALID_EXPONENT')
        );
    });

    it('computes ring arithmetic and canonical cancellation', () => {
        const ring = Qxy();
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const sum = algebraPolynomialAdd(x, y);
        const square = algebraPolynomialPower(sum, 2n);
        assert.equal(
            algebraPolynomialText(square),
            '1*x^2 + 2*x*y + 1*y^2'
        );
        assert.ok(algebraPolynomialEquals(
            algebraPolynomialMultiply(sum, sum),
            square
        ));
        assert.ok(algebraPolynomialEquals(
            algebraPolynomialSubtract(square, square),
            algebraPolynomialZero(ring)
        ));
        assert.equal(
            algebraPolynomialText(algebraPolynomialNegate(sum)),
            '-1*x + -1*y'
        );
        assert.equal(algebraPolynomialText(algebraPolynomialPower(x, 0n)), '1');
        assert.throws(
            () => algebraPolynomialPower(x, -1n),
            polynomialError('NEGATIVE_EXPONENT')
        );
    });

    it('uses the same sparse implementation over integer coefficients', () => {
        const ring = algebraPolynomialRing(INTEGER_DOMAIN, ['t'], 'lex');
        const t = algebraPolynomialVariable(ring, 0);
        const polynomial = algebraPolynomialMultiply(
            algebraPolynomialAdd(t, algebraPolynomialConstant(ring, '2')),
            algebraPolynomialSubtract(t, algebraPolynomialConstant(ring, '2'))
        );
        assert.equal(algebraPolynomialText(polynomial), '1*t^2 + -4');
        assert.throws(
            () => algebraPolynomialDivide(polynomial, [t]),
            polynomialError('NON_FIELD_COEFFICIENTS')
        );
    });

    it('rejects arithmetic across structurally different polynomial rings', () => {
        const grevlex = Qxy();
        const lex = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const left = algebraPolynomialVariable(grevlex, 0);
        const right = algebraPolynomialVariable(lex, 0);
        assert.throws(
            () => algebraPolynomialAdd(left, right as never),
            polynomialError('FOREIGN_POLYNOMIAL_RING')
        );
    });

    it('normalizes polynomial schema input and rejects inexact coefficients', () => {
        const ring = Qxy();
        const schema = algebraPolynomialSchema(ring);
        const normalized = schema.normalize({
            terms: [
                { coefficient: '2/4', exponents: ['1', '0'] },
                { coefficient: '1/2', exponents: [1n, 0n] }
            ]
        }, 'value');
        assert.equal(algebraPolynomialText(normalized), '1*x');
        assert.ok(Object.isFrozen(normalized));
        assert.throws(
            () => schema.normalize({
                terms: [{ coefficient: 0.5, exponents: [0n, 0n] }]
            }, 'value'),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.equal(error.code, 'INVALID_SCHEMA_VALUE');
                assert.ok(error.underlying instanceof AlgebraExactError);
                return true;
            }
        );
        const reconstructed = validateAlgebraPolynomial(ring, normalized);
        assert.ok(algebraPolynomialEquals(reconstructed, normalized));
    });

    it('serializes canonical terms without JSON bigint values', () => {
        const ring = Qxy();
        const polynomial = algebraPolynomial(ring, [
            { coefficient: '-3/2', exponents: [12n, 0n] },
            { coefficient: '1', exponents: [0n, 0n] }
        ]);
        const serialized = serializeAlgebraPolynomial(polynomial);
        const parsed = JSON.parse(serialized) as {
            serializationRevision: string;
            parent: { variables: string[]; monomialOrder: string };
            terms: { coefficient: string; exponents: string[] }[];
        };
        assert.equal(
            parsed.serializationRevision,
            ALGEBRA_POLYNOMIAL_PROFILE.serializationRevision
        );
        assert.deepEqual(parsed.parent.variables, ['x', 'y']);
        assert.equal(parsed.parent.monomialOrder, 'grevlex');
        assert.deepEqual(parsed.terms, [
            { coefficient: '-3/2', exponents: ['12', '0'] },
            { coefficient: '1', exponents: ['0', '0'] }
        ]);
        assert.ok(serialized.endsWith('\n'));
    });

    it('substitutes variables by polynomials in the same ring', () => {
        const ring = Qxy();
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const polynomial = algebraPolynomialAdd(x, y);
        const substituted = algebraPolynomialSubstitute(polynomial, [
            y,
            algebraPolynomialPower(x, 2n)
        ]);
        assert.equal(algebraPolynomialText(substituted), '1*x^2 + 1*y');
        assert.throws(
            () => algebraPolynomialSubstitute(polynomial, [x]),
            polynomialError('SUBSTITUTION_ARITY_MISMATCH')
        );
    });

    it('performs ordered multivariate division and reconstructs the dividend', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const divisor = algebraPolynomialAdd(x, y);
        const dividend = algebraPolynomialAdd(
            algebraPolynomialAdd(
                algebraPolynomialPower(x, 2n),
                algebraPolynomialMultiply(x, y)
            ),
            algebraPolynomialPower(y, 2n)
        );
        const division = algebraPolynomialDivide(dividend, [divisor]);
        assert.equal(algebraPolynomialText(division.quotients[0]), '1*x');
        assert.equal(algebraPolynomialText(division.remainder), '1*y^2');
        assert.ok(division.steps > 0);
        const reconstructed = algebraPolynomialAdd(
            algebraPolynomialMultiply(division.quotients[0], divisor),
            division.remainder
        );
        assert.ok(algebraPolynomialEquals(reconstructed, dividend));

        const empty = algebraPolynomialDivide(dividend, []);
        assert.equal(empty.quotients.length, 0);
        assert.ok(algebraPolynomialEquals(empty.remainder, dividend));
    });

    it('rejects zero divisors and exhausted division budgets', () => {
        const ring = Qxy();
        const x = algebraPolynomialVariable(ring, 0);
        assert.throws(
            () => algebraPolynomialDivide(x, [algebraPolynomialZero(ring)]),
            polynomialError('ZERO_DIVISOR')
        );
        assert.throws(
            () => algebraPolynomialDivide(
                algebraPolynomialAdd(x, algebraPolynomialOne(ring)),
                [],
                1
            ),
            polynomialError('POLYNOMIAL_LIMIT_EXCEEDED')
        );
    });

    it('supports a zero-variable polynomial ring as canonical constants', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [], 'lex');
        const constant = algebraPolynomial(ring, [{
            coefficient: '3/4' as AlgebraRationalInput,
            exponents: []
        }]);
        assert.equal(algebraPolynomialText(constant), '3/4');
        assert.throws(
            () => algebraPolynomialVariable(ring, 0),
            polynomialError('VARIABLE_OUT_OF_RANGE')
        );
    });
});
