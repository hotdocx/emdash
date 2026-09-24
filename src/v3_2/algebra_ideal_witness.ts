/** Positive ideal membership checked by arithmetic in the original parent. */

import {
    AlgebraRational, AlgebraRationalField, AlgebraRationalInput, RATIONAL_FIELD
} from './algebra_exact';
import { sameAlgebraParent } from './algebra_parent';
import {
    AlgebraPolynomial, AlgebraPolynomialRing, algebraPolynomialAdd,
    algebraPolynomialEquals, algebraPolynomialMultiply, algebraPolynomialSchema,
    algebraPolynomialZero, serializeAlgebraPolynomial
} from './algebra_polynomial';
import {
    AlgebraPolynomialIdeal, algebraPolynomialIdeal
} from './algebra_ideal';

export type AlgebraRationalPolynomial = AlgebraPolynomial<
    AlgebraRationalField, AlgebraRational, AlgebraRationalInput
>;
export type AlgebraRationalPolynomialRing = AlgebraPolynomialRing<
    AlgebraRationalField, AlgebraRational, AlgebraRationalInput
>;
export type AlgebraRationalPolynomialIdeal = AlgebraPolynomialIdeal<
    AlgebraRationalField, AlgebraRational, AlgebraRationalInput
>;

export interface AlgebraIdealWitnessInput {
    readonly ideal: AlgebraRationalPolynomialIdeal;
    readonly polynomial: AlgebraRationalPolynomial;
}

export interface AlgebraIdealWitness {
    /** Exact canonical source contents, not a backend handle or proof hash. */
    readonly source: string;
    readonly coefficients: readonly AlgebraRationalPolynomial[];
}

export class AlgebraIdealWitnessError extends Error {
    constructor(
        public readonly code: 'INVALID_INPUT' | 'STALE_SOURCE' | 'INVALID_WITNESS',
        message: string
    ) {
        super(message);
        this.name = 'AlgebraIdealWitnessError';
    }
}

export function normalizeAlgebraIdealWitnessInput(
    input: AlgebraIdealWitnessInput
): AlgebraIdealWitnessInput {
    if (!input?.ideal?.ring || !Array.isArray(input.ideal.generators) ||
        !sameAlgebraParent(input.ideal.ring.coefficientDomain.parent, RATIONAL_FIELD)) {
        throw new AlgebraIdealWitnessError('INVALID_INPUT',
            'This witness adapter requires a polynomial ideal over Q');
    }
    const ring = input.ideal.ring;
    return Object.freeze({
        ideal: algebraPolynomialIdeal(ring, input.ideal.generators),
        polynomial: algebraPolynomialSchema(ring).normalize(input.polynomial, 'witness.polynomial')
    });
}

/** Reuses the polynomial owner's full parent/coefficient/term encoding. */
export function algebraIdealWitnessSource(input: AlgebraIdealWitnessInput): string {
    const normalized = normalizeAlgebraIdealWitnessInput(input);
    return JSON.stringify({
        revision: 'emdash-ideal-witness-input-v1',
        polynomial: serializeAlgebraPolynomial(normalized.polynomial),
        generators: normalized.ideal.generators.map(serializeAlgebraPolynomial)
    });
}

/** No Gröbner algorithm or external result is trusted by this finite check. */
export function checkAlgebraIdealWitness(
    input: AlgebraIdealWitnessInput,
    witness: AlgebraIdealWitness
) {
    const normalized = normalizeAlgebraIdealWitnessInput(input);
    const source = algebraIdealWitnessSource(normalized);
    if (witness?.source !== source) {
        throw new AlgebraIdealWitnessError('STALE_SOURCE',
            'Witness does not belong to these exact ordered generators and query');
    }
    if (!Array.isArray(witness.coefficients) ||
        witness.coefficients.length !== normalized.ideal.generators.length) {
        throw new AlgebraIdealWitnessError('INVALID_WITNESS',
            'One coefficient is required for each original ideal generator');
    }
    const ring = normalized.ideal.ring;
    const schema = algebraPolynomialSchema(ring);
    const coefficients = Object.freeze(witness.coefficients.map((value, index) =>
        schema.normalize(value, `witness.coefficients[${index}]`)));
    const combination = coefficients.reduce((sum, coefficient, index) =>
        algebraPolynomialAdd(sum, algebraPolynomialMultiply(
            coefficient, normalized.ideal.generators[index]
        )), algebraPolynomialZero(ring));
    if (!algebraPolynomialEquals(combination, normalized.polynomial)) {
        throw new AlgebraIdealWitnessError('INVALID_WITNESS',
            'The coefficient combination does not equal the requested polynomial');
    }
    return Object.freeze({
        authority: 'exact-polynomial-arithmetic' as const,
        source,
        coefficients,
        combination
    });
}
