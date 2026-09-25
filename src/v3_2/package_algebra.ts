/**
 * Curated browser-safe computational entry: exact rational polynomials,
 * ideal membership and approximate plane-curve samples.
 *
 * Reuses the existing parent/arithmetic owners without importing Core,
 * formal adoption, external transports or a visualization library. A checked
 * coefficient identity is exact arithmetic evidence, not a kernel proof.
 */

export {
    RATIONAL_DOMAIN, RATIONAL_FIELD, algebraRational, AlgebraExactError
} from './algebra_exact';
export type {
    AlgebraRational, AlgebraRationalField, AlgebraRationalInput
} from './algebra_exact';
export {
    ALGEBRA_POLYNOMIAL_PROFILE, AlgebraPolynomialError,
    algebraPolynomial, algebraPolynomialRing, algebraPolynomialVariable,
    algebraPolynomialConstant, algebraPolynomialZero, algebraPolynomialOne,
    algebraPolynomialAdd, algebraPolynomialNegate, algebraPolynomialSubtract,
    algebraPolynomialMultiply, algebraPolynomialPower, algebraPolynomialEquals,
    algebraPolynomialText, algebraPolynomialSchema, serializeAlgebraPolynomial
} from './algebra_polynomial';
export type {
    AlgebraMonomialOrder, AlgebraPolynomial, AlgebraPolynomialRing,
    AlgebraPolynomialTerm, AlgebraPolynomialTermInput
} from './algebra_polynomial';
export {
    ALGEBRA_IDEAL_PROFILE, AlgebraIdealError,
    algebraPolynomialIdeal, algebraGroebnerBasis, algebraIdealMembership
} from './algebra_ideal';
export type {
    AlgebraPolynomialIdeal, AlgebraGroebnerBasis, AlgebraGroebnerOptions,
    AlgebraIdealMembership
} from './algebra_ideal';
export {
    AlgebraIdealWitnessError, algebraIdealWitnessSource,
    normalizeAlgebraIdealWitnessInput, checkAlgebraIdealWitness
} from './algebra_ideal_witness';
export type {
    AlgebraIdealWitnessInput, AlgebraIdealWitness, AlgebraRationalPolynomial,
    AlgebraRationalPolynomialRing, AlgebraRationalPolynomialIdeal
} from './algebra_ideal_witness';
export { ALGEBRA_CURVE_VIEWPORT, sampleAlgebraPolynomialCurves } from './algebra_polynomial_plot';
export type { AlgebraCurveViewport } from './algebra_polynomial_plot';
