/** Parent-aware sparse multivariate polynomials for the focused CAS. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent,
    defineAlgebraParent,
    validateAlgebraParent
} from './algebra_parent';
import {
    AlgebraCommutativeRingDomain,
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';

export const ALGEBRA_POLYNOMIAL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-v1' as const,
    serializationRevision: 'emdash-algebra-polynomial-json-v1' as const,
    representation: 'sparse-descending-canonical-terms' as const,
    maximumVariables: 1_024,
    maximumTerms: 1_000_000,
    maximumTermProducts: 2_000_000,
    maximumDivisionSteps: 1_000_000,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialErrorCode =
    | 'INVALID_RING'
    | 'INVALID_VARIABLE'
    | 'DUPLICATE_VARIABLE'
    | 'INVALID_MONOMIAL_ORDER'
    | 'INVALID_EXPONENT'
    | 'INVALID_TERM'
    | 'INVALID_POLYNOMIAL'
    | 'FOREIGN_POLYNOMIAL_RING'
    | 'VARIABLE_OUT_OF_RANGE'
    | 'NEGATIVE_EXPONENT'
    | 'NON_FIELD_COEFFICIENTS'
    | 'ZERO_DIVISOR'
    | 'SUBSTITUTION_ARITY_MISMATCH'
    | 'POLYNOMIAL_LIMIT_EXCEEDED';

export class AlgebraPolynomialError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialError';
    }
}

const fail = (
    code: AlgebraPolynomialErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraPolynomialError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const VARIABLE = /^[A-Za-z][A-Za-z0-9_]*$/u;

export type AlgebraMonomialOrder = 'lex' | 'grlex' | 'grevlex';

export interface AlgebraMonomial {
    readonly exponents: readonly bigint[];
}

export type AlgebraExponentInput = bigint | string;

export interface AlgebraPolynomialRing<
    CoefficientParent extends AlgebraParent,
    Coefficient extends AlgebraElement<CoefficientParent>,
    CoefficientInput
> extends AlgebraParent<'polynomial-ring'> {
    readonly coefficientDomain: AlgebraCommutativeRingDomain<
        CoefficientParent,
        Coefficient,
        CoefficientInput
    >;
    readonly variables: readonly string[];
    readonly monomialOrder: AlgebraMonomialOrder;
}

export interface AlgebraPolynomialTerm<
    CoefficientParent extends AlgebraParent,
    Coefficient extends AlgebraElement<CoefficientParent>
> {
    readonly coefficient: Coefficient;
    readonly monomial: AlgebraMonomial;
}

export interface AlgebraPolynomialTermInput<CoefficientInput, Coefficient> {
    readonly coefficient: CoefficientInput | Coefficient;
    readonly exponents: readonly AlgebraExponentInput[];
}

export interface AlgebraPolynomial<
    CoefficientParent extends AlgebraParent,
    Coefficient extends AlgebraElement<CoefficientParent>,
    CoefficientInput
> extends AlgebraElement<AlgebraPolynomialRing<
        CoefficientParent,
        Coefficient,
        CoefficientInput
    >> {
    readonly kind: 'algebra-polynomial';
    readonly terms: readonly AlgebraPolynomialTerm<
        CoefficientParent,
        Coefficient
    >[];
}

const assertMonomialOrder = (
    value: unknown,
    path: string
): AlgebraMonomialOrder => {
    if (value === 'lex' || value === 'grlex' || value === 'grevlex') {
        return value;
    }
    return fail(
        'INVALID_MONOMIAL_ORDER',
        path,
        'Expected lex, grlex, or grevlex monomial order'
    );
};

const assertCoefficientDomain = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    value: unknown,
    path: string
): AlgebraCommutativeRingDomain<P, C, I> => {
    if (
        !record(value) ||
        value.kind !== 'commutative-ring-domain' ||
        !record(value.parent) ||
        !record(value.schema) ||
        typeof value.normalize !== 'function' ||
        typeof value.add !== 'function' ||
        typeof value.negate !== 'function' ||
        typeof value.subtract !== 'function' ||
        typeof value.multiply !== 'function' ||
        typeof value.power !== 'function' ||
        typeof value.equals !== 'function' ||
        typeof value.isZero !== 'function' ||
        typeof value.isOne !== 'function' ||
        typeof value.text !== 'function'
    ) {
        return fail(
            'INVALID_RING',
            path,
            'Expected one operational commutative-ring domain'
        );
    }
    validateAlgebraParent(value.parent, `${path}.parent`);
    return value as unknown as AlgebraCommutativeRingDomain<P, C, I>;
};

const ringStructuralId = (
    coefficientParent: AlgebraParent,
    variables: readonly string[],
    order: AlgebraMonomialOrder
): string => [
    'algebra.polynomial-ring',
    coefficientParent.identity.id,
    order,
    variables.length === 0 ? 'constant' : variables.join('.')
].join('/');

export function algebraPolynomialRing<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    coefficientDomainInput: AlgebraCommutativeRingDomain<P, C, I>,
    variableInput: readonly string[],
    monomialOrderInput: AlgebraMonomialOrder = 'grevlex'
): AlgebraPolynomialRing<P, C, I> {
    const coefficientDomain = assertCoefficientDomain<P, C, I>(
        coefficientDomainInput,
        'polynomialRing.coefficientDomain'
    );
    if (!Array.isArray(variableInput)) {
        return fail(
            'INVALID_VARIABLE',
            'polynomialRing.variables',
            'Polynomial variables must be an array'
        );
    }
    if (variableInput.length > ALGEBRA_POLYNOMIAL_PROFILE.maximumVariables) {
        return fail(
            'POLYNOMIAL_LIMIT_EXCEEDED',
            'polynomialRing.variables',
            `Polynomial ring exceeds ` +
                `${ALGEBRA_POLYNOMIAL_PROFILE.maximumVariables} variables`
        );
    }
    const variables = variableInput.map((variable, index) => {
        if (typeof variable !== 'string' || !VARIABLE.test(variable)) {
            return fail(
                'INVALID_VARIABLE',
                `polynomialRing.variables[${index}]`,
                'Variable must use portable identifier spelling'
            );
        }
        return variable;
    });
    const seen = new Set<string>();
    variables.forEach((variable, index) => {
        if (seen.has(variable)) {
            fail(
                'DUPLICATE_VARIABLE',
                `polynomialRing.variables[${index}]`,
                `Duplicate polynomial variable '${variable}'`
            );
        }
        seen.add(variable);
    });
    const monomialOrder = assertMonomialOrder(
        monomialOrderInput,
        'polynomialRing.monomialOrder'
    );
    const parent = defineAlgebraParent(
        'polynomial-ring',
        ringStructuralId(coefficientDomain.parent, variables, monomialOrder),
        `v1.${coefficientDomain.parent.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        coefficientDomain,
        variables: Object.freeze(variables),
        monomialOrder
    });
}

const samePolynomialRing = (
    left: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>,
    right: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>
): boolean => sameAlgebraParent(left, right);

const exponentValue = (
    input: AlgebraExponentInput,
    path: string
): bigint => {
    if (typeof input === 'bigint') {
        if (input >= 0n) return input;
        return fail(
            'INVALID_EXPONENT',
            path,
            'Monomial exponent must be nonnegative'
        );
    }
    if (
        typeof input === 'string' &&
        /^(?:0|[1-9][0-9]*)$/u.test(input)
    ) {
        return BigInt(input);
    }
    return fail(
        'INVALID_EXPONENT',
        path,
        'Monomial exponent must be bigint or canonical natural-number text'
    );
};

const normalizeMonomial = (
    exponentsInput: readonly AlgebraExponentInput[],
    variableCount: number,
    path: string
): AlgebraMonomial => {
    if (!Array.isArray(exponentsInput) || exponentsInput.length !== variableCount) {
        return fail(
            'INVALID_EXPONENT',
            path,
            `Monomial requires exactly ${variableCount} exponents`
        );
    }
    return Object.freeze({
        exponents: Object.freeze(exponentsInput.map((value, index) =>
            exponentValue(value, `${path}[${index}]`)
        ))
    });
};

const monomialKey = (monomial: AlgebraMonomial): string =>
    monomial.exponents.map(value => value.toString(10)).join(',');

const monomialDegree = (monomial: AlgebraMonomial): bigint =>
    monomial.exponents.reduce((sum, value) => sum + value, 0n);

export const compareAlgebraMonomials = (
    order: AlgebraMonomialOrder,
    left: AlgebraMonomial,
    right: AlgebraMonomial
): -1 | 0 | 1 => {
    if (left.exponents.length !== right.exponents.length) {
        return fail(
            'INVALID_EXPONENT',
            'compareMonomials',
            'Cannot compare monomials from different arities'
        );
    }
    if (order !== 'lex') {
        const leftDegree = monomialDegree(left);
        const rightDegree = monomialDegree(right);
        if (leftDegree !== rightDegree) {
            return leftDegree < rightDegree ? -1 : 1;
        }
    }
    if (order === 'grevlex') {
        for (let index = left.exponents.length - 1; index >= 0; index--) {
            const leftValue = left.exponents[index];
            const rightValue = right.exponents[index];
            if (leftValue !== rightValue) {
                return leftValue < rightValue ? 1 : -1;
            }
        }
        return 0;
    }
    for (let index = 0; index < left.exponents.length; index++) {
        const leftValue = left.exponents[index];
        const rightValue = right.exponents[index];
        if (leftValue !== rightValue) return leftValue < rightValue ? -1 : 1;
    }
    return 0;
};

const monomialMultiply = (
    left: AlgebraMonomial,
    right: AlgebraMonomial
): AlgebraMonomial => Object.freeze({
    exponents: Object.freeze(left.exponents.map((value, index) =>
        value + right.exponents[index]
    ))
});

const monomialDivides = (
    divisor: AlgebraMonomial,
    dividend: AlgebraMonomial
): boolean => divisor.exponents.every((value, index) =>
    value <= dividend.exponents[index]
);

const monomialQuotient = (
    dividend: AlgebraMonomial,
    divisor: AlgebraMonomial
): AlgebraMonomial => Object.freeze({
    exponents: Object.freeze(dividend.exponents.map((value, index) =>
        value - divisor.exponents[index]
    ))
});

const assertPolynomialRing = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    path: string
): AlgebraPolynomialRing<P, C, I> => {
    if (
        !record(ring) ||
        ring.kind !== 'polynomial-ring' ||
        !Array.isArray(ring.variables) ||
        ring.variables.length > ALGEBRA_POLYNOMIAL_PROFILE.maximumVariables
    ) {
        return fail(
            'INVALID_RING',
            path,
            'Expected one polynomial ring'
        );
    }
    const parent = validateAlgebraParent(ring, path, 'polynomial-ring');
    const coefficientDomain = assertCoefficientDomain(
        ring.coefficientDomain,
        `${path}.coefficientDomain`
    );
    const monomialOrder = assertMonomialOrder(
        ring.monomialOrder,
        `${path}.monomialOrder`
    );
    const seen = new Set<string>();
    ring.variables.forEach((variable, index) => {
        if (typeof variable !== 'string' || !VARIABLE.test(variable)) {
            fail(
                'INVALID_VARIABLE',
                `${path}.variables[${index}]`,
                'Variable must use portable identifier spelling'
            );
        }
        if (seen.has(variable)) {
            fail(
                'DUPLICATE_VARIABLE',
                `${path}.variables[${index}]`,
                `Duplicate polynomial variable '${variable}'`
            );
        }
        seen.add(variable);
    });
    const expectedId = ringStructuralId(
        coefficientDomain.parent,
        ring.variables,
        monomialOrder
    );
    const expectedRevision = `v1.${coefficientDomain.parent.identity.revision}`;
    if (
        parent.identity.id !== expectedId ||
        parent.identity.revision !== expectedRevision
    ) {
        return fail(
            'INVALID_RING',
            `${path}.identity`,
            'Polynomial parent identity does not match its structural data'
        );
    }
    return ring;
};

const assertPolynomialParent = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    polynomial: AlgebraPolynomial<P, C, I>,
    ring: AlgebraPolynomialRing<P, C, I>,
    path: string
): void => {
    if (!samePolynomialRing(
        polynomial.parent as unknown as AlgebraPolynomialRing<
            AlgebraParent,
            AlgebraElement,
            unknown
        >,
        ring as unknown as AlgebraPolynomialRing<
            AlgebraParent,
            AlgebraElement,
            unknown
        >
    )) {
        fail(
            'FOREIGN_POLYNOMIAL_RING',
            `${path}.parent`,
            `Expected polynomial ring '${ring.identity.id}'`
        );
    }
};

export function algebraPolynomial<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ringInput: AlgebraPolynomialRing<P, C, I>,
    termInputs: readonly AlgebraPolynomialTermInput<I, C>[]
): AlgebraPolynomial<P, C, I> {
    const ring = assertPolynomialRing(ringInput, 'polynomial.parent');
    if (!Array.isArray(termInputs)) {
        return fail(
            'INVALID_POLYNOMIAL',
            'polynomial.terms',
            'Polynomial terms must be an array'
        );
    }
    if (termInputs.length > ALGEBRA_POLYNOMIAL_PROFILE.maximumTerms) {
        return fail(
            'POLYNOMIAL_LIMIT_EXCEEDED',
            'polynomial.terms',
            `Polynomial exceeds ${ALGEBRA_POLYNOMIAL_PROFILE.maximumTerms} terms`
        );
    }
    const combined = new Map<string, {
        monomial: AlgebraMonomial;
        coefficient: C;
    }>();
    termInputs.forEach((term, index) => {
        if (!record(term) || !Array.isArray(term.exponents)) {
            fail(
                'INVALID_TERM',
                `polynomial.terms[${index}]`,
                'Polynomial term requires coefficient and exponent array'
            );
        }
        const monomial = normalizeMonomial(
            term.exponents,
            ring.variables.length,
            `polynomial.terms[${index}].exponents`
        );
        const coefficient = ring.coefficientDomain.normalize(term.coefficient);
        const key = monomialKey(monomial);
        const previous = combined.get(key);
        combined.set(key, {
            monomial,
            coefficient: previous === undefined
                ? coefficient
                : ring.coefficientDomain.add(
                    previous.coefficient,
                    coefficient
                )
        });
    });
    const terms = [...combined.values()]
        .filter(term => !ring.coefficientDomain.isZero(term.coefficient))
        .sort((left, right) => -compareAlgebraMonomials(
            ring.monomialOrder,
            left.monomial,
            right.monomial
        ))
        .map(term => Object.freeze({
            coefficient: term.coefficient,
            monomial: term.monomial
        }));
    return Object.freeze({
        kind: 'algebra-polynomial',
        parent: ring,
        terms: Object.freeze(terms)
    });
}

export function validateAlgebraPolynomial<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path = 'polynomial'
): AlgebraPolynomial<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-polynomial' ||
        !Array.isArray(value.terms)
    ) {
        return fail(
            'INVALID_POLYNOMIAL',
            path,
            'Expected one sparse algebra polynomial'
        );
    }
    assertPolynomialParent(
        value as unknown as AlgebraPolynomial<P, C, I>,
        ring,
        path
    );
    return algebraPolynomial(ring, value.terms.map((term, index) => {
        if (
            !record(term) ||
            !record(term.monomial) ||
            !Array.isArray(term.monomial.exponents)
        ) {
            return fail(
                'INVALID_TERM',
                `${path}.terms[${index}]`,
                'Polynomial term has an invalid canonical shape'
            );
        }
        return {
            coefficient: term.coefficient as I | C,
            exponents: term.monomial.exponents as AlgebraExponentInput[]
        };
    }));
}

export function algebraPolynomialSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraRuntimeSchema<AlgebraPolynomial<P, C, I>> {
    assertPolynomialRing(ring, 'polynomialSchema.ring');
    return defineAlgebraRuntimeSchema({
        id: `algebra.polynomial/${ring.identity.id}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                record(value) &&
                value.kind === 'algebra-polynomial'
            ) {
                return validateAlgebraPolynomial(ring, value, path);
            }
            if (record(value) && Array.isArray(value.terms)) {
                return algebraPolynomial(
                    ring,
                    value.terms as AlgebraPolynomialTermInput<I, C>[]
                );
            }
            return fail(
                'INVALID_POLYNOMIAL',
                path,
                'Polynomial schema expects a polynomial or term record'
            );
        }
    });
}

export const algebraPolynomialZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>): AlgebraPolynomial<P, C, I> =>
    algebraPolynomial(ring, []);

export const algebraPolynomialConstant = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    coefficient: I | C
): AlgebraPolynomial<P, C, I> => algebraPolynomial(ring, [{
    coefficient,
    exponents: ring.variables.map(() => 0n)
}]);

export const algebraPolynomialOne = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>): AlgebraPolynomial<P, C, I> =>
    algebraPolynomialConstant(ring, ring.coefficientDomain.one);

export const algebraPolynomialVariable = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    index: number
): AlgebraPolynomial<P, C, I> => {
    if (!Number.isSafeInteger(index) || index < 0 || index >= ring.variables.length) {
        return fail(
            'VARIABLE_OUT_OF_RANGE',
            'variable.index',
            `Variable index must lie in [0, ${ring.variables.length})`
        );
    }
    const exponents = ring.variables.map((_, position) =>
        position === index ? 1n : 0n
    );
    return algebraPolynomial(ring, [{
        coefficient: ring.coefficientDomain.one,
        exponents
    }]);
};

export const algebraPolynomialFromMonomial = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    coefficient: I | C,
    exponents: readonly AlgebraExponentInput[]
): AlgebraPolynomial<P, C, I> => algebraPolynomial(ring, [{
    coefficient,
    exponents
}]);

const pairInSameRing = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    right: AlgebraPolynomial<P, C, I>,
    path: string
): AlgebraPolynomialRing<P, C, I> => {
    const ring = assertPolynomialRing(left.parent, `${path}.left.parent`);
    assertPolynomialParent(right, ring, `${path}.right`);
    return ring;
};

const termInputs = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(polynomial: AlgebraPolynomial<P, C, I>): AlgebraPolynomialTermInput<I, C>[] =>
    polynomial.terms.map(term => ({
        coefficient: term.coefficient,
        exponents: term.monomial.exponents
    }));

export const algebraPolynomialAdd = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    right: AlgebraPolynomial<P, C, I>
): AlgebraPolynomial<P, C, I> => {
    const ring = pairInSameRing(left, right, 'add');
    return algebraPolynomial(ring, [
        ...termInputs(left),
        ...termInputs(right)
    ]);
};

export const algebraPolynomialNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(polynomial: AlgebraPolynomial<P, C, I>): AlgebraPolynomial<P, C, I> => {
    const ring = assertPolynomialRing(polynomial.parent, 'negate.parent');
    return algebraPolynomial(ring, polynomial.terms.map(term => ({
        coefficient: ring.coefficientDomain.negate(term.coefficient),
        exponents: term.monomial.exponents
    })));
};

export const algebraPolynomialSubtract = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    right: AlgebraPolynomial<P, C, I>
): AlgebraPolynomial<P, C, I> => algebraPolynomialAdd(
    left,
    algebraPolynomialNegate(right)
);

export const algebraPolynomialMultiply = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    right: AlgebraPolynomial<P, C, I>
): AlgebraPolynomial<P, C, I> => {
    const ring = pairInSameRing(left, right, 'multiply');
    const products = left.terms.length * right.terms.length;
    if (products > ALGEBRA_POLYNOMIAL_PROFILE.maximumTermProducts) {
        return fail(
            'POLYNOMIAL_LIMIT_EXCEEDED',
            'multiply',
            `Polynomial multiplication exceeds ` +
                `${ALGEBRA_POLYNOMIAL_PROFILE.maximumTermProducts} term products`
        );
    }
    const terms: AlgebraPolynomialTermInput<I, C>[] = [];
    left.terms.forEach(leftTerm => {
        right.terms.forEach(rightTerm => {
            terms.push({
                coefficient: ring.coefficientDomain.multiply(
                    leftTerm.coefficient,
                    rightTerm.coefficient
                ),
                exponents: monomialMultiply(
                    leftTerm.monomial,
                    rightTerm.monomial
                ).exponents
            });
        });
    });
    return algebraPolynomial(ring, terms);
};

export const algebraPolynomialPower = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    baseInput: AlgebraPolynomial<P, C, I>,
    exponentInput: bigint
): AlgebraPolynomial<P, C, I> => {
    if (typeof exponentInput !== 'bigint' || exponentInput < 0n) {
        return fail(
            'NEGATIVE_EXPONENT',
            'power.exponent',
            'Polynomial exponent must be a nonnegative bigint'
        );
    }
    const ring = assertPolynomialRing(baseInput.parent, 'power.base.parent');
    let base = baseInput;
    let exponent = exponentInput;
    let result = algebraPolynomialOne(ring);
    while (exponent > 0n) {
        if ((exponent & 1n) === 1n) {
            result = algebraPolynomialMultiply(result, base);
        }
        exponent >>= 1n;
        if (exponent > 0n) base = algebraPolynomialMultiply(base, base);
    }
    return result;
};

export const algebraPolynomialEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomial<P, C, I>,
    right: AlgebraPolynomial<P, C, I>
): boolean => {
    const ring = pairInSameRing(left, right, 'equals');
    return left.terms.length === right.terms.length &&
        left.terms.every((term, index) => {
            const other = right.terms[index];
            return monomialKey(term.monomial) === monomialKey(other.monomial) &&
                ring.coefficientDomain.equals(
                    term.coefficient,
                    other.coefficient
                );
        });
};

export const algebraPolynomialLeadingTerm = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(polynomial: AlgebraPolynomial<P, C, I>):
    | AlgebraPolynomialTerm<P, C>
    | undefined => polynomial.terms[0];

const monomialText = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    monomial: AlgebraMonomial
): string => {
    const factors = monomial.exponents.flatMap((exponent, index) => {
        if (exponent === 0n) return [];
        return [exponent === 1n
            ? ring.variables[index]
            : `${ring.variables[index]}^${exponent.toString(10)}`];
    });
    return factors.length === 0 ? '1' : factors.join('*');
};

export const algebraPolynomialText = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(polynomial: AlgebraPolynomial<P, C, I>): string => {
    const ring = assertPolynomialRing(polynomial.parent, 'text.parent');
    if (polynomial.terms.length === 0) return '0';
    return polynomial.terms.map(term => {
        const coefficient = ring.coefficientDomain.text(term.coefficient);
        const monomial = monomialText(ring, term.monomial);
        return monomial === '1' ? coefficient : `${coefficient}*${monomial}`;
    }).join(' + ');
};

export const serializeAlgebraPolynomial = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(polynomial: AlgebraPolynomial<P, C, I>): string => {
    const ring = assertPolynomialRing(polynomial.parent, 'serialize.parent');
    return `${JSON.stringify({
        serializationRevision:
            ALGEBRA_POLYNOMIAL_PROFILE.serializationRevision,
        kind: 'algebra-polynomial',
        parent: {
            id: ring.identity.id,
            revision: ring.identity.revision,
            coefficientParent: {
                id: ring.coefficientDomain.parent.identity.id,
                revision: ring.coefficientDomain.parent.identity.revision
            },
            variables: ring.variables,
            monomialOrder: ring.monomialOrder
        },
        terms: polynomial.terms.map(term => ({
            coefficient: ring.coefficientDomain.text(term.coefficient),
            exponents: term.monomial.exponents.map(value => value.toString(10))
        }))
    })}\n`;
};

export const algebraPolynomialSubstitute = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    polynomial: AlgebraPolynomial<P, C, I>,
    replacementInput: readonly AlgebraPolynomial<P, C, I>[]
): AlgebraPolynomial<P, C, I> => {
    const ring = assertPolynomialRing(polynomial.parent, 'substitute.parent');
    if (
        !Array.isArray(replacementInput) ||
        replacementInput.length !== ring.variables.length
    ) {
        return fail(
            'SUBSTITUTION_ARITY_MISMATCH',
            'substitute.replacements',
            `Expected ${ring.variables.length} replacement polynomials`
        );
    }
    const replacements = replacementInput.map((value, index) => {
        assertPolynomialParent(value, ring, `substitute.replacements[${index}]`);
        return value;
    });
    let result = algebraPolynomialZero(ring);
    polynomial.terms.forEach(term => {
        let expanded = algebraPolynomialConstant(ring, term.coefficient);
        term.monomial.exponents.forEach((exponent, index) => {
            if (exponent !== 0n) {
                expanded = algebraPolynomialMultiply(
                    expanded,
                    algebraPolynomialPower(replacements[index], exponent)
                );
            }
        });
        result = algebraPolynomialAdd(result, expanded);
    });
    return result;
};

export interface AlgebraPolynomialDivision<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly quotients: readonly AlgebraPolynomial<P, C, I>[];
    readonly remainder: AlgebraPolynomial<P, C, I>;
    readonly steps: number;
}

const fieldDomain = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraFieldDomain<P, C, I> => {
    const domain = ring.coefficientDomain as Partial<
        AlgebraFieldDomain<P, C, I>
    >;
    if (
        domain.field !== true ||
        typeof domain.divide !== 'function' ||
        typeof domain.inverse !== 'function'
    ) {
        return fail(
            'NON_FIELD_COEFFICIENTS',
            'division.parent.coefficientDomain',
            'Multivariate division requires an operational field domain'
        );
    }
    return domain as AlgebraFieldDomain<P, C, I>;
};

export const algebraPolynomialDivide = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    dividendInput: AlgebraPolynomial<P, C, I>,
    divisorInput: readonly AlgebraPolynomial<P, C, I>[],
    maximumSteps: number = ALGEBRA_POLYNOMIAL_PROFILE.maximumDivisionSteps
): AlgebraPolynomialDivision<P, C, I> => {
    const ring = assertPolynomialRing(
        dividendInput.parent,
        'division.dividend.parent'
    );
    const field = fieldDomain(ring);
    if (!Array.isArray(divisorInput)) {
        return fail(
            'INVALID_POLYNOMIAL',
            'division.divisors',
            'Polynomial divisors must be an array'
        );
    }
    if (!Number.isSafeInteger(maximumSteps) || maximumSteps <= 0) {
        return fail(
            'POLYNOMIAL_LIMIT_EXCEEDED',
            'division.maximumSteps',
            'Division step limit must be a positive safe integer'
        );
    }
    const divisors = divisorInput.map((divisor, index) => {
        assertPolynomialParent(divisor, ring, `division.divisors[${index}]`);
        if (divisor.terms.length === 0) {
            return fail(
                'ZERO_DIVISOR',
                `division.divisors[${index}]`,
                'Polynomial divisor must be nonzero'
            );
        }
        return divisor;
    });
    const quotients = divisors.map(() => algebraPolynomialZero(ring));
    let remainder = algebraPolynomialZero(ring);
    let current = dividendInput;
    let steps = 0;

    while (current.terms.length > 0) {
        if (steps >= maximumSteps) {
            return fail(
                'POLYNOMIAL_LIMIT_EXCEEDED',
                'division.steps',
                `Polynomial division exceeded ${maximumSteps} steps`
            );
        }
        steps++;
        const currentLead = current.terms[0];
        let reduced = false;
        for (let index = 0; index < divisors.length; index++) {
            const divisorLead = divisors[index].terms[0];
            if (!monomialDivides(divisorLead.monomial, currentLead.monomial)) {
                continue;
            }
            const quotientTerm = algebraPolynomialFromMonomial(
                ring,
                field.divide(
                    currentLead.coefficient,
                    divisorLead.coefficient
                ),
                monomialQuotient(
                    currentLead.monomial,
                    divisorLead.monomial
                ).exponents
            );
            quotients[index] = algebraPolynomialAdd(
                quotients[index],
                quotientTerm
            );
            current = algebraPolynomialSubtract(
                current,
                algebraPolynomialMultiply(quotientTerm, divisors[index])
            );
            reduced = true;
            break;
        }
        if (!reduced) {
            const leadingPolynomial = algebraPolynomialFromMonomial(
                ring,
                currentLead.coefficient,
                currentLead.monomial.exponents
            );
            remainder = algebraPolynomialAdd(remainder, leadingPolynomial);
            current = algebraPolynomialSubtract(current, leadingPolynomial);
        }
    }
    return Object.freeze({
        quotients: Object.freeze(quotients),
        remainder,
        steps
    });
};
