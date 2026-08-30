/** Canonical polynomial quotient rings and exact quotient elements. */

import {
    AlgebraElement,
    AlgebraParent,
    defineAlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraGroebnerBasis,
    AlgebraGroebnerOptions,
    AlgebraIdealMembership,
    AlgebraPolynomialIdeal,
    algebraGroebnerBasis,
    algebraIdealMembership,
    algebraReducedGroebnerBasis
} from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialAdd,
    algebraPolynomialEquals,
    algebraPolynomialMultiply,
    algebraPolynomialNegate,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialSchema,
    algebraPolynomialText,
    algebraPolynomialZero,
    validateAlgebraPolynomial
} from './algebra_polynomial';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';

export const ALGEBRA_QUOTIENT_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-quotient-ring-v1' as const,
    serializationRevision: 'emdash-polynomial-quotient-json-v1' as const,
    normalForm: 'reduced-groebner-remainder' as const,
    identityOwner: 'polynomial-ring-and-reduced-basis' as const,
    orderedDomain: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuotientErrorCode =
    | 'INVALID_QUOTIENT_RING'
    | 'FOREIGN_POLYNOMIAL_RING'
    | 'FOREIGN_QUOTIENT_RING'
    | 'NEGATIVE_EXPONENT'
    | 'INVALID_QUOTIENT_ELEMENT';

export class AlgebraQuotientError extends Error {
    constructor(
        public readonly code: AlgebraQuotientErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuotientError';
    }
}

const fail = (
    code: AlgebraQuotientErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraQuotientError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export interface AlgebraPolynomialQuotientRing<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraParent<'polynomial-quotient-ring'> {
    readonly polynomialRing: AlgebraPolynomialRing<P, C, I>;
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
}

export interface AlgebraQuotientElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraElement<AlgebraPolynomialQuotientRing<P, C, I>> {
    readonly kind: 'algebra-quotient-element';
    readonly representative: AlgebraPolynomial<P, C, I>;
}

export interface AlgebraQuotientReduction<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-quotient-reduction';
    readonly quotient: AlgebraPolynomialQuotientRing<P, C, I>;
    readonly input: AlgebraPolynomial<P, C, I>;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
    readonly membership: AlgebraIdealMembership<P, C, I>;
    readonly representative: AlgebraPolynomial<P, C, I>;
}

const hexText = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0'))
    .join('');

const basisFingerprint = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    basis: AlgebraGroebnerBasis<P, C, I>
): string => basis.basis.length === 0
    ? 'zero'
    : basis.basis.map(polynomial => polynomial.terms.length === 0
        ? 'z'
        : polynomial.terms.map(term =>
            `c${hexText(polynomial.parent.coefficientDomain.text(term.coefficient))}` +
            `e${term.monomial.exponents.join('.')}`
        ).join('_')
    ).join('--');

export function algebraPolynomialQuotientRing<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraPolynomialQuotientRing<P, C, I> {
    const basis = algebraReducedGroebnerBasis(algebraGroebnerBasis(ideal, options));
    const parent = defineAlgebraParent(
        'polynomial-quotient-ring',
        `algebra.polynomial-quotient/${ideal.ring.identity.id}/` +
            basisFingerprint(basis),
        `v1.${ideal.ring.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        polynomialRing: ideal.ring,
        ideal,
        basis
    });
}

export function algebraQuotientReduce<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    quotient: AlgebraPolynomialQuotientRing<P, C, I>,
    polynomialInput: AlgebraPolynomial<P, C, I>
): AlgebraQuotientReduction<P, C, I> {
    let input: AlgebraPolynomial<P, C, I>;
    try {
        input = validateAlgebraPolynomial(
            quotient.polynomialRing,
            polynomialInput,
            'quotientReduction.input'
        );
    } catch (error: unknown) {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            'quotientReduction.input',
            'Quotient reduction requires a polynomial in the source ring',
            error
        );
    }
    const membership = algebraIdealMembership(input, quotient.basis);
    return Object.freeze({
        kind: 'algebra-quotient-reduction',
        quotient,
        input,
        basis: quotient.basis,
        membership,
        representative: membership.remainder
    });
}

export function algebraQuotientElement<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    quotient: AlgebraPolynomialQuotientRing<P, C, I>,
    polynomial: AlgebraPolynomial<P, C, I>
): AlgebraQuotientElement<P, C, I> {
    return Object.freeze({
        kind: 'algebra-quotient-element',
        parent: quotient,
        representative: algebraQuotientReduce(quotient, polynomial).representative
    });
}

const sameQuotient = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraQuotientElement<P, C, I>,
    right: AlgebraQuotientElement<P, C, I>,
    path: string
): AlgebraPolynomialQuotientRing<P, C, I> => {
    if (!sameAlgebraParent(left.parent, right.parent)) {
        return fail(
            'FOREIGN_QUOTIENT_RING',
            path,
            'Quotient elements belong to different quotient parents'
        );
    }
    return left.parent;
};

export const algebraQuotientZero = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    quotient: AlgebraPolynomialQuotientRing<P, C, I>
): AlgebraQuotientElement<P, C, I> => algebraQuotientElement(
    quotient,
    algebraPolynomialZero(quotient.polynomialRing)
);

export const algebraQuotientOne = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    quotient: AlgebraPolynomialQuotientRing<P, C, I>
): AlgebraQuotientElement<P, C, I> => algebraQuotientElement(
    quotient,
    algebraPolynomialOne(quotient.polynomialRing)
);

export const algebraQuotientAdd = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraQuotientElement<P, C, I>,
    right: AlgebraQuotientElement<P, C, I>
): AlgebraQuotientElement<P, C, I> => algebraQuotientElement(
    sameQuotient(left, right, 'quotientAdd'),
    algebraPolynomialAdd(left.representative, right.representative)
);

export const algebraQuotientNegate = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraQuotientElement<P, C, I>
): AlgebraQuotientElement<P, C, I> => algebraQuotientElement(
    value.parent,
    algebraPolynomialNegate(value.representative)
);

export const algebraQuotientMultiply = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraQuotientElement<P, C, I>,
    right: AlgebraQuotientElement<P, C, I>
): AlgebraQuotientElement<P, C, I> => algebraQuotientElement(
    sameQuotient(left, right, 'quotientMultiply'),
    algebraPolynomialMultiply(left.representative, right.representative)
);

export function algebraQuotientPower<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraQuotientElement<P, C, I>,
    exponent: bigint
): AlgebraQuotientElement<P, C, I> {
    if (typeof exponent !== 'bigint' || exponent < 0n) {
        return fail(
            'NEGATIVE_EXPONENT',
            'quotientPower.exponent',
            'Quotient-ring exponent must be a nonnegative bigint'
        );
    }
    return algebraQuotientElement(
        value.parent,
        algebraPolynomialPower(value.representative, exponent)
    );
}

export const algebraQuotientEquals = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraQuotientElement<P, C, I>,
    right: AlgebraQuotientElement<P, C, I>
): boolean => sameAlgebraParent(left.parent, right.parent) &&
    algebraPolynomialEquals(left.representative, right.representative);

export const algebraQuotientText = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraQuotientElement<P, C, I>
): string => `[${algebraPolynomialText(value.representative)}]`;

export function algebraQuotientElementSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(quotient: AlgebraPolynomialQuotientRing<P, C, I>): AlgebraRuntimeSchema<
    AlgebraQuotientElement<P, C, I>
> {
    const polynomialSchema = algebraPolynomialSchema(quotient.polynomialRing);
    return defineAlgebraRuntimeSchema({
        id: `algebra.quotient-element/${quotient.identity.id}`,
        revision: quotient.identity.revision,
        normalize(value: unknown, path: string) {
            if (typeof value === 'object' && value !== null &&
                (value as { kind?: unknown }).kind === 'algebra-quotient-element') {
                const element = value as AlgebraQuotientElement<P, C, I>;
                if (!sameAlgebraParent(element.parent, quotient)) {
                    return fail(
                        'FOREIGN_QUOTIENT_RING',
                        `${path}.parent`,
                        'Quotient element belongs to a foreign parent'
                    );
                }
                return algebraQuotientElement(quotient, element.representative);
            }
            return algebraQuotientElement(
                quotient,
                polynomialSchema.normalize(value, path)
            );
        }
    });
}

export const serializeAlgebraQuotientElement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraQuotientElement<P, C, I>): string => `${JSON.stringify({
    serializationRevision: ALGEBRA_QUOTIENT_PROFILE.serializationRevision,
    kind: value.kind,
    parent: {
        id: value.parent.identity.id,
        revision: value.parent.identity.revision
    },
    representative: value.representative.terms.map(term => ({
        coefficient: value.parent.polynomialRing.coefficientDomain.text(
            term.coefficient
        ),
        exponents: term.monomial.exponents.map(exponent => exponent.toString(10))
    }))
})}\n`;
