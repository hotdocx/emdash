/** Elimination-based ideal operations for constructible affine geometry. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraGroebnerBasis,
    AlgebraGroebnerOptions,
    AlgebraIdealMembership,
    AlgebraPolynomialIdeal,
    algebraGroebnerBasis,
    algebraIdealMembership,
    algebraPolynomialIdeal
} from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomial,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    validateAlgebraPolynomial
} from './algebra_polynomial';

export const ALGEBRA_IDEAL_GEOMETRY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-ideal-geometry-v1' as const,
    intersection: 'one-variable-elimination' as const,
    saturation: 'rabinowitsch-principal-saturation' as const,
    radicalMembership: 'rabinowitsch-unit-membership' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraIdealGeometryErrorCode =
    | 'FOREIGN_IDEAL_RING'
    | 'FOREIGN_POLYNOMIAL_RING'
    | 'ELIMINATION_PROJECTION_FAILED';

export class AlgebraIdealGeometryError extends Error {
    constructor(
        public readonly code: AlgebraIdealGeometryErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraIdealGeometryError';
    }
}

const fail = (
    code: AlgebraIdealGeometryErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraIdealGeometryError(code, path, message);
};

const sameRing = (
    left: { readonly identity: { readonly id: string; readonly revision: string } },
    right: { readonly identity: { readonly id: string; readonly revision: string } }
): boolean => left.identity.id === right.identity.id &&
    left.identity.revision === right.identity.revision;

const assertIdealPair = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialIdeal<P, C, I>,
    right: AlgebraPolynomialIdeal<P, C, I>
): AlgebraPolynomialRing<P, C, I> => {
    if (!sameRing(left.ring, right.ring)) {
        return fail(
            'FOREIGN_IDEAL_RING',
            'idealGeometry.right',
            'Ideal operation requires one polynomial ring'
        );
    }
    return left.ring;
};

const assertElement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    element: AlgebraPolynomial<P, C, I>
): AlgebraPolynomial<P, C, I> => {
    try {
        return validateAlgebraPolynomial(ideal.ring, element, 'idealGeometry.element');
    } catch {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            'idealGeometry.element',
            'Ideal element belongs to a foreign polynomial ring'
        );
    }
};

export const algebraIdealSum = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialIdeal<P, C, I>,
    right: AlgebraPolynomialIdeal<P, C, I>
): AlgebraPolynomialIdeal<P, C, I> => algebraPolynomialIdeal(
        assertIdealPair(left, right),
        [...left.generators, ...right.generators]
    );

export const algebraIdealProduct = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialIdeal<P, C, I>,
    right: AlgebraPolynomialIdeal<P, C, I>
): AlgebraPolynomialIdeal<P, C, I> => algebraPolynomialIdeal(
        assertIdealPair(left, right),
        left.generators.flatMap(first => right.generators.map(second =>
            algebraPolynomialMultiply(first, second)
        ))
    );

export interface AlgebraIdealElimination<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly extendedRing: AlgebraPolynomialRing<P, C, I>;
    readonly eliminationVariable: string;
    readonly extendedIdeal: AlgebraPolynomialIdeal<P, C, I>;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
    readonly projectedIdeal: AlgebraPolynomialIdeal<P, C, I>;
}

const freshVariable = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    ring: AlgebraPolynomialRing<P, C, I>
): string => {
    let candidate = 'emdash_elim';
    let index = 0;
    while (ring.variables.includes(candidate)) candidate = `emdash_elim${++index}`;
    return candidate;
};

const embed = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    polynomial: AlgebraPolynomial<P, C, I>,
    extended: AlgebraPolynomialRing<P, C, I>
): AlgebraPolynomial<P, C, I> => algebraPolynomial(
        extended,
        polynomial.terms.map(term => ({
            coefficient: term.coefficient,
            exponents: [0n, ...term.monomial.exponents]
        }))
    );

const project = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    polynomial: AlgebraPolynomial<P, C, I>,
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraPolynomial<P, C, I> => {
    if (polynomial.terms.some(term => term.monomial.exponents[0] !== 0n)) {
        return fail(
            'ELIMINATION_PROJECTION_FAILED',
            'idealGeometry.project',
            'Cannot project a polynomial containing the elimination variable'
        );
    }
    return algebraPolynomial(ring, polynomial.terms.map(term => ({
        coefficient: term.coefficient,
        exponents: term.monomial.exponents.slice(1)
    })));
};

const eliminate = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    ring: AlgebraPolynomialRing<P, C, I>,
    generators: (
        extended: AlgebraPolynomialRing<P, C, I>,
        variable: AlgebraPolynomial<P, C, I>
    ) => readonly AlgebraPolynomial<P, C, I>[],
    options: AlgebraGroebnerOptions = {}
): AlgebraIdealElimination<P, C, I> => {
    const eliminationVariable = freshVariable(ring);
    const extendedRing = algebraPolynomialRing(
        ring.coefficientDomain,
        [eliminationVariable, ...ring.variables],
        'lex'
    );
    const extendedIdeal = algebraPolynomialIdeal(
        extendedRing,
        generators(extendedRing, algebraPolynomialVariable(extendedRing, 0))
    );
    const basis = algebraGroebnerBasis(extendedIdeal, options);
    const projectedIdeal = algebraPolynomialIdeal(
        ring,
        basis.basis
            .filter(polynomial => polynomial.terms.every(
                term => term.monomial.exponents[0] === 0n
            ))
            .map(polynomial => project(polynomial, ring))
    );
    return Object.freeze({
        extendedRing,
        eliminationVariable,
        extendedIdeal,
        basis,
        projectedIdeal
    });
};

export interface AlgebraIdealIntersection<P extends AlgebraParent, C extends AlgebraElement<P>, I>
    extends AlgebraIdealElimination<P, C, I> {
    readonly kind: 'algebra-ideal-intersection';
    readonly left: AlgebraPolynomialIdeal<P, C, I>;
    readonly right: AlgebraPolynomialIdeal<P, C, I>;
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
}

export function algebraIdealIntersection<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraPolynomialIdeal<P, C, I>,
    right: AlgebraPolynomialIdeal<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraIdealIntersection<P, C, I> {
    const ring = assertIdealPair(left, right);
    const elimination = eliminate(ring, (extended, variable) => {
        const oneMinus = algebraPolynomialSubtract(
            algebraPolynomialOne(extended),
            variable
        );
        return [
            ...left.generators.map(value =>
                algebraPolynomialMultiply(variable, embed(value, extended))
            ),
            ...right.generators.map(value =>
                algebraPolynomialMultiply(oneMinus, embed(value, extended))
            )
        ];
    }, options);
    return Object.freeze({
        kind: 'algebra-ideal-intersection',
        left,
        right,
        ...elimination,
        ideal: elimination.projectedIdeal
    });
}

export interface AlgebraIdealSaturation<P extends AlgebraParent, C extends AlgebraElement<P>, I>
    extends AlgebraIdealElimination<P, C, I> {
    readonly kind: 'algebra-ideal-saturation';
    readonly source: AlgebraPolynomialIdeal<P, C, I>;
    readonly element: AlgebraPolynomial<P, C, I>;
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
}

export function algebraIdealSaturate<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    source: AlgebraPolynomialIdeal<P, C, I>,
    elementInput: AlgebraPolynomial<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraIdealSaturation<P, C, I> {
    const element = assertElement(source, elementInput);
    const elimination = eliminate(source.ring, (extended, variable) => [
        ...source.generators.map(value => embed(value, extended)),
        algebraPolynomialSubtract(
            algebraPolynomialOne(extended),
            algebraPolynomialMultiply(variable, embed(element, extended))
        )
    ], options);
    return Object.freeze({
        kind: 'algebra-ideal-saturation',
        source,
        element,
        ...elimination,
        ideal: elimination.projectedIdeal
    });
}

export interface AlgebraIdealRadicalMembership<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly kind: 'algebra-ideal-radical-membership';
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly element: AlgebraPolynomial<P, C, I>;
    readonly elimination: AlgebraIdealElimination<P, C, I>;
    readonly unitMembership: AlgebraIdealMembership<P, C, I>;
    readonly member: boolean;
}

export function algebraIdealRadicalMembership<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    elementInput: AlgebraPolynomial<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraIdealRadicalMembership<P, C, I> {
    const element = assertElement(ideal, elementInput);
    const elimination = eliminate(ideal.ring, (extended, variable) => [
        ...ideal.generators.map(value => embed(value, extended)),
        algebraPolynomialSubtract(
            algebraPolynomialOne(extended),
            algebraPolynomialMultiply(variable, embed(element, extended))
        )
    ], options);
    const unitMembership = algebraIdealMembership(
        algebraPolynomialOne(elimination.extendedRing),
        elimination.basis
    );
    return Object.freeze({
        kind: 'algebra-ideal-radical-membership',
        ideal,
        element,
        elimination,
        unitMembership,
        member: unitMembership.member
    });
}

export interface AlgebraIdealRadicalEquivalence<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly kind: 'algebra-ideal-radical-equivalence';
    readonly left: AlgebraPolynomialIdeal<P, C, I>;
    readonly right: AlgebraPolynomialIdeal<P, C, I>;
    readonly leftInRight: readonly AlgebraIdealRadicalMembership<P, C, I>[];
    readonly rightInLeft: readonly AlgebraIdealRadicalMembership<P, C, I>[];
    readonly equivalent: boolean;
}

export function algebraIdealRadicalEquivalence<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraPolynomialIdeal<P, C, I>,
    right: AlgebraPolynomialIdeal<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraIdealRadicalEquivalence<P, C, I> {
    assertIdealPair(left, right);
    const leftInRight = left.generators.map(value =>
        algebraIdealRadicalMembership(right, value, options)
    );
    const rightInLeft = right.generators.map(value =>
        algebraIdealRadicalMembership(left, value, options)
    );
    return Object.freeze({
        kind: 'algebra-ideal-radical-equivalence',
        left,
        right,
        leftInRight: Object.freeze(leftInRight),
        rightInLeft: Object.freeze(rightInLeft),
        equivalent: leftInRight.every(value => value.member) &&
            rightInLeft.every(value => value.member)
    });
}
