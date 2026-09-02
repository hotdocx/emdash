/** Whole bounded complexes and degreewise homology in polynomial Freyd. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialRing
} from './algebra_polynomial';
import {
    AlgebraPresentedPolynomialModule,
    algebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    algebraPolynomialSubmodule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialBoundedFreeComplex
} from './algebra_polynomial_bounded_complex';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialFreydZeroPresentation,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydChainPair,
    AlgebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';

export const ALGEBRA_POLYNOMIAL_FREYD_BOUNDED_COMPLEX_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-bounded-complex-v1' as const,
    grading: 'zero-based-consecutive-chain' as const,
    lawCarrier: 'presentation-morphism-agreement' as const,
    endpointDifferential: 'selected-zero-presentation' as const,
    retainsNegativeChainAgreements: true as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydBoundedComplexErrorCode =
    | 'INVALID_COMPLEX_TERMS'
    | 'FOREIGN_COMPLEX_RING'
    | 'INVALID_DIFFERENTIALS'
    | 'CHAIN_CONDITION_FAILED'
    | 'DEGREE_OUT_OF_RANGE';

export class AlgebraPolynomialFreydBoundedComplexError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydBoundedComplexErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydBoundedComplexError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydBoundedComplexErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydBoundedComplexError(code, path, message);
};

export interface AlgebraPolynomialFreydComplexTerm<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly object: AlgebraPresentedPolynomialModule<P, C, I>;
}

export interface AlgebraPolynomialFreydComplexDifferential<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydComplexCondition<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly upperDegree: number;
    readonly pair: AlgebraPolynomialFreydChainPair<P, C, I>;
    readonly agreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly zero: boolean;
}

export interface AlgebraPolynomialFreydFreeComplexSource<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-free-complex-source';
    readonly complex: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
}

export interface AlgebraPolynomialFreydBoundedComplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-bounded-complex';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly length: number;
    readonly terms: readonly AlgebraPolynomialFreydComplexTerm<P, C, I>[];
    readonly differentials:
        readonly AlgebraPolynomialFreydComplexDifferential<P, C, I>[];
    readonly conditions:
        readonly AlgebraPolynomialFreydComplexCondition<P, C, I>[];
    readonly isComplex: boolean;
    readonly freeSource?: AlgebraPolynomialFreydFreeComplexSource<P, C, I>;
}

/** Retain all adjacent quotient-zero agreements, including negative ones. */
export function algebraPolynomialFreydBoundedComplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly terms: readonly AlgebraPresentedPolynomialModule<P, C, I>[];
    readonly differentials:
        readonly AlgebraPolynomialPresentationMorphism<P, C, I>[];
    readonly freeSource?: AlgebraPolynomialFreydFreeComplexSource<P, C, I>;
}): AlgebraPolynomialFreydBoundedComplex<P, C, I> {
    if (!Array.isArray(input.terms) || input.terms.length === 0) {
        return fail(
            'INVALID_COMPLEX_TERMS',
            'freydComplex.terms',
            'A bounded Freyd complex requires a degree-zero term'
        );
    }
    if (
        !Array.isArray(input.differentials) ||
        input.differentials.length !== input.terms.length - 1
    ) {
        return fail(
            'INVALID_DIFFERENTIALS',
            'freydComplex.differentials',
            'Exactly one differential is required between consecutive terms'
        );
    }
    const ring = input.terms[0].ambient.ring;
    input.terms.forEach((term, index) => {
        if (!sameAlgebraParent(term.ambient.ring, ring)) {
            return fail(
                'FOREIGN_COMPLEX_RING',
                `freydComplex.terms[${index}]`,
                'Every presentation must use the selected polynomial ring'
            );
        }
    });
    input.differentials.forEach((differential, index) => {
        if (
            !algebraPresentedPolynomialModuleEquals(
                differential.source,
                input.terms[index + 1]
            ) ||
            !algebraPresentedPolynomialModuleEquals(
                differential.target,
                input.terms[index]
            )
        ) {
            return fail(
                'INVALID_DIFFERENTIALS',
                `freydComplex.differentials[${index}]`,
                `Expected d_${index + 1}: C_${index + 1} → C_${index}`
            );
        }
    });
    const terms = Object.freeze(input.terms.map((object, degree) =>
        Object.freeze({ degree, object })
    ));
    const differentials = Object.freeze(input.differentials.map(
        (morphism, index) => Object.freeze({ degree: index + 1, morphism })
    ));
    const conditions = Object.freeze(input.differentials.slice(1).map(
        (upper, offset) => {
            const pair = algebraPolynomialFreydChainPair(
                upper,
                input.differentials[offset]
            );
            return Object.freeze({
                upperDegree: offset + 2,
                pair,
                agreement: pair.chainAgreement,
                zero: pair.isChainPair
            });
        }
    ));
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-bounded-complex',
        ring,
        length: input.differentials.length,
        terms,
        differentials,
        conditions,
        isComplex: conditions.every(condition => condition.zero),
        ...(input.freeSource === undefined
            ? {}
            : { freeSource: input.freeSource })
    });
}

/** Embed the direct bounded-free representation as relation-free presentations. */
export function algebraPolynomialFreydBoundedComplexFromFree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(complex: AlgebraPolynomialBoundedFreeComplex<P, C, I>):
    AlgebraPolynomialFreydBoundedComplex<P, C, I> {
    const terms = complex.terms.map(term => algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(term.module, [])
    ));
    const differentials = complex.differentials.map((entry, index) =>
        algebraPolynomialPresentationMorphism({
            source: terms[index + 1],
            target: terms[index],
            map: entry.map
        })
    );
    return algebraPolynomialFreydBoundedComplex({
        terms,
        differentials,
        freeSource: Object.freeze({
            kind: 'algebra-polynomial-freyd-free-complex-source',
            complex
        })
    });
}

export interface AlgebraPolynomialFreydBoundedHomologyAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-bounded-homology-at';
    readonly complex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly degree: number;
    readonly pair: AlgebraPolynomialFreydChainPair<P, C, I>;
    readonly homology: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly lowerEndpoint: boolean;
    readonly upperEndpoint: boolean;
}

/** Select the adjacent pair at one degree and reuse the one-degree owner. */
export function algebraPolynomialFreydBoundedComplexHomology<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    complex: AlgebraPolynomialFreydBoundedComplex<P, C, I>,
    degree: number
): AlgebraPolynomialFreydBoundedHomologyAt<P, C, I> {
    if (!complex.isComplex) {
        return fail(
            'CHAIN_CONDITION_FAILED',
            'freydComplex.homology',
            'Degreewise homology requires every adjacent chain agreement'
        );
    }
    if (!Number.isSafeInteger(degree) || degree < 0 || degree > complex.length) {
        return fail(
            'DEGREE_OUT_OF_RANGE',
            'freydComplex.homology.degree',
            'Requested degree lies outside the bounded complex'
        );
    }
    const middle = complex.terms[degree].object;
    const zero = algebraPolynomialFreydZeroPresentation(complex.ring);
    const dNext = degree < complex.length
        ? complex.differentials[degree].morphism
        : algebraPolynomialPresentationMorphismZero(zero, middle);
    const d = degree > 0
        ? complex.differentials[degree - 1].morphism
        : algebraPolynomialPresentationMorphismZero(middle, zero);
    const pair = algebraPolynomialFreydChainPair(dNext, d);
    if (!pair.isChainPair) {
        return fail(
            'CHAIN_CONDITION_FAILED',
            'freydComplex.homology.pair',
            'Selected endpoint pair failed its chain agreement'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-bounded-homology-at',
        complex,
        degree,
        pair,
        homology: algebraPolynomialFreydHomologyAt(pair),
        lowerEndpoint: degree === 0,
        upperEndpoint: degree === complex.length
    });
}
