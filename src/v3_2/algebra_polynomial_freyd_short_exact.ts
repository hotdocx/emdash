/** Witness-rich short exact triples in the polynomial Freyd category. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialFreydExactnessAt,
    AlgebraPolynomialFreydHomologyAt,
    AlgebraPolynomialFreydChainPair,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialFreydEpimorphismWitness,
    AlgebraPolynomialFreydMonomorphismWitness,
    algebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydMonomorphismWitness
} from './algebra_polynomial_freyd_normality';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_SHORT_EXACT_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-short-exact-v1' as const,
    exactness: 'boundary-to-selected-kernel-epic' as const,
    retainsWitnesses: true as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydShortExactErrorCode =
    | 'ZERO_COMPOSITE_FAILED'
    | 'MIDDLE_EXACTNESS_FAILED'
    | 'INCOMING_MONICITY_FAILED'
    | 'OUTGOING_EPICITY_FAILED';

export class AlgebraPolynomialFreydShortExactError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydShortExactErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydShortExactError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydShortExactErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraPolynomialFreydShortExactError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export interface AlgebraPolynomialFreydShortExactTriple<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-short-exact-triple';
    readonly incoming: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly outgoing: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly pair: AlgebraPolynomialFreydChainPair<P, C, I>;
    readonly homology: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly exactness: AlgebraPolynomialFreydExactnessAt<P, C, I>;
    readonly incomingMonomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly outgoingEpimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly shortExact: true;
}

/** Select zero, middle-exactness, monicity, and epicity witnesses. */
export function algebraPolynomialFreydShortExactTriple<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    incoming: AlgebraPolynomialPresentationMorphism<P, C, I>,
    outgoing: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydShortExactTriple<P, C, I> {
    const pair = algebraPolynomialFreydChainPair(incoming, outgoing);
    if (!pair.chainAgreement.agrees) {
        return fail(
            'ZERO_COMPOSITE_FAILED',
            'freydShortExact.composite',
            'Short exact arrows must compose to zero'
        );
    }
    let homology: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    let exactness: AlgebraPolynomialFreydExactnessAt<P, C, I>;
    try {
        homology = algebraPolynomialFreydHomologyAt(pair, options);
        exactness = algebraPolynomialFreydExactnessAt(homology);
    } catch (error: unknown) {
        return fail(
            'MIDDLE_EXACTNESS_FAILED',
            'freydShortExact.middle',
            'The incoming arrow is not epic onto the selected kernel',
            error
        );
    }
    if (!exactness.exact || exactness.epimorphism === undefined) {
        return fail(
            'MIDDLE_EXACTNESS_FAILED',
            'freydShortExact.middle',
            'The incoming arrow is not epic onto the selected kernel'
        );
    }
    let incomingMonomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    try {
        incomingMonomorphism = algebraPolynomialFreydMonomorphismWitness(
            incoming,
            options
        );
    } catch (error: unknown) {
        return fail(
            'INCOMING_MONICITY_FAILED',
            'freydShortExact.incoming',
            'The incoming arrow is not monic',
            error
        );
    }
    let outgoingEpimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    try {
        outgoingEpimorphism = algebraPolynomialFreydEpimorphismWitness(outgoing);
    } catch (error: unknown) {
        return fail(
            'OUTGOING_EPICITY_FAILED',
            'freydShortExact.outgoing',
            'The outgoing arrow is not epic',
            error
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-short-exact-triple',
        incoming,
        outgoing,
        pair,
        homology,
        exactness,
        incomingMonomorphism,
        outgoingEpimorphism,
        shortExact: true
    });
}
