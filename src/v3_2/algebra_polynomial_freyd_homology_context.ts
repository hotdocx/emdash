/** Shared degree lookup for homological operations on a bounded sequence. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPolynomialFreydBoundedChainMap,
    AlgebraPolynomialFreydBoundedComplex,
    algebraPolynomialFreydBoundedComplexHomology
} from './algebra_polynomial_freyd_bounded_complex';
import { AlgebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact';
import {
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    algebraPolynomialPresentationMorphismCongruence as congruence,
    algebraPolynomialPresentationMorphismIdentity as identity,
    algebraPolynomialPresentationMorphismZero as zero
} from './algebra_polynomial_freyd_category';

export type AlgebraPolynomialFreydHomologyContextErrorCode =
    | 'INVALID_SEQUENCE'
    | 'DEGREE_OUT_OF_RANGE'
    | 'ENDPOINT_NOT_ZERO';

/** No global cache: callers retain and explicitly reuse the selected results. */
export function algebraPolynomialFreydHomologyContext<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(
    sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>,
    degree: number,
    operation: string,
    fail: (code: AlgebraPolynomialFreydHomologyContextErrorCode, path: string, message: string) => never
) {
    if (!sequence.isShortExact || !sequence.inclusion.isChainMap || !sequence.projection.isChainMap) {
        return fail('INVALID_SEQUENCE', operation + '.sequence', 'A checked short-exact sequence is required');
    }
    if (!Number.isSafeInteger(degree) || degree < 0 || degree > sequence.length + 1) {
        return fail('DEGREE_OUT_OF_RANGE', operation + '.degree',
            'Connecting degree must lie between zero and one above the finite support');
    }
    const term = (complex: AlgebraPolynomialFreydBoundedComplex<P, C, I>, n: number) =>
        n >= 0 && n <= complex.length ? complex.terms[n].object : sequence.zeroObject;
    const differential = (complex: AlgebraPolynomialFreydBoundedComplex<P, C, I>, n: number) =>
        n >= 1 && n <= complex.length
            ? complex.differentials[n - 1].morphism
            : zero(term(complex, n), term(complex, n - 1));
    const component = (map: AlgebraPolynomialFreydBoundedChainMap<P, C, I>, n: number) =>
        n >= 0 && n <= sequence.length
            ? map.components[n].morphism
            : sequence.zeroRow.incoming;
    const homologyAt = (complex: AlgebraPolynomialFreydBoundedComplex<P, C, I>, n: number) => {
        const bounded = n >= 0 && n <= complex.length
            ? algebraPolynomialFreydBoundedComplexHomology(complex, n)
            : undefined;
        const homology = bounded?.homology ?? algebraPolynomialFreydHomologyAt(
            algebraPolynomialFreydChainPair(differential(complex, n + 1), differential(complex, n))
        );
        const zeroIdentity = bounded === undefined
            ? congruence(identity(homology.homologyObject), zero(homology.homologyObject, homology.homologyObject))
            : undefined;
        if (zeroIdentity !== undefined && !zeroIdentity.agrees) {
            return fail('ENDPOINT_NOT_ZERO', operation + '.homology[' + n + ']',
                'Homology outside the finite support must be a zero object');
        }
        return Object.freeze({
            complex, degree: n, homology, bounded, zeroIdentity,
            location: bounded === undefined ? 'zero-extension' as const : 'support' as const
        });
    };

    return Object.freeze({ term, differential, component, homologyAt });
}
