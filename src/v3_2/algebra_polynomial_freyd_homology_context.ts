/** Shared degree lookup for homological operations on a bounded sequence. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPolynomialFreydBoundedChainMap,
    AlgebraPolynomialFreydBoundedComplex,
    algebraPolynomialFreydBoundedComplexHomology
} from './algebra_polynomial_freyd_bounded_complex';
import { AlgebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact';
import {
    AlgebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCongruence as congruence,
    algebraPolynomialPresentationMorphismIdentity as identity,
    algebraPolynomialPresentationMorphismZero as zero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialPresentationMorphism,
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPolynomialFreydHomologyChainMap,
    algebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_functorial_homology';

/** Exact presentation/raw-map agreement for reusing selected computation data. */
export const algebraPolynomialFreydSameHomologicalArrow = <
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(actual: AlgebraPolynomialPresentationMorphism<P, C, I>, expected: AlgebraPolynomialPresentationMorphism<P, C, I>) =>
    algebraPresentedPolynomialModuleEquals(actual.source, expected.source) &&
    algebraPresentedPolynomialModuleEquals(actual.target, expected.target) &&
    algebraPolynomialModuleMapEquals(actual.map, expected.map);

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

    const matchesHomologyAt = (
        homology: AlgebraPolynomialFreydHomologyAt<P, C, I>,
        complex: AlgebraPolynomialFreydBoundedComplex<P, C, I>, n: number
    ) => homology.pair.isChainPair && homology.pair.chainAgreement.agrees &&
        algebraPolynomialFreydSameHomologicalArrow(homology.pair.dNext, differential(complex, n + 1)) &&
        algebraPolynomialFreydSameHomologicalArrow(homology.pair.d, differential(complex, n));
    const induced = (
        map: AlgebraPolynomialFreydBoundedChainMap<P, C, I>, n: number,
        source: AlgebraPolynomialFreydHomologyAt<P, C, I>,
        target: AlgebraPolynomialFreydHomologyAt<P, C, I>
    ) => algebraPolynomialFreydInducedHomologyMap(algebraPolynomialFreydHomologyChainMap({
        source, target, fNext: component(map, n + 1), f: component(map, n), fPrev: component(map, n - 1)
    }));
    return Object.freeze({ term, differential, component, homologyAt, matchesHomologyAt, induced });
}

export type AlgebraPolynomialFreydHomologyDegree<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<ReturnType<typeof algebraPolynomialFreydHomologyContext<P, C, I>>['homologyAt']>;
