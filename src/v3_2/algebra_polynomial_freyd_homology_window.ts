/** A nonsplit five-term homology window over the existing Freyd owners. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialFreydBoundedChainMap } from './algebra_polynomial_freyd_bounded_complex';
import { AlgebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact';
import {
    AlgebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydExactnessAt
} from './algebra_polynomial_freyd_homology';
import {
    algebraPolynomialFreydHomologyChainMap,
    algebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_functorial_homology';
import { algebraPolynomialFreydHomologyContext } from './algebra_polynomial_freyd_homology_context';
import { algebraPolynomialFreydHomologyConnecting } from './algebra_polynomial_freyd_homology_connecting';

export const ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_WINDOW_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-homology-window-v2' as const,
    connecting: 'named-homology-connecting-operation' as const,
    homology: 'existing-selected-owner' as const,
    assumesSplitEpimorphisms: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydHomologyWindowErrorCode =
    | 'INVALID_SEQUENCE'
    | 'DEGREE_OUT_OF_RANGE'
    | 'COMPARISON_FAILED'
    | 'ENDPOINT_NOT_ZERO'
    | 'WINDOW_NOT_EXACT';

export class AlgebraPolynomialFreydHomologyWindowError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydHomologyWindowErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydHomologyWindowError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydHomologyWindowErrorCode,
    path: string,
    message: string
): never => { throw new AlgebraPolynomialFreydHomologyWindowError(code, path, message); };

/**
 * H_n(A) → H_n(B) → H_n(C) → H_(n-1)(A) → H_(n-1)(B).
 * Outside support, complex terms are the stored zero presentation. Homology
 * still uses the actual neighboring differentials, including 0 → C_top.
 */
export function algebraPolynomialFreydHomologyWindow<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>, degree: number) {
    const { component, homologyAt } = algebraPolynomialFreydHomologyContext(sequence, degree, 'homologyWindow', fail);
    const upperA = homologyAt(sequence.subcomplex, degree);
    const upperB = homologyAt(sequence.middleComplex, degree);
    const upperC = homologyAt(sequence.quotientComplex, degree);
    const lowerA = homologyAt(sequence.subcomplex, degree - 1);
    const lowerB = homologyAt(sequence.middleComplex, degree - 1);
    const induced = (
        map: AlgebraPolynomialFreydBoundedChainMap<P, C, I>,
        n: number,
        source: AlgebraPolynomialFreydHomologyAt<P, C, I>,
        target: AlgebraPolynomialFreydHomologyAt<P, C, I>
    ) => algebraPolynomialFreydInducedHomologyMap(algebraPolynomialFreydHomologyChainMap({
        source, target, fNext: component(map, n + 1), f: component(map, n), fPrev: component(map, n - 1)
    }));
    const inclusionUpper = induced(sequence.inclusion, degree, upperA.homology, upperB.homology);
    const projectionUpper = induced(sequence.projection, degree, upperB.homology, upperC.homology);
    const inclusionLower = induced(sequence.inclusion, degree - 1, lowerA.homology, lowerB.homology);
    const connecting = algebraPolynomialFreydHomologyConnecting(sequence, degree, {
        source: upperC.homology, target: lowerA.homology
    });
    const arrows = Object.freeze([
        inclusionUpper.homologyMap, projectionUpper.homologyMap,
        connecting.homologyMap, inclusionLower.homologyMap
    ] as const);
    const pairs = Object.freeze([0, 1, 2].map(index => algebraPolynomialFreydChainPair(arrows[index], arrows[index + 1])));
    const exactness = Object.freeze(pairs.map(pair => algebraPolynomialFreydExactnessAt(algebraPolynomialFreydHomologyAt(pair))));
    if (exactness.some(result => !result.exact)) {
        return fail('WINDOW_NOT_EXACT', 'homologyWindow.exactness', 'A displayed interior term is not exact');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-homology-window' as const,
        sequence, degree, upperA, upperB, upperC, lowerA, lowerB,
        inclusionUpper, projectionUpper, inclusionLower, connecting,
        arrows, pairs, exactness, isExact: true as const,
        assumesSplitEpimorphisms: false as const
    });
}

export type AlgebraPolynomialFreydHomologyWindow<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydHomologyWindow<P, C, I>>;
