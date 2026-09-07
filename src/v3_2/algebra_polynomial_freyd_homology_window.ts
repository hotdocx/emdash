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
    AlgebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_functorial_homology';
import {
    AlgebraPolynomialFreydHomologyDegree,
    algebraPolynomialFreydHomologyContext,
    algebraPolynomialFreydSameHomologicalArrow
} from './algebra_polynomial_freyd_homology_context';
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
    | 'INVALID_SELECTION'
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

/** Retained whole inputs for assembly; maps must refer to these exact homologies. */
export interface AlgebraPolynomialFreydHomologyWindowSelection<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> {
    readonly upperA: AlgebraPolynomialFreydHomologyDegree<P, C, I>;
    readonly upperB: AlgebraPolynomialFreydHomologyDegree<P, C, I>;
    readonly upperC: AlgebraPolynomialFreydHomologyDegree<P, C, I>;
    readonly lowerA: AlgebraPolynomialFreydHomologyDegree<P, C, I>;
    readonly lowerB: AlgebraPolynomialFreydHomologyDegree<P, C, I>;
    readonly inclusionUpper: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>;
    readonly projectionUpper: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>;
    readonly inclusionLower: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>;
}

/**
 * H_n(A) → H_n(B) → H_n(C) → H_(n-1)(A) → H_(n-1)(B).
 * Outside support, complex terms are the stored zero presentation. Homology
 * still uses the actual neighboring differentials, including 0 → C_top.
 */
export function algebraPolynomialFreydHomologyWindow<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(
    sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>, degree: number,
    retained?: AlgebraPolynomialFreydHomologyWindowSelection<P, C, I>
) {
    const { component, homologyAt, matchesHomologyAt, induced } =
        algebraPolynomialFreydHomologyContext(sequence, degree, 'homologyWindow', fail);
    const upperA = retained?.upperA ?? homologyAt(sequence.subcomplex, degree);
    const upperB = retained?.upperB ?? homologyAt(sequence.middleComplex, degree);
    const upperC = retained?.upperC ?? homologyAt(sequence.quotientComplex, degree);
    const lowerA = retained?.lowerA ?? homologyAt(sequence.subcomplex, degree - 1);
    const lowerB = retained?.lowerB ?? homologyAt(sequence.middleComplex, degree - 1);
    const checkView = (
        view: AlgebraPolynomialFreydHomologyDegree<P, C, I>,
        complex: typeof sequence.subcomplex, n: number, name: string
    ) => {
        const support = n >= 0 && n <= sequence.length;
        if (view.complex !== complex || view.degree !== n || !matchesHomologyAt(view.homology, complex, n) ||
            (support ? view.location !== 'support' || view.bounded === undefined ||
                view.bounded.complex !== complex || view.bounded.degree !== n ||
                view.bounded.homology !== view.homology || view.bounded.pair !== view.homology.pair ||
                view.bounded.lowerEndpoint !== (n === 0) || view.bounded.upperEndpoint !== (n === sequence.length)
                : view.location !== 'zero-extension' || view.bounded !== undefined || !view.zeroIdentity?.agrees)) {
            fail('INVALID_SELECTION', 'homologyWindow.' + name, 'The retained degree view has a different owner or differential');
        }
    };
    if (retained) {
        checkView(upperA, sequence.subcomplex, degree, 'upperA');
        checkView(upperB, sequence.middleComplex, degree, 'upperB');
        checkView(upperC, sequence.quotientComplex, degree, 'upperC');
        checkView(lowerA, sequence.subcomplex, degree - 1, 'lowerA');
        checkView(lowerB, sequence.middleComplex, degree - 1, 'lowerB');
    }
    const inclusionUpper = retained?.inclusionUpper ?? induced(sequence.inclusion, degree, upperA.homology, upperB.homology);
    const projectionUpper = retained?.projectionUpper ?? induced(sequence.projection, degree, upperB.homology, upperC.homology);
    const inclusionLower = retained?.inclusionLower ?? induced(sequence.inclusion, degree - 1, lowerA.homology, lowerB.homology);
    const checkInduced = (
        value: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>,
        map: AlgebraPolynomialFreydBoundedChainMap<P, C, I>,
        n: number,
        source: AlgebraPolynomialFreydHomologyAt<P, C, I>,
        target: AlgebraPolynomialFreydHomologyAt<P, C, I>, name: string
    ) => {
        const chain = value.chainMap;
        if (chain.source !== source || chain.target !== target || !chain.isChainMap ||
            !chain.upperAgreement.agrees || !chain.lowerAgreement.agrees ||
            !algebraPolynomialFreydSameHomologicalArrow(chain.fNext, component(map, n + 1)) ||
            !algebraPolynomialFreydSameHomologicalArrow(chain.f, component(map, n)) ||
            !algebraPolynomialFreydSameHomologicalArrow(chain.fPrev, component(map, n - 1))) {
            fail('INVALID_SELECTION', 'homologyWindow.' + name, 'The retained induced map belongs to different homology data');
        }
    };
    if (retained) {
        checkInduced(inclusionUpper, sequence.inclusion, degree, upperA.homology, upperB.homology, 'inclusionUpper');
        checkInduced(projectionUpper, sequence.projection, degree, upperB.homology, upperC.homology, 'projectionUpper');
        checkInduced(inclusionLower, sequence.inclusion, degree - 1, lowerA.homology, lowerB.homology, 'inclusionLower');
    }
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
