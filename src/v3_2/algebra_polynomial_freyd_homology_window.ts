/** A nonsplit five-term homology window over the existing Freyd owners. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialPresentationMorphism } from './algebra_polynomial_presentation_morphism';
import {
    algebraPolynomialPresentationMorphismCompose as compose,
    algebraPolynomialPresentationMorphismCongruence as congruence,
    algebraPolynomialPresentationMorphismIdentity as identity,
    algebraPolynomialPresentationMorphismZero as zero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydBoundedChainMap,
    AlgebraPolynomialFreydBoundedComplex,
    algebraPolynomialFreydBoundedComplexHomology
} from './algebra_polynomial_freyd_bounded_complex';
import {
    AlgebraPolynomialFreydBoundedShortExactSequence,
    algebraPolynomialFreydBoundedShortExactExtendedAt
} from './algebra_polynomial_freyd_bounded_short_exact';
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
import {
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift
} from './algebra_polynomial_freyd_cokernel';
import { algebraPolynomialFreydKernelLift } from './algebra_polynomial_freyd_kernel';
import {
    algebraPolynomialFreydColiftAlongEpimorphism,
    algebraPolynomialFreydLiftAlongMonomorphism,
    algebraPolynomialFreydMonomorphismWitness
} from './algebra_polynomial_freyd_normality';
import {
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydSnakeTriple
} from './algebra_polynomial_freyd_snake';

export const ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_WINDOW_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-homology-window-v1' as const,
    connecting: 'snake-endpoint-comparison-normal-mono-and-cokernel' as const,
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

/** Check actual inverse arrows; an isomorphism is not accepted as a flag. */
const comparisonIsomorphism = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    forward: AlgebraPolynomialPresentationMorphism<P, C, I>,
    inverse: AlgebraPolynomialPresentationMorphism<P, C, I>,
    path: string
) => {
    const sourceIdentity = identity(forward.source);
    const targetIdentity = identity(forward.target);
    const inverseAfterForward = compose(inverse, forward);
    const forwardAfterInverse = compose(forward, inverse);
    const sourceAgreement = congruence(inverseAfterForward, sourceIdentity);
    const targetAgreement = congruence(forwardAfterInverse, targetIdentity);
    if (!sourceAgreement.agrees || !targetAgreement.agrees) {
        return fail('COMPARISON_FAILED', path, 'The constructed comparison arrows are not inverse');
    }
    return Object.freeze({
        forward, inverse, sourceIdentity, targetIdentity,
        inverseAfterForward, forwardAfterInverse, sourceAgreement, targetAgreement,
        isomorphism: true as const
    });
};

/**
 * H_n(A) → H_n(B) → H_n(C) → H_(n-1)(A) → H_(n-1)(B).
 * Outside support, complex terms are the stored zero presentation. Homology
 * still uses the actual neighboring differentials, including 0 → C_top.
 */
export function algebraPolynomialFreydHomologyWindow<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>, degree: number) {
    if (!sequence.isShortExact || !sequence.inclusion.isChainMap || !sequence.projection.isChainMap) {
        return fail('INVALID_SEQUENCE', 'homologyWindow.sequence', 'A checked short-exact sequence is required');
    }
    if (!Number.isSafeInteger(degree) || degree < 0 || degree > sequence.length + 1) {
        return fail('DEGREE_OUT_OF_RANGE', 'homologyWindow.degree',
            'Window degree must lie between zero and one above the finite support');
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
            return fail('ENDPOINT_NOT_ZERO', `homologyWindow.homology[${n}]`,
                'Homology outside the finite support must be a zero object');
        }
        return Object.freeze({
            complex, degree: n, homology, bounded, zeroIdentity,
            location: bounded === undefined ? 'zero-extension' as const : 'support' as const
        });
    };
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
    const upperRow = algebraPolynomialFreydBoundedShortExactExtendedAt(sequence, degree);
    const lowerRow = algebraPolynomialFreydBoundedShortExactExtendedAt(sequence, degree - 1);
    const snake = algebraPolynomialFreydSnakeConnecting(algebraPolynomialFreydSnakeTriple(
        upperRow.triple.incoming,
        differential(sequence.middleComplex, degree),
        lowerRow.triple.outgoing
    ));

    // Coker(i_n) ⇄ C_n. The inverse goes into the cokernel, not into B_n.
    const upperForward = algebraPolynomialFreydCokernelColift(snake.deltaCokernel, upperRow.triple.outgoing);
    const upperInverse = algebraPolynomialFreydColiftAlongEpimorphism(
        upperRow.triple.outgoingEpimorphism, snake.epsilon
    );
    const upperComparison = comparisonIsomorphism(upperForward.colift, upperInverse.colift, 'homologyWindow.upperRow');

    // A_(n-1) ⇄ Ker(p_(n-1)), at the snake's actual selected kernel.
    const lowerForward = algebraPolynomialFreydKernelLift(snake.lambdaKernel, lowerRow.triple.incoming);
    const lowerInverse = algebraPolynomialFreydLiftAlongMonomorphism(
        lowerRow.triple.incomingMonomorphism, snake.mu
    );
    const lowerComparison = comparisonIsomorphism(lowerForward.lift, lowerInverse.lift, 'homologyWindow.lowerRow');
    const gammaAfterComparison = compose(upperC.homology.pair.d, upperComparison.forward);
    const alphaAfterComparison = compose(lowerComparison.forward, lowerA.homology.pair.dNext);
    const gammaAgreement = congruence(snake.gamma, gammaAfterComparison);
    const alphaAgreement = congruence(snake.alpha, alphaAfterComparison);
    if (!gammaAgreement.agrees || !alphaAgreement.agrees) {
        return fail('COMPARISON_FAILED', 'homologyWindow.differentials',
            'The compared snake side maps must be the actual complex differentials');
    }

    // Z_n(C) ⇄ Ker(gamma), without replacing the selected source cycles.
    const cycleForward = algebraPolynomialFreydKernelLift(
        snake.gammaKernel, compose(upperComparison.inverse, upperC.homology.cycleEmbedding)
    );
    const cycleInverse = algebraPolynomialFreydKernelLift(
        upperC.homology.cycles, compose(upperComparison.forward, snake.iota)
    );
    const cycleComparison = comparisonIsomorphism(cycleForward.lift, cycleInverse.lift, 'homologyWindow.sourceCycles');

    // Coker(alpha) ⇄ Coker(d^A_n). This intermediate cokernel is not homology.
    const differentialCokernel = algebraPolynomialFreydCokernel(lowerA.homology.pair.dNext);
    const targetForward = algebraPolynomialFreydCokernelColift(
        snake.alphaCokernel, compose(differentialCokernel.projection, lowerComparison.inverse)
    );
    const targetInverse = algebraPolynomialFreydCokernelColift(
        differentialCokernel, compose(snake.pi, lowerComparison.forward)
    );
    const targetComparison = comparisonIsomorphism(targetForward.colift, targetInverse.colift, 'homologyWindow.targetCokernel');

    // H_(n-1)(A) ↪ Coker(d^A_n), induced by the existing target-cycle embedding.
    // Normal-mono factorization retains the nonsplit quotient-level route.
    const homologyEmbedding = algebraPolynomialFreydCokernelColift(
        lowerA.homology.homology,
        compose(differentialCokernel.projection, lowerA.homology.cycleEmbedding)
    );
    const homologyMonomorphism = algebraPolynomialFreydMonomorphismWitness(homologyEmbedding.colift);
    const snakeAfterCycles = compose(snake.connecting, cycleComparison.forward);
    const comparedSnake = compose(targetComparison.forward, snakeAfterCycles);
    const targetFactor = algebraPolynomialFreydLiftAlongMonomorphism(homologyMonomorphism, comparedSnake);
    const descent = algebraPolynomialFreydCokernelColift(upperC.homology.homology, targetFactor.lift);
    const connecting = Object.freeze({
        snake, upperRow, lowerRow, upperForward, upperInverse, upperComparison,
        lowerForward, lowerInverse, lowerComparison,
        gammaAfterComparison, alphaAfterComparison, gammaAgreement, alphaAgreement,
        cycleForward, cycleInverse, cycleComparison, differentialCokernel,
        targetForward, targetInverse, targetComparison,
        homologyEmbedding, homologyMonomorphism, snakeAfterCycles, comparedSnake,
        targetFactor, descent, homologyMap: descent.colift
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
