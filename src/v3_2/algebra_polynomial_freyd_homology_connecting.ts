/** Homology connecting is an operation in its own right; snake is its current method. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialPresentationMorphism, algebraPolynomialModuleMapEquals } from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCompose as compose,
    algebraPolynomialPresentationMorphismCongruence as congruence,
    algebraPolynomialPresentationMorphismIdentity as identity
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydBoundedShortExactSequence,
    algebraPolynomialFreydBoundedShortExactExtendedAt
} from './algebra_polynomial_freyd_bounded_short_exact';
import {
    AlgebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
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
import {
    AlgebraPolynomialFreydHomologyContextErrorCode,
    algebraPolynomialFreydHomologyContext
} from './algebra_polynomial_freyd_homology_context';

export const ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_CONNECTING_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-homology-connecting-v1' as const,
    operation: 'homology-connecting' as const,
    method: 'snake-endpoint-comparison-normal-mono-and-cokernel' as const,
    homology: 'existing-selected-owner' as const,
    assumesSplitEpimorphisms: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydHomologyConnectingErrorCode =
    | AlgebraPolynomialFreydHomologyContextErrorCode
    | 'INVALID_HOMOLOGY_SELECTION'
    | 'COMPARISON_FAILED'
    | 'RECONSTRUCTION_FAILED';

export class AlgebraPolynomialFreydHomologyConnectingError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydHomologyConnectingErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydHomologyConnectingError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydHomologyConnectingErrorCode, path: string, message: string
): never => { throw new AlgebraPolynomialFreydHomologyConnectingError(code, path, message); };

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


export interface AlgebraPolynomialFreydHomologyConnectingSelection<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> {
    readonly source?: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly target?: AlgebraPolynomialFreydHomologyAt<P, C, I>;
}

/**
 * δ_n : H_n(C) → H_(n-1)(A), without a chosen section or global cycle lift.
 * Optional selections preserve the caller's actual whole homologies. They
 * must have the original raw adjacent differentials, not just congruent ones.
 */
export function algebraPolynomialFreydHomologyConnecting<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(
    sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>,
    degree: number,
    selected: AlgebraPolynomialFreydHomologyConnectingSelection<P, C, I> = {}
) {
    const context = algebraPolynomialFreydHomologyContext(sequence, degree, 'homologyConnecting', fail);
    const source = selected.source ?? context.homologyAt(sequence.quotientComplex, degree).homology;
    const target = selected.target ?? context.homologyAt(sequence.subcomplex, degree - 1).homology;
    const sameSelectedArrow = (
        actual: AlgebraPolynomialPresentationMorphism<P, C, I>,
        expected: AlgebraPolynomialPresentationMorphism<P, C, I>
    ) => algebraPresentedPolynomialModuleEquals(actual.source, expected.source) &&
        algebraPresentedPolynomialModuleEquals(actual.target, expected.target) &&
        algebraPolynomialModuleMapEquals(actual.map, expected.map);
    const checkSelection = (
        homology: AlgebraPolynomialFreydHomologyAt<P, C, I>,
        complex: typeof sequence.subcomplex, n: number, path: string
    ) => {
        if (!homology.pair.isChainPair || !homology.pair.chainAgreement.agrees ||
            !sameSelectedArrow(homology.pair.dNext, context.differential(complex, n + 1)) ||
            !sameSelectedArrow(homology.pair.d, context.differential(complex, n))) {
            fail('INVALID_HOMOLOGY_SELECTION', path,
                'Selected homology must use the actual adjacent differential representatives');
        }
    };
    checkSelection(source, sequence.quotientComplex, degree, 'homologyConnecting.source');
    checkSelection(target, sequence.subcomplex, degree - 1, 'homologyConnecting.target');

    const upperRow = algebraPolynomialFreydBoundedShortExactExtendedAt(sequence, degree);
    const lowerRow = algebraPolynomialFreydBoundedShortExactExtendedAt(sequence, degree - 1);
    const snake = algebraPolynomialFreydSnakeConnecting(algebraPolynomialFreydSnakeTriple(
        upperRow.triple.incoming,
        context.differential(sequence.middleComplex, degree),
        lowerRow.triple.outgoing
    ));

    // Coker(i_n) ⇄ C_n. The inverse goes into the cokernel, not into B_n.
    const upperForward = algebraPolynomialFreydCokernelColift(snake.deltaCokernel, upperRow.triple.outgoing);
    const upperInverse = algebraPolynomialFreydColiftAlongEpimorphism(
        upperRow.triple.outgoingEpimorphism, snake.epsilon
    );
    const upperComparison = comparisonIsomorphism(upperForward.colift, upperInverse.colift, 'homologyConnecting.upperRow');

    // A_(n-1) ⇄ Ker(p_(n-1)), at the snake's actual selected kernel.
    const lowerForward = algebraPolynomialFreydKernelLift(snake.lambdaKernel, lowerRow.triple.incoming);
    const lowerInverse = algebraPolynomialFreydLiftAlongMonomorphism(
        lowerRow.triple.incomingMonomorphism, snake.mu
    );
    const lowerComparison = comparisonIsomorphism(lowerForward.lift, lowerInverse.lift, 'homologyConnecting.lowerRow');
    const gammaAfterComparison = compose(source.pair.d, upperComparison.forward);
    const alphaAfterComparison = compose(lowerComparison.forward, target.pair.dNext);
    const gammaAgreement = congruence(snake.gamma, gammaAfterComparison);
    const alphaAgreement = congruence(snake.alpha, alphaAfterComparison);
    if (!gammaAgreement.agrees || !alphaAgreement.agrees) {
        return fail('COMPARISON_FAILED', 'homologyConnecting.differentials',
            'The compared snake side maps must be the actual complex differentials');
    }

    // Z_n(C) ⇄ Ker(gamma), without replacing the selected source cycles.
    const cycleForward = algebraPolynomialFreydKernelLift(
        snake.gammaKernel, compose(upperComparison.inverse, source.cycleEmbedding)
    );
    const cycleInverse = algebraPolynomialFreydKernelLift(
        source.cycles, compose(upperComparison.forward, snake.iota)
    );
    const cycleComparison = comparisonIsomorphism(cycleForward.lift, cycleInverse.lift, 'homologyConnecting.sourceCycles');

    // Coker(alpha) ⇄ Coker(d^A_n). This intermediate cokernel is not homology.
    const differentialCokernel = algebraPolynomialFreydCokernel(target.pair.dNext);
    const targetForward = algebraPolynomialFreydCokernelColift(
        snake.alphaCokernel, compose(differentialCokernel.projection, lowerComparison.inverse)
    );
    const targetInverse = algebraPolynomialFreydCokernelColift(
        differentialCokernel, compose(snake.pi, lowerComparison.forward)
    );
    const targetComparison = comparisonIsomorphism(targetForward.colift, targetInverse.colift, 'homologyConnecting.targetCokernel');

    // H_(n-1)(A) ↪ Coker(d^A_n), induced by the existing target-cycle embedding.
    // Normal-mono factorization retains the nonsplit quotient-level route.
    const homologyEmbedding = algebraPolynomialFreydCokernelColift(
        target.homology,
        compose(differentialCokernel.projection, target.cycleEmbedding)
    );
    const homologyMonomorphism = algebraPolynomialFreydMonomorphismWitness(homologyEmbedding.colift);
    const snakeAfterCycles = compose(snake.connecting, cycleComparison.forward);
    const comparedSnake = compose(targetComparison.forward, snakeAfterCycles);
    const targetFactor = algebraPolynomialFreydLiftAlongMonomorphism(homologyMonomorphism, comparedSnake);
    const descent = algebraPolynomialFreydCokernelColift(source.homology, targetFactor.lift);
    const trace = Object.freeze({
        kind: 'snake-homology-connecting-v1' as const,
        snake, upperRow, lowerRow, upperForward, upperInverse, upperComparison,
        lowerForward, lowerInverse, lowerComparison,
        gammaAfterComparison, alphaAfterComparison, gammaAgreement, alphaAgreement,
        cycleForward, cycleInverse, cycleComparison, differentialCokernel,
        targetForward, targetInverse, targetComparison,
        homologyEmbedding, homologyMonomorphism, snakeAfterCycles, comparedSnake,
        targetFactor, descent, homologyMap: descent.colift
    });

    // j_A ∘ δ_n ∘ q_C is the compared snake arrow on source cycles.
    const reconstructed = compose(homologyEmbedding.colift, compose(descent.colift, source.homologyProjection));
    const reconstructionAgreement = congruence(reconstructed, comparedSnake);
    if (!reconstructionAgreement.agrees) {
        return fail('RECONSTRUCTION_FAILED', 'homologyConnecting.reconstruction',
            'The homology arrow must reconstruct the selected universal factors');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-homology-connecting' as const,
        sequence, degree, source, target, homologyMap: descent.colift,
        reconstruction: Object.freeze({
            sourceProjection: source.homologyProjection,
            targetInclusion: homologyEmbedding.colift,
            comparedMap: comparedSnake,
            reconstructed, agreement: reconstructionAgreement
        }),
        trace,
        assumesSplitEpimorphisms: false as const
    });
}

export type AlgebraPolynomialFreydHomologyConnecting<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydHomologyConnecting<P, C, I>>;
