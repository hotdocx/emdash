/** The whole six-term snake result, with no endpoint-zero or splitting assumption. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPolynomialFreydSnakeConnecting,
    AlgebraPolynomialFreydSnakeTriple,
    algebraPolynomialFreydSnakeConnecting
} from './algebra_polynomial_freyd_snake';
import { algebraPolynomialFreydKernel, algebraPolynomialFreydKernelLift } from './algebra_polynomial_freyd_kernel';
import { algebraPolynomialFreydCokernel, algebraPolynomialFreydCokernelColift } from './algebra_polynomial_freyd_cokernel';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCompose as compose
} from './algebra_polynomial_freyd_category';
import {
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydExactnessAt
} from './algebra_polynomial_freyd_homology';
import { AlgebraPolynomialWeakKernelFactorOptions } from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_SNAKE_EXACT_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-snake-exact-v1' as const,
    shape: 'six-objects-five-arrows-four-interior-exactness' as const,
    maps: 'existing-kernel-lifts-and-cokernel-colifts' as const,
    assumesEndpointZeros: false as const,
    assumesSplitEpimorphisms: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydSnakeExactErrorCode =
    | 'INVALID_CONNECTING'
    | 'ENDPOINT_MISMATCH'
    | 'ADJACENT_ZERO_FAILED'
    | 'SEQUENCE_NOT_EXACT'
    | 'OWNER_MISMATCH';

export class AlgebraPolynomialFreydSnakeExactError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydSnakeExactErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydSnakeExactError';
    }
}

const fail = (code: AlgebraPolynomialFreydSnakeExactErrorCode, path: string, message: string): never => {
    throw new AlgebraPolynomialFreydSnakeExactError(code, path, message);
};

/** Reuse the actual whole connecting construction, including its universal owners. */
export function algebraPolynomialFreydSnakeExactSequenceFromConnecting<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(connecting: AlgebraPolynomialFreydSnakeConnecting<P, C, I>, options: AlgebraPolynomialWeakKernelFactorOptions = {}) {
    if (!connecting.triple.isSnakeTriple || !connecting.triple.tripleZeroAgreement.agrees ||
        !connecting.uColift.reconstructs || !connecting.connectingLift.reconstructs ||
        connecting.u !== connecting.uColift.colift || connecting.connecting !== connecting.connectingLift.lift ||
        connecting.source !== connecting.gammaKernel.object || connecting.target !== connecting.alphaCokernel.object) {
        return fail('INVALID_CONNECTING', 'snakeExact.connecting', 'An actual compatible connecting result is required');
    }
    const alphaKernel = algebraPolynomialFreydKernel(connecting.alpha);
    const betaKernel = algebraPolynomialFreydKernel(connecting.triple.beta);
    const betaCokernel = algebraPolynomialFreydCokernel(connecting.triple.beta);
    const gammaCokernel = algebraPolynomialFreydCokernel(connecting.gamma);
    const kernelAlphaBeta = algebraPolynomialFreydKernelLift(
        betaKernel, compose(connecting.triple.delta, alphaKernel.embedding), options
    );
    const kernelBetaGamma = algebraPolynomialFreydKernelLift(
        connecting.gammaKernel, compose(connecting.epsilon, betaKernel.embedding), options
    );
    const cokernelAlphaBeta = algebraPolynomialFreydCokernelColift(
        connecting.alphaCokernel, compose(betaCokernel.projection, connecting.mu)
    );
    const cokernelBetaGamma = algebraPolynomialFreydCokernelColift(
        betaCokernel, compose(gammaCokernel.projection, connecting.triple.lambda)
    );
    const objects = Object.freeze([
        alphaKernel.object, betaKernel.object, connecting.gammaKernel.object,
        connecting.alphaCokernel.object, betaCokernel.object, gammaCokernel.object
    ] as const);
    const arrows = Object.freeze([
        kernelAlphaBeta.lift, kernelBetaGamma.lift, connecting.connecting,
        cokernelAlphaBeta.colift, cokernelBetaGamma.colift
    ] as const);
    arrows.forEach((arrow, index) => {
        if (!algebraPresentedPolynomialModuleEquals(arrow.source, objects[index]) ||
            !algebraPresentedPolynomialModuleEquals(arrow.target, objects[index + 1])) {
            fail('ENDPOINT_MISMATCH', `snakeExact.arrows[${index}]`, 'Each map must use the selected adjacent objects');
        }
    });
    const pairs = Object.freeze([0, 1, 2, 3].map(index => algebraPolynomialFreydChainPair(arrows[index], arrows[index + 1])));
    if (pairs.some(pair => !pair.isChainPair || !pair.chainAgreement.agrees)) {
        return fail('ADJACENT_ZERO_FAILED', 'snakeExact.pairs', 'Every adjacent snake composite must vanish');
    }
    const exactness = Object.freeze(pairs.map(pair => algebraPolynomialFreydExactnessAt(algebraPolynomialFreydHomologyAt(pair))));
    if (exactness.some(result => !result.exact || !result.epimorphism)) {
        return fail('SEQUENCE_NOT_EXACT', 'snakeExact.exactness', 'All four interior positions require exactness witnesses');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-snake-exact-sequence' as const,
        connecting, alphaKernel, betaKernel, betaCokernel, gammaCokernel,
        kernelAlphaBeta, kernelBetaGamma, cokernelAlphaBeta, cokernelBetaGamma,
        objects, arrows, pairs, exactness, isExact: true as const,
        assumesEndpointZeros: false as const, assumesSplitEpimorphisms: false as const
    });
}

/** Standalone constructor; the from-connecting variant avoids recomputation in replay. */
export function algebraPolynomialFreydSnakeExactSequence<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(triple: AlgebraPolynomialFreydSnakeTriple<P, C, I>, options: AlgebraPolynomialWeakKernelFactorOptions = {}) {
    return algebraPolynomialFreydSnakeExactSequenceFromConnecting(algebraPolynomialFreydSnakeConnecting(triple, options), options);
}

export type AlgebraPolynomialFreydSnakeExactSequence<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydSnakeExactSequenceFromConnecting<P, C, I>>;
