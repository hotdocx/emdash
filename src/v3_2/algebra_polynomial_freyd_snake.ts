/** CAP-style non-split Abelian snake connecting morphism in polynomial Freyd. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCompose,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydCokernel,
    AlgebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraPolynomialFreydKernel,
    AlgebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydFiberProduct,
    algebraPolynomialFreydFiberProduct
} from './algebra_polynomial_freyd_fiber_product';
import {
    AlgebraPolynomialFreydPushout,
    algebraPolynomialFreydPushout
} from './algebra_polynomial_freyd_pushout';
import {
    AlgebraPolynomialFreydColiftAlongEpimorphism,
    AlgebraPolynomialFreydEpimorphismWitness,
    AlgebraPolynomialFreydLiftAlongMonomorphism,
    AlgebraPolynomialFreydMonomorphismWitness,
    algebraPolynomialFreydColiftAlongEpimorphism,
    algebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydLiftAlongMonomorphism,
    algebraPolynomialFreydMonomorphismWitness
} from './algebra_polynomial_freyd_normality';
import {
    AlgebraPolynomialFreydFiberProductEpicProjection,
    AlgebraPolynomialFreydPushoutMonicInjection,
    algebraPolynomialFreydFiberProductEpicProjection,
    algebraPolynomialFreydPushoutMonicInjection
} from './algebra_polynomial_freyd_stability';

export const ALGEBRA_POLYNOMIAL_FREYD_SNAKE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-snake-v1' as const,
    construction: 'cap-fiber-product-pushout-normal-factors' as const,
    assumesSplitEpimorphisms: false as const,
    retainsEveryIntermediate: true as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydSnakeErrorCode =
    | 'INVALID_TRIPLE'
    | 'TRIPLE_ZERO_FAILED';

export class AlgebraPolynomialFreydSnakeError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydSnakeErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydSnakeError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydSnakeErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydSnakeError(code, path, message);
};

export interface AlgebraPolynomialFreydSnakeTriple<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-snake-triple';
    readonly delta: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly beta: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly lambda: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly betaAfterDelta:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly tripleComposite:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly tripleZero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly tripleZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly isSnakeTriple: boolean;
}

/** Retain the composable triple and its computed λβδ ≃ 0 agreement. */
export function algebraPolynomialFreydSnakeTriple<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    delta: AlgebraPolynomialPresentationMorphism<P, C, I>,
    beta: AlgebraPolynomialPresentationMorphism<P, C, I>,
    lambda: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydSnakeTriple<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(delta.target, beta.source) ||
        !algebraPresentedPolynomialModuleEquals(beta.target, lambda.source)
    ) {
        fail(
            'INVALID_TRIPLE',
            'freydSnakeTriple.arrows',
            'Snake arrows must form a composable triple'
        );
    }
    const betaAfterDelta = algebraPolynomialPresentationMorphismCompose(
        beta,
        delta
    );
    const tripleComposite = algebraPolynomialPresentationMorphismCompose(
        lambda,
        betaAfterDelta
    );
    const tripleZero = algebraPolynomialPresentationMorphismZero(
        delta.source,
        lambda.target
    );
    const tripleZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            tripleComposite,
            tripleZero
        );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-snake-triple',
        delta,
        beta,
        lambda,
        betaAfterDelta,
        tripleComposite,
        tripleZero,
        tripleZeroAgreement,
        isSnakeTriple: tripleZeroAgreement.agrees
    });
}

export interface AlgebraPolynomialFreydSnakeConnecting<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-snake-connecting';
    readonly triple: AlgebraPolynomialFreydSnakeTriple<P, C, I>;
    readonly deltaCokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly epsilon: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly lambdaAfterBeta:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly gammaColift: AlgebraPolynomialFreydCokernelColift<P, C, I>;
    readonly gamma: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly gammaKernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly iota: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly lambdaKernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly mu: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly alphaLift: AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly alpha: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly alphaCokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly pi: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly epsilonEpimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly fiberProduct: AlgebraPolynomialFreydFiberProduct<P, C, I>;
    readonly fiberProductStability:
        AlgebraPolynomialFreydFiberProductEpicProjection<P, C, I>;
    readonly p1Epimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly muMonomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly pushout: AlgebraPolynomialFreydPushout<P, C, I>;
    readonly pushoutStability:
        AlgebraPolynomialFreydPushoutMonicInjection<P, C, I>;
    readonly q2Monomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly betaAfterP2: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly normalEpiTest: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly uColift:
        AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>;
    readonly u: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly connectingLift:
        AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>;
    readonly connecting: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly source: AlgebraPolynomialFreydKernel<P, C, I>['object'];
    readonly target: AlgebraPolynomialFreydCokernel<P, C, I>['object'];
    readonly assumesSplitEpimorphisms: false;
}

/** Compute the CAP snake morphism Ker(γ) → Coker(α) without a splitting. */
export function algebraPolynomialFreydSnakeConnecting<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    triple: AlgebraPolynomialFreydSnakeTriple<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydSnakeConnecting<P, C, I> {
    if (!triple.tripleZeroAgreement.agrees) {
        fail(
            'TRIPLE_ZERO_FAILED',
            'freydSnakeConnecting.triple',
            'The composite lambda after beta after delta is not zero'
        );
    }
    const deltaCokernel = algebraPolynomialFreydCokernel(triple.delta);
    const epsilon = deltaCokernel.projection;
    const lambdaAfterBeta = algebraPolynomialPresentationMorphismCompose(
        triple.lambda,
        triple.beta
    );
    const gammaColift = algebraPolynomialFreydCokernelColift(
        deltaCokernel,
        lambdaAfterBeta
    );
    const gamma = gammaColift.colift;
    const gammaKernel = algebraPolynomialFreydKernel(gamma);
    const iota = gammaKernel.embedding;

    const lambdaKernel = algebraPolynomialFreydKernel(triple.lambda);
    const mu = lambdaKernel.embedding;
    const alphaLift = algebraPolynomialFreydKernelLift(
        lambdaKernel,
        triple.betaAfterDelta,
        options
    );
    const alpha = alphaLift.lift;
    const alphaCokernel = algebraPolynomialFreydCokernel(alpha);
    const pi = alphaCokernel.projection;

    const epsilonEpimorphism = algebraPolynomialFreydEpimorphismWitness(epsilon);
    const fiberProduct = algebraPolynomialFreydFiberProduct(iota, epsilon);
    const fiberProductStability =
        algebraPolynomialFreydFiberProductEpicProjection(
            fiberProduct,
            epsilonEpimorphism
        );
    const p1Epimorphism = fiberProductStability.projectionEpimorphism;

    const muMonomorphism = algebraPolynomialFreydMonomorphismWitness(mu);
    const pushout = algebraPolynomialFreydPushout(mu, pi);
    const pushoutStability = algebraPolynomialFreydPushoutMonicInjection(
        pushout,
        muMonomorphism
    );
    const q2Monomorphism = pushoutStability.injectionMonomorphism;

    const betaAfterP2 = algebraPolynomialPresentationMorphismCompose(
        triple.beta,
        fiberProduct.projectionRight
    );
    const normalEpiTest = algebraPolynomialPresentationMorphismCompose(
        pushout.injectionLeft,
        betaAfterP2
    );
    const uColift = algebraPolynomialFreydColiftAlongEpimorphism(
        p1Epimorphism,
        normalEpiTest,
        options
    );
    const u = uColift.colift;
    const connectingLift = algebraPolynomialFreydLiftAlongMonomorphism(
        q2Monomorphism,
        u,
        options
    );
    const connecting = connectingLift.lift;
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-snake-connecting',
        triple,
        deltaCokernel,
        epsilon,
        lambdaAfterBeta,
        gammaColift,
        gamma,
        gammaKernel,
        iota,
        lambdaKernel,
        mu,
        alphaLift,
        alpha,
        alphaCokernel,
        pi,
        epsilonEpimorphism,
        fiberProduct,
        fiberProductStability,
        p1Epimorphism,
        muMonomorphism,
        pushout,
        pushoutStability,
        q2Monomorphism,
        betaAfterP2,
        normalEpiTest,
        uColift,
        u,
        connectingLift,
        connecting,
        source: gammaKernel.object,
        target: alphaCokernel.object,
        assumesSplitEpimorphisms: false
    });
}
