/** One-degree homology and witness-rich exactness in polynomial Freyd. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
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
    AlgebraPolynomialFreydKernel,
    AlgebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernel
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydEpimorphismWitness
} from './algebra_polynomial_freyd_normality';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_HOMOLOGY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-homology-v1' as const,
    differentialOrientation: 'd-next-then-d' as const,
    homologyConstruction: 'cokernel-of-boundary-lift-into-kernel' as const,
    exactness: 'boundary-lift-epimorphism' as const,
    retainsNegativeChainAgreement: true as const,
    claimsClosedFormalAbelianCategory: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydHomologyErrorCode =
    | 'INVALID_CHAIN_PAIR'
    | 'CHAIN_CONDITION_FAILED'
    | 'INVALID_HOMOLOGY_RESULT';

export class AlgebraPolynomialFreydHomologyError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydHomologyErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydHomologyError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydHomologyErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydHomologyError(code, path, message);
};

export interface AlgebraPolynomialFreydChainPair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-chain-pair';
    readonly dNext: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly d: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly composite: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly chainAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly isChainPair: boolean;
}

/** Retain the computed quotient chain agreement, including negative results. */
export function algebraPolynomialFreydChainPair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    dNext: AlgebraPolynomialPresentationMorphism<P, C, I>,
    d: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydChainPair<P, C, I> {
    if (!algebraPresentedPolynomialModuleEquals(dNext.target, d.source)) {
        return fail(
            'INVALID_CHAIN_PAIR',
            'freydChainPair.middle',
            'The incoming differential must target the outgoing source'
        );
    }
    const composite = algebraPolynomialPresentationMorphismCompose(d, dNext);
    const zero = algebraPolynomialPresentationMorphismZero(
        dNext.source,
        d.target
    );
    const chainAgreement = algebraPolynomialPresentationMorphismCongruence(
        composite,
        zero
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-chain-pair',
        dNext,
        d,
        composite,
        zero,
        chainAgreement,
        isChainPair: chainAgreement.agrees
    });
}

export interface AlgebraPolynomialFreydHomologyAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-homology-at';
    readonly pair: AlgebraPolynomialFreydChainPair<P, C, I>;
    readonly cycles: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly cycleObject: AlgebraPolynomialFreydKernel<P, C, I>['object'];
    readonly cycleEmbedding:
        AlgebraPolynomialFreydKernel<P, C, I>['embedding'];
    readonly boundary: AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly boundaryMorphism:
        AlgebraPolynomialFreydKernelLift<P, C, I>['lift'];
    readonly boundaryReconstruction:
        AlgebraPolynomialFreydKernelLift<P, C, I>['reconstructionAgreement'];
    readonly homology: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly homologyObject: AlgebraPolynomialFreydCokernel<P, C, I>['object'];
    readonly homologyProjection:
        AlgebraPolynomialFreydCokernel<P, C, I>['projection'];
    readonly homologyAnnihilation:
        AlgebraPolynomialFreydCokernel<P, C, I>['annihilationAgreement'];
}

/** Construct Z = Ker(d), b : source(dNext) -> Z, and H = Coker(b). */
export function algebraPolynomialFreydHomologyAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    pair: AlgebraPolynomialFreydChainPair<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydHomologyAt<P, C, I> {
    if (!pair.chainAgreement.agrees) {
        return fail(
            'CHAIN_CONDITION_FAILED',
            'freydHomology.pair.chainAgreement',
            'Homology requires the selected adjacent composite to agree with zero'
        );
    }
    const cycles = algebraPolynomialFreydKernel(pair.d, options);
    const boundary = algebraPolynomialFreydKernelLift(
        cycles,
        pair.dNext,
        options
    );
    const homology = algebraPolynomialFreydCokernel(boundary.lift);
    if (
        !boundary.reconstructionAgreement.agrees ||
        !homology.annihilationAgreement.agrees
    ) {
        return fail(
            'INVALID_HOMOLOGY_RESULT',
            'freydHomology.universalData',
            'Selected kernel/cokernel operations lost a homology equation'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-homology-at',
        pair,
        cycles,
        cycleObject: cycles.object,
        cycleEmbedding: cycles.embedding,
        boundary,
        boundaryMorphism: boundary.lift,
        boundaryReconstruction: boundary.reconstructionAgreement,
        homology,
        homologyObject: homology.object,
        homologyProjection: homology.projection,
        homologyAnnihilation: homology.annihilationAgreement
    });
}

export interface AlgebraPolynomialFreydExactnessAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-exactness-at';
    readonly homology: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly zeroProjection: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly projectionZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly exact: boolean;
    readonly epimorphism?: AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
}

/** Classify exactness by epicity of the boundary-to-cycle map. */
export function algebraPolynomialFreydExactnessAt<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(homology: AlgebraPolynomialFreydHomologyAt<P, C, I>):
    AlgebraPolynomialFreydExactnessAt<P, C, I> {
    const zeroProjection = algebraPolynomialPresentationMorphismZero(
        homology.cycleObject,
        homology.homologyObject
    );
    const projectionZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            homology.homologyProjection,
            zeroProjection
        );
    const epimorphism = projectionZeroAgreement.agrees
        ? algebraPolynomialFreydEpimorphismWitness(
            homology.boundaryMorphism
        )
        : undefined;
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-exactness-at',
        homology,
        zeroProjection,
        projectionZeroAgreement,
        exact: projectionZeroAgreement.agrees,
        ...(epimorphism === undefined ? {} : { epimorphism })
    });
}
