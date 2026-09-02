/** Induced maps on one-degree polynomial Freyd homology. */

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
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernelLift
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydCokernelColift
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_FUNCTORIAL_HOMOLOGY_PROFILE =
    Object.freeze({
        revision: 'emdash-algebra-polynomial-freyd-functorial-homology-v1' as const,
        cyclesMap: 'target-kernel-lift' as const,
        homologyMap: 'source-cokernel-colift' as const,
        retainsChainSquares: true as const,
        retainsFactorEquations: true as const,
        performsIo: false as const
    });

export type AlgebraPolynomialFreydFunctorialHomologyErrorCode =
    | 'INVALID_CHAIN_MAP'
    | 'CHAIN_MAP_CONDITION_FAILED'
    | 'INVALID_INDUCED_HOMOLOGY_MAP';

export class AlgebraPolynomialFreydFunctorialHomologyError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydFunctorialHomologyErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydFunctorialHomologyError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydFunctorialHomologyErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydFunctorialHomologyError(code, path, message);
};

export interface AlgebraPolynomialFreydHomologyChainMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-homology-chain-map';
    readonly source: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly target: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly fNext: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly f: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly fPrev: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly upperTargetAfterComponent:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly upperComponentAfterSource:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly upperAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly lowerTargetAfterComponent:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly lowerComponentAfterSource:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly lowerAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly isChainMap: boolean;
}

/** Retain both computed chain-square agreements, including negative results. */
export function algebraPolynomialFreydHomologyChainMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly source: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly target: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly fNext: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly f: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly fPrev: AlgebraPolynomialPresentationMorphism<P, C, I>;
}): AlgebraPolynomialFreydHomologyChainMap<P, C, I> {
    const sourcePair = input.source.pair;
    const targetPair = input.target.pair;
    const valid = (
        morphism: AlgebraPolynomialPresentationMorphism<P, C, I>,
        source: typeof morphism.source,
        target: typeof morphism.target
    ) => algebraPresentedPolynomialModuleEquals(morphism.source, source) &&
        algebraPresentedPolynomialModuleEquals(morphism.target, target);
    if (
        !valid(input.fNext, sourcePair.dNext.source, targetPair.dNext.source) ||
        !valid(input.f, sourcePair.dNext.target, targetPair.dNext.target) ||
        !valid(input.fPrev, sourcePair.d.target, targetPair.d.target)
    ) {
        return fail(
            'INVALID_CHAIN_MAP',
            'freydHomologyChainMap.components',
            'Chain-map components have incompatible presentation endpoints'
        );
    }
    const upperTargetAfterComponent =
        algebraPolynomialPresentationMorphismCompose(
            targetPair.dNext,
            input.fNext
        );
    const upperComponentAfterSource =
        algebraPolynomialPresentationMorphismCompose(
            input.f,
            sourcePair.dNext
        );
    const upperAgreement = algebraPolynomialPresentationMorphismCongruence(
        upperTargetAfterComponent,
        upperComponentAfterSource
    );
    const lowerTargetAfterComponent =
        algebraPolynomialPresentationMorphismCompose(targetPair.d, input.f);
    const lowerComponentAfterSource =
        algebraPolynomialPresentationMorphismCompose(input.fPrev, sourcePair.d);
    const lowerAgreement = algebraPolynomialPresentationMorphismCongruence(
        lowerTargetAfterComponent,
        lowerComponentAfterSource
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-homology-chain-map',
        source: input.source,
        target: input.target,
        fNext: input.fNext,
        f: input.f,
        fPrev: input.fPrev,
        upperTargetAfterComponent,
        upperComponentAfterSource,
        upperAgreement,
        lowerTargetAfterComponent,
        lowerComponentAfterSource,
        lowerAgreement,
        isChainMap: upperAgreement.agrees && lowerAgreement.agrees
    });
}

export interface AlgebraPolynomialFreydInducedHomologyMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-induced-homology-map';
    readonly chainMap: AlgebraPolynomialFreydHomologyChainMap<P, C, I>;
    readonly cyclesTest: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cyclesMap:
        AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly cyclesMorphism:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cyclesReconstruction:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly cyclesAfterBoundary:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly boundaryAfterNext:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly boundaryCompatibility:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly quotientTest: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly sourceBoundaryComposite:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly sourceBoundaryZero:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly sourceBoundaryZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly induced: AlgebraPolynomialFreydCokernelColift<P, C, I>;
    readonly homologyMap: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly homologyReconstruction:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
}

/** Lift to cycles, prove boundary compatibility, then descend by the cokernel. */
export function algebraPolynomialFreydInducedHomologyMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    chainMap: AlgebraPolynomialFreydHomologyChainMap<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydInducedHomologyMap<P, C, I> {
    if (!chainMap.isChainMap) {
        return fail(
            'CHAIN_MAP_CONDITION_FAILED',
            'freydInducedHomology.chainMap',
            'Induced homology requires both selected chain-square agreements'
        );
    }
    const cyclesTest = algebraPolynomialPresentationMorphismCompose(
        chainMap.f,
        chainMap.source.cycleEmbedding
    );
    const cyclesMap = algebraPolynomialFreydKernelLift(
        chainMap.target.cycles,
        cyclesTest,
        options
    );
    const cyclesAfterBoundary = algebraPolynomialPresentationMorphismCompose(
        cyclesMap.lift,
        chainMap.source.boundaryMorphism
    );
    const boundaryAfterNext = algebraPolynomialPresentationMorphismCompose(
        chainMap.target.boundaryMorphism,
        chainMap.fNext
    );
    const boundaryCompatibility =
        algebraPolynomialPresentationMorphismCongruence(
            cyclesAfterBoundary,
            boundaryAfterNext
        );
    const quotientTest = algebraPolynomialPresentationMorphismCompose(
        chainMap.target.homologyProjection,
        cyclesMap.lift
    );
    const sourceBoundaryComposite =
        algebraPolynomialPresentationMorphismCompose(
            quotientTest,
            chainMap.source.boundaryMorphism
        );
    const sourceBoundaryZero = algebraPolynomialPresentationMorphismZero(
        chainMap.source.pair.dNext.source,
        chainMap.target.homologyObject
    );
    const sourceBoundaryZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            sourceBoundaryComposite,
            sourceBoundaryZero
        );
    if (
        !cyclesMap.reconstructionAgreement.agrees ||
        !boundaryCompatibility.agrees ||
        !sourceBoundaryZeroAgreement.agrees
    ) {
        return fail(
            'INVALID_INDUCED_HOMOLOGY_MAP',
            'freydInducedHomology.factorization',
            'Selected cycle or boundary factorization failed'
        );
    }
    const induced = algebraPolynomialFreydCokernelColift(
        chainMap.source.homology,
        quotientTest
    );
    if (!induced.reconstructionAgreement.agrees) {
        return fail(
            'INVALID_INDUCED_HOMOLOGY_MAP',
            'freydInducedHomology.reconstruction',
            'Selected homology map failed cokernel reconstruction'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-induced-homology-map',
        chainMap,
        cyclesTest,
        cyclesMap,
        cyclesMorphism: cyclesMap.lift,
        cyclesReconstruction: cyclesMap.reconstructionAgreement,
        cyclesAfterBoundary,
        boundaryAfterNext,
        boundaryCompatibility,
        quotientTest,
        sourceBoundaryComposite,
        sourceBoundaryZero,
        sourceBoundaryZeroAgreement,
        induced,
        homologyMap: induced.colift,
        homologyReconstruction: induced.reconstructionAgreement
    });
}

/** Identity chain-map consumer at one homology degree. */
export function algebraPolynomialFreydHomologyIdentityMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(homology: AlgebraPolynomialFreydHomologyAt<P, C, I>):
    AlgebraPolynomialFreydInducedHomologyMap<P, C, I> {
    return algebraPolynomialFreydInducedHomologyMap(
        algebraPolynomialFreydHomologyChainMap({
            source: homology,
            target: homology,
            fNext: algebraPolynomialPresentationMorphismIdentity(
                homology.pair.dNext.source
            ),
            f: algebraPolynomialPresentationMorphismIdentity(
                homology.pair.dNext.target
            ),
            fPrev: algebraPolynomialPresentationMorphismIdentity(
                homology.pair.d.target
            )
        })
    );
}
