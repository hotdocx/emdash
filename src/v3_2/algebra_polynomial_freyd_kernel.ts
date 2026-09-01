/** Constructive kernels in the polynomial Freyd category from two weak pullbacks. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    algebraPolynomialSubmodule
} from './algebra_polynomial_module';
import {
    AlgebraPresentedPolynomialModule,
    algebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationRelationMap
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCompose,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialModuleGroebnerOptions
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraPolynomialWeakPullback,
    AlgebraPolynomialWeakPullbackFactorization,
    algebraPolynomialModuleMapWeakPullback,
    algebraPolynomialWeakPullbackFactor
} from './algebra_polynomial_weak_pullback';
import {
    AlgebraPolynomialModuleMap,
    algebraPolynomialModuleMapCompose
} from './algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';

export const ALGEBRA_POLYNOMIAL_FREYD_KERNEL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-kernel-v1' as const,
    construction: 'two-biased-weak-pullbacks' as const,
    zeroWitnessUse: 'first-lift-morphism-datum' as const,
    sourceWitnessUse: 'second-lift-relation-datum' as const,
    universalEquality: 'target-factorization-congruence' as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydKernelErrorCode =
    | 'INVALID_KERNEL'
    | 'INVALID_TEST'
    | 'NON_ANNIHILATED_TEST'
    | 'INVALID_LIFT'
    | 'INVALID_COMPETING_LIFT';

export class AlgebraPolynomialFreydKernelError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydKernelErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydKernelError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydKernelErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydKernelError(code, path, message);
};

export interface AlgebraPolynomialFreydKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-kernel';
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly firstWeakPullback: AlgebraPolynomialWeakPullback<P, C, I>;
    readonly secondWeakPullback: AlgebraPolynomialWeakPullback<P, C, I>;
    readonly object: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly embedding: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly expectedEmbeddingWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly expectedEmbeddingWitnessEquation: true;
    readonly annihilation:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly annihilationAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly annihilates: true;
}

export interface AlgebraPolynomialFreydKernelLift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-kernel-lift';
    readonly kernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zeroComposite:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly zeroWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly firstFactorization:
        AlgebraPolynomialWeakPullbackFactorization<P, C, I>;
    readonly sourceRelationsAfterFirstLift:
        AlgebraPolynomialModuleMap<P, C, I>;
    readonly secondFactorization:
        AlgebraPolynomialWeakPullbackFactorization<P, C, I>;
    readonly expectedRelationWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly lift: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly expectedRelationWitnessEquation: true;
    readonly reconstruction:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructs: true;
}

export interface AlgebraPolynomialFreydKernelUniqueness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-kernel-uniqueness';
    readonly selected: AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly candidate: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstruction:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniquenessAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniqueInQuotient: true;
}

/** Construct the Freyd kernel from the two biased weak pullbacks. */
export function algebraPolynomialFreydKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    morphism: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialFreydKernel<P, C, I> {
    if (!morphism.preservesRelations) {
        fail(
            'INVALID_KERNEL',
            'freydKernel.morphism',
            'Freyd kernel requires a relation-preserving morphism'
        );
    }
    const targetRelations = algebraPolynomialPresentationRelationMap(
        morphism.target
    );
    const sourceRelations = algebraPolynomialPresentationRelationMap(
        morphism.source
    );
    const firstWeakPullback = algebraPolynomialModuleMapWeakPullback(
        morphism.map,
        targetRelations,
        options
    );
    const secondWeakPullback = algebraPolynomialModuleMapWeakPullback(
        firstWeakPullback.projectionLeft,
        sourceRelations,
        options
    );
    const object = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(
            firstWeakPullback.object,
            secondWeakPullback.projectionLeft.columns
        ),
        options
    );
    const embedding = algebraPolynomialPresentationMorphism({
        source: object,
        target: morphism.source,
        map: firstWeakPullback.projectionLeft
    });
    if (!embedding.preservesRelations) {
        fail(
            'INVALID_KERNEL',
            'freydKernel.embedding',
            'Constructed weak-pullback projection failed relation preservation'
        );
    }
    const expectedEmbeddingWitness = secondWeakPullback.projectionRight;
    const expectedEmbeddingTarget = algebraPolynomialModuleMapCompose(
        sourceRelations,
        expectedEmbeddingWitness
    );
    const expectedEmbeddingSource = algebraPolynomialModuleMapCompose(
        firstWeakPullback.projectionLeft,
        secondWeakPullback.projectionLeft
    );
    if (!algebraPolynomialModuleMapEquals(
        expectedEmbeddingTarget,
        expectedEmbeddingSource
    )) {
        fail(
            'INVALID_KERNEL',
            'freydKernel.embeddingWitness',
            'Second weak-pullback projection is not an embedding relation witness'
        );
    }
    const annihilation = algebraPolynomialPresentationMorphismCompose(
        morphism,
        embedding
    );
    const zero = algebraPolynomialPresentationMorphismZero(
        object,
        morphism.target
    );
    const annihilationAgreement =
        algebraPolynomialPresentationMorphismCongruence(annihilation, zero);
    if (!annihilationAgreement.agrees) {
        fail(
            'INVALID_KERNEL',
            'freydKernel.annihilation',
            'Constructed Freyd kernel embedding is not annihilated in the quotient'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-kernel',
        morphism,
        firstWeakPullback,
        secondWeakPullback,
        object,
        embedding,
        expectedEmbeddingWitness,
        expectedEmbeddingWitnessEquation: true,
        annihilation,
        zero,
        annihilationAgreement,
        annihilates: true
    });
}

/** Construct a kernel lift using the zero witness and the source relation square. */
export function algebraPolynomialFreydKernelLift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    kernel: AlgebraPolynomialFreydKernel<P, C, I>,
    test: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydKernelLift<P, C, I> {
    if (!algebraPresentedPolynomialModuleEquals(
        test.target,
        kernel.morphism.source
    )) {
        fail(
            'INVALID_TEST',
            'freydKernelLift.test',
            'Kernel test must target the original morphism source'
        );
    }
    const zeroComposite = algebraPolynomialPresentationMorphismCompose(
        kernel.morphism,
        test
    );
    const zero = algebraPolynomialPresentationMorphismZero(
        test.source,
        kernel.morphism.target
    );
    const zeroAgreement = algebraPolynomialPresentationMorphismCongruence(
        zeroComposite,
        zero
    );
    if (!zeroAgreement.agrees) {
        fail(
            'NON_ANNIHILATED_TEST',
            'freydKernelLift.test',
            'Kernel test is not annihilated in the Freyd quotient'
        );
    }
    const zeroWitness = zeroAgreement.agreementWitness;
    const firstFactorization = algebraPolynomialWeakPullbackFactor(
        kernel.firstWeakPullback,
        test.map,
        zeroWitness,
        options
    );
    const testSourceRelations = algebraPolynomialPresentationRelationMap(
        test.source
    );
    const sourceRelationsAfterFirstLift = algebraPolynomialModuleMapCompose(
        firstFactorization.lift,
        testSourceRelations
    );
    const secondFactorization = algebraPolynomialWeakPullbackFactor(
        kernel.secondWeakPullback,
        sourceRelationsAfterFirstLift,
        test.relationWitness,
        options
    );
    const expectedRelationWitness = secondFactorization.lift;
    const lift = algebraPolynomialPresentationMorphism({
        source: test.source,
        target: kernel.object,
        map: firstFactorization.lift
    });
    if (!lift.preservesRelations) {
        fail(
            'INVALID_LIFT',
            'freydKernelLift.lift',
            'Second weak-pullback factor did not make the lift relation-preserving'
        );
    }
    const expectedRelationTarget = algebraPolynomialModuleMapCompose(
        kernel.secondWeakPullback.projectionLeft,
        expectedRelationWitness
    );
    if (!algebraPolynomialModuleMapEquals(
        expectedRelationTarget,
        sourceRelationsAfterFirstLift
    )) {
        fail(
            'INVALID_LIFT',
            'freydKernelLift.relationWitness',
            'Selected second weak-pullback lift does not reconstruct source relations'
        );
    }
    const reconstruction = algebraPolynomialPresentationMorphismCompose(
        kernel.embedding,
        lift
    );
    const reconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(reconstruction, test);
    if (!reconstructionAgreement.agrees) {
        fail(
            'INVALID_LIFT',
            'freydKernelLift.reconstruction',
            'Constructed Freyd kernel lift does not reconstruct the test map'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-kernel-lift',
        kernel,
        test,
        zeroComposite,
        zero,
        zeroAgreement,
        zeroWitness,
        firstFactorization,
        sourceRelationsAfterFirstLift,
        secondFactorization,
        expectedRelationWitness,
        lift,
        expectedRelationWitnessEquation: true,
        reconstruction,
        reconstructionAgreement,
        reconstructs: true
    });
}

/** Verify uniqueness of a competing kernel lift in the Freyd quotient. */
export function algebraPolynomialFreydKernelLiftUnique<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    selected: AlgebraPolynomialFreydKernelLift<P, C, I>,
    candidate: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydKernelUniqueness<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(
            candidate.source,
            selected.test.source
        ) ||
        !algebraPresentedPolynomialModuleEquals(
            candidate.target,
            selected.kernel.object
        )
    ) {
        fail(
            'INVALID_COMPETING_LIFT',
            'freydKernelLiftUnique.candidate',
            'Competing kernel lift has incorrect endpoints'
        );
    }
    const candidateReconstruction =
        algebraPolynomialPresentationMorphismCompose(
            selected.kernel.embedding,
            candidate
        );
    const candidateReconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidateReconstruction,
            selected.test
        );
    if (!candidateReconstructionAgreement.agrees) {
        fail(
            'INVALID_COMPETING_LIFT',
            'freydKernelLiftUnique.reconstruction',
            'Competing kernel lift does not reconstruct the test morphism'
        );
    }
    const uniquenessAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidate,
            selected.lift
        );
    if (!uniquenessAgreement.agrees) {
        fail(
            'INVALID_KERNEL',
            'freydKernelLiftUnique.uniqueness',
            'Kernel embedding failed quotient monomorphism uniqueness'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-kernel-uniqueness',
        selected,
        candidate,
        candidateReconstruction,
        candidateReconstructionAgreement,
        uniquenessAgreement,
        uniqueInQuotient: true
    });
}
