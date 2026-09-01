/** Constructive cokernels in the polynomial Freyd/presentation category. */

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
    algebraPolynomialModuleMapIdentity
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCompose,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';

export const ALGEBRA_POLYNOMIAL_FREYD_COKERNEL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-cokernel-v1' as const,
    construction: 'adjoin-morphism-columns-to-target-relations' as const,
    projectionDatum: 'target-ambient-identity' as const,
    universalEquality: 'target-factorization-congruence' as const,
    requiresWeakKernels: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydCokernelErrorCode =
    | 'INVALID_COKERNEL'
    | 'NON_ANNIHILATED_TEST'
    | 'INVALID_COLIFT'
    | 'INVALID_COMPETING_COLIFT';

export class AlgebraPolynomialFreydCokernelError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydCokernelErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydCokernelError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydCokernelErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydCokernelError(code, path, message);
};

export interface AlgebraPolynomialFreydCokernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-cokernel';
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly object: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly projection: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly annihilation:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly annihilationAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly annihilates: true;
}

export interface AlgebraPolynomialFreydCokernelColift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-cokernel-colift';
    readonly cokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zeroComposite:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly zeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly colift: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstruction:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructs: true;
}

export interface AlgebraPolynomialFreydCokernelUniqueness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-cokernel-uniqueness';
    readonly selected: AlgebraPolynomialFreydCokernelColift<P, C, I>;
    readonly candidate: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstruction:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniquenessAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniqueInQuotient: true;
}

/** Adjoin the morphism columns to the target relations. */
export function algebraPolynomialFreydCokernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    morphism: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydCokernel<P, C, I> {
    if (!morphism.preservesRelations) {
        fail(
            'INVALID_COKERNEL',
            'freydCokernel.morphism',
            'Freyd cokernel requires a relation-preserving morphism'
        );
    }
    const object = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(morphism.target.ambient, [
            ...morphism.target.relations.generators,
            ...morphism.map.columns
        ])
    );
    const projection = algebraPolynomialPresentationMorphism({
        source: morphism.target,
        target: object,
        map: algebraPolynomialModuleMapIdentity(morphism.target.ambient)
    });
    if (!projection.preservesRelations) {
        fail(
            'INVALID_COKERNEL',
            'freydCokernel.projection',
            'Constructed identity datum failed relation preservation'
        );
    }
    const annihilation = algebraPolynomialPresentationMorphismCompose(
        projection,
        morphism
    );
    const zero = algebraPolynomialPresentationMorphismZero(
        morphism.source,
        object
    );
    const annihilationAgreement =
        algebraPolynomialPresentationMorphismCongruence(annihilation, zero);
    if (!annihilationAgreement.agrees) {
        fail(
            'INVALID_COKERNEL',
            'freydCokernel.annihilation',
            'Constructed Freyd cokernel projection does not annihilate the map'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-cokernel',
        morphism,
        object,
        projection,
        annihilation,
        zero,
        annihilationAgreement,
        annihilates: true
    });
}

/** Construct and verify the induced map from a zero-composite test. */
export function algebraPolynomialFreydCokernelColift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    cokernel: AlgebraPolynomialFreydCokernel<P, C, I>,
    test: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydCokernelColift<P, C, I> {
    if (!algebraPresentedPolynomialModuleEquals(
        test.source,
        cokernel.morphism.target
    )) {
        fail(
            'INVALID_COLIFT',
            'freydCokernelColift.test',
            'Cokernel test must start at the original morphism target'
        );
    }
    const zeroComposite = algebraPolynomialPresentationMorphismCompose(
        test,
        cokernel.morphism
    );
    const zero = algebraPolynomialPresentationMorphismZero(
        cokernel.morphism.source,
        test.target
    );
    const zeroAgreement = algebraPolynomialPresentationMorphismCongruence(
        zeroComposite,
        zero
    );
    if (!zeroAgreement.agrees) {
        fail(
            'NON_ANNIHILATED_TEST',
            'freydCokernelColift.test',
            'Test morphism does not annihilate the cokernel input in the quotient'
        );
    }
    const colift = algebraPolynomialPresentationMorphism({
        source: cokernel.object,
        target: test.target,
        map: test.map
    });
    if (!colift.preservesRelations) {
        fail(
            'INVALID_COLIFT',
            'freydCokernelColift.colift',
            'Zero-composite witness did not make the induced map well-defined'
        );
    }
    const reconstruction = algebraPolynomialPresentationMorphismCompose(
        colift,
        cokernel.projection
    );
    const reconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(reconstruction, test);
    if (!reconstructionAgreement.agrees) {
        fail(
            'INVALID_COLIFT',
            'freydCokernelColift.reconstruction',
            'Constructed cokernel colift does not reconstruct the test morphism'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-cokernel-colift',
        cokernel,
        test,
        zeroComposite,
        zero,
        zeroAgreement,
        colift,
        reconstruction,
        reconstructionAgreement,
        reconstructs: true
    });
}

/** Verify uniqueness of a competing colift in the Freyd quotient. */
export function algebraPolynomialFreydCokernelColiftUnique<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    selected: AlgebraPolynomialFreydCokernelColift<P, C, I>,
    candidate: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydCokernelUniqueness<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(
            candidate.source,
            selected.cokernel.object
        ) ||
        !algebraPresentedPolynomialModuleEquals(
            candidate.target,
            selected.test.target
        )
    ) {
        fail(
            'INVALID_COMPETING_COLIFT',
            'freydCokernelColiftUnique.candidate',
            'Competing colift has incorrect endpoints'
        );
    }
    const candidateReconstruction =
        algebraPolynomialPresentationMorphismCompose(
            candidate,
            selected.cokernel.projection
        );
    const candidateReconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidateReconstruction,
            selected.test
        );
    if (!candidateReconstructionAgreement.agrees) {
        fail(
            'INVALID_COMPETING_COLIFT',
            'freydCokernelColiftUnique.reconstruction',
            'Competing colift does not reconstruct the test morphism'
        );
    }
    const uniquenessAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidate,
            selected.colift
        );
    if (!uniquenessAgreement.agrees) {
        fail(
            'INVALID_COKERNEL',
            'freydCokernelColiftUnique.uniqueness',
            'Cokernel projection failed quotient epimorphism uniqueness'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-cokernel-uniqueness',
        selected,
        candidate,
        candidateReconstruction,
        candidateReconstructionAgreement,
        uniquenessAgreement,
        uniqueInQuotient: true
    });
}
