/** Derived image/coimage comparison and isomorphism in polynomial Freyd. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPolynomialPresentationMorphismCompose,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismIdentity
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydKernel,
    AlgebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernel,
    AlgebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift
} from './algebra_polynomial_freyd_cokernel';
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

export const ALGEBRA_POLYNOMIAL_FREYD_IMAGES_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-images-v1' as const,
    coimage: 'cokernel-of-kernel' as const,
    image: 'kernel-of-cokernel' as const,
    comparison: 'universal-coimage-to-image' as const,
    inverse: 'normality-lift-and-colift' as const,
    postulatesIsomorphism: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydImagesErrorCode =
    | 'INVALID_IMAGE_COMPARISON'
    | 'INVALID_IMAGE_ISOMORPHISM';

export class AlgebraPolynomialFreydImagesError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydImagesErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydImagesError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydImagesErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydImagesError(code, path, message);
};

export interface AlgebraPolynomialFreydImageCoimageComparison<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-image-coimage-comparison';
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly kernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly coimage: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly cokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly image: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly coastriction: AlgebraPolynomialFreydCokernelColift<P, C, I>;
    readonly comparisonLift: AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly comparison: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly coastrictionToImage:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly astrictionFromCoimage:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly factorization:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly factorizationAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly factors: true;
}

/** Derive the canonical Coim(f) -> Im(f) comparison and factorization. */
export function algebraPolynomialFreydImageCoimageComparison<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraPolynomialPresentationMorphism<P, C, I>):
    AlgebraPolynomialFreydImageCoimageComparison<P, C, I> {
    const kernel = algebraPolynomialFreydKernel(morphism);
    const coimage = algebraPolynomialFreydCokernel(kernel.embedding);
    const cokernel = algebraPolynomialFreydCokernel(morphism);
    const image = algebraPolynomialFreydKernel(cokernel.projection);
    const coastriction = algebraPolynomialFreydCokernelColift(
        coimage,
        morphism
    );
    const comparisonLift = algebraPolynomialFreydKernelLift(
        image,
        coastriction.colift
    );
    const comparison = comparisonLift.lift;
    const comparisonAfterProjection =
        algebraPolynomialPresentationMorphismCompose(
            comparison,
            coimage.projection
        );
    const factorization = algebraPolynomialPresentationMorphismCompose(
        image.embedding,
        comparisonAfterProjection
    );
    const factorizationAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            factorization,
            morphism
        );
    if (!factorizationAgreement.agrees) {
        return fail(
            'INVALID_IMAGE_COMPARISON',
            'freydImageComparison.factorization',
            'Canonical image/coimage comparison does not factor the morphism'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-image-coimage-comparison',
        morphism,
        kernel,
        coimage,
        cokernel,
        image,
        coastriction,
        comparisonLift,
        comparison,
        coastrictionToImage: comparisonAfterProjection,
        astrictionFromCoimage: coastriction.colift,
        factorization,
        factorizationAgreement,
        factors: true
    });
}

export interface AlgebraPolynomialFreydImageCoimageIsomorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-image-coimage-isomorphism';
    readonly comparison:
        AlgebraPolynomialFreydImageCoimageComparison<P, C, I>;
    readonly monomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly epimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly identityImage: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly identityCoimage: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly inverseFromMonic:
        AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>;
    readonly inverseFromEpic:
        AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>;
    readonly inverseCandidatesAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly inverse: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly comparisonAfterInverse:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly inverseAfterComparison:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly rightInverseAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly leftInverseAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly isomorphism: true;
}

/** Construct the comparison inverse through normal mono/epi operations. */
export function algebraPolynomialFreydImageCoimageIsomorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(comparison: AlgebraPolynomialFreydImageCoimageComparison<P, C, I>):
    AlgebraPolynomialFreydImageCoimageIsomorphism<P, C, I> {
    const monomorphism = algebraPolynomialFreydMonomorphismWitness(
        comparison.comparison
    );
    const epimorphism = algebraPolynomialFreydEpimorphismWitness(
        comparison.comparison
    );
    const identityImage = algebraPolynomialPresentationMorphismIdentity(
        comparison.image.object
    );
    const identityCoimage = algebraPolynomialPresentationMorphismIdentity(
        comparison.coimage.object
    );
    const inverseFromMonic = algebraPolynomialFreydLiftAlongMonomorphism(
        monomorphism,
        identityImage
    );
    const inverseFromEpic = algebraPolynomialFreydColiftAlongEpimorphism(
        epimorphism,
        identityCoimage
    );
    const inverseCandidatesAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            inverseFromMonic.lift,
            inverseFromEpic.colift
        );
    if (!inverseCandidatesAgreement.agrees) {
        return fail(
            'INVALID_IMAGE_ISOMORPHISM',
            'freydImageIsomorphism.inverseCandidates',
            'Normal mono and epi constructions selected inequivalent inverses'
        );
    }
    const inverse = inverseFromMonic.lift;
    const comparisonAfterInverse =
        algebraPolynomialPresentationMorphismCompose(
            comparison.comparison,
            inverse
        );
    const inverseAfterComparison =
        algebraPolynomialPresentationMorphismCompose(
            inverse,
            comparison.comparison
        );
    const rightInverseAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            comparisonAfterInverse,
            identityImage
        );
    const leftInverseAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            inverseAfterComparison,
            identityCoimage
        );
    if (!rightInverseAgreement.agrees || !leftInverseAgreement.agrees) {
        return fail(
            'INVALID_IMAGE_ISOMORPHISM',
            'freydImageIsomorphism.inverseLaws',
            'Constructed coimage/image inverse failed a quotient inverse law'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-image-coimage-isomorphism',
        comparison,
        monomorphism,
        epimorphism,
        identityImage,
        identityCoimage,
        inverseFromMonic,
        inverseFromEpic,
        inverseCandidatesAgreement,
        inverse,
        comparisonAfterInverse,
        inverseAfterComparison,
        rightInverseAgreement,
        leftInverseAgreement,
        isomorphism: true
    });
}

/** Whole derived image/coimage computation including the comparison inverse. */
export function algebraPolynomialFreydImages<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraPolynomialPresentationMorphism<P, C, I>):
    AlgebraPolynomialFreydImageCoimageIsomorphism<P, C, I> {
    return algebraPolynomialFreydImageCoimageIsomorphism(
        algebraPolynomialFreydImageCoimageComparison(morphism)
    );
}
