/** Native witnesses for Abelian pullback/pushout stability in polynomial Freyd. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPolynomialPresentationMorphismCongruence
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydFiberProduct
} from './algebra_polynomial_freyd_fiber_product';
import {
    AlgebraPolynomialFreydPushout
} from './algebra_polynomial_freyd_pushout';
import {
    AlgebraPolynomialFreydEpimorphismWitness,
    AlgebraPolynomialFreydMonomorphismWitness,
    algebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydMonomorphismWitness
} from './algebra_polynomial_freyd_normality';

export const ALGEBRA_POLYNOMIAL_FREYD_STABILITY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-stability-v1' as const,
    pullbackOfEpic: true as const,
    pushoutOfMonic: true as const,
    witnessCarrier: 'selected-freyd-kernel-cokernel-agreement' as const,
    claimsGenericFormalProof: false as const,
    performsIo: false as const
});

export interface AlgebraPolynomialFreydFiberProductEpicProjection<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-fiber-product-epic-projection';
    readonly fiberProduct: AlgebraPolynomialFreydFiberProduct<P, C, I>;
    readonly pulledBackEpimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly selectedArrowAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly projectionEpimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly epic: true;
}

/** Witness that the projection opposite a pulled-back epimorphism is epic. */
export function algebraPolynomialFreydFiberProductEpicProjection<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    fiberProduct: AlgebraPolynomialFreydFiberProduct<P, C, I>,
    pulledBackEpimorphism:
        AlgebraPolynomialFreydEpimorphismWitness<P, C, I>
): AlgebraPolynomialFreydFiberProductEpicProjection<P, C, I> {
    const selectedArrowAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            pulledBackEpimorphism.morphism,
            fiberProduct.right
        );
    if (!selectedArrowAgreement.agrees) {
        throw new Error(
            'Fiber-product stability witness does not classify the right cospan arrow'
        );
    }
    const projectionEpimorphism = algebraPolynomialFreydEpimorphismWitness(
        fiberProduct.projectionLeft
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-fiber-product-epic-projection',
        fiberProduct,
        pulledBackEpimorphism,
        selectedArrowAgreement,
        projectionEpimorphism,
        epic: true
    });
}

export interface AlgebraPolynomialFreydPushoutMonicInjection<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-pushout-monic-injection';
    readonly pushout: AlgebraPolynomialFreydPushout<P, C, I>;
    readonly pushedOutMonomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly selectedArrowAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly injectionMonomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly monic: true;
}

/** Witness that the injection opposite a pushed-out monomorphism is monic. */
export function algebraPolynomialFreydPushoutMonicInjection<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    pushout: AlgebraPolynomialFreydPushout<P, C, I>,
    pushedOutMonomorphism:
        AlgebraPolynomialFreydMonomorphismWitness<P, C, I>
): AlgebraPolynomialFreydPushoutMonicInjection<P, C, I> {
    const selectedArrowAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            pushedOutMonomorphism.morphism,
            pushout.left
        );
    if (!selectedArrowAgreement.agrees) {
        throw new Error(
            'Pushout stability witness does not classify the left span arrow'
        );
    }
    const injectionMonomorphism = algebraPolynomialFreydMonomorphismWitness(
        pushout.injectionRight
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-pushout-monic-injection',
        pushout,
        pushedOutMonomorphism,
        selectedArrowAgreement,
        injectionMonomorphism,
        monic: true
    });
}
