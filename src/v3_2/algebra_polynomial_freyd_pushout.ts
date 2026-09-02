/** Genuine pushouts in the polynomial Freyd category. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialFreydBiproduct,
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialFreydBiproduct,
    algebraPolynomialPresentationMorphismAdd,
    algebraPolynomialPresentationMorphismCompose,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismNegate
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydCokernel,
    AlgebraPolynomialFreydCokernelColift,
    AlgebraPolynomialFreydCokernelUniqueness,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydCokernelColiftUnique
} from './algebra_polynomial_freyd_cokernel';

export const ALGEBRA_POLYNOMIAL_FREYD_PUSHOUT_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-pushout-v1' as const,
    construction: 'cokernel-of-biproduct-difference' as const,
    coconeRepresentation: 'copair-annihilating-difference' as const,
    claimsContractibleCofactors: true as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydPushoutErrorCode =
    | 'INVALID_SPAN'
    | 'INVALID_PUSHOUT'
    | 'INVALID_TEST_PAIR'
    | 'INCOMPATIBLE_TEST_PAIR';

export class AlgebraPolynomialFreydPushoutError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydPushoutErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydPushoutError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydPushoutErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydPushoutError(code, path, message);
};

const checkedAgreement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialPresentationMorphism<P, C, I>,
    right: AlgebraPolynomialPresentationMorphism<P, C, I>,
    path: string,
    message: string
): AlgebraPolynomialPresentationMorphismAgreement<P, C, I> => {
    const result = algebraPolynomialPresentationMorphismCongruence(left, right);
    if (!result.agrees) fail('INVALID_PUSHOUT', path, message);
    return result;
};

export interface AlgebraPolynomialFreydPushout<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-pushout';
    readonly left: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly right: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly biproduct: AlgebraPolynomialFreydBiproduct<P, C, I>;
    readonly leftIntoBiproduct:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly negatedRightIntoBiproduct:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly difference: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly object: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly combinedMorphism:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly injectionLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly injectionRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly compatibilityLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly compatibilityRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly compatibilityAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly compatible: true;
    readonly claimsContractibleCofactors: true;
}

export interface AlgebraPolynomialFreydPushoutCofactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-pushout-cofactor';
    readonly pushout: AlgebraPolynomialFreydPushout<P, C, I>;
    readonly testLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCompatibilityLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCompatibilityRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCompatibilityAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly copairLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly copairRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly copairTest: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cokernelColift: AlgebraPolynomialFreydCokernelColift<P, C, I>;
    readonly cofactor: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionCombined:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionCombinedAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructionLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionLeftAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructionRightAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructs: true;
    readonly claimsUniqueCofactor: true;
}

/** Construct the genuine pushout as Coker(⟨left,−right⟩). */
export function algebraPolynomialFreydPushout<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialPresentationMorphism<P, C, I>,
    right: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydPushout<P, C, I> {
    if (!algebraPresentedPolynomialModuleEquals(left.source, right.source)) {
        fail(
            'INVALID_SPAN',
            'freydPushout.span',
            'Pushout arrows must have the same source presentation'
        );
    }
    const biproduct = algebraPolynomialFreydBiproduct(
        left.target,
        right.target
    );
    const leftIntoBiproduct = algebraPolynomialPresentationMorphismCompose(
        biproduct.injectionLeft,
        left
    );
    const negatedRightIntoBiproduct =
        algebraPolynomialPresentationMorphismCompose(
            biproduct.injectionRight,
            algebraPolynomialPresentationMorphismNegate(right)
        );
    const difference = algebraPolynomialPresentationMorphismAdd(
        leftIntoBiproduct,
        negatedRightIntoBiproduct
    );
    const cokernel = algebraPolynomialFreydCokernel(difference);
    const combinedMorphism = cokernel.projection;
    const injectionLeft = algebraPolynomialPresentationMorphismCompose(
        combinedMorphism,
        biproduct.injectionLeft
    );
    const injectionRight = algebraPolynomialPresentationMorphismCompose(
        combinedMorphism,
        biproduct.injectionRight
    );
    const compatibilityLeft = algebraPolynomialPresentationMorphismCompose(
        injectionLeft,
        left
    );
    const compatibilityRight = algebraPolynomialPresentationMorphismCompose(
        injectionRight,
        right
    );
    const compatibilityAgreement = checkedAgreement(
        compatibilityLeft,
        compatibilityRight,
        'freydPushout.compatibility',
        'Selected difference cokernel does not coequalize the span'
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-pushout',
        left,
        right,
        biproduct,
        leftIntoBiproduct,
        negatedRightIntoBiproduct,
        difference,
        cokernel,
        object: cokernel.object,
        combinedMorphism,
        injectionLeft,
        injectionRight,
        compatibilityLeft,
        compatibilityRight,
        compatibilityAgreement,
        compatible: true,
        claimsContractibleCofactors: true
    });
}

/** Select the unique-in-the-Freyd-quotient cofactor of a compatible pair. */
export function algebraPolynomialFreydPushoutCofactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    pushout: AlgebraPolynomialFreydPushout<P, C, I>,
    testLeft: AlgebraPolynomialPresentationMorphism<P, C, I>,
    testRight: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydPushoutCofactor<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(testLeft.target, testRight.target) ||
        !algebraPresentedPolynomialModuleEquals(
            testLeft.source,
            pushout.left.target
        ) ||
        !algebraPresentedPolynomialModuleEquals(
            testRight.source,
            pushout.right.target
        )
    ) {
        fail(
            'INVALID_TEST_PAIR',
            'freydPushoutCofactor.tests',
            'Pushout tests must share a target and start at the span targets'
        );
    }
    const testCompatibilityLeft =
        algebraPolynomialPresentationMorphismCompose(
            testLeft,
            pushout.left
        );
    const testCompatibilityRight =
        algebraPolynomialPresentationMorphismCompose(
            testRight,
            pushout.right
        );
    const testCompatibilityAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            testCompatibilityLeft,
            testCompatibilityRight
        );
    if (!testCompatibilityAgreement.agrees) {
        fail(
            'INCOMPATIBLE_TEST_PAIR',
            'freydPushoutCofactor.compatibility',
            'Pushout test maps do not coequalize the span'
        );
    }
    const copairLeft = algebraPolynomialPresentationMorphismCompose(
        testLeft,
        pushout.biproduct.projectionLeft
    );
    const copairRight = algebraPolynomialPresentationMorphismCompose(
        testRight,
        pushout.biproduct.projectionRight
    );
    const copairTest = algebraPolynomialPresentationMorphismAdd(
        copairLeft,
        copairRight
    );
    const cokernelColift = algebraPolynomialFreydCokernelColift(
        pushout.cokernel,
        copairTest
    );
    const cofactor = cokernelColift.colift;
    const reconstructionCombined =
        algebraPolynomialPresentationMorphismCompose(
            cofactor,
            pushout.combinedMorphism
        );
    const reconstructionCombinedAgreement = checkedAgreement(
        reconstructionCombined,
        copairTest,
        'freydPushoutCofactor.combined',
        'Selected pushout cofactor does not reconstruct the copair cocone'
    );
    const reconstructionLeft = algebraPolynomialPresentationMorphismCompose(
        cofactor,
        pushout.injectionLeft
    );
    const reconstructionRight = algebraPolynomialPresentationMorphismCompose(
        cofactor,
        pushout.injectionRight
    );
    const reconstructionLeftAgreement = checkedAgreement(
        reconstructionLeft,
        testLeft,
        'freydPushoutCofactor.left',
        'Selected pushout cofactor does not reconstruct the left test'
    );
    const reconstructionRightAgreement = checkedAgreement(
        reconstructionRight,
        testRight,
        'freydPushoutCofactor.right',
        'Selected pushout cofactor does not reconstruct the right test'
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-pushout-cofactor',
        pushout,
        testLeft,
        testRight,
        testCompatibilityLeft,
        testCompatibilityRight,
        testCompatibilityAgreement,
        copairLeft,
        copairRight,
        copairTest,
        cokernelColift,
        cofactor,
        reconstructionCombined,
        reconstructionCombinedAgreement,
        reconstructionLeft,
        reconstructionRight,
        reconstructionLeftAgreement,
        reconstructionRightAgreement,
        reconstructs: true,
        claimsUniqueCofactor: true
    });
}

/** Check uniqueness of a competing cofactor using cokernel contractibility. */
export function algebraPolynomialFreydPushoutCofactorUnique<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    selected: AlgebraPolynomialFreydPushoutCofactor<P, C, I>,
    candidate: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydCokernelUniqueness<P, C, I> {
    return algebraPolynomialFreydCokernelColiftUnique(
        selected.cokernelColift,
        candidate
    );
}
