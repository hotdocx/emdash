/** Genuine fiber products in the polynomial Freyd category. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleGroebnerOptions
} from './algebra_polynomial_module';
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
    AlgebraPolynomialFreydKernel,
    AlgebraPolynomialFreydKernelLift,
    AlgebraPolynomialFreydKernelUniqueness,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernelLiftUnique
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_FIBER_PRODUCT_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-fiber-product-v1' as const,
    construction: 'kernel-of-biproduct-difference' as const,
    coneRepresentation: 'paired-arrow-annihilated-by-difference' as const,
    claimsContractibleFactors: true as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydFiberProductErrorCode =
    | 'INVALID_COSPAN'
    | 'INVALID_FIBER_PRODUCT'
    | 'INVALID_TEST_PAIR'
    | 'INCOMPATIBLE_TEST_PAIR';

export class AlgebraPolynomialFreydFiberProductError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydFiberProductErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydFiberProductError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydFiberProductErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydFiberProductError(code, path, message);
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
    if (!result.agrees) fail('INVALID_FIBER_PRODUCT', path, message);
    return result;
};

export interface AlgebraPolynomialFreydFiberProduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-fiber-product';
    readonly left: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly right: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly biproduct: AlgebraPolynomialFreydBiproduct<P, C, I>;
    readonly leftFromBiproduct:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly negatedRightFromBiproduct:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly difference: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly kernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly object: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly combinedMorphism:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly projectionLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly projectionRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly compatibilityLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly compatibilityRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly compatibilityAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly compatible: true;
    readonly claimsContractibleFactors: true;
}

export interface AlgebraPolynomialFreydFiberProductFactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-fiber-product-factor';
    readonly fiberProduct: AlgebraPolynomialFreydFiberProduct<P, C, I>;
    readonly testLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCompatibilityLeft:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCompatibilityRight:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCompatibilityAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly pairedLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly pairedRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly pairedTest: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly kernelLift: AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly lift: AlgebraPolynomialPresentationMorphism<P, C, I>;
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
    readonly claimsUniqueFactor: true;
}

/** Construct the genuine fiber product as Ker([left,−right]). */
export function algebraPolynomialFreydFiberProduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialPresentationMorphism<P, C, I>,
    right: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialFreydFiberProduct<P, C, I> {
    if (!algebraPresentedPolynomialModuleEquals(left.target, right.target)) {
        fail(
            'INVALID_COSPAN',
            'freydFiberProduct.cospan',
            'Fiber-product arrows must have the same target presentation'
        );
    }
    const biproduct = algebraPolynomialFreydBiproduct(
        left.source,
        right.source
    );
    const leftFromBiproduct = algebraPolynomialPresentationMorphismCompose(
        left,
        biproduct.projectionLeft
    );
    const negatedRightFromBiproduct =
        algebraPolynomialPresentationMorphismCompose(
            algebraPolynomialPresentationMorphismNegate(right),
            biproduct.projectionRight
        );
    const difference = algebraPolynomialPresentationMorphismAdd(
        leftFromBiproduct,
        negatedRightFromBiproduct
    );
    const kernel = algebraPolynomialFreydKernel(difference, options);
    const combinedMorphism = kernel.embedding;
    const projectionLeft = algebraPolynomialPresentationMorphismCompose(
        biproduct.projectionLeft,
        combinedMorphism
    );
    const projectionRight = algebraPolynomialPresentationMorphismCompose(
        biproduct.projectionRight,
        combinedMorphism
    );
    const compatibilityLeft = algebraPolynomialPresentationMorphismCompose(
        left,
        projectionLeft
    );
    const compatibilityRight = algebraPolynomialPresentationMorphismCompose(
        right,
        projectionRight
    );
    const compatibilityAgreement = checkedAgreement(
        compatibilityLeft,
        compatibilityRight,
        'freydFiberProduct.compatibility',
        'Selected difference kernel does not equalize the cospan'
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-fiber-product',
        left,
        right,
        biproduct,
        leftFromBiproduct,
        negatedRightFromBiproduct,
        difference,
        kernel,
        object: kernel.object,
        combinedMorphism,
        projectionLeft,
        projectionRight,
        compatibilityLeft,
        compatibilityRight,
        compatibilityAgreement,
        compatible: true,
        claimsContractibleFactors: true
    });
}

/** Select the unique-in-the-Freyd-quotient factor of a compatible pair. */
export function algebraPolynomialFreydFiberProductFactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    fiberProduct: AlgebraPolynomialFreydFiberProduct<P, C, I>,
    testLeft: AlgebraPolynomialPresentationMorphism<P, C, I>,
    testRight: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydFiberProductFactor<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(testLeft.source, testRight.source) ||
        !algebraPresentedPolynomialModuleEquals(
            testLeft.target,
            fiberProduct.left.source
        ) ||
        !algebraPresentedPolynomialModuleEquals(
            testRight.target,
            fiberProduct.right.source
        )
    ) {
        fail(
            'INVALID_TEST_PAIR',
            'freydFiberProductFactor.tests',
            'Fiber-product tests must share a source and target the cospan sources'
        );
    }
    const testCompatibilityLeft =
        algebraPolynomialPresentationMorphismCompose(
            fiberProduct.left,
            testLeft
        );
    const testCompatibilityRight =
        algebraPolynomialPresentationMorphismCompose(
            fiberProduct.right,
            testRight
        );
    const testCompatibilityAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            testCompatibilityLeft,
            testCompatibilityRight
        );
    if (!testCompatibilityAgreement.agrees) {
        fail(
            'INCOMPATIBLE_TEST_PAIR',
            'freydFiberProductFactor.compatibility',
            'Fiber-product test maps do not equalize the cospan'
        );
    }
    const pairedLeft = algebraPolynomialPresentationMorphismCompose(
        fiberProduct.biproduct.injectionLeft,
        testLeft
    );
    const pairedRight = algebraPolynomialPresentationMorphismCompose(
        fiberProduct.biproduct.injectionRight,
        testRight
    );
    const pairedTest = algebraPolynomialPresentationMorphismAdd(
        pairedLeft,
        pairedRight
    );
    const kernelLift = algebraPolynomialFreydKernelLift(
        fiberProduct.kernel,
        pairedTest,
        options
    );
    const lift = kernelLift.lift;
    const reconstructionCombined =
        algebraPolynomialPresentationMorphismCompose(
            fiberProduct.combinedMorphism,
            lift
        );
    const reconstructionCombinedAgreement = checkedAgreement(
        reconstructionCombined,
        pairedTest,
        'freydFiberProductFactor.combined',
        'Selected fiber-product factor does not reconstruct the paired cone'
    );
    const reconstructionLeft = algebraPolynomialPresentationMorphismCompose(
        fiberProduct.projectionLeft,
        lift
    );
    const reconstructionRight = algebraPolynomialPresentationMorphismCompose(
        fiberProduct.projectionRight,
        lift
    );
    const reconstructionLeftAgreement = checkedAgreement(
        reconstructionLeft,
        testLeft,
        'freydFiberProductFactor.left',
        'Selected fiber-product factor does not reconstruct the left test'
    );
    const reconstructionRightAgreement = checkedAgreement(
        reconstructionRight,
        testRight,
        'freydFiberProductFactor.right',
        'Selected fiber-product factor does not reconstruct the right test'
    );
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-fiber-product-factor',
        fiberProduct,
        testLeft,
        testRight,
        testCompatibilityLeft,
        testCompatibilityRight,
        testCompatibilityAgreement,
        pairedLeft,
        pairedRight,
        pairedTest,
        kernelLift,
        lift,
        reconstructionCombined,
        reconstructionCombinedAgreement,
        reconstructionLeft,
        reconstructionRight,
        reconstructionLeftAgreement,
        reconstructionRightAgreement,
        reconstructs: true,
        claimsUniqueFactor: true
    });
}

/** Check uniqueness of a competing factor using kernel contractibility. */
export function algebraPolynomialFreydFiberProductFactorUnique<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    selected: AlgebraPolynomialFreydFiberProductFactor<P, C, I>,
    candidate: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydKernelUniqueness<P, C, I> {
    return algebraPolynomialFreydKernelLiftUnique(
        selected.kernelLift,
        candidate
    );
}
