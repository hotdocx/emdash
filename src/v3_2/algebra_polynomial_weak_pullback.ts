/** Computational weak pullbacks derived from additive biproducts and weak kernels. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleGroebnerOptions,
    algebraPolynomialModuleVector
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIsZero,
    algebraPolynomialModuleMapNegate
} from './algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialWeakKernel,
    AlgebraPolynomialWeakKernelFactorOptions,
    AlgebraPolynomialWeakKernelFactorization,
    algebraPolynomialModuleMapWeakKernel,
    algebraPolynomialWeakKernelFactor
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraPolynomialFiniteFreeBiproduct,
    algebraPolynomialFiniteFreeBiproduct
} from './algebra_polynomial_weak_kernel_category';

export const ALGEBRA_POLYNOMIAL_WEAK_PULLBACK_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-weak-pullback-v1' as const,
    construction: 'weak-kernel-of-additive-difference' as const,
    coneRepresentation: 'annihilated-map-into-biproduct' as const,
    claimsUniqueLifts: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialWeakPullbackErrorCode =
    | 'INVALID_COSPAN'
    | 'INVALID_WEAK_PULLBACK'
    | 'INVALID_TEST_PAIR'
    | 'INCOMPATIBLE_TEST_PAIR';

export class AlgebraPolynomialWeakPullbackError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialWeakPullbackErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialWeakPullbackError';
    }
}

const fail = (
    code: AlgebraPolynomialWeakPullbackErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialWeakPullbackError(code, path, message);
};

export interface AlgebraPolynomialWeakPullback<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-weak-pullback';
    readonly left: AlgebraPolynomialModuleMap<P, C, I>;
    readonly right: AlgebraPolynomialModuleMap<P, C, I>;
    readonly biproduct: AlgebraPolynomialFiniteFreeBiproduct<P, C, I>;
    readonly difference: AlgebraPolynomialModuleMap<P, C, I>;
    readonly weakKernel: AlgebraPolynomialWeakKernel<P, C, I>;
    readonly object: AlgebraPolynomialWeakKernel<P, C, I>['object'];
    readonly combinedMorphism: AlgebraPolynomialModuleMap<P, C, I>;
    readonly projectionLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly projectionRight: AlgebraPolynomialModuleMap<P, C, I>;
    readonly compatibilityLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly compatibilityRight: AlgebraPolynomialModuleMap<P, C, I>;
    readonly compatible: true;
    readonly claimsUniqueLifts: false;
}

export interface AlgebraPolynomialWeakPullbackFactorization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-weak-pullback-factorization';
    readonly weakPullback: AlgebraPolynomialWeakPullback<P, C, I>;
    readonly testLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly testRight: AlgebraPolynomialModuleMap<P, C, I>;
    readonly pairedTest: AlgebraPolynomialModuleMap<P, C, I>;
    readonly testCompatibilityLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly testCompatibilityRight: AlgebraPolynomialModuleMap<P, C, I>;
    readonly weakKernelFactorization:
        AlgebraPolynomialWeakKernelFactorization<P, C, I>;
    readonly lift: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstructionCombined: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstructionLeft: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstructionRight: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstructs: true;
    readonly claimsUniqueLift: false;
}

const assertCommonTarget = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>
): void => {
    if (!sameAlgebraParent(left.target, right.target)) {
        fail(
            'INVALID_COSPAN',
            'weakPullback.cospan',
            'Weak-pullback arrows must have one target free module'
        );
    }
};

/** Compute the weak pullback as the weak kernel of [left,-right]. */
export function algebraPolynomialModuleMapWeakPullback<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialModuleMap<P, C, I>,
    right: AlgebraPolynomialModuleMap<P, C, I>,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialWeakPullback<P, C, I> {
    assertCommonTarget(left, right);
    const biproduct = algebraPolynomialFiniteFreeBiproduct(
        left.source,
        right.source
    );
    const negatedRight = algebraPolynomialModuleMapNegate(right);
    const difference = algebraPolynomialModuleMap(
        biproduct.object,
        left.target,
        [...left.columns, ...negatedRight.columns]
    );
    const weakKernel = algebraPolynomialModuleMapWeakKernel(difference, options);
    const combinedMorphism = weakKernel.morphism;
    const projectionLeft = algebraPolynomialModuleMapCompose(
        biproduct.projectionLeft,
        combinedMorphism
    );
    const projectionRight = algebraPolynomialModuleMapCompose(
        biproduct.projectionRight,
        combinedMorphism
    );
    const compatibilityLeft = algebraPolynomialModuleMapCompose(
        left,
        projectionLeft
    );
    const compatibilityRight = algebraPolynomialModuleMapCompose(
        right,
        projectionRight
    );
    if (!algebraPolynomialModuleMapEquals(
        compatibilityLeft,
        compatibilityRight
    )) {
        fail(
            'INVALID_WEAK_PULLBACK',
            'weakPullback.compatibility',
            'Selected difference weak kernel does not equalize the cospan'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-weak-pullback',
        left,
        right,
        biproduct,
        difference,
        weakKernel,
        object: weakKernel.object,
        combinedMorphism,
        projectionLeft,
        projectionRight,
        compatibilityLeft,
        compatibilityRight,
        compatible: true,
        claimsUniqueLifts: false
    });
}

/** Select a weak-pullback lift of one compatible pair of test maps. */
export function algebraPolynomialWeakPullbackFactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    weakPullback: AlgebraPolynomialWeakPullback<P, C, I>,
    testLeft: AlgebraPolynomialModuleMap<P, C, I>,
    testRight: AlgebraPolynomialModuleMap<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialWeakPullbackFactorization<P, C, I> {
    if (
        !sameAlgebraParent(testLeft.source, testRight.source) ||
        !sameAlgebraParent(testLeft.target, weakPullback.left.source) ||
        !sameAlgebraParent(testRight.target, weakPullback.right.source)
    ) {
        fail(
            'INVALID_TEST_PAIR',
            'weakPullbackFactor.tests',
            'Weak-pullback tests must share a source and target the cospan sources'
        );
    }
    const testCompatibilityLeft = algebraPolynomialModuleMapCompose(
        weakPullback.left,
        testLeft
    );
    const testCompatibilityRight = algebraPolynomialModuleMapCompose(
        weakPullback.right,
        testRight
    );
    if (!algebraPolynomialModuleMapEquals(
        testCompatibilityLeft,
        testCompatibilityRight
    )) {
        fail(
            'INCOMPATIBLE_TEST_PAIR',
            'weakPullbackFactor.tests',
            'Weak-pullback test maps do not equalize the cospan'
        );
    }
    const pairedTest = algebraPolynomialModuleMap(
        testLeft.source,
        weakPullback.biproduct.object,
        testLeft.columns.map((leftColumn, index) =>
            algebraPolynomialModuleVector(
                weakPullback.biproduct.object,
                [
                    ...leftColumn.components,
                    ...testRight.columns[index].components
                ]
            )
        )
    );
    const pairedAnnihilation = algebraPolynomialModuleMapCompose(
        weakPullback.difference,
        pairedTest
    );
    if (!algebraPolynomialModuleMapIsZero(pairedAnnihilation)) {
        fail(
            'INCOMPATIBLE_TEST_PAIR',
            'weakPullbackFactor.pairedTest',
            'Compatible test maps did not form an annihilated difference map'
        );
    }
    const weakKernelFactorization = algebraPolynomialWeakKernelFactor(
        weakPullback.weakKernel,
        pairedTest,
        options
    );
    const lift = weakKernelFactorization.lift;
    const reconstructionCombined = weakKernelFactorization.reconstruction;
    const reconstructionLeft = algebraPolynomialModuleMapCompose(
        weakPullback.projectionLeft,
        lift
    );
    const reconstructionRight = algebraPolynomialModuleMapCompose(
        weakPullback.projectionRight,
        lift
    );
    if (
        !algebraPolynomialModuleMapEquals(reconstructionLeft, testLeft) ||
        !algebraPolynomialModuleMapEquals(reconstructionRight, testRight)
    ) {
        fail(
            'INVALID_WEAK_PULLBACK',
            'weakPullbackFactor.reconstruction',
            'Selected weak-pullback lift does not reconstruct both test maps'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-weak-pullback-factorization',
        weakPullback,
        testLeft,
        testRight,
        pairedTest,
        testCompatibilityLeft,
        testCompatibilityRight,
        weakKernelFactorization,
        lift,
        reconstructionCombined,
        reconstructionLeft,
        reconstructionRight,
        reconstructs: true,
        claimsUniqueLift: false
    });
}
