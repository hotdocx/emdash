/** Presented tensor products and affine fiber products. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraGroebnerOptions, algebraPolynomialIdeal } from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomial,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from './algebra_polynomial';
import {
    AlgebraQuotientElement,
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientEquals
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebra,
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebra,
    algebraPresentedAlgebraEquals,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapApply,
    algebraPresentedAlgebraMapEquals
} from './algebra_presented_algebra';
import {
    AlgebraAffineMorphism,
    AlgebraAffineScheme,
    algebraAffineMorphism,
    algebraAffineMorphismCompose,
    algebraAffineMorphismEquals,
    algebraAffineScheme,
    algebraAffineSchemeEquals
} from './algebra_affine_scheme';

export const ALGEBRA_TENSOR_PROFILE = Object.freeze({
    revision: 'emdash-presented-tensor-product-v1' as const,
    variableLayout: 'left-block-then-right-block' as const,
    monomialOrder: 'lex' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraTensorErrorCode =
    | 'INVALID_BASE_MAP'
    | 'INCOMPATIBLE_TENSOR_MAPS'
    | 'INVALID_UNIVERSAL_TARGET'
    | 'NON_PARALLEL_FIBER_PRODUCT';

export class AlgebraTensorError extends Error {
    constructor(
        public readonly code: AlgebraTensorErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraTensorError';
    }
}

const fail = (
    code: AlgebraTensorErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraTensorError(code, path, message);
};

const embed = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    polynomial: AlgebraPolynomial<P, C, I>,
    target: AlgebraPolynomialRing<P, C, I>,
    offset: number
): AlgebraPolynomial<P, C, I> => algebraPolynomial(
    target,
    polynomial.terms.map(term => ({
        coefficient: term.coefficient,
        exponents: [
            ...Array.from({ length: offset }, () => 0n),
            ...term.monomial.exponents,
            ...Array.from({
                length: target.variables.length - offset -
                    term.monomial.exponents.length
            }, () => 0n)
        ]
    }))
);

export interface AlgebraTensorCompatibility<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly baseGenerator: number;
    readonly leftImage: AlgebraQuotientElement<P, C, I>;
    readonly rightImage: AlgebraQuotientElement<P, C, I>;
    readonly equal: boolean;
}

export interface AlgebraPresentedTensorProduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-tensor-product';
    readonly base: AlgebraPresentedAlgebra<P, C, I>;
    readonly left: AlgebraPresentedAlgebra<P, C, I>;
    readonly right: AlgebraPresentedAlgebra<P, C, I>;
    readonly leftBaseMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly rightBaseMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly polynomialRing: AlgebraPolynomialRing<P, C, I>;
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly leftMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly rightMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly compatibility: readonly AlgebraTensorCompatibility<P, C, I>[];
}

export function algebraPresentedTensorProduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    base: AlgebraPresentedAlgebra<P, C, I>,
    leftBaseMap: AlgebraPresentedAlgebraMap<P, C, I>,
    rightBaseMap: AlgebraPresentedAlgebraMap<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraPresentedTensorProduct<P, C, I> {
    if (!algebraPresentedAlgebraEquals(leftBaseMap.source, base) ||
        !algebraPresentedAlgebraEquals(rightBaseMap.source, base)) {
        return fail(
            'INVALID_BASE_MAP',
            'tensorProduct.baseMaps',
            'Tensor-product maps must share the selected source algebra'
        );
    }
    const left = leftBaseMap.target;
    const right = rightBaseMap.target;
    const leftRing = left.quotient.polynomialRing;
    const rightRing = right.quotient.polynomialRing;
    const polynomialRing = algebraPolynomialRing(
        leftRing.coefficientDomain,
        [
            ...leftRing.variables.map(name => `left_${name}`),
            ...rightRing.variables.map(name => `right_${name}`)
        ],
        ALGEBRA_TENSOR_PROFILE.monomialOrder
    );
    const rightOffset = leftRing.variables.length;
    const relations = [
        ...left.quotient.ideal.generators.map(value =>
            embed(value, polynomialRing, 0)
        ),
        ...right.quotient.ideal.generators.map(value =>
            embed(value, polynomialRing, rightOffset)
        ),
        ...leftBaseMap.generatorImages.map((leftImage, index) =>
            algebraPolynomialSubtract(
                embed(leftImage.representative, polynomialRing, 0),
                embed(
                    rightBaseMap.generatorImages[index].representative,
                    polynomialRing,
                    rightOffset
                )
            )
        )
    ];
    const algebra = algebraPresentedAlgebra(algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(polynomialRing, relations),
        options
    ));
    const leftMap = algebraPresentedAlgebraMap(
        left,
        algebra,
        leftRing.variables.map((_, index) => algebraQuotientElement(
            algebra.quotient,
            algebraPolynomialVariable(polynomialRing, index)
        ))
    );
    const rightMap = algebraPresentedAlgebraMap(
        right,
        algebra,
        rightRing.variables.map((_, index) => algebraQuotientElement(
            algebra.quotient,
            algebraPolynomialVariable(polynomialRing, rightOffset + index)
        ))
    );
    const compatibility = Object.freeze(leftBaseMap.generatorImages.map(
        (image, index) => {
            const leftImage = algebraPresentedAlgebraMapApply(leftMap, image);
            const rightImage = algebraPresentedAlgebraMapApply(
                rightMap,
                rightBaseMap.generatorImages[index]
            );
            return Object.freeze({
                baseGenerator: index,
                leftImage,
                rightImage,
                equal: algebraQuotientEquals(leftImage, rightImage)
            });
        }
    ));
    if (compatibility.some(value => !value.equal)) {
        return fail(
            'INCOMPATIBLE_TENSOR_MAPS',
            'tensorProduct.compatibility',
            'Canonical tensor maps do not agree on the base algebra'
        );
    }
    return Object.freeze({
        kind: 'algebra-presented-tensor-product',
        base,
        left,
        right,
        leftBaseMap,
        rightBaseMap,
        polynomialRing,
        algebra,
        leftMap,
        rightMap,
        compatibility
    });
}

export interface AlgebraTensorFactorization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-tensor-factorization';
    readonly tensor: AlgebraPresentedTensorProduct<P, C, I>;
    readonly leftMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly rightMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly compatibility: readonly AlgebraTensorCompatibility<P, C, I>[];
    readonly map: AlgebraPresentedAlgebraMap<P, C, I>;
}

export function algebraPresentedTensorFactor<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    tensor: AlgebraPresentedTensorProduct<P, C, I>,
    leftMap: AlgebraPresentedAlgebraMap<P, C, I>,
    rightMap: AlgebraPresentedAlgebraMap<P, C, I>
): AlgebraTensorFactorization<P, C, I> {
    if (!algebraPresentedAlgebraEquals(leftMap.source, tensor.left) ||
        !algebraPresentedAlgebraEquals(rightMap.source, tensor.right) ||
        !algebraPresentedAlgebraEquals(leftMap.target, rightMap.target)) {
        return fail(
            'INVALID_UNIVERSAL_TARGET',
            'tensorFactor.maps',
            'Tensor factor maps require the two factors and one common target'
        );
    }
    const compatibility = Object.freeze(tensor.leftBaseMap.generatorImages.map(
        (image, index) => {
            const leftImage = algebraPresentedAlgebraMapApply(leftMap, image);
            const rightImage = algebraPresentedAlgebraMapApply(
                rightMap,
                tensor.rightBaseMap.generatorImages[index]
            );
            return Object.freeze({
                baseGenerator: index,
                leftImage,
                rightImage,
                equal: algebraQuotientEquals(leftImage, rightImage)
            });
        }
    ));
    if (compatibility.some(value => !value.equal)) {
        return fail(
            'INCOMPATIBLE_TENSOR_MAPS',
            'tensorFactor.compatibility',
            'Candidate factor maps disagree on the base algebra'
        );
    }
    return Object.freeze({
        kind: 'algebra-tensor-factorization',
        tensor,
        leftMap,
        rightMap,
        compatibility,
        map: algebraPresentedAlgebraMap(
            tensor.algebra,
            leftMap.target,
            [...leftMap.generatorImages, ...rightMap.generatorImages]
        )
    });
}

export interface AlgebraAffineFiberProduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-fiber-product';
    readonly left: AlgebraAffineMorphism<P, C, I>;
    readonly right: AlgebraAffineMorphism<P, C, I>;
    readonly tensor: AlgebraPresentedTensorProduct<P, C, I>;
    readonly scheme: AlgebraAffineScheme<P, C, I>;
    readonly leftProjection: AlgebraAffineMorphism<P, C, I>;
    readonly rightProjection: AlgebraAffineMorphism<P, C, I>;
    readonly leftComposite: AlgebraAffineMorphism<P, C, I>;
    readonly rightComposite: AlgebraAffineMorphism<P, C, I>;
    readonly compatible: boolean;
}

export function algebraAffineFiberProduct<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraAffineMorphism<P, C, I>,
    right: AlgebraAffineMorphism<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraAffineFiberProduct<P, C, I> {
    if (!algebraAffineSchemeEquals(left.target, right.target)) {
        return fail(
            'NON_PARALLEL_FIBER_PRODUCT',
            'affineFiberProduct.targets',
            'Affine fiber-product maps require one target scheme'
        );
    }
    const tensor = algebraPresentedTensorProduct(
        left.target.coordinateAlgebra,
        left.coordinateMap,
        right.coordinateMap,
        options
    );
    const scheme = algebraAffineScheme(tensor.algebra);
    const leftProjection = algebraAffineMorphism(
        scheme,
        left.source,
        tensor.leftMap
    );
    const rightProjection = algebraAffineMorphism(
        scheme,
        right.source,
        tensor.rightMap
    );
    const leftComposite = algebraAffineMorphismCompose(left, leftProjection);
    const rightComposite = algebraAffineMorphismCompose(right, rightProjection);
    return Object.freeze({
        kind: 'algebra-affine-fiber-product',
        left,
        right,
        tensor,
        scheme,
        leftProjection,
        rightProjection,
        leftComposite,
        rightComposite,
        compatible: algebraAffineMorphismEquals(leftComposite, rightComposite)
    });
}
