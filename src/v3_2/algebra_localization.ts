/** Principal localizations and affine basic-open coordinate charts. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { AlgebraGroebnerOptions, algebraPolynomialIdeal } from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomial,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from './algebra_polynomial';
import {
    AlgebraQuotientElement,
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientOne
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebra,
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapApply
} from './algebra_presented_algebra';

export const ALGEBRA_LOCALIZATION_PROFILE = Object.freeze({
    revision: 'emdash-principal-localization-v1' as const,
    presentation: 'adjoin-inverse-variable-and-tf-minus-one' as const,
    inverseVariableBase: 'emdash_inv' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraLocalizationErrorCode = 'FOREIGN_LOCALIZED_ELEMENT';

export class AlgebraLocalizationError extends Error {
    constructor(
        public readonly code: AlgebraLocalizationErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraLocalizationError';
    }
}

const fail = (path: string, message: string): never => {
    throw new AlgebraLocalizationError('FOREIGN_LOCALIZED_ELEMENT', path, message);
};

const freshInverseVariable = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    ring: AlgebraPolynomialRing<P, C, I>
): string => {
    let candidate: string = ALGEBRA_LOCALIZATION_PROFILE.inverseVariableBase;
    let index = 0;
    while (ring.variables.includes(candidate)) {
        candidate = `${ALGEBRA_LOCALIZATION_PROFILE.inverseVariableBase}${++index}`;
    }
    return candidate;
};

const embed = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    polynomial: AlgebraPolynomial<P, C, I>,
    extended: AlgebraPolynomialRing<P, C, I>
): AlgebraPolynomial<P, C, I> => algebraPolynomial(
    extended,
    polynomial.terms.map(term => ({
        coefficient: term.coefficient,
        exponents: [...term.monomial.exponents, 0n]
    }))
);

export interface AlgebraPrincipalLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-principal-localization';
    readonly source: AlgebraPresentedAlgebra<P, C, I>;
    readonly element: AlgebraQuotientElement<P, C, I>;
    readonly inverseVariable: string;
    readonly extendedRing: AlgebraPolynomialRing<P, C, I>;
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly canonicalMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly inverse: AlgebraQuotientElement<P, C, I>;
    readonly elementImage: AlgebraQuotientElement<P, C, I>;
    readonly inverseProduct: AlgebraQuotientElement<P, C, I>;
    readonly inverseEquation: boolean;
}

export function algebraPrincipalLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebra<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraPrincipalLocalization<P, C, I> {
    if (!sameAlgebraParent(element.parent, source.quotient)) {
        return fail(
            'principalLocalization.element',
            'Localized element belongs to a foreign presented algebra'
        );
    }
    const sourceRing = source.quotient.polynomialRing;
    const inverseVariable = freshInverseVariable(sourceRing);
    const extendedRing = algebraPolynomialRing(
        sourceRing.coefficientDomain,
        [...sourceRing.variables, inverseVariable],
        sourceRing.monomialOrder
    );
    const inversePolynomial = algebraPolynomialVariable(
        extendedRing,
        extendedRing.variables.length - 1
    );
    const inverseRelation = algebraPolynomialSubtract(
        algebraPolynomialMultiply(
            inversePolynomial,
            embed(element.representative, extendedRing)
        ),
        algebraPolynomialOne(extendedRing)
    );
    const ideal = algebraPolynomialIdeal(extendedRing, [
        ...source.quotient.ideal.generators.map(relation =>
            embed(relation, extendedRing)
        ),
        inverseRelation
    ]);
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(ideal, options)
    );
    const canonicalMap = algebraPresentedAlgebraMap(
        source,
        algebra,
        sourceRing.variables.map((_, index) => algebraQuotientElement(
            algebra.quotient,
            algebraPolynomialVariable(extendedRing, index)
        ))
    );
    const inverse = algebraQuotientElement(algebra.quotient, inversePolynomial);
    const elementImage = algebraPresentedAlgebraMapApply(canonicalMap, element);
    const inverseProduct = algebraQuotientMultiply(elementImage, inverse);
    const inverseEquation = algebraQuotientEquals(
        inverseProduct,
        algebraQuotientOne(algebra.quotient)
    );
    return Object.freeze({
        kind: 'algebra-principal-localization',
        source,
        element,
        inverseVariable,
        extendedRing,
        algebra,
        canonicalMap,
        inverse,
        elementImage,
        inverseProduct,
        inverseEquation
    });
}

export interface AlgebraBasicOpenChart<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-basic-open-chart';
    readonly source: AlgebraPresentedAlgebra<P, C, I>;
    readonly element: AlgebraQuotientElement<P, C, I>;
    readonly localization: AlgebraPrincipalLocalization<P, C, I>;
    readonly coordinateAlgebra: AlgebraPresentedAlgebra<P, C, I>;
}

export function algebraBasicOpenChart<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebra<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraBasicOpenChart<P, C, I> {
    const localization = algebraPrincipalLocalization(source, element, options);
    return Object.freeze({
        kind: 'algebra-basic-open-chart',
        source,
        element,
        localization,
        coordinateAlgebra: localization.algebra
    });
}
