/** Finitely presented commutative algebras and relation-checked maps. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { AlgebraRuntimeSchema, defineAlgebraRuntimeSchema } from './algebra_engine';
import {
    AlgebraPolynomial,
    algebraPolynomialConstant,
    algebraPolynomialVariable,
    validateAlgebraPolynomial
} from './algebra_polynomial';
import {
    AlgebraPolynomialQuotientRing,
    AlgebraQuotientElement,
    algebraQuotientAdd,
    algebraQuotientElement,
    algebraQuotientElementSchema,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientOne,
    algebraQuotientPower,
    algebraQuotientZero
} from './algebra_quotient';

export const ALGEBRA_PRESENTED_ALGEBRA_PROFILE = Object.freeze({
    revision: 'emdash-presented-commutative-algebra-v1' as const,
    mapRepresentation: 'ordered-generator-images' as const,
    mapValidation: 'source-relations-evaluate-to-canonical-zero' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPresentedAlgebraErrorCode =
    | 'FOREIGN_BASE_FIELD'
    | 'INVALID_GENERATOR_IMAGES'
    | 'SOURCE_RELATION_FAILED'
    | 'FOREIGN_SOURCE_ALGEBRA'
    | 'NON_COMPOSABLE_ALGEBRA_MAPS';

export class AlgebraPresentedAlgebraError extends Error {
    constructor(
        public readonly code: AlgebraPresentedAlgebraErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPresentedAlgebraError';
    }
}

const fail = (
    code: AlgebraPresentedAlgebraErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraPresentedAlgebraError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export interface AlgebraPresentedAlgebra<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-algebra';
    readonly quotient: AlgebraPolynomialQuotientRing<P, C, I>;
}

export const algebraPresentedAlgebra = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(quotient: AlgebraPolynomialQuotientRing<P, C, I>):
    AlgebraPresentedAlgebra<P, C, I> => Object.freeze({
        kind: 'algebra-presented-algebra',
        quotient
    });

export const algebraPresentedAlgebraEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebra<P, C, I>,
    right: AlgebraPresentedAlgebra<P, C, I>
): boolean => sameAlgebraParent(left.quotient, right.quotient);

export interface AlgebraRelationImage<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly relation: AlgebraPolynomial<P, C, I>;
    readonly image: AlgebraQuotientElement<P, C, I>;
}

export interface AlgebraPresentedAlgebraMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-algebra-map';
    readonly source: AlgebraPresentedAlgebra<P, C, I>;
    readonly target: AlgebraPresentedAlgebra<P, C, I>;
    readonly generatorImages: readonly AlgebraQuotientElement<P, C, I>[];
    readonly relationImages: readonly AlgebraRelationImage<P, C, I>[];
}

const assertCommonField = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    source: AlgebraPresentedAlgebra<P, C, I>,
    target: AlgebraPresentedAlgebra<P, C, I>
): void => {
    if (!sameAlgebraParent(
        source.quotient.polynomialRing.coefficientDomain.parent,
        target.quotient.polynomialRing.coefficientDomain.parent
    )) {
        fail(
            'FOREIGN_BASE_FIELD',
            'algebraMap.target',
            'Presented algebra maps require one coefficient field'
        );
    }
};

export function algebraPresentedAlgebraMapApplyPolynomial<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: Pick<AlgebraPresentedAlgebraMap<P, C, I>,
        'source' | 'target' | 'generatorImages'>,
    polynomialInput: AlgebraPolynomial<P, C, I>
): AlgebraQuotientElement<P, C, I> {
    let polynomial: AlgebraPolynomial<P, C, I>;
    try {
        polynomial = validateAlgebraPolynomial(
            map.source.quotient.polynomialRing,
            polynomialInput,
            'algebraMapApply.polynomial'
        );
    } catch (error: unknown) {
        return fail(
            'FOREIGN_SOURCE_ALGEBRA',
            'algebraMapApply.polynomial',
            'Map application requires a source polynomial',
            error
        );
    }
    let result = algebraQuotientZero(map.target.quotient);
    polynomial.terms.forEach(term => {
        let image = algebraQuotientElement(
            map.target.quotient,
            algebraPolynomialConstant(
                map.target.quotient.polynomialRing,
                term.coefficient
            )
        );
        term.monomial.exponents.forEach((exponent, index) => {
            image = algebraQuotientMultiply(
                image,
                algebraQuotientPower(map.generatorImages[index], exponent)
            );
        });
        result = algebraQuotientAdd(result, image);
    });
    return result;
}

export function algebraPresentedAlgebraMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebra<P, C, I>,
    target: AlgebraPresentedAlgebra<P, C, I>,
    imageInput: readonly AlgebraQuotientElement<P, C, I>[]
): AlgebraPresentedAlgebraMap<P, C, I> {
    assertCommonField(source, target);
    if (!Array.isArray(imageInput) ||
        imageInput.length !== source.quotient.polynomialRing.variables.length) {
        return fail(
            'INVALID_GENERATOR_IMAGES',
            'algebraMap.generatorImages',
            `Expected ${source.quotient.polynomialRing.variables.length} images`
        );
    }
    const targetSchema = algebraQuotientElementSchema(target.quotient);
    const generatorImages = Object.freeze(imageInput.map((image, index) =>
        targetSchema.normalize(image, `algebraMap.generatorImages[${index}]`)
    ));
    const partial = { source, target, generatorImages };
    const zero = algebraQuotientZero(target.quotient);
    const relationImages = Object.freeze(source.quotient.ideal.generators.map(
        (relation, index) => {
            const image = algebraPresentedAlgebraMapApplyPolynomial(
                partial,
                relation
            );
            if (!algebraQuotientEquals(image, zero)) {
                return fail(
                    'SOURCE_RELATION_FAILED',
                    `algebraMap.relationImages[${index}]`,
                    'A source relation does not vanish in the target'
                );
            }
            return Object.freeze({ relation, image });
        }
    ));
    return Object.freeze({
        kind: 'algebra-presented-algebra-map',
        source,
        target,
        generatorImages,
        relationImages
    });
}

export function algebraPresentedAlgebraMapApply<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: AlgebraPresentedAlgebraMap<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>
): AlgebraQuotientElement<P, C, I> {
    if (!sameAlgebraParent(element.parent, map.source.quotient)) {
        return fail(
            'FOREIGN_SOURCE_ALGEBRA',
            'algebraMapApply.element',
            'Element belongs to a foreign source algebra'
        );
    }
    return algebraPresentedAlgebraMapApplyPolynomial(map, element.representative);
}

export function algebraPresentedAlgebraMapIdentity<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(algebra: AlgebraPresentedAlgebra<P, C, I>): AlgebraPresentedAlgebraMap<P, C, I> {
    return algebraPresentedAlgebraMap(
        algebra,
        algebra,
        algebra.quotient.polynomialRing.variables.map((_, index) =>
            algebraQuotientElement(
                algebra.quotient,
                algebraPolynomialVariable(algebra.quotient.polynomialRing, index)
            )
        )
    );
}

export function algebraPresentedAlgebraMapCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraPresentedAlgebraMap<P, C, I>,
    before: AlgebraPresentedAlgebraMap<P, C, I>
): AlgebraPresentedAlgebraMap<P, C, I> {
    if (!algebraPresentedAlgebraEquals(before.target, after.source)) {
        return fail(
            'NON_COMPOSABLE_ALGEBRA_MAPS',
            'algebraMapCompose',
            'Presented algebra maps are not composable'
        );
    }
    return algebraPresentedAlgebraMap(
        before.source,
        after.target,
        before.generatorImages.map(image =>
            algebraPresentedAlgebraMapApply(after, image)
        )
    );
}

export const algebraPresentedAlgebraMapEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedAlgebraMap<P, C, I>,
    right: AlgebraPresentedAlgebraMap<P, C, I>
): boolean => algebraPresentedAlgebraEquals(left.source, right.source) &&
    algebraPresentedAlgebraEquals(left.target, right.target) &&
    left.generatorImages.every((image, index) =>
        algebraQuotientEquals(image, right.generatorImages[index])
    );

export function algebraPresentedAlgebraMapSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebra<P, C, I>,
    target: AlgebraPresentedAlgebra<P, C, I>
): AlgebraRuntimeSchema<AlgebraPresentedAlgebraMap<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.presented-map/${source.quotient.identity.id}/` +
            target.quotient.identity.id,
        revision: `${source.quotient.identity.revision}.` +
            target.quotient.identity.revision,
        normalize(value: unknown, path: string) {
            if (typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-presented-algebra-map' ||
                !Array.isArray((value as { generatorImages?: unknown }).generatorImages)) {
                throw new Error(`presented algebra map expected at ${path}`);
            }
            return algebraPresentedAlgebraMap(
                source,
                target,
                (value as AlgebraPresentedAlgebraMap<P, C, I>).generatorImages
            );
        }
    });
}

export const algebraPresentedAlgebraUnit = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(algebra: AlgebraPresentedAlgebra<P, C, I>): AlgebraQuotientElement<P, C, I> =>
    algebraQuotientOne(algebra.quotient);
