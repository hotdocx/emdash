/** Affine schemes, contravariant morphisms, and standard immersions. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    ComputableCategory,
    createCategoryOperationRegistry,
    defineComputableCategory
} from './algebra_category';
import {
    AlgebraGroebnerOptions,
    algebraPolynomialIdeal
} from './algebra_ideal';
import {
    AlgebraPolynomialQuotientRing,
    AlgebraQuotientElement,
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebra,
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebra,
    algebraPresentedAlgebraEquals,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapCompose,
    algebraPresentedAlgebraMapEquals,
    algebraPresentedAlgebraMapIdentity
} from './algebra_presented_algebra';
import {
    AlgebraBasicOpenChart,
    algebraBasicOpenChart
} from './algebra_localization';
import { algebraPolynomialVariable } from './algebra_polynomial';

export const ALGEBRA_AFFINE_SCHEME_PROFILE = Object.freeze({
    revision: 'emdash-affine-scheme-v1' as const,
    variance: 'Spec-B-to-Spec-A-is-algebra-map-A-to-B' as const,
    semantics: 'strict-set-level-computational-category' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraAffineSchemeErrorCode =
    | 'INVALID_COORDINATE_MAP'
    | 'NON_COMPOSABLE_AFFINE_MORPHISMS'
    | 'FOREIGN_CLOSED_EQUATION';

export class AlgebraAffineSchemeError extends Error {
    constructor(
        public readonly code: AlgebraAffineSchemeErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraAffineSchemeError';
    }
}

const fail = (
    code: AlgebraAffineSchemeErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraAffineSchemeError(code, path, message);
};

export interface AlgebraAffineScheme<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-scheme';
    readonly coordinateAlgebra: AlgebraPresentedAlgebra<P, C, I>;
}

export const algebraAffineScheme = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(coordinateAlgebra: AlgebraPresentedAlgebra<P, C, I>):
    AlgebraAffineScheme<P, C, I> => Object.freeze({
        kind: 'algebra-affine-scheme',
        coordinateAlgebra
    });

export const algebraAffineSchemeEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraAffineScheme<P, C, I>, right: AlgebraAffineScheme<P, C, I>):
    boolean => algebraPresentedAlgebraEquals(
        left.coordinateAlgebra,
        right.coordinateAlgebra
    );

export interface AlgebraAffineMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-morphism';
    readonly source: AlgebraAffineScheme<P, C, I>;
    readonly target: AlgebraAffineScheme<P, C, I>;
    /** Contravariant coordinate map O(target) -> O(source). */
    readonly coordinateMap: AlgebraPresentedAlgebraMap<P, C, I>;
}

export function algebraAffineMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraAffineScheme<P, C, I>,
    target: AlgebraAffineScheme<P, C, I>,
    coordinateMap: AlgebraPresentedAlgebraMap<P, C, I>
): AlgebraAffineMorphism<P, C, I> {
    if (!algebraPresentedAlgebraEquals(
        coordinateMap.source,
        target.coordinateAlgebra
    ) || !algebraPresentedAlgebraEquals(
        coordinateMap.target,
        source.coordinateAlgebra
    )) {
        return fail(
            'INVALID_COORDINATE_MAP',
            'affineMorphism.coordinateMap',
            'Affine coordinate map has the wrong contravariant endpoints'
        );
    }
    return Object.freeze({
        kind: 'algebra-affine-morphism',
        source,
        target,
        coordinateMap
    });
}

export const algebraAffineMorphismIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(scheme: AlgebraAffineScheme<P, C, I>): AlgebraAffineMorphism<P, C, I> =>
    algebraAffineMorphism(
        scheme,
        scheme,
        algebraPresentedAlgebraMapIdentity(scheme.coordinateAlgebra)
    );

export function algebraAffineMorphismCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraAffineMorphism<P, C, I>,
    before: AlgebraAffineMorphism<P, C, I>
): AlgebraAffineMorphism<P, C, I> {
    if (!algebraAffineSchemeEquals(before.target, after.source)) {
        return fail(
            'NON_COMPOSABLE_AFFINE_MORPHISMS',
            'affineMorphismCompose',
            'Affine morphisms are not composable'
        );
    }
    return algebraAffineMorphism(
        before.source,
        after.target,
        algebraPresentedAlgebraMapCompose(
            before.coordinateMap,
            after.coordinateMap
        )
    );
}

export const algebraAffineMorphismEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraAffineMorphism<P, C, I>, right: AlgebraAffineMorphism<P, C, I>):
    boolean => algebraAffineSchemeEquals(left.source, right.source) &&
    algebraAffineSchemeEquals(left.target, right.target) &&
    algebraPresentedAlgebraMapEquals(left.coordinateMap, right.coordinateMap);

export interface AlgebraClosedAffineSubscheme<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-closed-affine-subscheme';
    readonly ambient: AlgebraAffineScheme<P, C, I>;
    readonly equations: readonly AlgebraQuotientElement<P, C, I>[];
    readonly coordinateRing: AlgebraPolynomialQuotientRing<P, C, I>;
    readonly scheme: AlgebraAffineScheme<P, C, I>;
    readonly immersion: AlgebraAffineMorphism<P, C, I>;
}

export function algebraClosedAffineSubscheme<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ambient: AlgebraAffineScheme<P, C, I>,
    equationInput: readonly AlgebraQuotientElement<P, C, I>[],
    options: AlgebraGroebnerOptions = {}
): AlgebraClosedAffineSubscheme<P, C, I> {
    const ambientAlgebra = ambient.coordinateAlgebra;
    const equations = Object.freeze(equationInput.map((equation, index) => {
        if (!sameAlgebraParent(equation.parent, ambientAlgebra.quotient)) {
            return fail(
                'FOREIGN_CLOSED_EQUATION',
                `closedSubscheme.equations[${index}]`,
                'Closed equation belongs to a foreign ambient algebra'
            );
        }
        return equation;
    }));
    const ring = ambientAlgebra.quotient.polynomialRing;
    const coordinateRing = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [
            ...ambientAlgebra.quotient.ideal.generators,
            ...equations.map(equation => equation.representative)
        ]),
        options
    );
    const coordinateAlgebra = algebraPresentedAlgebra(coordinateRing);
    const scheme = algebraAffineScheme(coordinateAlgebra);
    const coordinateMap = algebraPresentedAlgebraMap(
        ambientAlgebra,
        coordinateAlgebra,
        ring.variables.map((_, index) => algebraQuotientElement(
            coordinateRing,
            algebraPolynomialVariable(ring, index)
        ))
    );
    return Object.freeze({
        kind: 'algebra-closed-affine-subscheme',
        ambient,
        equations,
        coordinateRing,
        scheme,
        immersion: algebraAffineMorphism(scheme, ambient, coordinateMap)
    });
}

export interface AlgebraBasicOpenAffineSubscheme<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-basic-open-affine-subscheme';
    readonly ambient: AlgebraAffineScheme<P, C, I>;
    readonly chart: AlgebraBasicOpenChart<P, C, I>;
    readonly scheme: AlgebraAffineScheme<P, C, I>;
    readonly immersion: AlgebraAffineMorphism<P, C, I>;
}

export function algebraBasicOpenAffineSubscheme<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ambient: AlgebraAffineScheme<P, C, I>,
    element: AlgebraQuotientElement<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraBasicOpenAffineSubscheme<P, C, I> {
    const chart = algebraBasicOpenChart(ambient.coordinateAlgebra, element, options);
    const scheme = algebraAffineScheme(chart.coordinateAlgebra);
    return Object.freeze({
        kind: 'algebra-basic-open-affine-subscheme',
        ambient,
        chart,
        scheme,
        immersion: algebraAffineMorphism(
            scheme,
            ambient,
            chart.localization.canonicalMap
        )
    });
}

export interface AlgebraAffineSchemeComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly category: ComputableCategory<
        AlgebraAffineScheme<P, C, I>,
        AlgebraAffineMorphism<P, C, I>
    >;
    readonly objectSchema: AlgebraRuntimeSchema<AlgebraAffineScheme<P, C, I>>;
    readonly morphismSchema: AlgebraRuntimeSchema<AlgebraAffineMorphism<P, C, I>>;
}

export function algebraAffineSchemeComputableCategory<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraAffineSchemeComputableCategory<P, C, I> {
    const objectSchema = defineAlgebraRuntimeSchema<AlgebraAffineScheme<P, C, I>>({
        id: 'algebra.affine-scheme',
        revision: ALGEBRA_AFFINE_SCHEME_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-affine-scheme') {
                throw new Error(`affine scheme expected at ${path}`);
            }
            return value as AlgebraAffineScheme<P, C, I>;
        }
    });
    const morphismSchema = defineAlgebraRuntimeSchema<AlgebraAffineMorphism<P, C, I>>({
        id: 'algebra.affine-morphism',
        revision: ALGEBRA_AFFINE_SCHEME_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-affine-morphism') {
                throw new Error(`affine morphism expected at ${path}`);
            }
            const morphism = value as AlgebraAffineMorphism<P, C, I>;
            return algebraAffineMorphism(
                morphism.source,
                morphism.target,
                morphism.coordinateMap
            );
        }
    });
    return Object.freeze({
        objectSchema,
        morphismSchema,
        category: defineComputableCategory({
            id: 'algebra.category.affine-schemes',
            revision: ALGEBRA_AFFINE_SCHEME_PROFILE.revision,
            objectSchema,
            morphismSchema,
            operations: createCategoryOperationRegistry([]),
            source: morphism => morphism.source,
            target: morphism => morphism.target,
            identityMorphism: algebraAffineMorphismIdentity,
            compose: algebraAffineMorphismCompose,
            equalObjects: algebraAffineSchemeEquals,
            equalMorphisms: algebraAffineMorphismEquals
        })
    });
}
