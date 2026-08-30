/** Finite affine basic-open covers and initial Cech nerve/cochain data. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { AlgebraGroebnerOptions, algebraPolynomialIdeal } from './algebra_ideal';
import { AlgebraUnimodularCombination, algebraUnimodularCombination } from './algebra_zariski';
import {
    AlgebraQuotientElement,
    algebraQuotientElement,
    algebraQuotientMultiply,
    algebraQuotientOne
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapApply
} from './algebra_presented_algebra';
import {
    AlgebraAffineScheme,
    AlgebraBasicOpenAffineSubscheme,
    algebraBasicOpenAffineSubscheme
} from './algebra_affine_scheme';

export const ALGEBRA_CECH_PROFILE = Object.freeze({
    revision: 'emdash-affine-cech-nerve-v1' as const,
    simplexIndexing: 'strictly-increasing-chart-indices' as const,
    overlap: 'localization-at-product' as const,
    faceSign: 'minus-one-to-removed-position' as const,
    defaultMaximumDegree: 2,
    maximumDegree: 16,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraCechErrorCode =
    | 'FOREIGN_COVER_ELEMENT'
    | 'NOT_A_COVER'
    | 'INVALID_MAXIMUM_DEGREE';

export class AlgebraCechError extends Error {
    constructor(
        public readonly code: AlgebraCechErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraCechError';
    }
}

const fail = (code: AlgebraCechErrorCode, path: string, message: string): never => {
    throw new AlgebraCechError(code, path, message);
};

export interface AlgebraCechFace<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly removedPosition: number;
    readonly removedChart: number;
    readonly targetIndices: readonly number[];
    readonly sign: 1 | -1;
    /** Restriction on coordinates: O(face chart) -> O(simplex chart). */
    readonly restrictionMap: AlgebraPresentedAlgebraMap<P, C, I>;
}

export interface AlgebraCechSimplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-cech-simplex';
    readonly degree: number;
    readonly indices: readonly number[];
    readonly product: AlgebraQuotientElement<P, C, I>;
    readonly chart: AlgebraBasicOpenAffineSubscheme<P, C, I>;
    readonly faces: readonly AlgebraCechFace<P, C, I>[];
}

export interface AlgebraCechCochainDegree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly simplices: readonly AlgebraCechSimplex<P, C, I>[];
    readonly incomingFaces: readonly AlgebraCechFace<P, C, I>[];
}

export interface AlgebraAffineCover<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-cover';
    readonly ambient: AlgebraAffineScheme<P, C, I>;
    readonly elements: readonly AlgebraQuotientElement<P, C, I>[];
    readonly unimodular: AlgebraUnimodularCombination<P, C, I>;
    readonly relationGeneratorCount: number;
    readonly elementCoefficients: readonly AlgebraQuotientElement<P, C, I>[];
    readonly charts: readonly AlgebraBasicOpenAffineSubscheme<P, C, I>[];
    readonly maximumDegree: number;
    readonly simplices: readonly AlgebraCechSimplex<P, C, I>[];
    readonly cochainDegrees: readonly AlgebraCechCochainDegree<P, C, I>[];
}

const combinations = (count: number, size: number): readonly number[][] => {
    const output: number[][] = [];
    const visit = (start: number, selected: number[]): void => {
        if (selected.length === size) {
            output.push([...selected]);
            return;
        }
        for (let index = start; index < count; index++) {
            selected.push(index);
            visit(index + 1, selected);
            selected.pop();
        }
    };
    visit(0, []);
    return output;
};

const key = (indices: readonly number[]): string => indices.join(',');

export function algebraAffineCover<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ambient: AlgebraAffineScheme<P, C, I>,
    elementInput: readonly AlgebraQuotientElement<P, C, I>[],
    maximumDegreeInput: number = ALGEBRA_CECH_PROFILE.defaultMaximumDegree,
    options: AlgebraGroebnerOptions = {}
): AlgebraAffineCover<P, C, I> {
    if (!Number.isSafeInteger(maximumDegreeInput) || maximumDegreeInput < 0 ||
        maximumDegreeInput > ALGEBRA_CECH_PROFILE.maximumDegree) {
        return fail(
            'INVALID_MAXIMUM_DEGREE',
            'affineCover.maximumDegree',
            'Cech maximum degree must be a bounded nonnegative safe integer'
        );
    }
    const algebra = ambient.coordinateAlgebra;
    const elements = Object.freeze(elementInput.map((element, index) => {
        if (!sameAlgebraParent(element.parent, algebra.quotient)) {
            return fail(
                'FOREIGN_COVER_ELEMENT',
                `affineCover.elements[${index}]`,
                'Cover element belongs to a foreign coordinate algebra'
            );
        }
        return element;
    }));
    const relationGeneratorCount = algebra.quotient.ideal.generators.length;
    const combinedIdeal = algebraPolynomialIdeal(
        algebra.quotient.polynomialRing,
        [
            ...algebra.quotient.ideal.generators,
            ...elements.map(element => element.representative)
        ]
    );
    const unimodular = algebraUnimodularCombination(combinedIdeal, options);
    if (!unimodular.unimodular) {
        return fail(
            'NOT_A_COVER',
            'affineCover.elements',
            'Basic-open family does not generate one in the coordinate algebra'
        );
    }
    const elementCoefficients = Object.freeze(
        unimodular.coefficients.slice(relationGeneratorCount).map(coefficient =>
            algebraQuotientElement(algebra.quotient, coefficient)
        )
    );
    const maximumDegree = Math.min(maximumDegreeInput, elements.length - 1);
    const preliminary = new Map<string, {
        degree: number;
        indices: readonly number[];
        product: AlgebraQuotientElement<P, C, I>;
        chart: AlgebraBasicOpenAffineSubscheme<P, C, I>;
    }>();
    for (let size = 1; size <= maximumDegree + 1; size++) {
        combinations(elements.length, size).forEach(indices => {
            const product = indices.reduce(
                (value, index) => algebraQuotientMultiply(value, elements[index]),
                algebraQuotientOne(algebra.quotient)
            );
            preliminary.set(key(indices), Object.freeze({
                degree: size - 1,
                indices: Object.freeze(indices),
                product,
                chart: algebraBasicOpenAffineSubscheme(ambient, product, options)
            }));
        });
    }
    const simplices = Object.freeze([...preliminary.values()].map(simplex => {
        const faces = simplex.degree === 0 ? [] : simplex.indices.map(
            (removedChart, removedPosition) => {
                const targetIndices = simplex.indices.filter(
                    (_, index) => index !== removedPosition
                );
                const target = preliminary.get(key(targetIndices))!;
                const removedImage = algebraPresentedAlgebraMapApply(
                    simplex.chart.chart.localization.canonicalMap,
                    elements[removedChart]
                );
                const inverseImage = algebraQuotientMultiply(
                    removedImage,
                    simplex.chart.chart.localization.inverse
                );
                const restrictionMap = algebraPresentedAlgebraMap(
                    target.chart.chart.coordinateAlgebra,
                    simplex.chart.chart.coordinateAlgebra,
                    [
                        ...simplex.chart.chart.localization.canonicalMap.generatorImages,
                        inverseImage
                    ]
                );
                return Object.freeze({
                    removedPosition,
                    removedChart,
                    targetIndices: Object.freeze(targetIndices),
                    sign: (removedPosition % 2 === 0 ? 1 : -1) as 1 | -1,
                    restrictionMap
                });
            }
        );
        return Object.freeze({
            kind: 'algebra-cech-simplex' as const,
            ...simplex,
            faces: Object.freeze(faces)
        });
    }));
    const cochainDegrees = Object.freeze(Array.from(
        { length: Math.max(0, maximumDegree + 1) },
        (_, degree) => Object.freeze({
            degree,
            simplices: Object.freeze(simplices.filter(value => value.degree === degree)),
            incomingFaces: Object.freeze(
                simplices.filter(value => value.degree === degree + 1)
                    .flatMap(value => value.faces)
            )
        })
    ));
    return Object.freeze({
        kind: 'algebra-affine-cover',
        ambient,
        elements,
        unimodular,
        relationGeneratorCount,
        elementCoefficients,
        charts: Object.freeze(simplices.filter(value => value.degree === 0)
            .map(value => value.chart)),
        maximumDegree,
        simplices,
        cochainDegrees
    });
}
