/** Whole bounded free complexes and chain maps over one polynomial ring. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialFreeModule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPolynomialSchreyerResolution,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapIsZero
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialChainMapSquare,
    algebraPolynomialChainMapSquare,
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';

export const ALGEBRA_POLYNOMIAL_BOUNDED_COMPLEX_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-bounded-free-complex-v1' as const,
    grading: 'zero-based-consecutive-chain' as const,
    differentialOrientation: 'd_i-from-degree-i-to-i-minus-one' as const,
    wholeNegativeResults: true as const,
    quotientCarrier: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialBoundedComplexErrorCode =
    | 'INVALID_COMPLEX_TERMS'
    | 'FOREIGN_COMPLEX_RING'
    | 'INVALID_DIFFERENTIALS'
    | 'INVALID_CHAIN_MAP'
    | 'NON_COMPOSABLE_CHAIN_MAPS';

export class AlgebraPolynomialBoundedComplexError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialBoundedComplexErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialBoundedComplexError';
    }
}

const fail = (
    code: AlgebraPolynomialBoundedComplexErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialBoundedComplexError(code, path, message);
};

export interface AlgebraPolynomialComplexTerm<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly module: AlgebraPolynomialFreeModule<P, C, I>;
}

export interface AlgebraPolynomialComplexDifferential<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
}

export interface AlgebraPolynomialComplexCondition<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly upperDegree: number;
    readonly lower: AlgebraPolynomialModuleMap<P, C, I>;
    readonly upper: AlgebraPolynomialModuleMap<P, C, I>;
    readonly composite: AlgebraPolynomialModuleMap<P, C, I>;
    readonly zero: boolean;
}

export interface AlgebraPolynomialSchreyerComplexSource<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-schreyer-complex-source';
    readonly resolution: AlgebraPolynomialSchreyerResolution<P, C, I>;
    readonly complete: boolean;
    readonly maximumLength: number;
}

export interface AlgebraPolynomialBoundedFreeComplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-bounded-free-complex';
    readonly ring: AlgebraPolynomialFreeModule<P, C, I>['ring'];
    readonly length: number;
    readonly terms: readonly AlgebraPolynomialComplexTerm<P, C, I>[];
    readonly differentials:
        readonly AlgebraPolynomialComplexDifferential<P, C, I>[];
    readonly conditions: readonly AlgebraPolynomialComplexCondition<P, C, I>[];
    readonly isComplex: boolean;
    readonly schreyerSource?: AlgebraPolynomialSchreyerComplexSource<P, C, I>;
}

export function algebraPolynomialBoundedFreeComplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly terms: readonly AlgebraPolynomialFreeModule<P, C, I>[];
    readonly differentials: readonly AlgebraPolynomialModuleMap<P, C, I>[];
    readonly schreyerSource?: AlgebraPolynomialSchreyerComplexSource<P, C, I>;
}): AlgebraPolynomialBoundedFreeComplex<P, C, I> {
    if (!Array.isArray(input.terms) || input.terms.length === 0) {
        return fail(
            'INVALID_COMPLEX_TERMS',
            'polynomialComplex.terms',
            'A bounded complex requires at least its degree-zero free module'
        );
    }
    if (
        !Array.isArray(input.differentials) ||
        input.differentials.length !== input.terms.length - 1
    ) {
        return fail(
            'INVALID_DIFFERENTIALS',
            'polynomialComplex.differentials',
            'Exactly one differential is required between consecutive terms'
        );
    }
    const ring = input.terms[0].ring;
    input.terms.forEach((term, index) => {
        if (!sameAlgebraParent(term.ring, ring)) {
            return fail(
                'FOREIGN_COMPLEX_RING',
                `polynomialComplex.terms[${index}]`,
                'Every free module must use one polynomial ring'
            );
        }
    });
    input.differentials.forEach((differential, index) => {
        if (
            !sameAlgebraParent(differential.source, input.terms[index + 1]) ||
            !sameAlgebraParent(differential.target, input.terms[index])
        ) {
            return fail(
                'INVALID_DIFFERENTIALS',
                `polynomialComplex.differentials[${index}]`,
                `Expected d_${index + 1}: C_${index + 1} -> C_${index}`
            );
        }
    });
    const terms = Object.freeze(input.terms.map((module, degree) =>
        Object.freeze({ degree, module })
    ));
    const differentials = Object.freeze(input.differentials.map((map, index) =>
        Object.freeze({ degree: index + 1, map })
    ));
    const conditions = Object.freeze(input.differentials.slice(1).map(
        (upper, offset) => {
            const upperDegree = offset + 2;
            const lower = input.differentials[offset];
            const composite = algebraPolynomialModuleMapCompose(lower, upper);
            return Object.freeze({
                upperDegree,
                lower,
                upper,
                composite,
                zero: algebraPolynomialModuleMapIsZero(composite)
            });
        }
    ));
    return Object.freeze({
        kind: 'algebra-polynomial-bounded-free-complex',
        ring,
        length: input.differentials.length,
        terms,
        differentials,
        conditions,
        isComplex: conditions.every(condition => condition.zero),
        ...(input.schreyerSource === undefined
            ? {}
            : { schreyerSource: input.schreyerSource })
    });
}

export function algebraPolynomialBoundedFreeComplexFromSchreyer<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(resolution: AlgebraPolynomialSchreyerResolution<P, C, I>):
    AlgebraPolynomialBoundedFreeComplex<P, C, I> {
    if (
        resolution.freeModules.length !== resolution.differentials.length + 1 ||
        resolution.length !== resolution.differentials.length
    ) {
        return fail(
            'INVALID_DIFFERENTIALS',
            'schreyerComplex.resolution',
            'Resolution term/differential counts are inconsistent'
        );
    }
    return algebraPolynomialBoundedFreeComplex({
        terms: resolution.freeModules,
        differentials: resolution.differentials,
        schreyerSource: Object.freeze({
            kind: 'algebra-polynomial-schreyer-complex-source',
            resolution,
            complete: resolution.complete,
            maximumLength: resolution.maximumLength
        })
    });
}

export const algebraPolynomialBoundedFreeComplexEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialBoundedFreeComplex<P, C, I>,
    right: AlgebraPolynomialBoundedFreeComplex<P, C, I>
): boolean => left.length === right.length &&
    left.terms.length === right.terms.length &&
    left.terms.every((term, index) =>
        sameAlgebraParent(term.module, right.terms[index].module)
    ) &&
    left.differentials.every((entry, index) =>
        algebraPolynomialModuleMapEquals(
            entry.map,
            right.differentials[index].map
        )
    );

export interface AlgebraPolynomialChainMapComponent<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
}

export interface AlgebraPolynomialBoundedChainMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-bounded-chain-map';
    readonly source: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly target: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly components: readonly AlgebraPolynomialChainMapComponent<P, C, I>[];
    readonly squares: readonly AlgebraPolynomialChainMapSquare<P, C, I>[];
    readonly isChainMap: boolean;
}

export function algebraPolynomialBoundedChainMap<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly source: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly target: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly components: readonly AlgebraPolynomialModuleMap<P, C, I>[];
}): AlgebraPolynomialBoundedChainMap<P, C, I> {
    if (
        input.source.length !== input.target.length ||
        !sameAlgebraParent(input.source.ring, input.target.ring) ||
        !Array.isArray(input.components) ||
        input.components.length !== input.source.terms.length
    ) {
        return fail(
            'INVALID_CHAIN_MAP',
            'polynomialChainMap',
            'Chain maps require one ring, degree range, and component per term'
        );
    }
    input.components.forEach((component, index) => {
        if (
            !sameAlgebraParent(component.source, input.source.terms[index].module) ||
            !sameAlgebraParent(component.target, input.target.terms[index].module)
        ) {
            return fail(
                'INVALID_CHAIN_MAP',
                `polynomialChainMap.components[${index}]`,
                `Component F_${index} has incorrect endpoints`
            );
        }
    });
    const components = Object.freeze(input.components.map((map, degree) =>
        Object.freeze({ degree, map })
    ));
    const squares = Object.freeze(input.source.differentials.map(
        (sourceDifferential, index) => algebraPolynomialChainMapSquare({
            differentialSource: sourceDifferential.map,
            differentialTarget: input.target.differentials[index].map,
            componentPrevious: input.components[index],
            componentNow: input.components[index + 1]
        })
    ));
    return Object.freeze({
        kind: 'algebra-polynomial-bounded-chain-map',
        source: input.source,
        target: input.target,
        components,
        squares,
        isChainMap: input.source.isComplex && input.target.isComplex &&
            squares.every(square => square.commutes)
    });
}

export const algebraPolynomialBoundedChainMapIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(complex: AlgebraPolynomialBoundedFreeComplex<P, C, I>):
    AlgebraPolynomialBoundedChainMap<P, C, I> =>
    algebraPolynomialBoundedChainMap({
        source: complex,
        target: complex,
        components: complex.terms.map(term =>
            algebraPolynomialModuleMapIdentity(term.module)
        )
    });

export function algebraPolynomialBoundedChainMapCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraPolynomialBoundedChainMap<P, C, I>,
    before: AlgebraPolynomialBoundedChainMap<P, C, I>
): AlgebraPolynomialBoundedChainMap<P, C, I> {
    if (!algebraPolynomialBoundedFreeComplexEquals(before.target, after.source)) {
        return fail(
            'NON_COMPOSABLE_CHAIN_MAPS',
            'polynomialChainMapCompose',
            'Chain-map intermediate complexes differ'
        );
    }
    return algebraPolynomialBoundedChainMap({
        source: before.source,
        target: after.target,
        components: before.components.map((component, index) =>
            algebraPolynomialModuleMapCompose(
                after.components[index].map,
                component.map
            )
        )
    });
}

export const algebraPolynomialBoundedChainMapEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialBoundedChainMap<P, C, I>,
    right: AlgebraPolynomialBoundedChainMap<P, C, I>
): boolean => algebraPolynomialBoundedFreeComplexEquals(left.source, right.source) &&
    algebraPolynomialBoundedFreeComplexEquals(left.target, right.target) &&
    left.components.length === right.components.length &&
    left.components.every((component, index) =>
        algebraPolynomialModuleMapEquals(
            component.map,
            right.components[index].map
        )
    );
