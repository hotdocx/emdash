/** Explicit-Core laws and recursive recipes for bounded polynomial complexes. */

import {
    algebraFormalCompositeZeroClaimType,
    algebraFormalMatrixTerm
} from './algebra_formal_finite_module';
import {
    AlgebraFormalChainMapSquareRealization,
    defineAlgebraFormalChainMapSquareRealization
} from './algebra_formal_presentation_morphism';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialBoundedChainMap,
    AlgebraPolynomialBoundedFreeComplex,
    AlgebraPolynomialComplexCondition
} from './algebra_polynomial_bounded_complex';
import {
    serializeAlgebraPolynomialBoundedChainMap,
    serializeAlgebraPolynomialBoundedFreeComplex
} from './algebra_polynomial_bounded_complex_reference_operations';
import {
    KernelExpression
} from './kernel';

export const ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-bounded-complex-v1' as const,
    complexRevision: 'emdash-formal-bounded-complex-realization-v1' as const,
    chainMapRevision: 'emdash-formal-bounded-chain-map-realization-v1' as const,
    recipeRevision: 'emdash-formal-bounded-complex-recipe-v1' as const,
    lawOrder: 'ascending-upper-degree' as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

const assertReifierRing = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    complex: AlgebraPolynomialBoundedFreeComplex<P, C, I>,
    path: string
): void => {
    if (!sameAlgebraParent(
        reifier.algebra.quotient.polynomialRing,
        complex.ring
    )) throw new Error(`Formal reifier has a foreign complex ring at ${path}`);
};

export interface AlgebraFormalBoundedComplexCondition<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly upperDegree: number;
    readonly condition: AlgebraPolynomialComplexCondition<P, C, I>;
    readonly formalLower: KernelExpression;
    readonly formalUpper: KernelExpression;
    readonly claimType: KernelExpression;
}

export interface AlgebraFormalBoundedComplexRecipe {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.recipeRevision;
    readonly length: number;
    readonly ranks: readonly number[];
    readonly differentials: readonly KernelExpression[];
    readonly lawTypes: readonly KernelExpression[];
    readonly constructibleWhenLawsSupplied: true;
}

export interface AlgebraFormalBoundedComplexRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.complexRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalDifferentials: readonly KernelExpression[];
    readonly conditions:
        readonly AlgebraFormalBoundedComplexCondition<P, C, I>[];
    readonly recipe: AlgebraFormalBoundedComplexRecipe;
}

export function defineAlgebraFormalBoundedComplexRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialBoundedFreeComplex<P, C, I>;
}): AlgebraFormalBoundedComplexRealization<P, C, I> {
    assertReifierRing(input.reifier, input.selected, 'boundedComplex');
    const formalDifferentials = Object.freeze(
        input.selected.differentials.map(entry => algebraFormalMatrixTerm(
            input.reifier,
            entry.map.columns,
            entry.map.target.rank
        ))
    );
    const conditions = Object.freeze(input.selected.conditions.map(condition => {
        const lowerIndex = condition.upperDegree - 2;
        const upperIndex = condition.upperDegree - 1;
        return Object.freeze({
            upperDegree: condition.upperDegree,
            condition,
            formalLower: formalDifferentials[lowerIndex],
            formalUpper: formalDifferentials[upperIndex],
            claimType: algebraFormalCompositeZeroClaimType({
                reifier: input.reifier,
                left: condition.lower,
                right: condition.upper
            })
        });
    }));
    const recipe = Object.freeze({
        profileRevision: ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.recipeRevision,
        length: input.selected.length,
        ranks: Object.freeze(input.selected.terms.map(term => term.module.rank)),
        differentials: formalDifferentials,
        lawTypes: Object.freeze(conditions.map(condition => condition.claimType)),
        constructibleWhenLawsSupplied: true as const
    });
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.complexRevision,
        reifier: input.reifier,
        selected: input.selected,
        selectedOutputData: serializeAlgebraPolynomialBoundedFreeComplex(
            input.selected
        ),
        formalDifferentials,
        conditions,
        recipe
    });
}

export interface AlgebraFormalBoundedChainMapRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.chainMapRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialBoundedChainMap<P, C, I>;
    readonly selectedOutputData: string;
    readonly source: AlgebraFormalBoundedComplexRealization<P, C, I>;
    readonly target: AlgebraFormalBoundedComplexRealization<P, C, I>;
    readonly formalComponents: readonly KernelExpression[];
    readonly squares: readonly AlgebraFormalChainMapSquareRealization<P, C, I>[];
}

export function defineAlgebraFormalBoundedChainMapRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialBoundedChainMap<P, C, I>;
}): AlgebraFormalBoundedChainMapRealization<P, C, I> {
    const source = defineAlgebraFormalBoundedComplexRealization({
        reifier: input.reifier,
        selected: input.selected.source
    });
    const target = defineAlgebraFormalBoundedComplexRealization({
        reifier: input.reifier,
        selected: input.selected.target
    });
    const formalComponents = Object.freeze(input.selected.components.map(entry =>
        algebraFormalMatrixTerm(
            input.reifier,
            entry.map.columns,
            entry.map.target.rank
        )
    ));
    const squares = Object.freeze(input.selected.squares.map(square =>
        defineAlgebraFormalChainMapSquareRealization({
            reifier: input.reifier,
            selected: square
        })
    ));
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_BOUNDED_COMPLEX_PROFILE.chainMapRevision,
        reifier: input.reifier,
        selected: input.selected,
        selectedOutputData: serializeAlgebraPolynomialBoundedChainMap(
            input.selected
        ),
        source,
        target,
        formalComponents,
        squares
    });
}
