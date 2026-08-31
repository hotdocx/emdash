/** Compatibility from public presented-module maps to formal relation witnesses. */

import {
    AlgebraFormalPresentationMorphismRealization,
    defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    algebraPolynomialModuleMap,
    algebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedAlgebraEquals,
    algebraPresentedAlgebraMapEquals,
    algebraPresentedAlgebraMapIdentity
} from './algebra_presented_algebra';
import {
    algebraPresentedAlgebraModuleVectorLift
} from './algebra_presented_module';
import {
    AlgebraPresentedAlgebraModuleSemilinearMap
} from './algebra_presented_module_map';

export const ALGEBRA_FORMAL_PRESENTATION_MORPHISM_CATEGORY_PROFILE =
    Object.freeze({
        revision: 'emdash-formal-presentation-morphism-category-v1' as const,
        scope: 'fixed-ring-linear-presented-algebra-module-maps' as const,
        directRepresentation: true as const,
        formalCategoryClaim: false as const,
        addsCoreOwner: false as const,
        performsIo: false as const
    });

export interface AlgebraFormalPresentationMorphismCategoryCompatibility<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_PRESENTATION_MORPHISM_CATEGORY_PROFILE.revision;
    readonly publicMap: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly computation: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly formal: AlgebraFormalPresentationMorphismRealization<P, C, I>;
}

export function defineAlgebraFormalPresentationMorphismCategoryCompatibility<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
}): AlgebraFormalPresentationMorphismCategoryCompatibility<P, C, I> {
    const map = input.map;
    if (!algebraPresentedAlgebraEquals(
        map.source.freeModule.algebra,
        map.target.freeModule.algebra
    )) {
        throw new Error('Presentation compatibility requires one scalar algebra');
    }
    if (!algebraPresentedAlgebraMapEquals(
        map.scalarMap,
        algebraPresentedAlgebraMapIdentity(map.source.freeModule.algebra)
    )) {
        throw new Error('Presentation compatibility requires a linear map');
    }
    const source = algebraPresentedPolynomialModule(
        map.source.combinedRelations
    );
    const target = algebraPresentedPolynomialModule(
        map.target.combinedRelations
    );
    const polynomialMap = algebraPolynomialModuleMap(
        source.ambient,
        target.ambient,
        map.generatorImages.map(image =>
            algebraPresentedAlgebraModuleVectorLift(image.representative)
        )
    );
    const computation = algebraPolynomialPresentationMorphism({
        source,
        target,
        map: polynomialMap
    });
    if (!computation.preservesRelations) {
        throw new Error('Validated public map lost its relation witness');
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_PRESENTATION_MORPHISM_CATEGORY_PROFILE.revision,
        publicMap: map,
        computation,
        formal: defineAlgebraFormalPresentationMorphismRealization({
            reifier: input.reifier,
            selected: computation
        })
    });
}
