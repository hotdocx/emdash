/** Bounded free resolutions for presented modules over an operational field. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    algebraIdentityMatrix,
    algebraMatrixSpace,
    algebraZeroMatrix
} from './algebra_matrix';
import {
    AlgebraModuleKernel,
    AlgebraModuleMorphism,
    AlgebraModuleRealization,
    AlgebraPresentedModule,
    algebraFreeModule,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleKernel,
    algebraModuleMorphism,
    algebraModuleMorphismEquivalent,
    algebraModuleMorphismIsZero,
    algebraModuleRealization,
    algebraPresentedModuleEquals
} from './algebra_module';
import {
    AlgebraModuleChainComplex,
    AlgebraModuleComplexHomology,
    algebraModuleChainComplex,
    algebraModuleChainComplexHomology
} from './algebra_homological';

export const ALGEBRA_RESOLUTION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-field-resolution-v1' as const,
    presentationResolution: 'relations-and-first-syzygy' as const,
    splitResolution: 'minimal-length-zero-over-field' as const,
    maximumPresentationLength: 2 as const,
    polynomialModuleResolution: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraResolutionErrorCode = 'RESOLUTION_VALIDATION_FAILED';

export class AlgebraResolutionError extends Error {
    constructor(
        public readonly code: AlgebraResolutionErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraResolutionError';
    }
}

const fail = (path: string, message: string): never => {
    throw new AlgebraResolutionError(
        'RESOLUTION_VALIDATION_FAILED',
        path,
        message
    );
};

export interface AlgebraModulePresentationResolution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-presentation-resolution';
    readonly module: AlgebraPresentedModule<P, C, I>;
    readonly complex: AlgebraModuleChainComplex<P, C, I>;
    readonly augmentation: AlgebraModuleMorphism<P, C, I>;
    readonly relationMorphism: AlgebraModuleMorphism<P, C, I>;
    readonly syzygyKernel: AlgebraModuleKernel<P, C, I>;
    readonly homology: readonly AlgebraModuleComplexHomology<P, C, I>[];
    readonly projectiveLength: 0 | 1 | 2;
}

/**
 * Resolve one presentation by its relation map and the relation-map kernel.
 * All three complex terms are free; zero-rank terms are retained explicitly.
 */
export function algebraModulePresentationResolution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedModule<P, C, I>):
    AlgebraModulePresentationResolution<P, C, I> {
    const field = module.field;
    const generators = algebraFreeModule(field, module.generators);
    const relations = algebraFreeModule(
        field,
        module.relations.parent.columns
    );
    const relationMorphism = algebraModuleMorphism(
        relations,
        generators,
        module.relations,
        algebraZeroMatrix(algebraMatrixSpace(field, 0, 0))
    );
    const syzygyKernel = algebraModuleKernel(relationMorphism);
    const complex = algebraModuleChainComplex(
        field,
        [
            { degree: 0, object: generators },
            { degree: 1, object: relations },
            { degree: 2, object: syzygyKernel.object }
        ],
        [
            { degree: 1, morphism: relationMorphism },
            { degree: 2, morphism: syzygyKernel.inclusion }
        ]
    );
    const augmentation = algebraModuleMorphism(
        generators,
        module,
        algebraIdentityMatrix(field, module.generators),
        algebraZeroMatrix(algebraMatrixSpace(
            field,
            module.relations.parent.columns,
            0
        ))
    );
    const homology = Object.freeze([0, 1, 2].map(value =>
        algebraModuleChainComplexHomology(complex, value)
    ));
    if (
        !algebraModuleMorphismIsZero(algebraModuleCompose(
            augmentation,
            relationMorphism
        )) ||
        !algebraPresentedModuleEquals(homology[0].object, module) ||
        algebraModuleRealization(homology[1].object).dimension !== 0 ||
        algebraModuleRealization(homology[2].object).dimension !== 0
    ) {
        return fail(
            'presentationResolution',
            'Presentation-derived complex failed its augmentation or homology checks'
        );
    }
    const projectiveLength: 0 | 1 | 2 =
        syzygyKernel.object.generators > 0
            ? 2
            : relations.generators > 0
                ? 1
                : 0;
    return Object.freeze({
        kind: 'algebra-module-presentation-resolution',
        module,
        complex,
        augmentation,
        relationMorphism,
        syzygyKernel,
        homology,
        projectiveLength
    });
}

export interface AlgebraModuleSplitResolution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-split-resolution';
    readonly module: AlgebraPresentedModule<P, C, I>;
    readonly realization: AlgebraModuleRealization<P, C, I>;
    readonly complex: AlgebraModuleChainComplex<P, C, I>;
    readonly augmentation: AlgebraModuleMorphism<P, C, I>;
    readonly inverse: AlgebraModuleMorphism<P, C, I>;
    readonly homology: AlgebraModuleComplexHomology<P, C, I>;
    readonly projectiveLength: 0;
}

/** The minimal length-zero free resolution supplied by field-linear splitting. */
export function algebraModuleSplitResolution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedModule<P, C, I>):
    AlgebraModuleSplitResolution<P, C, I> {
    const realization = algebraModuleRealization(module);
    const free = algebraFreeModule(module.field, realization.dimension);
    const augmentation = algebraModuleMorphism(
        free,
        module,
        realization.section,
        algebraZeroMatrix(algebraMatrixSpace(
            module.field,
            module.relations.parent.columns,
            0
        ))
    );
    const inverse = algebraModuleMorphism(
        module,
        free,
        realization.projection,
        algebraZeroMatrix(algebraMatrixSpace(
            module.field,
            0,
            module.relations.parent.columns
        ))
    );
    if (
        !algebraModuleMorphismEquivalent(
            algebraModuleCompose(inverse, augmentation),
            algebraModuleIdentity(free)
        ) ||
        !algebraModuleMorphismEquivalent(
            algebraModuleCompose(augmentation, inverse),
            algebraModuleIdentity(module)
        )
    ) {
        return fail(
            'splitResolution',
            'Quotient realization did not provide inverse augmentation maps'
        );
    }
    const complex = algebraModuleChainComplex(
        module.field,
        [{ degree: 0, object: free }],
        []
    );
    return Object.freeze({
        kind: 'algebra-module-split-resolution',
        module,
        realization,
        complex,
        augmentation,
        inverse,
        homology: algebraModuleChainComplexHomology(complex, 0),
        projectiveLength: 0
    });
}
