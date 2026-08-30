/** Initial generalized module morphisms by monic-source spans. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraKernelBasis,
    AlgebraMatrix,
    algebraMatrix,
    algebraMatrixKernelBasis,
    algebraMatrixLeftInverse,
    algebraMatrixMultiply,
    algebraMatrixSpace,
    algebraZeroMatrix
} from './algebra_matrix';
import {
    AlgebraModuleError,
    AlgebraModuleMorphism,
    AlgebraModuleRealization,
    AlgebraPresentedModule,
    algebraFreeModule,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleInducedMatrix,
    algebraModuleLiftAlongMonomorphism,
    algebraModuleMorphism,
    algebraModuleMorphismEquivalent,
    algebraModuleRealization,
    algebraPresentedModuleEquals
} from './algebra_module';

export const ALGEBRA_GENERALIZED_MORPHISM_PROFILE = Object.freeze({
    revision: 'emdash-algebra-generalized-span-v1' as const,
    representation: 'monic-source-aid-span' as const,
    composition: 'fiber-product-of-middle-legs' as const,
    threeArrowRepresentation: false as const,
    cospanRepresentation: false as const,
    serreQuotients: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraGeneralizedMorphismErrorCode =
    | 'INVALID_PULLBACK'
    | 'PULLBACK_CONDITION_FAILED'
    | 'INVALID_GENERALIZED_SPAN'
    | 'NON_MONIC_SOURCE_AID'
    | 'NON_COMPOSABLE_GENERALIZED_SPANS'
    | 'NO_HONEST_REPRESENTATIVE';

export class AlgebraGeneralizedMorphismError extends Error {
    constructor(
        public readonly code: AlgebraGeneralizedMorphismErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraGeneralizedMorphismError';
    }
}

const fail = (
    code: AlgebraGeneralizedMorphismErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraGeneralizedMorphismError(code, path, message);
};

const verticalConcat = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    top: AlgebraMatrix<P, C, I>,
    bottom: AlgebraMatrix<P, C, I>
): AlgebraMatrix<P, C, I> => {
    if (
        top.parent.columns !== bottom.parent.columns ||
        !sameAlgebraParent(
            top.parent.coefficientDomain.parent,
            bottom.parent.coefficientDomain.parent
        )
    ) {
        return fail(
            'INVALID_PULLBACK',
            'pullback.verticalConcat',
            'Pullback coordinate matrices must have one column domain'
        );
    }
    return algebraMatrix(
        algebraMatrixSpace(
            top.parent.coefficientDomain,
            top.parent.rows + bottom.parent.rows,
            top.parent.columns
        ),
        [...top.entries, ...bottom.entries]
    );
};

export interface AlgebraModulePullback<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-pullback';
    readonly left: AlgebraModuleMorphism<P, C, I>;
    readonly right: AlgebraModuleMorphism<P, C, I>;
    readonly object: AlgebraPresentedModule<P, C, I>;
    readonly leftProjection: AlgebraModuleMorphism<P, C, I>;
    readonly rightProjection: AlgebraModuleMorphism<P, C, I>;
    readonly comparisonMatrix: AlgebraMatrix<P, C, I>;
    readonly kernelBasis: AlgebraKernelBasis<P, C, I>;
    readonly leftRealization: AlgebraModuleRealization<P, C, I>;
    readonly rightRealization: AlgebraModuleRealization<P, C, I>;
}

export function algebraModulePullback<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraModuleMorphism<P, C, I>,
    right: AlgebraModuleMorphism<P, C, I>
): AlgebraModulePullback<P, C, I> {
    if (!algebraPresentedModuleEquals(left.target, right.target)) {
        return fail(
            'INVALID_PULLBACK',
            'pullback.target',
            'A pullback requires morphisms with one target'
        );
    }
    const leftRealization = algebraModuleRealization(left.source);
    const rightRealization = algebraModuleRealization(right.source);
    const leftInduced = algebraModuleInducedMatrix(left);
    const rightInduced = algebraModuleInducedMatrix(right);
    const field = left.source.field;
    const comparisonMatrix = algebraMatrix(
        algebraMatrixSpace(
            field,
            leftInduced.parent.rows,
            leftInduced.parent.columns + rightInduced.parent.columns
        ),
        leftInduced.entries.map((row, rowIndex) => [
            ...row,
            ...rightInduced.entries[rowIndex].map(value =>
                field.negate(value)
            )
        ])
    );
    const kernelBasis = algebraMatrixKernelBasis(comparisonMatrix);
    const object = algebraFreeModule(field, kernelBasis.nullity);
    const leftCoordinates = algebraMatrix(
        algebraMatrixSpace(
            field,
            leftRealization.dimension,
            kernelBasis.nullity
        ),
        kernelBasis.generators.entries.slice(0, leftRealization.dimension)
    );
    const rightCoordinates = algebraMatrix(
        algebraMatrixSpace(
            field,
            rightRealization.dimension,
            kernelBasis.nullity
        ),
        kernelBasis.generators.entries.slice(leftRealization.dimension)
    );
    const leftProjection = algebraModuleMorphism(
        object,
        left.source,
        algebraMatrixMultiply(leftRealization.section, leftCoordinates),
        algebraZeroMatrix(algebraMatrixSpace(
            field,
            left.source.relations.parent.columns,
            0
        ))
    );
    const rightProjection = algebraModuleMorphism(
        object,
        right.source,
        algebraMatrixMultiply(rightRealization.section, rightCoordinates),
        algebraZeroMatrix(algebraMatrixSpace(
            field,
            right.source.relations.parent.columns,
            0
        ))
    );
    if (!algebraModuleMorphismEquivalent(
        algebraModuleCompose(left, leftProjection),
        algebraModuleCompose(right, rightProjection)
    )) {
        return fail(
            'PULLBACK_CONDITION_FAILED',
            'pullback',
            'Computed pullback projections do not form a commuting square'
        );
    }
    return Object.freeze({
        kind: 'algebra-module-pullback',
        left,
        right,
        object,
        leftProjection,
        rightProjection,
        comparisonMatrix,
        kernelBasis,
        leftRealization,
        rightRealization
    });
}

export function algebraModulePullbackLift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    pullback: AlgebraModulePullback<P, C, I>,
    testLeft: AlgebraModuleMorphism<P, C, I>,
    testRight: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (
        !algebraPresentedModuleEquals(testLeft.source, testRight.source) ||
        !algebraPresentedModuleEquals(testLeft.target, pullback.left.source) ||
        !algebraPresentedModuleEquals(testRight.target, pullback.right.source) ||
        !algebraModuleMorphismEquivalent(
            algebraModuleCompose(pullback.left, testLeft),
            algebraModuleCompose(pullback.right, testRight)
        )
    ) {
        return fail(
            'PULLBACK_CONDITION_FAILED',
            'pullbackLift',
            'Test morphisms do not form a cone over the cospan'
        );
    }
    const stacked = verticalConcat(
        algebraModuleInducedMatrix(testLeft),
        algebraModuleInducedMatrix(testRight)
    );
    const coordinates = algebraMatrixMultiply(
        algebraMatrixLeftInverse(pullback.kernelBasis.generators),
        stacked
    );
    const sourceRealization = algebraModuleRealization(testLeft.source);
    const lift = algebraModuleMorphism(
        testLeft.source,
        pullback.object,
        algebraMatrixMultiply(coordinates, sourceRealization.projection),
        algebraZeroMatrix(algebraMatrixSpace(
            testLeft.source.field,
            0,
            testLeft.source.relations.parent.columns
        ))
    );
    if (
        !algebraModuleMorphismEquivalent(
            algebraModuleCompose(pullback.leftProjection, lift),
            testLeft
        ) ||
        !algebraModuleMorphismEquivalent(
            algebraModuleCompose(pullback.rightProjection, lift),
            testRight
        )
    ) {
        return fail(
            'PULLBACK_CONDITION_FAILED',
            'pullbackLift',
            'Computed pullback lift does not recover the test cone'
        );
    }
    return lift;
}

export interface AlgebraModuleGeneralizedSpan<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-generalized-span';
    readonly source: AlgebraPresentedModule<P, C, I>;
    readonly target: AlgebraPresentedModule<P, C, I>;
    readonly domain: AlgebraPresentedModule<P, C, I>;
    readonly sourceAid: AlgebraModuleMorphism<P, C, I>;
    readonly arrow: AlgebraModuleMorphism<P, C, I>;
}

export function algebraModuleGeneralizedSpan<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    sourceAid: AlgebraModuleMorphism<P, C, I>,
    arrow: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleGeneralizedSpan<P, C, I> {
    if (!algebraPresentedModuleEquals(sourceAid.source, arrow.source)) {
        return fail(
            'INVALID_GENERALIZED_SPAN',
            'generalizedSpan',
            'The source aid and arrow must share the span apex'
        );
    }
    try {
        algebraModuleLiftAlongMonomorphism(sourceAid, sourceAid);
    } catch (error: unknown) {
        if (error instanceof AlgebraModuleError) {
            return fail(
                'NON_MONIC_SOURCE_AID',
                'generalizedSpan.sourceAid',
                'A generalized span requires a monic source aid'
            );
        }
        throw error;
    }
    return Object.freeze({
        kind: 'algebra-module-generalized-span',
        source: sourceAid.target,
        target: arrow.target,
        domain: sourceAid.source,
        sourceAid,
        arrow
    });
}

export const algebraModuleAsGeneralizedSpan = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraModuleMorphism<P, C, I>):
    AlgebraModuleGeneralizedSpan<P, C, I> => algebraModuleGeneralizedSpan(
        algebraModuleIdentity(morphism.source),
        morphism
    );

export const algebraModuleGeneralizedSpanIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(object: AlgebraPresentedModule<P, C, I>):
    AlgebraModuleGeneralizedSpan<P, C, I> => algebraModuleAsGeneralizedSpan(
        algebraModuleIdentity(object)
    );

export interface AlgebraModuleGeneralizedSpanComposition<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-generalized-span-composition';
    readonly after: AlgebraModuleGeneralizedSpan<P, C, I>;
    readonly before: AlgebraModuleGeneralizedSpan<P, C, I>;
    readonly pullback: AlgebraModulePullback<P, C, I>;
    readonly result: AlgebraModuleGeneralizedSpan<P, C, I>;
}

export function algebraModuleGeneralizedSpanComposition<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraModuleGeneralizedSpan<P, C, I>,
    before: AlgebraModuleGeneralizedSpan<P, C, I>
): AlgebraModuleGeneralizedSpanComposition<P, C, I> {
    if (!algebraPresentedModuleEquals(before.target, after.source)) {
        return fail(
            'NON_COMPOSABLE_GENERALIZED_SPANS',
            'generalizedSpanComposition',
            'Generalized spans are not composable'
        );
    }
    const pullback = algebraModulePullback(before.arrow, after.sourceAid);
    const result = algebraModuleGeneralizedSpan(
        algebraModuleCompose(before.sourceAid, pullback.leftProjection),
        algebraModuleCompose(after.arrow, pullback.rightProjection)
    );
    return Object.freeze({
        kind: 'algebra-module-generalized-span-composition',
        after,
        before,
        pullback,
        result
    });
}

export const algebraModuleGeneralizedSpanCompose = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraModuleGeneralizedSpan<P, C, I>,
    before: AlgebraModuleGeneralizedSpan<P, C, I>
): AlgebraModuleGeneralizedSpan<P, C, I> =>
    algebraModuleGeneralizedSpanComposition(after, before).result;

export function algebraModuleGeneralizedSpanHonestRepresentative<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(span: AlgebraModuleGeneralizedSpan<P, C, I>):
    AlgebraModuleMorphism<P, C, I> {
    try {
        const inverse = algebraModuleLiftAlongMonomorphism(
            span.sourceAid,
            algebraModuleIdentity(span.source)
        );
        return algebraModuleCompose(span.arrow, inverse);
    } catch (error: unknown) {
        if (error instanceof AlgebraModuleError) {
            return fail(
                'NO_HONEST_REPRESENTATIVE',
                'generalizedSpan.honestRepresentative',
                'The generalized span does not have full domain'
            );
        }
        throw error;
    }
}
