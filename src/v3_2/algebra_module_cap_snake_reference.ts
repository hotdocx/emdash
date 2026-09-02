/** Non-authoritative finite-dimensional CAP snake differential. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraMatrix,
    algebraMatrix,
    algebraMatrixEquals,
    algebraMatrixKernelBasis,
    algebraMatrixLeftInverse,
    algebraMatrixMultiply,
    algebraMatrixNegate,
    algebraMatrixRightInverse,
    algebraMatrixSpace,
    algebraZeroMatrix
} from './algebra_matrix';
import {
    AlgebraModuleCokernel,
    AlgebraModuleKernel,
    AlgebraModuleMorphism,
    algebraModuleCokernel,
    algebraModuleCokernelColift,
    algebraModuleCompose,
    algebraModuleInducedMatrix,
    algebraModuleKernel,
    algebraModuleKernelLift,
    algebraModuleMorphismIsZero,
    algebraModuleRealization,
    algebraPresentedModule
} from './algebra_module';

export const ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-module-cap-snake-reference-v1' as const,
    purpose: 'non-authoritative-constant-field-differential' as const,
    construction: 'cap-fiber-product-pushout-normal-factors' as const,
    usesFieldSplittings: true as const,
    suitableForGeneralModules: false as const,
    performsIo: false as const
});

export interface AlgebraModuleCapSnakeConnecting<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-cap-snake-connecting';
    readonly deltaCokernel: AlgebraModuleCokernel<P, C, I>;
    readonly gamma: AlgebraModuleMorphism<P, C, I>;
    readonly gammaKernel: AlgebraModuleKernel<P, C, I>;
    readonly lambdaKernel: AlgebraModuleKernel<P, C, I>;
    readonly alpha: AlgebraModuleMorphism<P, C, I>;
    readonly alphaCokernel: AlgebraModuleCokernel<P, C, I>;
    readonly fiberDifference: AlgebraMatrix<P, C, I>;
    readonly fiberCombined: AlgebraMatrix<P, C, I>;
    readonly p1: AlgebraMatrix<P, C, I>;
    readonly p2: AlgebraMatrix<P, C, I>;
    readonly pushoutDifference: AlgebraMatrix<P, C, I>;
    readonly q1: AlgebraMatrix<P, C, I>;
    readonly q2: AlgebraMatrix<P, C, I>;
    readonly middle: AlgebraMatrix<P, C, I>;
    readonly u: AlgebraMatrix<P, C, I>;
    readonly connecting: AlgebraMatrix<P, C, I>;
    readonly fiberCompatible: true;
    readonly pushoutCompatible: true;
    readonly uReconstructs: true;
    readonly connectingReconstructs: true;
    readonly nonAuthoritative: true;
}

const horizontalConcat = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraMatrix<P, C, I>, right: AlgebraMatrix<P, C, I>) => {
    if (
        left.parent.rows !== right.parent.rows ||
        !sameAlgebraParent(
            left.parent.coefficientDomain.parent,
            right.parent.coefficientDomain.parent
        )
    ) throw new Error('CAP reference horizontal dimensions disagree');
    return algebraMatrix(
        algebraMatrixSpace(
            left.parent.coefficientDomain,
            left.parent.rows,
            left.parent.columns + right.parent.columns
        ),
        left.entries.map((row, index) => [...row, ...right.entries[index]])
    );
};

const verticalConcat = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(top: AlgebraMatrix<P, C, I>, bottom: AlgebraMatrix<P, C, I>) => {
    if (
        top.parent.columns !== bottom.parent.columns ||
        !sameAlgebraParent(
            top.parent.coefficientDomain.parent,
            bottom.parent.coefficientDomain.parent
        )
    ) throw new Error('CAP reference vertical dimensions disagree');
    return algebraMatrix(
        algebraMatrixSpace(
            top.parent.coefficientDomain,
            top.parent.rows + bottom.parent.rows,
            top.parent.columns
        ),
        [...top.entries, ...bottom.entries]
    );
};

const rows = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraMatrix<P, C, I>,
    start: number,
    count: number
) => algebraMatrix(
    algebraMatrixSpace(
        value.parent.coefficientDomain,
        count,
        value.parent.columns
    ),
    value.entries.slice(start, start + count)
);

const columns = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraMatrix<P, C, I>,
    start: number,
    count: number
) => algebraMatrix(
    algebraMatrixSpace(
        value.parent.coefficientDomain,
        value.parent.rows,
        count
    ),
    value.entries.map(row => row.slice(start, start + count))
);

const assertEqual = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraMatrix<P, C, I>,
    right: AlgebraMatrix<P, C, I>,
    message: string
): true => {
    if (!algebraMatrixEquals(left, right)) throw new Error(message);
    return true;
};

/** Execute the CAP construction independently in quotient vector spaces. */
export function algebraModuleCapSnakeConnecting<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    delta: AlgebraModuleMorphism<P, C, I>,
    beta: AlgebraModuleMorphism<P, C, I>,
    lambda: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleCapSnakeConnecting<P, C, I> {
    if (!algebraModuleMorphismIsZero(algebraModuleCompose(
        lambda,
        algebraModuleCompose(beta, delta)
    ))) throw new Error('CAP reference requires lambda-beta-delta zero');
    const deltaCokernel = algebraModuleCokernel(delta);
    const gamma = algebraModuleCokernelColift(
        deltaCokernel,
        algebraModuleCompose(lambda, beta)
    );
    const gammaKernel = algebraModuleKernel(gamma);
    const lambdaKernel = algebraModuleKernel(lambda);
    const alpha = algebraModuleKernelLift(
        lambdaKernel,
        algebraModuleCompose(beta, delta)
    );
    const alphaCokernel = algebraModuleCokernel(alpha);

    const iota = algebraModuleInducedMatrix(gammaKernel.inclusion);
    const epsilon = algebraModuleInducedMatrix(deltaCokernel.projection);
    const fiberDifference = horizontalConcat(
        iota,
        algebraMatrixNegate(epsilon)
    );
    const fiberCombined = algebraMatrixKernelBasis(
        fiberDifference
    ).generators;
    const p1 = rows(fiberCombined, 0, iota.parent.columns);
    const p2 = rows(
        fiberCombined,
        iota.parent.columns,
        epsilon.parent.columns
    );
    const fiberCompatible = assertEqual(
        algebraMatrixMultiply(iota, p1),
        algebraMatrixMultiply(epsilon, p2),
        'CAP reference fiber-product compatibility failed'
    );

    const mu = algebraModuleInducedMatrix(lambdaKernel.inclusion);
    const pi = algebraModuleInducedMatrix(alphaCokernel.projection);
    const pushoutDifference = verticalConcat(mu, algebraMatrixNegate(pi));
    const pushoutPresentation = algebraPresentedModule(
        delta.source.field,
        pushoutDifference.parent.rows,
        pushoutDifference
    );
    const pushoutProjection = algebraModuleRealization(
        pushoutPresentation
    ).projection;
    const q1 = columns(pushoutProjection, 0, mu.parent.rows);
    const q2 = columns(
        pushoutProjection,
        mu.parent.rows,
        pi.parent.rows
    );
    const pushoutCompatible = assertEqual(
        algebraMatrixMultiply(q1, mu),
        algebraMatrixMultiply(q2, pi),
        'CAP reference pushout compatibility failed'
    );

    const betaMatrix = algebraModuleInducedMatrix(beta);
    const middle = algebraMatrixMultiply(
        q1,
        algebraMatrixMultiply(betaMatrix, p2)
    );
    const u = algebraMatrixMultiply(middle, algebraMatrixRightInverse(p1));
    const uReconstructs = assertEqual(
        algebraMatrixMultiply(u, p1),
        middle,
        'CAP reference normal-epi factor failed reconstruction'
    );
    const connecting = algebraMatrixMultiply(algebraMatrixLeftInverse(q2), u);
    const connectingReconstructs = assertEqual(
        algebraMatrixMultiply(q2, connecting),
        u,
        'CAP reference normal-mono factor failed reconstruction'
    );
    assertEqual(
        algebraMatrixMultiply(fiberDifference, fiberCombined),
        algebraZeroMatrix(algebraMatrixSpace(
            fiberDifference.parent.coefficientDomain,
            fiberDifference.parent.rows,
            fiberCombined.parent.columns
        )),
        'CAP reference kernel basis failed'
    );
    return Object.freeze({
        kind: 'algebra-module-cap-snake-connecting',
        deltaCokernel,
        gamma,
        gammaKernel,
        lambdaKernel,
        alpha,
        alphaCokernel,
        fiberDifference,
        fiberCombined,
        p1,
        p2,
        pushoutDifference,
        q1,
        q2,
        middle,
        u,
        connecting,
        fiberCompatible,
        pushoutCompatible,
        uReconstructs,
        connectingReconstructs,
        nonAuthoritative: true
    });
}
