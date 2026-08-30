/** Field-linear finitely presented modules and morphisms. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraMatrix,
    AlgebraMatrixError,
    AlgebraMatrixSpace,
    AlgebraKernelBasis,
    algebraIdentityMatrix,
    algebraMatrix,
    algebraMatrixEquals,
    algebraMatrixKernelBasis,
    algebraMatrixLeftInverse,
    algebraMatrixMultiply,
    algebraMatrixRightInverse,
    algebraMatrixRref,
    algebraMatrixSpace,
    algebraMatrixText,
    algebraMatrixTranspose,
    algebraZeroMatrix
} from './algebra_matrix';

export const ALGEBRA_MODULE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-field-module-v1' as const,
    presentation: 'cokernel-of-column-relation-matrix' as const,
    morphismLaw: 'F-times-source-relations-equals-target-relations-times-W' as const,
    quotientModel: 'left-annihilator-projection-with-explicit-section' as const,
    morphismEquality: 'induced-matrix-on-quotient-coordinates' as const,
    universalFactorization: 'one-sided-inverse-lift-and-colift' as const,
    polynomialModuleGroebner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraModuleErrorCode =
    | 'INVALID_MODULE'
    | 'NON_FIELD_COEFFICIENTS'
    | 'FOREIGN_MODULE'
    | 'INVALID_MORPHISM'
    | 'MORPHISM_LAW_FAILED'
    | 'DIMENSION_MISMATCH'
    | 'NOT_MONOMORPHISM'
    | 'NOT_EPIMORPHISM'
    | 'NOT_LIFTABLE'
    | 'NOT_COLIFTABLE';

export class AlgebraModuleError extends Error {
    constructor(
        public readonly code: AlgebraModuleErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraModuleError';
    }
}

const fail = (
    code: AlgebraModuleErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraModuleError(code, path, message);
};

export interface AlgebraPresentedModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module';
    readonly field: AlgebraFieldDomain<P, C, I>;
    readonly generators: number;
    /** Columns are relations in the free generator space. */
    readonly relations: AlgebraMatrix<P, C, I>;
}

export interface AlgebraModuleMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-morphism';
    readonly source: AlgebraPresentedModule<P, C, I>;
    readonly target: AlgebraPresentedModule<P, C, I>;
    /** target.generators x source.generators. */
    readonly matrix: AlgebraMatrix<P, C, I>;
    /** F*R_source = R_target*relationWitness. */
    readonly relationWitness: AlgebraMatrix<P, C, I>;
}

const assertField = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraFieldDomain<P, C, I>): AlgebraFieldDomain<P, C, I> => {
    if (
        value.field !== true ||
        typeof value.divide !== 'function' ||
        typeof value.inverse !== 'function'
    ) {
        return fail(
            'NON_FIELD_COEFFICIENTS',
            'module.field',
            'Presented field-linear modules require an operational field'
        );
    }
    return value;
};

const count = (value: number, path: string): number => {
    if (Number.isSafeInteger(value) && value >= 0) return value;
    return fail(
        'INVALID_MODULE',
        path,
        'Module rank must be a nonnegative safe integer'
    );
};

export function algebraPresentedModule<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    fieldInput: AlgebraFieldDomain<P, C, I>,
    generatorInput: number,
    relations?: AlgebraMatrix<P, C, I>
): AlgebraPresentedModule<P, C, I> {
    const field = assertField(fieldInput);
    const generators = count(generatorInput, 'module.generators');
    const relationMatrix = relations ?? algebraZeroMatrix(
        algebraMatrixSpace(field, generators, 0)
    );
    if (
        relationMatrix.parent.rows !== generators ||
        !sameAlgebraParent(
            relationMatrix.parent.coefficientDomain.parent,
            field.parent
        )
    ) {
        return fail(
            'DIMENSION_MISMATCH',
            'module.relations',
            'Relation matrix must have one row per generator over the field'
        );
    }
    return Object.freeze({
        kind: 'algebra-presented-module',
        field,
        generators,
        relations: relationMatrix
    });
}

export const algebraFreeModule = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(field: AlgebraFieldDomain<P, C, I>, rank: number):
    AlgebraPresentedModule<P, C, I> => algebraPresentedModule(field, rank);

export const algebraPresentedModuleEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPresentedModule<P, C, I>,
    right: AlgebraPresentedModule<P, C, I>
): boolean => left.generators === right.generators &&
    sameAlgebraParent(left.field.parent, right.field.parent) &&
    algebraMatrixEquals(left.relations, right.relations);

export function algebraModuleMorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedModule<P, C, I>,
    target: AlgebraPresentedModule<P, C, I>,
    matrix: AlgebraMatrix<P, C, I>,
    relationWitness: AlgebraMatrix<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (!sameAlgebraParent(source.field.parent, target.field.parent)) {
        return fail(
            'FOREIGN_MODULE',
            'morphism.target',
            'Module morphism requires one coefficient field'
        );
    }
    if (
        matrix.parent.rows !== target.generators ||
        matrix.parent.columns !== source.generators ||
        relationWitness.parent.rows !== target.relations.parent.columns ||
        relationWitness.parent.columns !== source.relations.parent.columns
    ) {
        return fail(
            'DIMENSION_MISMATCH',
            'morphism',
            'Module morphism or relation-witness dimensions are invalid'
        );
    }
    const left = algebraMatrixMultiply(matrix, source.relations);
    const right = algebraMatrixMultiply(target.relations, relationWitness);
    if (!algebraMatrixEquals(left, right)) {
        return fail(
            'MORPHISM_LAW_FAILED',
            'morphism.relationWitness',
            'Relation witness does not carry source relations into target relations'
        );
    }
    return Object.freeze({
        kind: 'algebra-module-morphism',
        source,
        target,
        matrix,
        relationWitness
    });
}

export const algebraModuleIdentity = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedModule<P, C, I>): AlgebraModuleMorphism<P, C, I> =>
    algebraModuleMorphism(
        module,
        module,
        algebraIdentityMatrix(module.field, module.generators),
        algebraIdentityMatrix(module.field, module.relations.parent.columns)
    );

export function algebraModuleCompose<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    after: AlgebraModuleMorphism<P, C, I>,
    before: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (!algebraPresentedModuleEquals(before.target, after.source)) {
        return fail(
            'FOREIGN_MODULE',
            'compose',
            'Module morphisms are not composable'
        );
    }
    return algebraModuleMorphism(
        before.source,
        after.target,
        algebraMatrixMultiply(after.matrix, before.matrix),
        algebraMatrixMultiply(
            after.relationWitness,
            before.relationWitness
        )
    );
}

export const algebraModuleZeroMorphism = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedModule<P, C, I>,
    target: AlgebraPresentedModule<P, C, I>
): AlgebraModuleMorphism<P, C, I> => algebraModuleMorphism(
    source,
    target,
    algebraZeroMatrix(algebraMatrixSpace(
        source.field,
        target.generators,
        source.generators
    )),
    algebraZeroMatrix(algebraMatrixSpace(
        source.field,
        target.relations.parent.columns,
        source.relations.parent.columns
    ))
);

const horizontalConcat = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraMatrix<P, C, I>,
    right: AlgebraMatrix<P, C, I>
): AlgebraMatrix<P, C, I> => {
    if (
        left.parent.rows !== right.parent.rows ||
        !sameAlgebraParent(
            left.parent.coefficientDomain.parent,
            right.parent.coefficientDomain.parent
        )
    ) {
        return fail(
            'DIMENSION_MISMATCH',
            'horizontalConcat',
            'Horizontal matrix concatenation requires equal row counts'
        );
    }
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
            'DIMENSION_MISMATCH',
            'verticalConcat',
            'Vertical matrix concatenation requires equal column counts'
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

export interface AlgebraModuleCokernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-cokernel';
    readonly morphism: AlgebraModuleMorphism<P, C, I>;
    readonly object: AlgebraPresentedModule<P, C, I>;
    readonly projection: AlgebraModuleMorphism<P, C, I>;
}

export function algebraModuleCokernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraModuleMorphism<P, C, I>): AlgebraModuleCokernel<P, C, I> {
    const targetRelations = morphism.target.relations;
    const relations = horizontalConcat(targetRelations, morphism.matrix);
    const object = algebraPresentedModule(
        morphism.target.field,
        morphism.target.generators,
        relations
    );
    const top = algebraIdentityMatrix(
        morphism.target.field,
        targetRelations.parent.columns
    );
    const bottom = algebraZeroMatrix(algebraMatrixSpace(
        morphism.target.field,
        morphism.source.generators,
        targetRelations.parent.columns
    ));
    const witness = verticalConcat(top, bottom);
    const projection = algebraModuleMorphism(
        morphism.target,
        object,
        algebraIdentityMatrix(
            morphism.target.field,
            morphism.target.generators
        ),
        witness
    );
    return Object.freeze({
        kind: 'algebra-module-cokernel',
        morphism,
        object,
        projection
    });
}

export interface AlgebraModuleRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-quotient-realization';
    readonly module: AlgebraPresentedModule<P, C, I>;
    readonly dimension: number;
    /** projection: field^generators -> field^dimension. */
    readonly projection: AlgebraMatrix<P, C, I>;
    /** section: field^dimension -> field^generators. */
    readonly section: AlgebraMatrix<P, C, I>;
}

export function algebraModuleRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedModule<P, C, I>): AlgebraModuleRealization<P, C, I> {
    const annihilator = algebraMatrixKernelBasis(
        algebraMatrixTranspose(module.relations)
    ).generators;
    const projection = algebraMatrixTranspose(annihilator);
    const reduction = algebraMatrixRref(projection);
    const sectionRows = Array.from(
        { length: module.generators },
        () => Array.from({ length: projection.parent.rows }, () => module.field.zero)
    );
    reduction.pivotColumns.forEach((pivotColumn, pivotRow) => {
        sectionRows[pivotColumn] = [...reduction.leftTransformation.entries[pivotRow]];
    });
    const section = algebraMatrix(
        algebraMatrixSpace(
            module.field,
            module.generators,
            projection.parent.rows
        ),
        sectionRows
    );
    return Object.freeze({
        kind: 'algebra-module-quotient-realization',
        module,
        dimension: projection.parent.rows,
        projection,
        section
    });
}

const inducedMatrixFromRealizations = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    morphism: AlgebraModuleMorphism<P, C, I>,
    source: AlgebraModuleRealization<P, C, I>,
    target: AlgebraModuleRealization<P, C, I>
): AlgebraMatrix<P, C, I> => algebraMatrixMultiply(
    algebraMatrixMultiply(target.projection, morphism.matrix),
    source.section
);

/** Matrix of a module morphism on canonical quotient coordinates. */
export function algebraModuleInducedMatrix<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraModuleMorphism<P, C, I>): AlgebraMatrix<P, C, I> {
    return inducedMatrixFromRealizations(
        morphism,
        algebraModuleRealization(morphism.source),
        algebraModuleRealization(morphism.target)
    );
}

/** Equality of represented module morphisms after passage to the quotients. */
export const algebraModuleMorphismEquivalent = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraModuleMorphism<P, C, I>,
    right: AlgebraModuleMorphism<P, C, I>
): boolean =>
    algebraPresentedModuleEquals(left.source, right.source) &&
    algebraPresentedModuleEquals(left.target, right.target) &&
    algebraMatrixEquals(
        algebraModuleInducedMatrix(left),
        algebraModuleInducedMatrix(right)
    );

export const algebraModuleMorphismIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraModuleMorphism<P, C, I>): boolean => {
    const induced = algebraModuleInducedMatrix(morphism);
    return algebraMatrixEquals(
        induced,
        algebraZeroMatrix(induced.parent)
    );
};

/** Return lambda with iota * lambda equal to tau in quotient coordinates. */
export function algebraModuleLiftAlongMonomorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    iota: AlgebraModuleMorphism<P, C, I>,
    tau: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (!algebraPresentedModuleEquals(iota.target, tau.target)) {
        return fail(
            'NOT_LIFTABLE',
            'moduleLift.target',
            'A lift requires morphisms with one target'
        );
    }
    let inverse: AlgebraMatrix<P, C, I>;
    try {
        inverse = algebraMatrixLeftInverse(algebraModuleInducedMatrix(iota));
    } catch (error: unknown) {
        if (
            error instanceof AlgebraMatrixError &&
            error.code === 'NO_LEFT_INVERSE'
        ) {
            return fail(
                'NOT_MONOMORPHISM',
                'moduleLift.iota',
                'The proposed monomorphism is not injective'
            );
        }
        throw error;
    }
    const sourceRealization = algebraModuleRealization(tau.source);
    const targetRealization = algebraModuleRealization(iota.source);
    const induced = algebraMatrixMultiply(
        inverse,
        algebraModuleInducedMatrix(tau)
    );
    const matrix = algebraMatrixMultiply(
        algebraMatrixMultiply(targetRealization.section, induced),
        sourceRealization.projection
    );
    const lift = algebraModuleMorphism(
        tau.source,
        iota.source,
        matrix,
        algebraZeroMatrix(algebraMatrixSpace(
            tau.source.field,
            iota.source.relations.parent.columns,
            tau.source.relations.parent.columns
        ))
    );
    if (!algebraModuleMorphismEquivalent(
        algebraModuleCompose(iota, lift),
        tau
    )) {
        return fail(
            'NOT_LIFTABLE',
            'moduleLift.tau',
            'The test morphism does not factor through the monomorphism'
        );
    }
    return lift;
}

/** Return lambda with lambda * epsilon equal to tau in quotient coordinates. */
export function algebraModuleColiftAlongEpimorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    epsilon: AlgebraModuleMorphism<P, C, I>,
    tau: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (!algebraPresentedModuleEquals(epsilon.source, tau.source)) {
        return fail(
            'NOT_COLIFTABLE',
            'moduleColift.source',
            'A colift requires morphisms with one source'
        );
    }
    let inverse: AlgebraMatrix<P, C, I>;
    try {
        inverse = algebraMatrixRightInverse(
            algebraModuleInducedMatrix(epsilon)
        );
    } catch (error: unknown) {
        if (
            error instanceof AlgebraMatrixError &&
            error.code === 'NO_RIGHT_INVERSE'
        ) {
            return fail(
                'NOT_EPIMORPHISM',
                'moduleColift.epsilon',
                'The proposed epimorphism is not surjective'
            );
        }
        throw error;
    }
    const sourceRealization = algebraModuleRealization(epsilon.target);
    const targetRealization = algebraModuleRealization(tau.target);
    const induced = algebraMatrixMultiply(
        algebraModuleInducedMatrix(tau),
        inverse
    );
    const matrix = algebraMatrixMultiply(
        algebraMatrixMultiply(targetRealization.section, induced),
        sourceRealization.projection
    );
    const colift = algebraModuleMorphism(
        epsilon.target,
        tau.target,
        matrix,
        algebraZeroMatrix(algebraMatrixSpace(
            epsilon.source.field,
            tau.target.relations.parent.columns,
            epsilon.target.relations.parent.columns
        ))
    );
    if (!algebraModuleMorphismEquivalent(
        algebraModuleCompose(colift, epsilon),
        tau
    )) {
        return fail(
            'NOT_COLIFTABLE',
            'moduleColift.tau',
            'The test morphism does not factor through the epimorphism'
        );
    }
    return colift;
}

export interface AlgebraModuleKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-kernel';
    readonly morphism: AlgebraModuleMorphism<P, C, I>;
    readonly object: AlgebraPresentedModule<P, C, I>;
    readonly inclusion: AlgebraModuleMorphism<P, C, I>;
    readonly inducedMatrix: AlgebraMatrix<P, C, I>;
    readonly sourceRealization: AlgebraModuleRealization<P, C, I>;
    readonly targetRealization: AlgebraModuleRealization<P, C, I>;
}

export function algebraModuleKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraModuleMorphism<P, C, I>): AlgebraModuleKernel<P, C, I> {
    const sourceRealization = algebraModuleRealization(morphism.source);
    const targetRealization = algebraModuleRealization(morphism.target);
    const inducedMatrix = inducedMatrixFromRealizations(
        morphism,
        sourceRealization,
        targetRealization
    );
    const quotientKernel: AlgebraKernelBasis<P, C, I> =
        algebraMatrixKernelBasis(inducedMatrix);
    const lifted = algebraMatrixMultiply(
        sourceRealization.section,
        quotientKernel.generators
    );
    const object = algebraFreeModule(morphism.source.field, quotientKernel.nullity);
    const witness = algebraZeroMatrix(algebraMatrixSpace(
        morphism.source.field,
        morphism.source.relations.parent.columns,
        0
    ));
    const inclusion = algebraModuleMorphism(
        object,
        morphism.source,
        lifted,
        witness
    );
    return Object.freeze({
        kind: 'algebra-module-kernel',
        morphism,
        object,
        inclusion,
        inducedMatrix,
        sourceRealization,
        targetRealization
    });
}

export function algebraModuleKernelLift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    kernel: AlgebraModuleKernel<P, C, I>,
    testMorphism: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (!algebraModuleMorphismIsZero(algebraModuleCompose(
        kernel.morphism,
        testMorphism
    ))) {
        return fail(
            'NOT_LIFTABLE',
            'kernelLift.testMorphism',
            'A kernel lift requires a zero composite'
        );
    }
    return algebraModuleLiftAlongMonomorphism(
        kernel.inclusion,
        testMorphism
    );
}

export function algebraModuleCokernelColift<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    cokernel: AlgebraModuleCokernel<P, C, I>,
    testMorphism: AlgebraModuleMorphism<P, C, I>
): AlgebraModuleMorphism<P, C, I> {
    if (!algebraModuleMorphismIsZero(algebraModuleCompose(
        testMorphism,
        cokernel.morphism
    ))) {
        return fail(
            'NOT_COLIFTABLE',
            'cokernelColift.testMorphism',
            'A cokernel colift requires a zero composite'
        );
    }
    return algebraModuleColiftAlongEpimorphism(
        cokernel.projection,
        testMorphism
    );
}

export const algebraMatrixSyzygies = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(matrix: AlgebraMatrix<P, C, I>): AlgebraKernelBasis<P, C, I> =>
    algebraMatrixKernelBasis(matrix);

export const algebraPresentedModuleText = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(module: AlgebraPresentedModule<P, C, I>): string =>
    `coker(${algebraMatrixText(module.relations)})`;
