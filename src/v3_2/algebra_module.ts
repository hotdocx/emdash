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
    AlgebraMatrixSpace,
    AlgebraKernelBasis,
    algebraIdentityMatrix,
    algebraMatrix,
    algebraMatrixEquals,
    algebraMatrixKernelBasis,
    algebraMatrixMultiply,
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
    | 'DIMENSION_MISMATCH';

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

const sameModule = <
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
    if (!sameModule(before.target, after.source)) {
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

export interface AlgebraModuleKernel<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-module-kernel';
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
    const inducedMatrix = algebraMatrixMultiply(
        algebraMatrixMultiply(targetRealization.projection, morphism.matrix),
        sourceRealization.section
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
        object,
        inclusion,
        inducedMatrix,
        sourceRealization,
        targetRealization
    });
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
