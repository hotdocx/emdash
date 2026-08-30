/** Exact row-major matrices with explicit column-vector orientation. */

import {
    AlgebraElement,
    AlgebraParent,
    defineAlgebraParent,
    sameAlgebraParent,
    validateAlgebraParent
} from './algebra_parent';
import {
    AlgebraCommutativeRingDomain,
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraComputationContextInput,
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema,
    normalizeAlgebraComputationContext
} from './algebra_engine';

export const ALGEBRA_MATRIX_PROFILE = Object.freeze({
    revision: 'emdash-algebra-matrix-v1' as const,
    serializationRevision: 'emdash-algebra-matrix-json-v1' as const,
    storage: 'immutable-row-major' as const,
    orientation: 'm-by-n-is-map-Rn-to-Rm-on-column-vectors' as const,
    composition: 'left-matrix-multiplication' as const,
    kernelGenerators: 'columns-of-n-by-k-matrix' as const,
    oneSidedInverses: 'rref-full-rank-left-and-right-inverses' as const,
    maximumRows: 100_000,
    maximumColumns: 100_000,
    maximumEntries: 10_000_000,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraMatrixErrorCode =
    | 'INVALID_MATRIX_SPACE'
    | 'INVALID_MATRIX'
    | 'FOREIGN_MATRIX_SPACE'
    | 'DIMENSION_MISMATCH'
    | 'INDEX_OUT_OF_RANGE'
    | 'NON_FIELD_COEFFICIENTS'
    | 'NO_LEFT_INVERSE'
    | 'NO_RIGHT_INVERSE'
    | 'MATRIX_LIMIT_EXCEEDED'
    | 'CANCELLED';

export class AlgebraMatrixError extends Error {
    constructor(
        public readonly code: AlgebraMatrixErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraMatrixError';
    }
}

const fail = (
    code: AlgebraMatrixErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraMatrixError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export interface AlgebraMatrixSpace<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraParent<'matrix-space'> {
    readonly coefficientDomain: AlgebraCommutativeRingDomain<P, C, I>;
    readonly rows: number;
    readonly columns: number;
}

export interface AlgebraMatrix<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraElement<AlgebraMatrixSpace<P, C, I>> {
    readonly kind: 'algebra-matrix';
    readonly entries: readonly (readonly C[])[];
}

const dimension = (value: unknown, path: string): number => {
    if (Number.isSafeInteger(value) && (value as number) >= 0) {
        return value as number;
    }
    return fail(
        'INVALID_MATRIX_SPACE',
        path,
        'Matrix dimension must be a nonnegative safe integer'
    );
};

const spaceId = (
    parent: AlgebraParent,
    rows: number,
    columns: number
): string => `algebra.matrix-space/${parent.identity.id}/${rows}x${columns}`;

export function algebraMatrixSpace<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    coefficientDomain: AlgebraCommutativeRingDomain<P, C, I>,
    rowInput: number,
    columnInput: number
): AlgebraMatrixSpace<P, C, I> {
    const rows = dimension(rowInput, 'matrixSpace.rows');
    const columns = dimension(columnInput, 'matrixSpace.columns');
    if (
        rows > ALGEBRA_MATRIX_PROFILE.maximumRows ||
        columns > ALGEBRA_MATRIX_PROFILE.maximumColumns ||
        rows * columns > ALGEBRA_MATRIX_PROFILE.maximumEntries
    ) {
        return fail(
            'MATRIX_LIMIT_EXCEEDED',
            'matrixSpace',
            'Matrix space exceeds configured dimension or entry limits'
        );
    }
    const parent = defineAlgebraParent(
        'matrix-space',
        spaceId(coefficientDomain.parent, rows, columns),
        `v1.${coefficientDomain.parent.identity.revision}`
    );
    return Object.freeze({
        ...parent,
        coefficientDomain,
        rows,
        columns
    });
}

const validateSpace = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    value: AlgebraMatrixSpace<P, C, I>,
    path: string
): AlgebraMatrixSpace<P, C, I> => {
    if (
        !record(value) ||
        value.kind !== 'matrix-space' ||
        !record(value.coefficientDomain)
    ) {
        return fail(
            'INVALID_MATRIX_SPACE',
            path,
            'Expected one matrix space'
        );
    }
    const parent = validateAlgebraParent(value, path, 'matrix-space');
    const rows = dimension(value.rows, `${path}.rows`);
    const columns = dimension(value.columns, `${path}.columns`);
    const expectedId = spaceId(value.coefficientDomain.parent, rows, columns);
    if (
        parent.identity.id !== expectedId ||
        parent.identity.revision !==
            `v1.${value.coefficientDomain.parent.identity.revision}`
    ) {
        return fail(
            'INVALID_MATRIX_SPACE',
            `${path}.identity`,
            'Matrix-space identity disagrees with its structural data'
        );
    }
    return value;
};

const sameSpace = (
    left: AlgebraMatrixSpace<AlgebraParent, AlgebraElement, unknown>,
    right: AlgebraMatrixSpace<AlgebraParent, AlgebraElement, unknown>
): boolean => sameAlgebraParent(left, right);

export function algebraMatrix<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    spaceInput: AlgebraMatrixSpace<P, C, I>,
    rowInput: readonly (readonly (I | C)[])[]
): AlgebraMatrix<P, C, I> {
    const space = validateSpace(spaceInput, 'matrix.parent');
    if (!Array.isArray(rowInput) || rowInput.length !== space.rows) {
        return fail(
            'INVALID_MATRIX',
            'matrix.entries',
            `Matrix requires exactly ${space.rows} rows`
        );
    }
    const entries = rowInput.map((row, rowIndex) => {
        if (!Array.isArray(row) || row.length !== space.columns) {
            return fail(
                'INVALID_MATRIX',
                `matrix.entries[${rowIndex}]`,
                `Matrix row requires exactly ${space.columns} entries`
            );
        }
        return Object.freeze(row.map(entry =>
            space.coefficientDomain.normalize(entry)
        ));
    });
    return Object.freeze({
        kind: 'algebra-matrix',
        parent: space,
        entries: Object.freeze(entries)
    });
}

export function validateAlgebraMatrix<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    space: AlgebraMatrixSpace<P, C, I>,
    value: unknown,
    path = 'matrix'
): AlgebraMatrix<P, C, I> {
    if (
        !record(value) ||
        value.kind !== 'algebra-matrix' ||
        !record(value.parent) ||
        !Array.isArray(value.entries)
    ) {
        return fail(
            'INVALID_MATRIX',
            path,
            'Expected one exact matrix'
        );
    }
    if (!sameSpace(
        value.parent as unknown as AlgebraMatrixSpace<
            AlgebraParent,
            AlgebraElement,
            unknown
        >,
        space as unknown as AlgebraMatrixSpace<
            AlgebraParent,
            AlgebraElement,
            unknown
        >
    )) {
        return fail(
            'FOREIGN_MATRIX_SPACE',
            `${path}.parent`,
            `Expected matrix space '${space.identity.id}'`
        );
    }
    return algebraMatrix(space, value.entries as (I | C)[][]);
}

export function algebraMatrixSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(space: AlgebraMatrixSpace<P, C, I>): AlgebraRuntimeSchema<
    AlgebraMatrix<P, C, I>
> {
    validateSpace(space, 'matrixSchema.space');
    return defineAlgebraRuntimeSchema({
        id: `algebra.matrix/${space.identity.id}`,
        revision: space.identity.revision,
        normalize(value: unknown, path: string) {
            if (record(value) && value.kind === 'algebra-matrix') {
                return validateAlgebraMatrix(space, value, path);
            }
            if (record(value) && Array.isArray(value.entries)) {
                return algebraMatrix(space, value.entries as (I | C)[][]);
            }
            throw new Error(`matrix expected at ${path}`);
        }
    });
}

export const algebraZeroMatrix = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(space: AlgebraMatrixSpace<P, C, I>): AlgebraMatrix<P, C, I> =>
    algebraMatrix(space, Array.from(
        { length: space.rows },
        () => Array.from(
            { length: space.columns },
            () => space.coefficientDomain.zero
        )
    ));

export const algebraIdentityMatrix = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    coefficientDomain: AlgebraCommutativeRingDomain<P, C, I>,
    size: number
): AlgebraMatrix<P, C, I> => {
    const space = algebraMatrixSpace(coefficientDomain, size, size);
    return algebraMatrix(space, Array.from(
        { length: size },
        (_, row) => Array.from(
            { length: size },
            (_, column) => row === column
                ? coefficientDomain.one
                : coefficientDomain.zero
        )
    ));
};

const sameMatrixPair = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraMatrix<P, C, I>,
    right: AlgebraMatrix<P, C, I>,
    path: string
): AlgebraMatrixSpace<P, C, I> => {
    if (!sameSpace(
        left.parent as unknown as AlgebraMatrixSpace<
            AlgebraParent,
            AlgebraElement,
            unknown
        >,
        right.parent as unknown as AlgebraMatrixSpace<
            AlgebraParent,
            AlgebraElement,
            unknown
        >
    )) {
        return fail(
            'FOREIGN_MATRIX_SPACE',
            path,
            'Matrix operands inhabit different spaces'
        );
    }
    return left.parent;
};

export const algebraMatrixEntry = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(matrix: AlgebraMatrix<P, C, I>, row: number, column: number): C => {
    if (
        !Number.isSafeInteger(row) ||
        !Number.isSafeInteger(column) ||
        row < 0 ||
        column < 0 ||
        row >= matrix.parent.rows ||
        column >= matrix.parent.columns
    ) {
        return fail(
            'INDEX_OUT_OF_RANGE',
            'matrix.entry',
            'Matrix entry index is out of range'
        );
    }
    return matrix.entries[row][column];
};

export const algebraMatrixAdd = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraMatrix<P, C, I>, right: AlgebraMatrix<P, C, I>):
    AlgebraMatrix<P, C, I> => {
    const space = sameMatrixPair(left, right, 'matrixAdd');
    return algebraMatrix(space, left.entries.map((row, rowIndex) =>
        row.map((entry, column) => space.coefficientDomain.add(
            entry,
            right.entries[rowIndex][column]
        ))
    ));
};

export const algebraMatrixNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(matrix: AlgebraMatrix<P, C, I>): AlgebraMatrix<P, C, I> =>
    algebraMatrix(matrix.parent, matrix.entries.map(row =>
        row.map(entry => matrix.parent.coefficientDomain.negate(entry))
    ));

export const algebraMatrixSubtract = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraMatrix<P, C, I>, right: AlgebraMatrix<P, C, I>):
    AlgebraMatrix<P, C, I> => algebraMatrixAdd(left, algebraMatrixNegate(right));

export const algebraMatrixTranspose = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(matrix: AlgebraMatrix<P, C, I>): AlgebraMatrix<P, C, I> => {
    const space = algebraMatrixSpace(
        matrix.parent.coefficientDomain,
        matrix.parent.columns,
        matrix.parent.rows
    );
    return algebraMatrix(space, Array.from(
        { length: space.rows },
        (_, row) => Array.from(
            { length: space.columns },
            (_, column) => matrix.entries[column][row]
        )
    ));
};

export const algebraMatrixMultiply = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraMatrix<P, C, I>,
    right: AlgebraMatrix<P, C, I>
): AlgebraMatrix<P, C, I> => {
    if (
        left.parent.columns !== right.parent.rows ||
        !sameAlgebraParent(
            left.parent.coefficientDomain.parent,
            right.parent.coefficientDomain.parent
        )
    ) {
        return fail(
            'DIMENSION_MISMATCH',
            'matrixMultiply',
            'For left*right, left columns must equal right rows over one domain'
        );
    }
    const domain = left.parent.coefficientDomain;
    const space = algebraMatrixSpace(
        domain,
        left.parent.rows,
        right.parent.columns
    );
    return algebraMatrix(space, Array.from(
        { length: space.rows },
        (_, row) => Array.from(
            { length: space.columns },
            (_, column) => {
                let sum = domain.zero;
                for (let index = 0; index < left.parent.columns; index++) {
                    sum = domain.add(
                        sum,
                        domain.multiply(
                            left.entries[row][index],
                            right.entries[index][column]
                        )
                    );
                }
                return sum;
            }
        )
    ));
};

export const algebraMatrixEquals = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(left: AlgebraMatrix<P, C, I>, right: AlgebraMatrix<P, C, I>): boolean => {
    if (!sameAlgebraParent(left.parent, right.parent)) return false;
    const domain = left.parent.coefficientDomain;
    return left.entries.every((row, rowIndex) => row.every(
        (entry, column) => domain.equals(
            entry,
            right.entries[rowIndex][column]
        )
    ));
};

const fieldDomain = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(space: AlgebraMatrixSpace<P, C, I>): AlgebraFieldDomain<P, C, I> => {
    const domain = space.coefficientDomain as Partial<
        AlgebraFieldDomain<P, C, I>
    >;
    if (
        domain.field !== true ||
        typeof domain.divide !== 'function' ||
        typeof domain.inverse !== 'function'
    ) {
        return fail(
            'NON_FIELD_COEFFICIENTS',
            'matrix.coefficientDomain',
            'Row reduction requires an operational field domain'
        );
    }
    return domain as AlgebraFieldDomain<P, C, I>;
};

export interface AlgebraRowReduction<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-row-reduction';
    readonly input: AlgebraMatrix<P, C, I>;
    readonly rref: AlgebraMatrix<P, C, I>;
    /** leftTransformation * input = rref. */
    readonly leftTransformation: AlgebraMatrix<P, C, I>;
    readonly pivotColumns: readonly number[];
    readonly rank: number;
    readonly steps: number;
}

export function algebraMatrixRref<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    matrix: AlgebraMatrix<P, C, I>,
    contextInput: AlgebraComputationContextInput = {}
): AlgebraRowReduction<P, C, I> {
    const context = normalizeAlgebraComputationContext(contextInput);
    const field = fieldDomain(matrix.parent);
    const intermediateEntries = matrix.parent.rows * matrix.parent.columns +
        matrix.parent.rows * matrix.parent.rows;
    if (
        context.limits.maximumIntermediateItems !== undefined &&
        intermediateEntries > context.limits.maximumIntermediateItems
    ) {
        return fail(
            'MATRIX_LIMIT_EXCEEDED',
            'rref.intermediateEntries',
            `Row reduction requires ${intermediateEntries} mutable entries; ` +
                `limit is ${context.limits.maximumIntermediateItems}`
        );
    }
    const entries = matrix.entries.map(row => [...row]);
    const transformation = algebraIdentityMatrix(
        matrix.parent.coefficientDomain,
        matrix.parent.rows
    ).entries.map(row => [...row]);
    const pivots: number[] = [];
    let pivotRow = 0;
    let steps = 0;
    const tick = (): void => {
        steps++;
        if (
            context.limits.fuel !== undefined &&
            steps > context.limits.fuel
        ) {
            fail(
                'MATRIX_LIMIT_EXCEEDED',
                'rref.steps',
                `Row reduction exceeded fuel ${context.limits.fuel}`
            );
        }
    };

    for (
        let column = 0;
        column < matrix.parent.columns && pivotRow < matrix.parent.rows;
        column++
    ) {
        if (context.cancellation?.requested()) {
            return fail(
                'CANCELLED',
                'rref',
                context.cancellation.reason?.() ?? 'Row reduction cancelled'
            );
        }
        let selected = pivotRow;
        while (
            selected < matrix.parent.rows &&
            field.isZero(entries[selected][column])
        ) selected++;
        if (selected === matrix.parent.rows) continue;
        if (selected !== pivotRow) {
            [entries[pivotRow], entries[selected]] = [
                entries[selected],
                entries[pivotRow]
            ];
            [transformation[pivotRow], transformation[selected]] = [
                transformation[selected],
                transformation[pivotRow]
            ];
            tick();
        }
        const inverse = field.inverse(entries[pivotRow][column]);
        entries[pivotRow] = entries[pivotRow].map(value =>
            field.multiply(inverse, value)
        );
        transformation[pivotRow] = transformation[pivotRow].map(value =>
            field.multiply(inverse, value)
        );
        tick();
        for (let row = 0; row < matrix.parent.rows; row++) {
            if (row === pivotRow || field.isZero(entries[row][column])) continue;
            const scalar = entries[row][column];
            entries[row] = entries[row].map((value, index) => field.subtract(
                value,
                field.multiply(scalar, entries[pivotRow][index])
            ));
            transformation[row] = transformation[row].map(
                (value, index) => field.subtract(
                    value,
                    field.multiply(scalar, transformation[pivotRow][index])
                )
            );
            tick();
        }
        pivots.push(column);
        pivotRow++;
        context.onProgress?.({
            phase: 'algebra.matrix.rref',
            completed: pivotRow,
            total: Math.min(matrix.parent.rows, matrix.parent.columns)
        });
    }
    return Object.freeze({
        kind: 'algebra-row-reduction',
        input: matrix,
        rref: algebraMatrix(matrix.parent, entries),
        leftTransformation: algebraMatrix(
            algebraMatrixSpace(
                matrix.parent.coefficientDomain,
                matrix.parent.rows,
                matrix.parent.rows
            ),
            transformation
        ),
        pivotColumns: Object.freeze(pivots),
        rank: pivots.length,
        steps
    });
}

export interface AlgebraKernelBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-kernel-basis';
    readonly input: AlgebraMatrix<P, C, I>;
    readonly reduction: AlgebraRowReduction<P, C, I>;
    /** Columns form a basis; input * generators = 0. */
    readonly generators: AlgebraMatrix<P, C, I>;
    readonly nullity: number;
}

export function algebraMatrixKernelBasis<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    matrix: AlgebraMatrix<P, C, I>,
    context: AlgebraComputationContextInput = {}
): AlgebraKernelBasis<P, C, I> {
    const reduction = algebraMatrixRref(matrix, context);
    const domain = matrix.parent.coefficientDomain;
    const pivotSet = new Set(reduction.pivotColumns);
    const freeColumns = Array.from(
        { length: matrix.parent.columns },
        (_, index) => index
    ).filter(index => !pivotSet.has(index));
    const rows = Array.from(
        { length: matrix.parent.columns },
        () => Array.from({ length: freeColumns.length }, () => domain.zero)
    );
    freeColumns.forEach((freeColumn, basisColumn) => {
        rows[freeColumn][basisColumn] = domain.one;
        reduction.pivotColumns.forEach((pivotColumn, pivotRow) => {
            rows[pivotColumn][basisColumn] = domain.negate(
                reduction.rref.entries[pivotRow][freeColumn]
            );
        });
    });
    const generators = algebraMatrix(
        algebraMatrixSpace(
            domain,
            matrix.parent.columns,
            freeColumns.length
        ),
        rows
    );
    return Object.freeze({
        kind: 'algebra-kernel-basis',
        input: matrix,
        reduction,
        generators,
        nullity: freeColumns.length
    });
}

/**
 * Return a left inverse L with L * matrix = identity.
 *
 * A left inverse exists exactly when the columns are linearly independent.
 */
export function algebraMatrixLeftInverse<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    matrix: AlgebraMatrix<P, C, I>,
    context: AlgebraComputationContextInput = {}
): AlgebraMatrix<P, C, I> {
    const reduction = algebraMatrixRref(matrix, context);
    if (reduction.rank !== matrix.parent.columns) {
        return fail(
            'NO_LEFT_INVERSE',
            'matrixLeftInverse',
            'A left inverse requires full column rank'
        );
    }
    return algebraMatrix(
        algebraMatrixSpace(
            matrix.parent.coefficientDomain,
            matrix.parent.columns,
            matrix.parent.rows
        ),
        reduction.leftTransformation.entries.slice(
            0,
            matrix.parent.columns
        )
    );
}

/**
 * Return a right inverse R with matrix * R = identity.
 *
 * A right inverse exists exactly when the rows are linearly independent.
 */
export function algebraMatrixRightInverse<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    matrix: AlgebraMatrix<P, C, I>,
    context: AlgebraComputationContextInput = {}
): AlgebraMatrix<P, C, I> {
    try {
        return algebraMatrixTranspose(algebraMatrixLeftInverse(
            algebraMatrixTranspose(matrix),
            context
        ));
    } catch (error: unknown) {
        if (
            error instanceof AlgebraMatrixError &&
            error.code === 'NO_LEFT_INVERSE'
        ) {
            return fail(
                'NO_RIGHT_INVERSE',
                'matrixRightInverse',
                'A right inverse requires full row rank',
                error
            );
        }
        throw error;
    }
}

export const algebraMatrixText = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(matrix: AlgebraMatrix<P, C, I>): string => matrix.entries
    .map(row => `[${row.map(value =>
        matrix.parent.coefficientDomain.text(value)
    ).join(', ')}]`)
    .join('\n');

export const serializeAlgebraMatrix = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(matrix: AlgebraMatrix<P, C, I>): string => `${JSON.stringify({
    serializationRevision: ALGEBRA_MATRIX_PROFILE.serializationRevision,
    kind: matrix.kind,
    parent: {
        id: matrix.parent.identity.id,
        revision: matrix.parent.identity.revision,
        coefficientParent: {
            id: matrix.parent.coefficientDomain.parent.identity.id,
            revision: matrix.parent.coefficientDomain.parent.identity.revision
        },
        rows: matrix.parent.rows,
        columns: matrix.parent.columns,
        orientation: ALGEBRA_MATRIX_PROFILE.orientation
    },
    entries: matrix.entries.map(row => row.map(value =>
        matrix.parent.coefficientDomain.text(value)
    ))
})}\n`;
