/** Space-specific matrix operations for the native TypeScript engine. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraKernelBasis,
    AlgebraMatrix,
    AlgebraMatrixSpace,
    AlgebraRowReduction,
    algebraMatrixAdd,
    algebraMatrixKernelBasis,
    algebraMatrixNegate,
    algebraMatrixRref,
    algebraMatrixSchema,
    algebraMatrixSpace,
    algebraMatrixTranspose
} from './algebra_matrix';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_MATRIX_REFERENCE_OPERATIONS_PROFILE = Object.freeze({
    revision: 'emdash-algebra-matrix-reference-operations-v1' as const,
    algorithmRevision: 'typescript-row-major-matrix-reference-v1' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraMatrixBinaryInput<T> {
    readonly left: T;
    readonly right: T;
}

export interface AlgebraMatrixReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly space: AlgebraMatrixSpace<P, C, I>;
    readonly transposeSpace: AlgebraMatrixSpace<P, C, I>;
    readonly matrixSchema: AlgebraRuntimeSchema<AlgebraMatrix<P, C, I>>;
    readonly transposeSchema: AlgebraRuntimeSchema<AlgebraMatrix<P, C, I>>;
    readonly binarySchema: AlgebraRuntimeSchema<
        AlgebraMatrixBinaryInput<AlgebraMatrix<P, C, I>>
    >;
    readonly rowReductionSchema: AlgebraRuntimeSchema<
        AlgebraRowReduction<P, C, I>
    >;
    readonly kernelSchema: AlgebraRuntimeSchema<AlgebraKernelBasis<P, C, I>>;
    readonly negate: AlgebraOperation<
        AlgebraMatrix<P, C, I>,
        AlgebraMatrix<P, C, I>
    >;
    readonly add: AlgebraOperation<
        AlgebraMatrixBinaryInput<AlgebraMatrix<P, C, I>>,
        AlgebraMatrix<P, C, I>
    >;
    readonly transpose: AlgebraOperation<
        AlgebraMatrix<P, C, I>,
        AlgebraMatrix<P, C, I>
    >;
    readonly rref: AlgebraOperation<
        AlgebraMatrix<P, C, I>,
        AlgebraRowReduction<P, C, I>
    >;
    readonly kernel: AlgebraOperation<
        AlgebraMatrix<P, C, I>,
        AlgebraKernelBasis<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const algorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_MATRIX_REFERENCE_OPERATIONS_PROFILE.algorithmRevision
);

export function algebraMatrixReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    space: AlgebraMatrixSpace<P, C, I>
): AlgebraMatrixReferenceOperations<P, C, I> {
    const suffix = space.identity.id;
    const matrixSchema = algebraMatrixSchema(space);
    const transposeSpace = algebraMatrixSpace(
        space.coefficientDomain,
        space.columns,
        space.rows
    );
    const transposeSchema = algebraMatrixSchema(transposeSpace);
    const binarySchema = defineAlgebraRuntimeSchema<
        AlgebraMatrixBinaryInput<AlgebraMatrix<P, C, I>>
    >({
        id: `algebra.matrix.binary-input/${suffix}`,
        revision: space.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || !('left' in value) || !('right' in value)) {
                throw new Error(`matrix binary input expected at ${path}`);
            }
            return Object.freeze({
                left: matrixSchema.normalize(value.left, `${path}.left`),
                right: matrixSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const rowReductionSchema = defineAlgebraRuntimeSchema<
        AlgebraRowReduction<P, C, I>
    >({
        id: `algebra.matrix.row-reduction/${suffix}`,
        revision: space.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-row-reduction' ||
                !Array.isArray(value.pivotColumns) ||
                !Number.isSafeInteger(value.rank) ||
                !Number.isSafeInteger(value.steps)
            ) {
                throw new Error(`row-reduction result expected at ${path}`);
            }
            const square = algebraMatrixSpace(
                space.coefficientDomain,
                space.rows,
                space.rows
            );
            const pivots = value.pivotColumns.map((pivot, index) => {
                if (
                    !Number.isSafeInteger(pivot) ||
                    (pivot as number) < 0 ||
                    (pivot as number) >= space.columns
                ) {
                    throw new Error(`invalid pivot at ${path}[${index}]`);
                }
                return pivot as number;
            });
            if (
                pivots.length !== value.rank ||
                pivots.some((pivot, index) =>
                    index > 0 && pivot <= pivots[index - 1]
                )
            ) {
                throw new Error(`inconsistent pivots and rank at ${path}`);
            }
            return Object.freeze({
                kind: 'algebra-row-reduction',
                input: matrixSchema.normalize(value.input, `${path}.input`),
                rref: matrixSchema.normalize(value.rref, `${path}.rref`),
                leftTransformation: algebraMatrixSchema(square).normalize(
                    value.leftTransformation,
                    `${path}.leftTransformation`
                ),
                pivotColumns: Object.freeze(pivots),
                rank: value.rank as number,
                steps: value.steps as number
            });
        }
    });
    const kernelSchema = defineAlgebraRuntimeSchema<AlgebraKernelBasis<P, C, I>>({
        id: `algebra.matrix.kernel-basis/${suffix}`,
        revision: space.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-kernel-basis' ||
                !Number.isSafeInteger(value.nullity) ||
                (value.nullity as number) < 0 ||
                (value.nullity as number) > space.columns
            ) {
                throw new Error(`kernel-basis result expected at ${path}`);
            }
            const actualKernelSpace = algebraMatrixSpace(
                space.coefficientDomain,
                space.columns,
                value.nullity as number
            );
            const reduction = rowReductionSchema.normalize(
                value.reduction,
                `${path}.reduction`
            );
            if (
                (value.nullity as number) !==
                    space.columns - reduction.rank
            ) {
                throw new Error(`inconsistent kernel nullity at ${path}`);
            }
            return Object.freeze({
                kind: 'algebra-kernel-basis',
                input: matrixSchema.normalize(value.input, `${path}.input`),
                reduction,
                generators: algebraMatrixSchema(actualKernelSpace).normalize(
                    value.generators,
                    `${path}.generators`
                ),
                nullity: value.nullity as number
            });
        }
    });
    const negate = defineAlgebraOperation({
        id: `algebra.matrix.negate/${suffix}`,
        revision: space.identity.revision,
        input: matrixSchema,
        output: matrixSchema
    });
    const add = defineAlgebraOperation({
        id: `algebra.matrix.add/${suffix}`,
        revision: space.identity.revision,
        input: binarySchema,
        output: matrixSchema
    });
    const transpose = defineAlgebraOperation({
        id: `algebra.matrix.transpose/${suffix}`,
        revision: space.identity.revision,
        input: matrixSchema,
        output: transposeSchema
    });
    const rref = defineAlgebraOperation({
        id: `algebra.matrix.rref/${suffix}`,
        revision: space.identity.revision,
        input: matrixSchema,
        output: rowReductionSchema
    });
    const kernel = defineAlgebraOperation({
        id: `algebra.matrix.kernel/${suffix}`,
        revision: space.identity.revision,
        input: matrixSchema,
        output: kernelSchema
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: negate,
            algorithm: algorithm(negate.identity.id),
            execute: algebraMatrixNegate
        }),
        defineAlgebraReferenceImplementation({
            operation: add,
            algorithm: algorithm(add.identity.id),
            execute: input => algebraMatrixAdd(input.left, input.right)
        }),
        defineAlgebraReferenceImplementation({
            operation: transpose,
            algorithm: algorithm(transpose.identity.id),
            execute: algebraMatrixTranspose
        }),
        defineAlgebraReferenceImplementation({
            operation: rref,
            algorithm: algorithm(rref.identity.id),
            execute: (input, context) => algebraMatrixRref(input, context)
        }),
        defineAlgebraReferenceImplementation({
            operation: kernel,
            algorithm: algorithm(kernel.identity.id),
            execute: (input, context) => algebraMatrixKernelBasis(input, context)
        })
    ]);
    return Object.freeze({
        space,
        transposeSpace,
        matrixSchema,
        transposeSchema,
        binarySchema,
        rowReductionSchema,
        kernelSchema,
        negate,
        add,
        transpose,
        rref,
        kernel,
        implementations
    });
}
