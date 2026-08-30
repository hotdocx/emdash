/** Focused CAS-MATRIX-4A exact-matrix tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    INTEGER_DOMAIN,
    RATIONAL_DOMAIN,
    algebraRationalText
} from '../src/v3_2/algebra_exact';
import {
    ALGEBRA_MATRIX_PROFILE,
    AlgebraMatrixError,
    algebraIdentityMatrix,
    algebraMatrix,
    algebraMatrixAdd,
    algebraMatrixEntry,
    algebraMatrixEquals,
    algebraMatrixKernelBasis,
    algebraMatrixLeftInverse,
    algebraMatrixMultiply,
    algebraMatrixNegate,
    algebraMatrixRref,
    algebraMatrixRightInverse,
    algebraMatrixSchema,
    algebraMatrixSpace,
    algebraMatrixSubtract,
    algebraMatrixText,
    algebraMatrixTranspose,
    algebraZeroMatrix,
    serializeAlgebraMatrix
} from '../src/v3_2/algebra_matrix';
import {
    algebraMatrixReferenceOperations
} from '../src/v3_2/algebra_matrix_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import {
    createAlgebraTypeScriptReferenceEngine
} from '../src/v3_2/algebra_reference_engine';
import {
    computeAlgebraOperation
} from '../src/v3_2/algebra_engine';

const matrixError = (
    expected: AlgebraMatrixError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraMatrixError);
    assert.equal(error.code, expected);
    return true;
};

describe('v3.2 exact row-major matrices', () => {
    it('fixes m-by-n column-vector orientation and immutable storage', () => {
        const space = algebraMatrixSpace(RATIONAL_DOMAIN, 2, 3);
        const matrix = algebraMatrix(space, [
            ['1', '2', '3'],
            ['4', '5', '6']
        ]);
        assert.equal(space.rows, 2);
        assert.equal(space.columns, 3);
        assert.equal(ALGEBRA_MATRIX_PROFILE.orientation,
            'm-by-n-is-map-Rn-to-Rm-on-column-vectors');
        assert.equal(algebraRationalText(algebraMatrixEntry(matrix, 1, 2)), '6');
        assert.equal(algebraMatrixText(matrix), '[1, 2, 3]\n[4, 5, 6]');
        assert.ok(Object.isFrozen(space));
        assert.ok(Object.isFrozen(matrix));
        assert.ok(Object.isFrozen(matrix.entries));
        assert.ok(Object.isFrozen(matrix.entries[0]));
        assert.throws(
            () => algebraMatrixEntry(matrix, 2, 0),
            matrixError('INDEX_OUT_OF_RANGE')
        );
    });

    it('constructs zero and identity matrices including empty dimensions', () => {
        const zero = algebraZeroMatrix(algebraMatrixSpace(
            RATIONAL_DOMAIN,
            2,
            3
        ));
        assert.equal(algebraMatrixText(zero), '[0, 0, 0]\n[0, 0, 0]');
        const identity = algebraIdentityMatrix(RATIONAL_DOMAIN, 3);
        assert.equal(
            algebraMatrixText(identity),
            '[1, 0, 0]\n[0, 1, 0]\n[0, 0, 1]'
        );
        const empty = algebraZeroMatrix(algebraMatrixSpace(
            RATIONAL_DOMAIN,
            0,
            4
        ));
        assert.equal(empty.entries.length, 0);
        assert.equal(algebraMatrixTranspose(empty).parent.rows, 4);
        assert.equal(algebraMatrixTranspose(empty).parent.columns, 0);
    });

    it('computes addition, negation, subtraction, transpose, and equality', () => {
        const space = algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2);
        const left = algebraMatrix(space, [['1', '2'], ['3', '4']]);
        const right = algebraMatrix(space, [['4', '3'], ['2', '1']]);
        assert.equal(
            algebraMatrixText(algebraMatrixAdd(left, right)),
            '[5, 5]\n[5, 5]'
        );
        assert.equal(
            algebraMatrixText(algebraMatrixNegate(left)),
            '[-1, -2]\n[-3, -4]'
        );
        assert.ok(algebraMatrixEquals(
            algebraMatrixSubtract(left, right),
            algebraMatrix(space, [['-3', '-1'], ['1', '3']])
        ));
        assert.equal(
            algebraMatrixText(algebraMatrixTranspose(left)),
            '[1, 3]\n[2, 4]'
        );
        assert.ok(algebraMatrixEquals(
            algebraMatrixTranspose(algebraMatrixTranspose(left)),
            left
        ));
    });

    it('uses left multiplication for composition on column vectors', () => {
        const left = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 3),
            [['1', '2', '3'], ['0', '1', '1']]
        );
        const right = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 3, 1),
            [['2'], ['3'], ['4']]
        );
        const composite = algebraMatrixMultiply(left, right);
        assert.equal(composite.parent.rows, 2);
        assert.equal(composite.parent.columns, 1);
        assert.equal(algebraMatrixText(composite), '[20]\n[7]');
        assert.throws(
            () => algebraMatrixMultiply(right, left),
            matrixError('DIMENSION_MISMATCH')
        );
    });

    it('computes RREF and retains the left row-operation transformation', () => {
        const matrix = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 3),
            [['1', '2', '3'], ['2', '4', '6']]
        );
        const reduction = algebraMatrixRref(matrix);
        assert.equal(reduction.rank, 1);
        assert.deepEqual(reduction.pivotColumns, [0]);
        assert.equal(algebraMatrixText(reduction.rref), '[1, 2, 3]\n[0, 0, 0]');
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(reduction.leftTransformation, matrix),
            reduction.rref
        ));
        assert.ok(reduction.steps > 0);
        assert.ok(Object.isFrozen(reduction));
        assert.ok(Object.isFrozen(reduction.pivotColumns));
    });

    it('returns kernel generators as columns of an n-by-k matrix', () => {
        const matrix = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 3),
            [['1', '2', '3'], ['2', '4', '6']]
        );
        const kernel = algebraMatrixKernelBasis(matrix);
        assert.equal(kernel.nullity, 2);
        assert.equal(kernel.generators.parent.rows, 3);
        assert.equal(kernel.generators.parent.columns, 2);
        const composite = algebraMatrixMultiply(matrix, kernel.generators);
        assert.ok(algebraMatrixEquals(
            composite,
            algebraZeroMatrix(composite.parent)
        ));
    });

    it('constructs left and right inverses exactly when ranks permit', () => {
        const tall = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 3, 2),
            [['1', '0'], ['0', '1'], ['1', '1']]
        );
        const leftInverse = algebraMatrixLeftInverse(tall);
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(leftInverse, tall),
            algebraIdentityMatrix(RATIONAL_DOMAIN, 2)
        ));
        const wide = algebraMatrixTranspose(tall);
        const rightInverse = algebraMatrixRightInverse(wide);
        assert.ok(algebraMatrixEquals(
            algebraMatrixMultiply(wide, rightInverse),
            algebraIdentityMatrix(RATIONAL_DOMAIN, 2)
        ));
        const singular = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
            [['1', '1'], ['1', '1']]
        );
        assert.throws(
            () => algebraMatrixLeftInverse(singular),
            matrixError('NO_LEFT_INVERSE')
        );
        assert.throws(
            () => algebraMatrixRightInverse(singular),
            matrixError('NO_RIGHT_INVERSE')
        );
    });

    it('rejects foreign dimensions, non-fields, fuel exhaustion, and cancellation', () => {
        const first = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2),
            [['1', '2']]
        );
        const second = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
            [['1'], ['2']]
        );
        assert.throws(
            () => algebraMatrixAdd(first, second as never),
            matrixError('FOREIGN_MATRIX_SPACE')
        );
        const integer = algebraMatrix(
            algebraMatrixSpace(INTEGER_DOMAIN, 1, 1),
            [['2']]
        );
        assert.throws(
            () => algebraMatrixRref(integer),
            matrixError('NON_FIELD_COEFFICIENTS')
        );
        const matrix = algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
            [['1', '2'], ['3', '4']]
        );
        assert.throws(
            () => algebraMatrixRref(matrix, { limits: { fuel: 1 } }),
            matrixError('MATRIX_LIMIT_EXCEEDED')
        );
        assert.throws(
            () => algebraMatrixRref(matrix, {
                cancellation: { requested: () => true }
            }),
            matrixError('CANCELLED')
        );
        assert.throws(
            () => algebraMatrixRref(matrix, {
                limits: { maximumIntermediateItems: 1 }
            }),
            matrixError('MATRIX_LIMIT_EXCEEDED')
        );
    });

    it('normalizes matrix schemas and serializes coefficients as text', () => {
        const space = algebraMatrixSpace(RATIONAL_DOMAIN, 1, 2);
        const schema = algebraMatrixSchema(space);
        const matrix = schema.normalize({ entries: [['2/4', '-3']] }, 'value');
        assert.equal(algebraMatrixText(matrix), '[1/2, -3]');
        const text = serializeAlgebraMatrix(matrix);
        const parsed = JSON.parse(text);
        assert.equal(
            parsed.serializationRevision,
            ALGEBRA_MATRIX_PROFILE.serializationRevision
        );
        assert.equal(parsed.parent.orientation, ALGEBRA_MATRIX_PROFILE.orientation);
        assert.deepEqual(parsed.entries, [['1/2', '-3']]);
        assert.ok(text.endsWith('\n'));
    });

    it('executes matrix RREF/kernel operations and a transpose graph', async () => {
        const space = algebraMatrixSpace(RATIONAL_DOMAIN, 2, 3);
        const matrix = algebraMatrix(space, [
            ['1', '2', '3'],
            ['2', '4', '6']
        ]);
        const operations = algebraMatrixReferenceOperations(space);
        const transposeOperations = algebraMatrixReferenceOperations(
            operations.transposeSpace
        );
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: [
                ...operations.implementations,
                ...transposeOperations.implementations
            ]
        });
        const reduction = await computeAlgebraOperation({
            engine,
            operation: operations.rref,
            input: matrix,
            context: {
                limits: { fuel: 20, maximumIntermediateItems: 20 }
            }
        });
        const kernel = await computeAlgebraOperation({
            engine,
            operation: operations.kernel,
            input: matrix,
            context: {
                limits: { fuel: 20, maximumIntermediateItems: 20 }
            }
        });
        assert.equal(reduction.value.rank, 1);
        assert.equal(kernel.value.nullity, 2);

        const builder = createAlgebraComputationGraphBuilder(
            'fixture.matrix.double-transpose',
            'v1'
        );
        const input = builder.input('matrix', operations.matrixSchema);
        const transposed = builder.operation(
            'transposed',
            operations.transpose,
            input
        );
        const restored = builder.operation(
            'restored',
            transposeOperations.transpose,
            transposed
        );
        const graph = builder.build([{ id: 'result', value: restored }]);
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine,
            inputs: [{ id: 'matrix', value: matrix }]
        });
        assert.ok(algebraMatrixEquals(
            execution.outputs[0].value as typeof matrix,
            matrix
        ));
    });
});
