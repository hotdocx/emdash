/**
 * Non-authoritative constant-Q differential. Both engines receive the same
 * input matrices, then independently construct homology and connecting maps.
 * Q[] is Q itself: no specialization of a polynomial variable is performed.
 * The field sections below are test-only coordinate comparisons, not a
 * splitting assumption on the native polynomial Freyd implementation.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE,
    RATIONAL_DOMAIN,
    algebraFreeModule,
    algebraIdentityMatrix,
    algebraMatrix,
    algebraMatrixEquals,
    algebraMatrixLeftInverse,
    algebraMatrixMultiply as multiply,
    algebraMatrixSpace,
    algebraModuleCapSnakeConnecting,
    algebraModuleChainComplex,
    algebraModuleChainComplexHomology,
    algebraModuleChainMap,
    algebraModuleChainMapHomology,
    algebraModuleCompose,
    algebraModuleConnectingMorphism,
    algebraModuleHomology,
    algebraModuleInducedMatrix,
    algebraModuleMorphism,
    algebraModuleMorphismIsZero,
    algebraModuleRealization,
    algebraModuleShortExactSequence,
    algebraPolynomialConstant,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydBoundedChainMap,
    algebraPolynomialFreydBoundedComplex,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialText,
    algebraPresentedModule,
    algebraPresentedPolynomialModule,
    algebraZeroMatrix
} from '../src/v3_2';
import { algebraPolynomialFreydBoundedShortExactSequence } from '../src/v3_2/algebra_polynomial_freyd_bounded_short_exact';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';

const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [], 'lex');
const matrix = (rows: number, columns: number, entries: readonly (readonly string[])[]) =>
    algebraMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, rows, columns), entries);
const zero = (rows: number, columns: number) =>
    algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, rows, columns));
type Matrix = ReturnType<typeof matrix>;
const matrixText = (value: Matrix) => value.entries.map(row => row.map(RATIONAL_DOMAIN.text));
const equal = (actual: Matrix, expected: Matrix, label: string) => {
    assert.deepEqual([actual.parent.rows, actual.parent.columns],
        [expected.parent.rows, expected.parent.columns], label + ' dimensions');
    assert.deepEqual(matrixText(actual), matrixText(expected), label);
};
const isZero = (value: Matrix) => algebraMatrixEquals(value, zero(value.parent.rows, value.parent.columns));
const fromColumns = (rows: number, columns: readonly (readonly string[])[]) =>
    matrix(rows, columns.length, Array.from({ length: rows }, (_, row) => columns.map(column => column[row])));

/**
 * B_n = A_n + C_n with i(a)=(2a,0), p(a,c)=3c. In three degrees:
 * dA_1=diag(1,0), dA_2=0, dC_1=0, dC_2=(0,1)^t.
 * The off-diagonal block of dB_1 sends c_1 to 6k*a_2; hence delta_1=k.
 * H_1(C) and H_0(A) are both genuine quotients by nonzero boundaries.
 */
const inputFixture = (connecting: string, singleDegree = false) => {
    const a = singleDegree ? [2] : [2, 2, 1];
    const c = singleDegree ? [1] : [1, 2, 1];
    const b = a.map((rank, n) => rank + c[n]);
    const inclusion = a.map((rank, n) => matrix(b[n], rank,
        Array.from({ length: b[n] }, (_, row) =>
            Array.from({ length: rank }, (_, column) => row === column ? '2' : '0'))));
    const projection = c.map((rank, n) => matrix(rank, b[n],
        Array.from({ length: rank }, (_, row) =>
            Array.from({ length: b[n] }, (_, column) => column === a[n] + row ? '3' : '0'))));
    const cross = RATIONAL_DOMAIN.text(RATIONAL_DOMAIN.multiply('6', connecting));
    return {
        a, b, c, inclusion, projection,
        dA: singleDegree ? [] : [matrix(2, 2, [['1', '0'], ['0', '0']]), zero(2, 1)],
        dC: singleDegree ? [] : [zero(1, 2), matrix(2, 1, [['0'], ['1']])],
        dB: singleDegree ? [] : [
            matrix(3, 4, [['1', '0', '0', '0'], ['0', '0', cross, '0'], ['0', '0', '0', '0']]),
            matrix(4, 2, [['0', '0'], ['0', '0'], ['0', '0'], ['0', '1']])
        ]
    };
};

const nativeFixture = (input: ReturnType<typeof inputFixture>) => {
    const object = (rank: number) => algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(algebraPolynomialFreeModule(ring, rank), []));
    const map = (source: ReturnType<typeof object>, target: ReturnType<typeof object>, value: Matrix) =>
        algebraPolynomialPresentationMorphism({
            source, target,
            map: algebraPolynomialModuleMap(source.ambient, target.ambient,
                Array.from({ length: value.parent.columns }, (_, column) =>
                    algebraPolynomialModuleVector(target.ambient, value.entries.map(row =>
                        algebraPolynomialConstant(ring, RATIONAL_DOMAIN.text(row[column]))))))
        });
    const complex = (ranks: readonly number[], differentials: readonly Matrix[]) => {
        const terms = ranks.map(object);
        return algebraPolynomialFreydBoundedComplex({
            terms, differentials: differentials.map((value, n) => map(terms[n + 1], terms[n], value))
        });
    };
    const A = complex(input.a, input.dA);
    const B = complex(input.b, input.dB);
    const C = complex(input.c, input.dC);
    const chainMap = (source: typeof A, target: typeof A, values: readonly Matrix[]) =>
        algebraPolynomialFreydBoundedChainMap({
            source, target,
            components: values.map((value, n) => map(source.terms[n].object, target.terms[n].object, value))
        });
    return algebraPolynomialFreydBoundedLongExactHomology(algebraPolynomialFreydBoundedShortExactSequence({
        subcomplex: A, middleComplex: B, quotientComplex: C,
        inclusion: chainMap(A, B, input.inclusion), projection: chainMap(B, C, input.projection)
    }));
};
type Native = ReturnType<typeof nativeFixture>;
type NativeMap = Native['arrows'][number];
type NativeObject = NativeMap['source'];

const fieldFixture = (input: ReturnType<typeof inputFixture>) => {
    const object = (rank: number) => algebraFreeModule(RATIONAL_DOMAIN, rank);
    const map = (source: ReturnType<typeof object>, target: ReturnType<typeof object>, value: Matrix) =>
        algebraModuleMorphism(source, target, value, zero(0, 0));
    // Explicit zero extension lets the existing field connecting operation
    // exercise degrees 0 and L+1 with their actual neighboring differentials.
    const complex = (ranks: readonly number[], differentials: readonly Matrix[]) => {
        const terms = [0, ...ranks, 0].map((rank, n) => ({ degree: n - 1, object: object(rank) }));
        const values = [zero(0, ranks[0]), ...differentials, zero(ranks[ranks.length - 1], 0)];
        return algebraModuleChainComplex(RATIONAL_DOMAIN, terms, values.map((value, n) => ({
            degree: n, morphism: map(terms[n + 1].object, terms[n].object, value)
        })));
    };
    const A = complex(input.a, input.dA);
    const B = complex(input.b, input.dB);
    const C = complex(input.c, input.dC);
    const chainMap = (source: typeof A, target: typeof A, values: readonly Matrix[]) =>
        algebraModuleChainMap(source, target, [zero(0, 0), ...values, zero(0, 0)].map((value, n) => ({
            degree: n - 1, morphism: map(source.terms[n].object, target.terms[n].object, value)
        })));
    const inclusion = chainMap(A, B, input.inclusion);
    const projection = chainMap(B, C, input.projection);
    const sequence = algebraModuleShortExactSequence(inclusion, projection);
    const homologies = [A, B, C].map(complex => complex.terms.map(term =>
        algebraModuleChainComplexHomology(complex, term.degree)));
    const homology = (degree: number, role: 'A' | 'B' | 'C') =>
        homologies[role === 'A' ? 0 : role === 'B' ? 1 : 2][degree + 1];
    const windows = Array.from({ length: input.a.length + 1 }, (_, degree) => ({
        degree,
        connecting: algebraModuleConnectingMorphism(sequence, degree),
        inclusionUpper: algebraModuleChainMapHomology(inclusion, degree),
        projectionUpper: algebraModuleChainMapHomology(projection, degree),
        inclusionLower: algebraModuleChainMapHomology(inclusion, degree - 1)
    }));
    return { A, B, C, sequence, windows, homology };
};
type Field = ReturnType<typeof fieldFixture>;

const realize = (object: NativeObject) => algebraModuleRealization(algebraPresentedModule(
    RATIONAL_DOMAIN, object.ambient.rank,
    fromColumns(object.ambient.rank, object.relations.generators.map(relation => relation.components.map(algebraPolynomialText)))));
const rawMatrix = (value: NativeMap) => fromColumns(value.target.ambient.rank,
    value.map.columns.map(column => column.components.map(algebraPolynomialText)));
const inducedMatrix = (value: NativeMap) =>
    multiply(multiply(realize(value.target).projection, rawMatrix(value)), realize(value.source).section);

const isomorphism = (forward: Matrix, label: string) => {
    assert.equal(forward.parent.rows, forward.parent.columns, label + ' equal quotient dimensions');
    const inverse = algebraMatrixLeftInverse(forward);
    const identity = algebraIdentityMatrix(RATIONAL_DOMAIN, forward.parent.rows);
    equal(multiply(forward, inverse), identity, label + ' forward-inverse');
    equal(multiply(inverse, forward), identity, label + ' inverse-forward');
    return { forward, inverse };
};

/** Identify selected cycles via the common original free complex term. */
const homologyCoordinates = (
    native: Native['terms'][number]['view']['homology'],
    field: ReturnType<Field['homology']>
) => {
    const nativeQuotient = realize(native.homologyObject);
    const fieldCycles = algebraModuleInducedMatrix(field.cycles.inclusion);
    const cycleCoordinates = multiply(algebraMatrixLeftInverse(fieldCycles), rawMatrix(native.cycleEmbedding));
    equal(multiply(fieldCycles, cycleCoordinates), rawMatrix(native.cycleEmbedding), 'cycle coordinate reconstruction');
    const quotientCoordinates = multiply(algebraModuleInducedMatrix(field.quotient.projection), cycleCoordinates);
    assert.ok(isZero(multiply(quotientCoordinates, nativeQuotient.module.relations)), 'coordinates kill native boundaries');
    return isomorphism(multiply(quotientCoordinates, nativeQuotient.section), 'homology coordinate comparison');
};

const compareMap = (native: NativeMap, field: Matrix,
    source: ReturnType<typeof isomorphism>, target: ReturnType<typeof isomorphism>, label: string) =>
    equal(multiply(multiply(target.forward, inducedMatrix(native)), source.inverse), field, label);

/** Compare the retained snake arrow with the independent CAP operation order. */
const compareSnake = (native: Native, field: Field, degree: number) => {
    const trace = native.windows[degree].connecting.trace;
    const result = algebraModuleCapSnakeConnecting(
        field.sequence.inclusion.components[degree + 1].morphism,
        field.B.differentials[degree].morphism,
        field.sequence.projection.components[degree].morphism
    );
    const deltaCoordinates = multiply(algebraModuleInducedMatrix(result.deltaCokernel.projection),
        realize(trace.snake.deltaCokernel.object).section);
    const gammaCoordinates = isomorphism(multiply(
        algebraMatrixLeftInverse(algebraModuleInducedMatrix(result.gammaKernel.inclusion)),
        multiply(deltaCoordinates, inducedMatrix(trace.snake.iota))), 'snake source coordinates');
    const lambdaCoordinates = multiply(
        algebraMatrixLeftInverse(algebraModuleInducedMatrix(result.lambdaKernel.inclusion)),
        rawMatrix(trace.snake.mu));
    const alphaCoordinates = isomorphism(multiply(multiply(
        algebraModuleInducedMatrix(result.alphaCokernel.projection), lambdaCoordinates),
        realize(trace.snake.alphaCokernel.object).section), 'snake target coordinates');
    compareMap(trace.snake.connecting, result.connecting, gammaCoordinates, alphaCoordinates, 'CAP snake connecting');
    assert.equal(result.nonAuthoritative, true);
    assert.equal(result.fiberCompatible && result.pushoutCompatible && result.uReconstructs && result.connectingReconstructs, true);
};

const compareSequence = (connecting: string, singleDegree = false) => {
    const input = inputFixture(connecting, singleDegree);
    const native = nativeFixture(input);
    const field = fieldFixture(input);
    const coordinate = (degree: number, role: 'A' | 'B' | 'C') =>
        homologyCoordinates(native.degrees[degree + 1][role].homology, field.homology(degree, role));
    const fieldArrows = [field.windows[input.a.length].connecting.morphism];
    for (let degree = input.a.length - 1; degree >= 0; degree--) {
        fieldArrows.push(field.windows[degree].inclusionUpper.morphism,
            field.windows[degree].projectionUpper.morphism, field.windows[degree].connecting.morphism);
    }
    const coordinates = native.terms.map(term => coordinate(term.degree, term.role));
    assert.equal(native.arrows.length, fieldArrows.length);
    native.arrows.forEach((arrow, position) => compareMap(arrow, algebraModuleInducedMatrix(fieldArrows[position]),
        coordinates[position], coordinates[position + 1], `long-exact arrow ${position}`));
    native.interior.forEach((point, index) => {
        assert.equal(algebraModuleMorphismIsZero(algebraModuleCompose(fieldArrows[index + 1], fieldArrows[index])),
            point.pair.chainAgreement.agrees, `adjacent zero ${index}`);
        const homology = algebraModuleHomology(fieldArrows[index], fieldArrows[index + 1]);
        assert.equal(algebraModuleRealization(homology.object).dimension, 0, `field interior exactness ${index}`);
        assert.equal(point.exactness.exact, true, `native interior exactness ${index}`);
    });
    native.windows.forEach((window, degree) => {
        const expected = field.windows[degree];
        const fieldMaps = [expected.inclusionUpper.morphism, expected.projectionUpper.morphism,
            expected.connecting.morphism, expected.inclusionLower.morphism];
        const views = [[degree, 'A'], [degree, 'B'], [degree, 'C'], [degree - 1, 'A'], [degree - 1, 'B']] as const;
        const changes = views.map(([n, role]) => coordinate(n, role));
        window.arrows.forEach((arrow, index) => compareMap(arrow, algebraModuleInducedMatrix(fieldMaps[index]),
            changes[index], changes[index + 1], `window ${degree} arrow ${index}`));
        window.pairs.forEach((pair, index) => {
            assert.equal(algebraModuleMorphismIsZero(algebraModuleCompose(fieldMaps[index + 1], fieldMaps[index])), pair.chainAgreement.agrees);
            assert.equal(algebraModuleRealization(algebraModuleHomology(fieldMaps[index], fieldMaps[index + 1]).object).dimension, 0);
            assert.equal(window.exactness[index].exact, true);
        });
        compareSnake(native, field, degree);
    });
    assert.equal(native.endpoints.initialZero.agrees && native.endpoints.finalZero.agrees, true);
    assert.equal(coordinates[0].forward.parent.rows, 0);
    assert.equal(coordinates[coordinates.length - 1].forward.parent.rows, 0);
    assert.ok(algebraModuleMorphismIsZero(fieldArrows[0]));
    assert.ok(algebraModuleMorphismIsZero(fieldArrows[fieldArrows.length - 1]));
    return { native, field };
};

describe('v3.2 constant-field/Freyd bounded long-exact differential', () => {
    for (const scalar of ['3/2', '-2/3']) {
        it(`compares every arrow, window, snake and exact pair with nonzero connecting ${scalar}`, () => {
            const { native, field } = compareSequence(scalar);
            const dimensions = native.terms.map(term => realize(term.view.homology.homologyObject).dimension);
            assert.deepEqual(dimensions, [0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0]);
            equal(algebraModuleInducedMatrix(field.windows[1].connecting.morphism), matrix(1, 1, [[scalar]]), 'expected connecting scalar');
            equal(algebraModuleInducedMatrix(field.windows[2].inclusionUpper.morphism), matrix(1, 1, [['2']]), 'expected top inclusion');
            equal(algebraModuleInducedMatrix(field.windows[0].projectionUpper.morphism), matrix(1, 1, [['3']]), 'expected bottom projection');
            const connecting = native.windows[1].connecting;
            assert.ok(connecting.homologyMap.source.ambient.rank > 1, 'raw source is not its one-dimensional homology');
            assert.ok(connecting.homologyMap.target.ambient.rank > 1, 'raw target is not its one-dimensional homology');
            assert.equal(isZero(inducedMatrix(connecting.source.boundaryMorphism)), false);
            assert.equal(isZero(inducedMatrix(connecting.target.boundaryMorphism)), false);
            assert.equal(isZero(inducedMatrix(connecting.homologyMap)), false);
            assert.equal(connecting.reconstruction.agreement.agrees, true);
            assert.equal(connecting.trace.descent.zeroAgreement.agrees, true);
            assert.equal(connecting.trace.targetFactor.testCokernelZeroAgreement.agrees, true);
        });
    }

    it('compares a zero connecting map while the neighboring induced maps remain nonzero', () => {
        const { native, field } = compareSequence('0');
        assert.deepEqual(native.terms.map(term => realize(term.view.homology.homologyObject).dimension),
            [0, 1, 1, 0, 1, 2, 1, 1, 2, 1, 0]);
        assert.equal(algebraModuleMorphismIsZero(field.windows[1].connecting.morphism), true);
        assert.equal(algebraModuleMorphismIsZero(field.windows[1].projectionUpper.morphism), false);
        assert.equal(algebraModuleMorphismIsZero(field.windows[1].inclusionLower.morphism), false);
    });

    it('compares the single-degree sequence and both supported connecting endpoints', () => {
        const { native } = compareSequence('1', true);
        assert.equal(native.windows.length, 2);
        assert.deepEqual(native.terms.map(term => realize(term.view.homology.homologyObject).dimension), [0, 2, 3, 1, 0]);
        assert.equal(native.arrows.length, 4);
        assert.equal(native.interior.length, 3);
        assert.equal(ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE.purpose, 'non-authoritative-constant-field-differential');
        assert.equal(ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE.usesFieldSplittings, true);
        assert.equal(ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE.suitableForGeneralModules, false);
        assert.equal(ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE.performsIo, false);
    });
});
