/** Whole bounded exactness and sharing at the original homology/window owners. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydHomologyRole,
    AlgebraPolynomialFreydLongExactError,
    algebraPolynomialFreydBoundedLongExactHomology,
    algebraPolynomialFreydLongExactAt,
    algebraPolynomialFreydLongExactPosition,
    algebraPolynomialFreydLongExactTermAt,
    algebraPolynomialFreydLongExactWindowAt
} from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import { serializeAlgebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact_serialization';
import {
    AlgebraPolynomialFreydHomologyWindowError,
    algebraPolynomialFreydHomologyWindow
} from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import { serializeAlgebraPolynomialFreydHomologyWindow } from '../src/v3_2/algebra_polynomial_freyd_homology_window_serialization';
import {
    polynomialFreydHomologyFixture as fixture,
    isPolynomialFreydMorphismZero as isZero
} from './v3_2_algebra_polynomial_freyd_homology_fixtures';

const selectionError = (error: unknown) => error instanceof AlgebraPolynomialFreydHomologyWindowError &&
    error.code === 'INVALID_SELECTION';
const indexError = (error: unknown) => error instanceof AlgebraPolynomialFreydLongExactError &&
    ['DEGREE_OUT_OF_RANGE', 'POSITION_OUT_OF_RANGE', 'INVALID_ROLE'].includes(error.code);

describe('v3.2 bounded long exact polynomial Freyd homology', () => {
    it('constructs every displayed term, arrow, zero pair, and exactness witness', () => {
        const sequence = fixture('boundary');
        const result = algebraPolynomialFreydBoundedLongExactHomology(sequence);
        assert.equal(result.sequence, sequence);
        assert.equal(result.topDegree, 2);
        assert.equal(result.terms.length, 11);
        assert.equal(result.arrows.length, 10);
        assert.equal(result.interior.length, 9);
        assert.equal(result.windows.length, 4);
        assert.equal(result.degrees.length, 5);
        assert.deepEqual(result.terms.map(term => [term.degree, term.role]), [
            [3, 'C'], [2, 'A'], [2, 'B'], [2, 'C'],
            [1, 'A'], [1, 'B'], [1, 'C'],
            [0, 'A'], [0, 'B'], [0, 'C'], [-1, 'A']
        ]);
        for (const point of result.interior) {
            assert.equal(point.pair.dNext, result.arrows[point.term.position - 1]);
            assert.equal(point.pair.d, result.arrows[point.term.position]);
            assert.equal(point.exactness.homology.pair, point.pair);
            assert.equal(point.pair.chainAgreement.agrees, true);
            assert.equal(point.exactness.exact, true);
            assert.ok(point.exactness.epimorphism);
            assert.equal(point.window, result.windows[point.windowDegree]);
            assert.equal(point.exactness, point.window.exactness[point.slot]);
        }
        assert.equal(result.assumesSplitEpimorphisms, false);
        assert.equal(result.isExact, true);
        assert.ok(Object.isFrozen(result));
        assert.ok(Object.isFrozen(result.terms));
        assert.ok(Object.isFrozen(result.interior));
    });

    it('shares actual homology and induced-map results between adjacent windows', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture());
        result.windows.forEach((window, degree) => {
            const upper = result.degrees[degree + 1];
            const lower = result.degrees[degree];
            assert.equal(window.upperA, upper.A);
            assert.equal(window.upperB, upper.B);
            assert.equal(window.upperC, upper.C);
            assert.equal(window.lowerA, lower.A);
            assert.equal(window.lowerB, lower.B);
            assert.equal(window.inclusionUpper, upper.inclusion);
            assert.equal(window.projectionUpper, upper.projection);
            assert.equal(window.inclusionLower, lower.inclusion);
            assert.equal(window.connecting.source, upper.C.homology);
            assert.equal(window.connecting.target, lower.A.homology);
            if (degree > 0) assert.equal(window.inclusionLower, result.windows[degree - 1].inclusionUpper);
        });
        for (const term of result.terms) assert.equal(term.view, result.degrees[term.degree + 1][term.role]);
    });

    it('retains the nonzero boundary descent and nonsplit connecting operation in its window', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture('boundary'));
        const connecting = result.windows[1].connecting;
        assert.equal(isZero(connecting.source.boundaryMorphism), false);
        assert.equal(isZero(connecting.homologyMap), false);
        assert.equal(connecting.trace.descent.zeroAgreement.agrees, true);
        assert.equal(connecting.trace.targetFactor.testCokernelZeroAgreement.agrees, true);
        const position = algebraPolynomialFreydLongExactPosition(result, 1, 'C');
        assert.equal(result.arrows[position], connecting.homologyMap);
    });

    it('uses the true neighboring differentials at both selected zero endpoints', () => {
        const sequence = fixture();
        const result = algebraPolynomialFreydBoundedLongExactHomology(sequence);
        const initial = result.terms[0];
        const final = result.terms[result.terms.length - 1];
        assert.equal(initial.location, 'endpoint-zero');
        assert.equal(final.location, 'endpoint-zero');
        assert.equal(initial.view.homology.pair.d.target, sequence.quotientComplex.terms[sequence.length].object);
        assert.equal(final.view.homology.pair.dNext.source, sequence.subcomplex.terms[0].object);
        assert.equal(result.endpoints.initialZero, initial.view.zeroIdentity);
        assert.equal(result.endpoints.finalZero, final.view.zeroIdentity);
        assert.equal(result.endpoints.initialZero.agrees && result.endpoints.finalZero.agrees, true);
        assert.equal(isZero(result.arrows[0]), true);
        assert.equal(isZero(result.arrows[result.arrows.length - 1]), true);
    });

    it('projects retained windows, terms, and exactness with reversible degree/role indexing', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture());
        for (const term of result.terms) {
            const position = algebraPolynomialFreydLongExactPosition(result, term.degree, term.role);
            assert.equal(position, term.position);
            assert.equal(algebraPolynomialFreydLongExactTermAt(result, position), term);
            if (position > 0 && position < result.terms.length - 1) {
                assert.equal(algebraPolynomialFreydLongExactAt(result, position), result.interior[position - 1]);
            }
        }
        result.windows.forEach((window, degree) => assert.equal(algebraPolynomialFreydLongExactWindowAt(result, degree), window));
    });

    it('handles a single supported degree as a five-term exact sequence', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture('one'));
        assert.equal(result.topDegree, 0);
        assert.equal(result.terms.length, 5);
        assert.equal(result.arrows.length, 4);
        assert.equal(result.interior.length, 3);
        assert.deepEqual(result.interior.map(point => point.term.role), ['A', 'B', 'C']);
        assert.ok(result.interior.every(point => point.exactness.exact));
    });

    it('rejects invalid sequence flags and malformed degree metadata', () => {
        const sequence = fixture();
        for (const bad of [
            { ...sequence, inclusion: { ...sequence.inclusion, isChainMap: false } },
            { ...sequence, length: NaN },
            { ...sequence, length: 4 }
        ]) {
            assert.throws(() => algebraPolynomialFreydBoundedLongExactHomology(bad),
                (error: unknown) => error instanceof AlgebraPolynomialFreydLongExactError && error.code === 'INVALID_SEQUENCE');
        }
    });

    it('rejects indices outside the displayed sequence or retained windows', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture('one'));
        for (const position of [-1, result.terms.length, 0.5, NaN, Infinity]) {
            assert.throws(() => algebraPolynomialFreydLongExactTermAt(result, position), indexError);
        }
        for (const position of [0, result.terms.length - 1, 0.5, NaN]) {
            assert.throws(() => algebraPolynomialFreydLongExactAt(result, position), indexError);
        }
        for (const degree of [-1, result.windows.length, 0.5, NaN]) {
            assert.throws(() => algebraPolynomialFreydLongExactWindowAt(result, degree), indexError);
        }
        assert.throws(() => algebraPolynomialFreydLongExactPosition(result, 1, 'A'), indexError);
        assert.throws(() => algebraPolynomialFreydLongExactPosition(result, -1, 'C'), indexError);
        assert.throws(() => algebraPolynomialFreydLongExactPosition(result, 0, 'X' as AlgebraPolynomialFreydHomologyRole), indexError);
    });

    it('reuses retained selections but rejects wrong degree views or induced-map owners', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture());
        const window = result.windows[1];
        const repeated = algebraPolynomialFreydHomologyWindow(result.sequence, 1, { ...window, upperA: { ...window.upperA } });
        assert.equal(repeated.upperA.homology, window.upperA.homology);
        assert.equal(repeated.inclusionUpper, window.inclusionUpper);
        assert.equal(serializeAlgebraPolynomialFreydHomologyWindow(repeated), serializeAlgebraPolynomialFreydHomologyWindow(window));
        assert.throws(() => algebraPolynomialFreydHomologyWindow(result.sequence, 1, {
            ...window, upperA: { ...window.upperA, degree: 0 }
        }), selectionError);
        assert.throws(() => algebraPolynomialFreydHomologyWindow(result.sequence, 1, {
            ...window, upperA: window.upperB
        }), selectionError);
        assert.throws(() => algebraPolynomialFreydHomologyWindow(result.sequence, 1, {
            ...window, inclusionUpper: result.windows[0].inclusionUpper
        }), selectionError);
    });

    it('serializes the full selected result deterministically, retaining late-window witnesses', () => {
        const sequence = fixture();
        const result = algebraPolynomialFreydBoundedLongExactHomology(sequence);
        const serialized = serializeAlgebraPolynomialFreydBoundedLongExactHomology(result);
        assert.equal(serialized, serializeAlgebraPolynomialFreydBoundedLongExactHomology(
            algebraPolynomialFreydBoundedLongExactHomology(sequence)));
        const data = JSON.parse(serialized);
        assert.equal(data.terms.length, result.terms.length);
        assert.equal(data.interior.length, result.interior.length);
        assert.equal(data.windows.length, result.windows.length);
        assert.ok(data.interior.every((point: { exactness: string }) => point.exactness.length > 0));
        const old = result.windows[1];
        const changed = {
            ...old, connecting: {
                ...old.connecting, trace: {
                    ...old.connecting.trace, descent: {
                        ...old.connecting.trace.descent, zeroAgreement: {
                            ...old.connecting.trace.descent.zeroAgreement,
                            reductionSteps: old.connecting.trace.descent.zeroAgreement.reductionSteps + 1
                        }
                    }
                }
            }
        };
        const altered = {
            ...result,
            windows: result.windows.map((window, degree) => degree === 1 ? changed : window),
            interior: result.interior.map(point => point.windowDegree === 1 ? { ...point, window: changed } : point)
        };
        assert.notEqual(serialized, serializeAlgebraPolynomialFreydBoundedLongExactHomology(altered));
    });

    it('refuses to serialize broken selected-owner references', () => {
        const result = algebraPolynomialFreydBoundedLongExactHomology(fixture('one'));
        const altered = { ...result, terms: result.terms.map((term, index) => index === 1 ? { ...term, view: result.terms[2].view } : term) };
        assert.throws(() => serializeAlgebraPolynomialFreydBoundedLongExactHomology(altered),
            (error: unknown) => error instanceof AlgebraPolynomialFreydLongExactError && error.code === 'OWNER_MISMATCH');
    });
});
