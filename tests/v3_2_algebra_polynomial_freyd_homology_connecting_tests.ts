/** Public homology connecting, selected-object reuse, and complete method traces. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydHomologyConnectingError,
    algebraPolynomialFreydHomologyConnecting
} from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import { serializeAlgebraPolynomialFreydHomologyConnecting } from '../src/v3_2/algebra_polynomial_freyd_homology_connecting_serialization';
import { algebraPolynomialFreydHomologyWindow } from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import { algebraPolynomialFreydBoundedComplexHomology } from '../src/v3_2/algebra_polynomial_freyd_bounded_complex';
import {
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydHomologyAt
} from '../src/v3_2/algebra_polynomial_freyd_homology';
import {
    algebraPolynomialPresentationMorphismAdd,
    algebraPolynomialPresentationMorphismCongruence
} from '../src/v3_2/algebra_polynomial_freyd_category';
import {
    polynomialFreydHomologyFixture as fixture,
    isPolynomialFreydMorphismZero as isZero
} from './v3_2_algebra_polynomial_freyd_homology_fixtures';

const selectionError = (error: unknown) =>
    error instanceof AlgebraPolynomialFreydHomologyConnectingError &&
    error.code === 'INVALID_HOMOLOGY_SELECTION';

describe('v3.2 polynomial Freyd homology connecting', () => {
    it('constructs the homology arrow directly from the sequence and degree', () => {
        const sequence = fixture();
        const result = algebraPolynomialFreydHomologyConnecting(sequence, 1);
        assert.equal(result.kind, 'algebra-polynomial-freyd-homology-connecting');
        assert.equal(result.sequence, sequence);
        assert.equal(result.degree, 1);
        assert.equal(result.homologyMap.source, result.source.homologyObject);
        assert.equal(result.homologyMap.target, result.target.homologyObject);
        assert.equal(isZero(result.homologyMap), false);
        assert.equal(result.assumesSplitEpimorphisms, false);
        assert.equal(result.trace.kind, 'snake-homology-connecting-v1');
        assert.ok(Object.isFrozen(result));
        assert.ok(Object.isFrozen(result.trace));
        assert.ok(Object.isFrozen(result.reconstruction));
    });

    it('reconstructs j_A composed with delta_n composed with q_C', () => {
        const result = algebraPolynomialFreydHomologyConnecting(fixture(), 1);
        assert.equal(result.reconstruction.sourceProjection, result.source.homologyProjection);
        assert.equal(result.reconstruction.targetInclusion, result.trace.homologyEmbedding.colift);
        assert.equal(result.reconstruction.comparedMap, result.trace.comparedSnake);
        assert.equal(result.reconstruction.agreement.agrees, true);
        assert.equal(result.homologyMap, result.trace.descent.colift);
    });

    it('the window delegates to the same operation on its actual homology objects', () => {
        const sequence = fixture();
        const window = algebraPolynomialFreydHomologyWindow(sequence, 1);
        const direct = algebraPolynomialFreydHomologyConnecting(sequence, 1);
        assert.equal(window.connecting.source, window.upperC.homology);
        assert.equal(window.connecting.target, window.lowerA.homology);
        assert.equal(window.arrows[2], window.connecting.homologyMap);
        assert.equal(
            serializeAlgebraPolynomialFreydHomologyConnecting(window.connecting),
            serializeAlgebraPolynomialFreydHomologyConnecting(direct)
        );
    });

    it('retains supplied valid whole homologies rather than selecting replacements', () => {
        const sequence = fixture();
        const source = algebraPolynomialFreydBoundedComplexHomology(sequence.quotientComplex, 1).homology;
        const target = algebraPolynomialFreydBoundedComplexHomology(sequence.subcomplex, 0).homology;
        const result = algebraPolynomialFreydHomologyConnecting(sequence, 1, { source, target });
        assert.equal(result.source, source);
        assert.equal(result.target, target);
        assert.equal(result.trace.descent.cokernel, source.homology);
        assert.equal(result.trace.homologyEmbedding.cokernel, target.homology);
        const anotherSource = algebraPolynomialFreydHomologyAt(source.pair);
        const another = algebraPolynomialFreydHomologyConnecting(sequence, 1, { source: anotherSource, target });
        assert.equal(another.source, anotherSource);
        assert.equal(another.target, target);
        assert.equal(serializeAlgebraPolynomialFreydHomologyConnecting(another),
            serializeAlgebraPolynomialFreydHomologyConnecting(result));
    });

    it('descends a nonzero boundary and produces a nonzero connecting map without splitting', () => {
        const result = algebraPolynomialFreydHomologyConnecting(fixture('boundary'), 1);
        assert.equal(isZero(result.source.boundaryMorphism), false);
        assert.equal(isZero(result.homologyMap), false);
        assert.equal(result.trace.descent.zeroAgreement.agrees, true);
        assert.equal(result.trace.targetFactor.testCokernelZeroAgreement.agrees, true);
        assert.equal(result.reconstruction.agreement.agrees, true);
    });

    it('handles both endpoint-zero connecting maps and length-zero support', () => {
        for (const sequence of [fixture(), fixture('one')]) {
            const lower = algebraPolynomialFreydHomologyConnecting(sequence, 0);
            const upper = algebraPolynomialFreydHomologyConnecting(sequence, sequence.length + 1);
            assert.equal(isZero(lower.homologyMap), true);
            assert.equal(isZero(upper.homologyMap), true);
            assert.equal(lower.target.pair.dNext.source, sequence.subcomplex.terms[0].object);
            assert.equal(upper.source.pair.d.target, sequence.quotientComplex.terms[sequence.length].object);
            assert.equal(lower.trace.lowerRow.triple, sequence.zeroRow);
            assert.equal(upper.trace.upperRow.triple, sequence.zeroRow);
        }
    });

    it('rejects invalid degrees and failed input chain maps', () => {
        const sequence = fixture();
        for (const n of [-1, sequence.length + 2, 0.5, NaN, Infinity]) {
            assert.throws(() => algebraPolynomialFreydHomologyConnecting(sequence, n),
                (error: unknown) => error instanceof AlgebraPolynomialFreydHomologyConnectingError &&
                    error.code === 'DEGREE_OUT_OF_RANGE');
        }
        assert.throws(() => algebraPolynomialFreydHomologyConnecting({
            ...sequence, inclusion: { ...sequence.inclusion, isChainMap: false }
        }, 1), (error: unknown) => error instanceof AlgebraPolynomialFreydHomologyConnectingError &&
            error.code === 'INVALID_SEQUENCE');
    });

    it('rejects wrong presentations, degrees, rings, and failed selected chain data', () => {
        const sequence = fixture();
        const middle = algebraPolynomialFreydBoundedComplexHomology(sequence.middleComplex, 1).homology;
        const wrongDegree = algebraPolynomialFreydBoundedComplexHomology(sequence.quotientComplex, 0).homology;
        const foreign = fixture('two', 'y');
        const foreignSource = algebraPolynomialFreydBoundedComplexHomology(foreign.quotientComplex, 1).homology;
        for (const source of [middle, wrongDegree, foreignSource]) {
            assert.throws(() => algebraPolynomialFreydHomologyConnecting(sequence, 1, { source }), selectionError);
        }
        assert.throws(() => algebraPolynomialFreydHomologyConnecting(sequence, 1, { target: wrongDegree }), selectionError);
        const source = algebraPolynomialFreydBoundedComplexHomology(sequence.quotientComplex, 1).homology;
        assert.throws(() => algebraPolynomialFreydHomologyConnecting(sequence, 1, {
            source: { ...source, pair: { ...source.pair, isChainPair: false } }
        }), selectionError);
    });

    it('does not identify different raw differential representatives by quotient congruence', () => {
        const sequence = fixture();
        const source = algebraPolynomialFreydBoundedComplexHomology(sequence.quotientComplex, 1).homology;
        const changed = algebraPolynomialPresentationMorphismAdd(source.pair.d, source.pair.d);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(changed, source.pair.d).agrees, true);
        const changedHomology = algebraPolynomialFreydHomologyAt(algebraPolynomialFreydChainPair(source.pair.dNext, changed));
        assert.throws(() => algebraPolynomialFreydHomologyConnecting(sequence, 1, { source: changedHomology }), selectionError);
    });

    it('serializes both the public reconstruction and every retained method witness', () => {
        const result = algebraPolynomialFreydHomologyConnecting(fixture(), 1);
        const serialized = serializeAlgebraPolynomialFreydHomologyConnecting(result);
        const data = JSON.parse(serialized);
        assert.equal(data.trace.kind, 'snake-homology-connecting-v1');
        assert.equal(data.trace.cycleComparison.isomorphism, true);
        assert.ok(data.reconstruction.agreement.length > 0);
        const alteredReconstruction = {
            ...result, reconstruction: {
                ...result.reconstruction, agreement: {
                    ...result.reconstruction.agreement,
                    reductionSteps: result.reconstruction.agreement.reductionSteps + 1
                }
            }
        };
        assert.notEqual(serialized, serializeAlgebraPolynomialFreydHomologyConnecting(alteredReconstruction));
        const alteredTrace = {
            ...result, trace: {
                ...result.trace, descent: {
                    ...result.trace.descent, zeroAgreement: {
                        ...result.trace.descent.zeroAgreement,
                        reductionSteps: result.trace.descent.zeroAgreement.reductionSteps + 1
                    }
                }
            }
        };
        assert.notEqual(serialized, serializeAlgebraPolynomialFreydHomologyConnecting(alteredTrace));
    });
});
