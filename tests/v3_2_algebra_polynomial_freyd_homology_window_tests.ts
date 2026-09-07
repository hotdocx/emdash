/** Nonsplit homology windows, genuine boundary descent, and endpoint zeros. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    polynomialFreydHomologyFixture as fixture,
    isPolynomialFreydMorphismZero as isZero
} from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import {
    AlgebraPolynomialFreydHomologyWindowError,
    algebraPolynomialFreydHomologyWindow
} from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import {
    serializeAlgebraPolynomialFreydHomologyWindow
} from '../src/v3_2/algebra_polynomial_freyd_homology_window_serialization';

describe('v3.2 polynomial Freyd homology windows', () => {
    it('constructs a nonzero connecting map and all three exactness witnesses', () => {
        const sequence = fixture();
        const window = algebraPolynomialFreydHomologyWindow(sequence, 1);
        assert.equal(window.sequence, sequence);
        assert.equal(window.assumesSplitEpimorphisms, false);
        assert.equal(window.connecting.trace.snake.assumesSplitEpimorphisms, false);
        assert.equal(isZero(window.connecting.homologyMap), false);
        assert.equal(window.arrows.length, 4);
        assert.equal(window.pairs.length, 3);
        window.pairs.forEach((pair, index) => {
            assert.equal(pair.dNext, window.arrows[index]);
            assert.equal(pair.d, window.arrows[index + 1]);
            assert.equal(pair.chainAgreement.agrees, true);
            assert.equal(window.exactness[index].homology.pair, pair);
            assert.equal(window.exactness[index].exact, true);
            assert.ok(window.exactness[index].epimorphism);
        });
        assert.ok(Object.isFrozen(window));
    });

    it('retains the actual five selected homologies in every arrow consumer', () => {
        const window = algebraPolynomialFreydHomologyWindow(fixture(), 1);
        for (const value of [window.upperA, window.upperB, window.upperC, window.lowerA, window.lowerB]) {
            assert.equal(value.homology, value.bounded?.homology);
        }
        assert.equal(window.inclusionUpper.chainMap.source, window.upperA.homology);
        assert.equal(window.inclusionUpper.chainMap.target, window.upperB.homology);
        assert.equal(window.projectionUpper.chainMap.source, window.upperB.homology);
        assert.equal(window.projectionUpper.chainMap.target, window.upperC.homology);
        assert.equal(window.inclusionLower.chainMap.source, window.lowerA.homology);
        assert.equal(window.inclusionLower.chainMap.target, window.lowerB.homology);
        assert.equal(window.connecting.trace.descent.cokernel, window.upperC.homology.homology);
        assert.equal(window.connecting.trace.homologyEmbedding.cokernel, window.lowerA.homology.homology);
        assert.equal(window.connecting.homologyMap.source, window.upperC.homology.homologyObject);
        assert.equal(window.connecting.homologyMap.target, window.lowerA.homology.homologyObject);
    });

    it('checks both inverse laws for every endpoint comparison', () => {
        const { connecting } = algebraPolynomialFreydHomologyWindow(fixture(), 1);
        for (const iso of [connecting.trace.upperComparison, connecting.trace.lowerComparison,
            connecting.trace.cycleComparison, connecting.trace.targetComparison]) {
            assert.equal(iso.sourceAgreement.agrees, true);
            assert.equal(iso.targetAgreement.agrees, true);
        }
        assert.equal(connecting.trace.upperInverse.colift.target, connecting.trace.snake.deltaCokernel.object);
        assert.equal(connecting.trace.gammaAgreement.agrees, true);
        assert.equal(connecting.trace.alphaAgreement.agrees, true);
        assert.equal(connecting.trace.homologyMonomorphism.monic, true);
        assert.equal(connecting.trace.targetFactor.reconstructionAgreement.agrees, true);
        assert.equal(connecting.trace.descent.reconstructionAgreement.agrees, true);
    });

    it('descends a genuinely nonzero source boundary in a three-degree complex', () => {
        const sequence = fixture('boundary');
        const window = algebraPolynomialFreydHomologyWindow(sequence, 1);
        assert.equal(isZero(window.upperC.homology.pair.dNext), false);
        assert.equal(isZero(window.upperC.homology.boundaryMorphism), false);
        assert.equal(isZero(window.connecting.homologyMap), false);
        assert.equal(window.connecting.trace.targetFactor.testCokernelZeroAgreement.agrees, true);
        assert.equal(window.connecting.trace.descent.zeroAgreement.agrees, true);
        assert.equal(window.isExact, true);
    });

    it('keeps the true neighboring differentials in both endpoint-zero windows', () => {
        const sequence = fixture();
        const lower = algebraPolynomialFreydHomologyWindow(sequence, 0);
        const upper = algebraPolynomialFreydHomologyWindow(sequence, sequence.length + 1);
        assert.equal(lower.lowerA.location, 'zero-extension');
        assert.equal(lower.lowerA.zeroIdentity?.agrees, true);
        assert.equal(lower.lowerA.homology.pair.dNext.source, sequence.subcomplex.terms[0].object);
        assert.equal(upper.upperC.location, 'zero-extension');
        assert.equal(upper.upperC.zeroIdentity?.agrees, true);
        assert.equal(upper.upperC.homology.pair.d.target, sequence.quotientComplex.terms[sequence.length].object);
        assert.equal(upper.connecting.trace.snake.triple.beta.target, sequence.middleComplex.terms[sequence.length].object);
        assert.equal(lower.connecting.trace.lowerRow.triple, sequence.zeroRow);
        assert.equal(upper.connecting.trace.upperRow.triple, sequence.zeroRow);
        assert.equal(isZero(lower.connecting.homologyMap), true);
        assert.equal(isZero(upper.connecting.homologyMap), true);
        assert.equal(lower.isExact && upper.isExact, true);
    });

    it('handles length-zero support and rejects invalid window indices', () => {
        const sequence = fixture('one');
        assert.equal(algebraPolynomialFreydHomologyWindow(sequence, 0).isExact, true);
        assert.equal(algebraPolynomialFreydHomologyWindow(sequence, 1).isExact, true);
        for (const n of [-1, 2, 0.5, NaN, Infinity]) {
            assert.throws(() => algebraPolynomialFreydHomologyWindow(sequence, n),
                (error: unknown) => error instanceof AlgebraPolynomialFreydHomologyWindowError && error.code === 'DEGREE_OUT_OF_RANGE');
        }
    });

    it('rejects a retained failed input chain map', () => {
        const sequence = fixture();
        assert.throws(() => algebraPolynomialFreydHomologyWindow({
            ...sequence, inclusion: { ...sequence.inclusion, isChainMap: false }
        }, 1), (error: unknown) => error instanceof AlgebraPolynomialFreydHomologyWindowError && error.code === 'INVALID_SEQUENCE');
    });

    it('serializes the whole selected result deterministically and retains exact witnesses', () => {
        const sequence = fixture();
        const first = algebraPolynomialFreydHomologyWindow(sequence, 1);
        const second = algebraPolynomialFreydHomologyWindow(sequence, 1);
        const serialized = serializeAlgebraPolynomialFreydHomologyWindow(first);
        assert.equal(serialized, serializeAlgebraPolynomialFreydHomologyWindow(second));
        const data = JSON.parse(serialized);
        assert.equal(data.arrows.length, 4);
        assert.equal(data.pairs.length, 3);
        assert.equal(data.exactness.length, 3);
        assert.equal(JSON.parse(data.connecting.trace.descent).zeroAgreement.length > 0, true);
        assert.equal(data.connecting.trace.cycleComparison.isomorphism, true);
        const altered = {
            ...first,
            connecting: {
                ...first.connecting,
                trace: {
                    ...first.connecting.trace,
                    descent: {
                        ...first.connecting.trace.descent,
                        zeroAgreement: {
                            ...first.connecting.trace.descent.zeroAgreement,
                            reductionSteps: first.connecting.trace.descent.zeroAgreement.reductionSteps + 1
                        }
                    }
                }
            }
        };
        assert.notEqual(serialized, serializeAlgebraPolynomialFreydHomologyWindow(altered));
    });
});
