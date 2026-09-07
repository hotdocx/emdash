/** Native six-term snake consumers, including open endpoints and retained reuse. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydSnakeExactError,
    algebraPolynomialFreydSnakeExactSequence,
    algebraPolynomialFreydSnakeExactSequenceFromConnecting
} from '../src/v3_2/algebra_polynomial_freyd_snake_exact';
import { serializeAlgebraPolynomialFreydSnakeExactSequence } from '../src/v3_2/algebra_polynomial_freyd_snake_exact_serialization';
import { AlgebraPolynomialFreydSnakeError, algebraPolynomialFreydSnakeTriple } from '../src/v3_2/algebra_polynomial_freyd_snake';
import {
    algebraPolynomialPresentationMorphismIdentity as identity,
    algebraPolynomialPresentationMorphismZero as zero
} from '../src/v3_2/algebra_polynomial_freyd_category';
import { algebraPolynomialFreydHomologyConnecting } from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import {
    polynomialFreydHomologyFixture as fixture,
    isPolynomialFreydMorphismZero as isZero
} from './v3_2_algebra_polynomial_freyd_homology_fixtures';

describe('v3.2 native six-term polynomial Freyd snake', () => {
    it('constructs all five maps, four zero composites, and four exactness witnesses', () => {
        const connecting = algebraPolynomialFreydHomologyConnecting(fixture('boundary'), 1).trace.snake;
        const result = algebraPolynomialFreydSnakeExactSequenceFromConnecting(connecting);
        assert.equal(result.objects.length, 6);
        assert.equal(result.arrows.length, 5);
        assert.equal(result.pairs.length, 4);
        assert.equal(result.exactness.length, 4);
        assert.equal(result.connecting, connecting);
        assert.equal(result.arrows[2], connecting.connecting);
        assert.equal(isZero(result.arrows[2]), false);
        assert.equal(result.objects[2], connecting.gammaKernel.object);
        assert.equal(result.objects[3], connecting.alphaCokernel.object);
        result.pairs.forEach((pair, index) => {
            assert.equal(pair.dNext, result.arrows[index]);
            assert.equal(pair.d, result.arrows[index + 1]);
            assert.equal(pair.chainAgreement.agrees, true);
            assert.equal(result.exactness[index].homology.pair, pair);
            assert.equal(result.exactness[index].exact, true);
            assert.ok(result.exactness[index].epimorphism);
        });
        assert.equal(result.kernelAlphaBeta.reconstructionAgreement.agrees, true);
        assert.equal(result.kernelBetaGamma.reconstructionAgreement.agrees, true);
        assert.equal(result.cokernelAlphaBeta.reconstructionAgreement.agrees, true);
        assert.equal(result.cokernelBetaGamma.reconstructionAgreement.agrees, true);
        assert.equal(result.assumesSplitEpimorphisms, false);
        assert.ok(Object.isFrozen(result));
        assert.ok(Object.isFrozen(result.objects));
        assert.ok(Object.isFrozen(result.arrows));
    });

    it('agrees with standalone construction and accepts a wrapper over the same retained owners', () => {
        const connecting = algebraPolynomialFreydHomologyConnecting(fixture(), 1).trace.snake;
        const reused = algebraPolynomialFreydSnakeExactSequenceFromConnecting(connecting);
        const standalone = algebraPolynomialFreydSnakeExactSequence(connecting.triple);
        const wrapped = algebraPolynomialFreydSnakeExactSequenceFromConnecting({ ...connecting });
        assert.equal(serializeAlgebraPolynomialFreydSnakeExactSequence(reused),
            serializeAlgebraPolynomialFreydSnakeExactSequence(standalone));
        assert.equal(serializeAlgebraPolynomialFreydSnakeExactSequence(reused),
            serializeAlgebraPolynomialFreydSnakeExactSequence(wrapped));
        assert.equal(wrapped.objects[2], connecting.gammaKernel.object);
        assert.equal(wrapped.arrows[2], connecting.connecting);
    });

    it('does not assume zero objects or monic/epic arrows at the two open ends', () => {
        const object = fixture('one').subcomplex.terms[0].object;
        const z = zero(object, object);
        const result = algebraPolynomialFreydSnakeExactSequence(algebraPolynomialFreydSnakeTriple(z, z, z));
        assert.equal(result.assumesEndpointZeros, false);
        assert.equal(isZero(identity(result.objects[0])), false);
        assert.equal(isZero(identity(result.objects[5])), false);
        assert.equal(isZero(result.arrows[0]), true);
        assert.equal(isZero(result.arrows[1]), false);
        assert.equal(isZero(result.arrows[2]), true);
        assert.equal(isZero(result.arrows[3]), false);
        assert.equal(isZero(result.arrows[4]), true);
        assert.ok(result.exactness.every(value => value.exact));
    });

    it('reuses each existing connecting construction from a bounded homology result', () => {
        const whole = algebraPolynomialFreydBoundedLongExactHomology(fixture());
        const sequences = whole.windows.map(window =>
            algebraPolynomialFreydSnakeExactSequenceFromConnecting(window.connecting.trace.snake));
        sequences.forEach((sequence, degree) => {
            assert.equal(sequence.connecting, whole.windows[degree].connecting.trace.snake);
            assert.equal(sequence.arrows[2], whole.windows[degree].connecting.trace.snake.connecting);
            assert.ok(sequence.exactness.every(value => value.exact));
        });
    });

    it('rejects a failed triple or an inconsistent retained connecting result', () => {
        const sequence = fixture('one');
        const object = sequence.subcomplex.terms[0].object;
        const id = identity(object);
        const invalid = algebraPolynomialFreydSnakeTriple(id, id, id);
        assert.throws(() => algebraPolynomialFreydSnakeExactSequence(invalid),
            (error: unknown) => error instanceof AlgebraPolynomialFreydSnakeError && error.code === 'TRIPLE_ZERO_FAILED');
        const connecting = algebraPolynomialFreydHomologyConnecting(fixture(), 1).trace.snake;
        assert.throws(() => algebraPolynomialFreydSnakeExactSequenceFromConnecting({
            ...connecting, triple: { ...connecting.triple, isSnakeTriple: false }
        }), (error: unknown) => error instanceof AlgebraPolynomialFreydSnakeExactError && error.code === 'INVALID_CONNECTING');
        assert.throws(() => algebraPolynomialFreydSnakeExactSequenceFromConnecting({
            ...connecting, connecting: zero(connecting.source, connecting.target)
        }), (error: unknown) => error instanceof AlgebraPolynomialFreydSnakeExactError && error.code === 'INVALID_CONNECTING');
    });

    it('serializes complete factors and remains sensitive to a changed retained zero witness', () => {
        const connecting = algebraPolynomialFreydHomologyConnecting(fixture(), 1).trace.snake;
        const result = algebraPolynomialFreydSnakeExactSequenceFromConnecting(connecting);
        const serialized = serializeAlgebraPolynomialFreydSnakeExactSequence(result);
        const data = JSON.parse(serialized);
        assert.equal(data.objectOwners.length, 6);
        assert.equal(data.arrows.length, 5);
        assert.equal(data.pairs.length, 4);
        assert.equal(data.exactness.length, 4);
        assert.equal(data.ringIdentity, connecting.triple.delta.source.ambient.ring.identity.id);
        assert.ok(data.kernelAlphaBeta.length > 0 && data.cokernelBetaGamma.length > 0);
        const altered = {
            ...result, kernelAlphaBeta: {
                ...result.kernelAlphaBeta, zeroAgreement: {
                    ...result.kernelAlphaBeta.zeroAgreement,
                    reductionSteps: result.kernelAlphaBeta.zeroAgreement.reductionSteps + 1
                }
            }
        };
        assert.notEqual(serialized, serializeAlgebraPolynomialFreydSnakeExactSequence(altered));
    });

    it('rejects serialized object references that no longer designate their owners', () => {
        const object = fixture('one').subcomplex.terms[0].object;
        const z = zero(object, object);
        const result = algebraPolynomialFreydSnakeExactSequence(algebraPolynomialFreydSnakeTriple(z, z, z));
        const altered = {
            ...result, objects: Object.freeze([
                result.objects[1], result.objects[1], result.objects[2],
                result.objects[3], result.objects[4], result.objects[5]
            ] as const)
        };
        assert.throws(() => serializeAlgebraPolynomialFreydSnakeExactSequence(altered),
            (error: unknown) => error instanceof AlgebraPolynomialFreydSnakeExactError && error.code === 'OWNER_MISMATCH');
    });
});
