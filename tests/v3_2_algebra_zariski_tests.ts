/** Focused CAS-ZARISKI-3B computational cover tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraEngineError,
    computeAlgebraOperation
} from '../src/v3_2/algebra_engine';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraIdealCombination,
    algebraPolynomialIdeal
} from '../src/v3_2/algebra_ideal';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import {
    algebraPolynomialEquals,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialText,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    createAlgebraTypeScriptReferenceEngine
} from '../src/v3_2/algebra_reference_engine';
import {
    ALGEBRA_ZARISKI_PROFILE,
    AlgebraZariskiError,
    algebraUnimodularCombination,
    algebraUnimodularCombinationSchema,
    algebraUnimodularFamily,
    algebraZariskiCoverPresentation,
    algebraZariskiCoverPresentationSchema,
    serializeAlgebraUnimodularCombination,
    serializeAlgebraZariskiCoverPresentation,
    validateAlgebraUnimodularCombination,
    validateAlgebraZariskiCoverPresentation
} from '../src/v3_2/algebra_zariski';
import {
    algebraZariskiReferenceOperations
} from '../src/v3_2/algebra_zariski_reference_operations';

const zariskiError = (
    expected: AlgebraZariskiError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraZariskiError);
    assert.equal(error.code, expected);
    return true;
};

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const one = algebraPolynomialOne(ring);
    const oneMinusX = algebraPolynomialSubtract(one, x);
    return { ring, x, one, oneMinusX };
};

describe('v3.2 computational unimodular and Zariski-cover data', () => {
    it('computes coefficients witnessing that x and 1-x generate one', () => {
        const { ring, x, one, oneMinusX } = fixture();
        const result = algebraUnimodularFamily(ring, [x, oneMinusX]);
        assert.equal(result.unimodular, true);
        assert.equal(result.membership.member, true);
        assert.equal(result.coefficients.length, 2);
        assert.equal(algebraPolynomialText(result.remainder), '0');
        assert.ok(algebraPolynomialEquals(result.combination, one));
        assert.ok(algebraPolynomialEquals(
            algebraIdealCombination(result.ideal, result.coefficients),
            one
        ));
        assert.ok(Object.isFrozen(result));
        assert.ok(Object.isFrozen(result.coefficients));
    });

    it('constructs a finite basic-open cover only from unimodular data', () => {
        const { ring, x, one, oneMinusX } = fixture();
        const result = algebraUnimodularFamily(ring, [x, oneMinusX]);
        const cover = algebraZariskiCoverPresentation(result);
        assert.equal(cover.kind, 'algebra-zariski-cover-presentation');
        assert.deepEqual(cover.generators, [x, oneMinusX]);
        assert.equal(cover.coefficients.length, 2);
        assert.ok(algebraPolynomialEquals(cover.combination, one));
        assert.equal(cover.source, result);
        assert.ok(Object.isFrozen(cover));
    });

    it('retains a nonzero remainder for a non-unimodular family', () => {
        const { ring, x } = fixture();
        const result = algebraUnimodularFamily(ring, [x]);
        assert.equal(result.unimodular, false);
        assert.notEqual(algebraPolynomialText(result.remainder), '0');
        assert.throws(
            () => algebraZariskiCoverPresentation(result),
            zariskiError('NOT_UNIMODULAR')
        );
    });

    it('classifies the empty family as non-unimodular', () => {
        const { ring } = fixture();
        const result = algebraUnimodularFamily(ring, []);
        assert.equal(result.unimodular, false);
        assert.equal(algebraPolynomialText(result.combination), '0');
        assert.equal(algebraPolynomialText(result.remainder), '1');
        assert.equal(result.coefficients.length, 0);
    });

    it('normalizes whole-result schemas and rejects projection drift', () => {
        const { ring, x, oneMinusX } = fixture();
        const result = algebraUnimodularCombination(
            algebraPolynomialIdeal(ring, [x, oneMinusX])
        );
        const schema = algebraUnimodularCombinationSchema(ring);
        const normalized = schema.normalize(result, 'unimodular');
        assert.ok(validateAlgebraUnimodularCombination(ring, normalized));
        const cover = algebraZariskiCoverPresentation(normalized);
        const coverSchema = algebraZariskiCoverPresentationSchema(ring);
        assert.ok(coverSchema.normalize(cover, 'cover'));
        assert.ok(validateAlgebraZariskiCoverPresentation(ring, cover));
        assert.throws(
            () => coverSchema.normalize({
                ...cover,
                combination: algebraPolynomialZero(ring)
            }, 'cover'),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.ok(error.underlying instanceof AlgebraZariskiError);
                assert.equal(
                    error.underlying.code,
                    'INVALID_COVER_PRESENTATION'
                );
                return true;
            }
        );
    });

    it('serializes computational witness data deterministically', () => {
        const { ring, x, oneMinusX } = fixture();
        const result = algebraUnimodularFamily(ring, [x, oneMinusX]);
        const cover = algebraZariskiCoverPresentation(result);
        const resultJson = JSON.parse(
            serializeAlgebraUnimodularCombination(result)
        );
        const coverText = serializeAlgebraZariskiCoverPresentation(cover);
        const coverJson = JSON.parse(coverText);
        assert.equal(
            resultJson.serializationRevision,
            ALGEBRA_ZARISKI_PROFILE.serializationRevision
        );
        assert.equal(resultJson.unimodular, true);
        assert.equal(resultJson.coefficients.length, 2);
        assert.equal(coverJson.generators.length, 2);
        assert.equal(coverJson.combination, '1');
        assert.ok(coverText.endsWith('\n'));
    });

    it('executes and chains unimodular and cover operations in a graph', async () => {
        const { ring, x, oneMinusX } = fixture();
        const ideal = algebraPolynomialIdeal(ring, [x, oneMinusX]);
        const operations = algebraZariskiReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const direct = await computeAlgebraOperation({
            engine,
            operation: operations.unimodular,
            input: ideal,
            context: {
                limits: {
                    fuel: 100,
                    maximumOutputItems: 20,
                    maximumIntermediateItems: 10_000
                }
            }
        });
        assert.equal(direct.value.unimodular, true);

        const builder = createAlgebraComputationGraphBuilder(
            'fixture.zariski.cover-pipeline',
            'v1'
        );
        const input = builder.input('ideal', operations.idealSchema);
        const unimodular = builder.operation(
            'unimodular',
            operations.unimodular,
            input
        );
        const cover = builder.operation('cover', operations.cover, unimodular);
        const graph = builder.build([{ id: 'result', value: cover }]);
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine,
            inputs: [{ id: 'ideal', value: ideal }]
        });
        const result = execution.outputs[0].value as ReturnType<
            typeof algebraZariskiCoverPresentation
        >;
        assert.equal(result.kind, 'algebra-zariski-cover-presentation');
        assert.equal(algebraPolynomialText(result.combination), '1');
    });

    it('propagates bounded and cancelled Groebner work through the engine', async () => {
        const { ring, x, oneMinusX } = fixture();
        const ideal = algebraPolynomialIdeal(ring, [x, oneMinusX]);
        const operations = algebraZariskiReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation: operations.unimodular,
                input: ideal,
                context: { limits: { fuel: 1 } }
            }),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.equal(error.code, 'ENGINE_FAILURE');
                return true;
            }
        );
        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation: operations.unimodular,
                input: ideal,
                context: {
                    cancellation: {
                        requested: () => true,
                        reason: () => 'cancelled by Zariski test'
                    }
                }
            }),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.equal(error.code, 'ENGINE_FAILURE');
                return true;
            }
        );
    });

    it('keeps formal proof-assistant adoption explicitly outside this profile', () => {
        assert.equal(ALGEBRA_ZARISKI_PROFILE.formalAdapter, false);
    });
});
