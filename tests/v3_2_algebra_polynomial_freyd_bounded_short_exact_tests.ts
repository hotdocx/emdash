/** Bounded degreewise exactness, retained chain maps, and explicit zero extension. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydBoundedChainMap,
    algebraPolynomialFreydBoundedChainMapIdentity,
    algebraPolynomialFreydBoundedComplex,
    algebraPolynomialFreydBoundedComplexFromFree,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydZeroPresentation,
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydSnakeTriple,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule
} from '../src/v3_2';
import {
    AlgebraPolynomialFreydBoundedShortExactError,
    algebraPolynomialFreydBoundedShortExactAt,
    algebraPolynomialFreydBoundedShortExactExtendedAt,
    algebraPolynomialFreydBoundedShortExactSequence
} from '../src/v3_2/algebra_polynomial_freyd_bounded_short_exact';
import {
    serializeAlgebraPolynomialFreydBoundedChainMap,
    serializeAlgebraPolynomialFreydBoundedComplex,
    serializeAlgebraPolynomialFreydBoundedShortExactSequence
} from '../src/v3_2/algebra_polynomial_freyd_bounded_short_exact_serialization';

const sequenceError = (code: AlgebraPolynomialFreydBoundedShortExactError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydBoundedShortExactError);
        assert.equal(error.code, code);
        return true;
    };

// R/(x) is x-torsion whereas R is torsion-free: these degree rows do not split.
const fixture = (variable = 'x') => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const ambient = algebraPolynomialFreeModule(ring, 1);
    const free = algebraPresentedPolynomialModule(algebraPolynomialSubmodule(ambient, []));
    const multiplication = algebraPolynomialPresentationMorphism({
        source: free,
        target: free,
        map: algebraPolynomialModuleMap(ambient, ambient, [
            algebraPolynomialModuleVector(ambient, [x])
        ])
    });
    const quotient = algebraPolynomialFreydCokernel(multiplication);
    const subcomplex = algebraPolynomialFreydBoundedComplex({
        terms: [free, free], differentials: [multiplication]
    });
    const middleComplex = algebraPolynomialFreydBoundedComplex({
        terms: [free, free], differentials: [multiplication]
    });
    const quotientComplex = algebraPolynomialFreydBoundedComplex({
        terms: [quotient.object, quotient.object],
        differentials: [algebraPolynomialPresentationMorphismZero(quotient.object, quotient.object)]
    });
    const inclusion = algebraPolynomialFreydBoundedChainMap({
        source: subcomplex, target: middleComplex,
        components: [multiplication, multiplication]
    });
    const projection = algebraPolynomialFreydBoundedChainMap({
        source: middleComplex, target: quotientComplex,
        components: [quotient.projection, quotient.projection]
    });
    return { ring, free, multiplication, quotient, subcomplex, middleComplex,
        quotientComplex, inclusion, projection };
};

describe('v3.2 bounded short-exact polynomial Freyd sequences', () => {
    it('computes both nonsplit rows and retains the existing square owners', () => {
        const input = fixture();
        const result = algebraPolynomialFreydBoundedShortExactSequence(input);
        assert.equal(result.length, 1);
        assert.equal(result.inclusion, input.inclusion);
        assert.equal(result.projection, input.projection);
        assert.equal(result.inclusion.squares, input.inclusion.squares);
        assert.equal(result.projection.squares[0].agreement, input.projection.squares[0].agreement);
        result.rows.forEach((row, degree) => {
            assert.equal(row.degree, degree);
            assert.equal(row.location, 'support');
            assert.equal(row.triple.incoming, input.inclusion.components[degree].morphism);
            assert.equal(row.triple.outgoing, input.projection.components[degree].morphism);
            assert.equal(row.triple.exactness.exact, true);
            assert.equal(row.triple.incomingMonomorphism.monic, true);
            assert.equal(row.triple.outgoingEpimorphism.epic, true);
            assert.equal(algebraPolynomialFreydBoundedShortExactAt(result, degree), row);
        });
        assert.ok(Object.isFrozen(result));
        assert.ok(Object.isFrozen(result.rows));
        assert.ok(Object.isFrozen(result.rows[0]));
    });

    it('provides a nonzero snake connecting consumer at the adjacent degree', () => {
        const result = algebraPolynomialFreydBoundedShortExactSequence(fixture());
        const snake = algebraPolynomialFreydSnakeConnecting(algebraPolynomialFreydSnakeTriple(
            result.inclusion.components[1].morphism,
            result.middleComplex.differentials[0].morphism,
            result.projection.components[0].morphism
        ));
        assert.equal(snake.assumesSplitEpimorphisms, false);
        assert.equal(snake.connectingLift.reconstructs, true);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(
            snake.connecting,
            algebraPolynomialPresentationMorphismZero(snake.source, snake.target)
        ).agrees, false);
    });

    it('reuses one zero row for both endpoint extensions and checks degree input', () => {
        const result = algebraPolynomialFreydBoundedShortExactSequence(fixture());
        const lower = algebraPolynomialFreydBoundedShortExactExtendedAt(result, -1);
        const upper = algebraPolynomialFreydBoundedShortExactExtendedAt(result, 2);
        assert.equal(lower.triple, result.zeroRow);
        assert.equal(upper.triple, result.zeroRow);
        assert.equal(result.zeroRow.incoming.source, result.zeroObject);
        assert.equal(result.zeroRow.shortExact, true);
        assert.equal(lower.location, 'zero-extension');
        assert.equal(algebraPolynomialFreydBoundedShortExactExtendedAt(result, 1), result.rows[1]);
        for (const degree of [-1, 2, 0.5, NaN, Infinity]) {
            assert.throws(() => algebraPolynomialFreydBoundedShortExactAt(result, degree),
                sequenceError('DEGREE_OUT_OF_RANGE'));
        }
        for (const degree of [0.5, NaN, Number.MAX_SAFE_INTEGER + 1]) {
            assert.throws(() => algebraPolynomialFreydBoundedShortExactExtendedAt(result, degree),
                sequenceError('DEGREE_OUT_OF_RANGE'));
        }
    });

    it('accepts identical reconstructed complex data without rebuilding input maps', () => {
        const input = fixture();
        const subcomplex = algebraPolynomialFreydBoundedComplex({
            terms: input.subcomplex.terms.map(term => term.object),
            differentials: input.subcomplex.differentials.map(entry => entry.morphism)
        });
        const result = algebraPolynomialFreydBoundedShortExactSequence({ ...input, subcomplex });
        assert.equal(result.subcomplex, subcomplex);
        assert.equal(result.inclusion, input.inclusion);
    });

    it('rejects a chain map whose equal term objects hide different differentials', () => {
        const input = fixture();
        const differentMiddle = algebraPolynomialFreydBoundedComplex({
            terms: [input.free, input.free],
            differentials: [algebraPolynomialPresentationMorphismZero(input.free, input.free)]
        });
        const projection = algebraPolynomialFreydBoundedChainMap({
            source: differentMiddle, target: input.quotientComplex,
            components: [input.quotient.projection, input.quotient.projection]
        });
        assert.equal(projection.isChainMap, true);
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({ ...input, projection }),
            sequenceError('CHAIN_MAP_ENDPOINT_MISMATCH'));
    });

    it('rejects a retained failed square before computing row exactness', () => {
        const input = fixture();
        const inclusion = algebraPolynomialFreydBoundedChainMap({
            source: input.subcomplex, target: input.middleComplex,
            components: [
                algebraPolynomialPresentationMorphismZero(input.free, input.free),
                input.multiplication
            ]
        });
        assert.equal(inclusion.isChainMap, false);
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({ ...input, inclusion }),
            sequenceError('INVALID_CHAIN_MAP'));
    });

    it('requires the same raw differential even when quotient maps agree', () => {
        const input = fixture();
        const object = input.quotient.object;
        const zero = algebraPolynomialFreydZeroPresentation(input.ring);
        const difference = algebraPolynomialPresentationMorphism({
            source: object,
            target: object,
            map: input.multiplication.map
        });
        const plain = algebraPolynomialPresentationMorphismZero(object, object);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(difference, plain).agrees, true);
        const subcomplex = algebraPolynomialFreydBoundedComplex({
            terms: [object, object], differentials: [plain]
        });
        const middleComplex = subcomplex;
        const otherMiddle = algebraPolynomialFreydBoundedComplex({
            terms: [object, object], differentials: [difference]
        });
        const quotientComplex = algebraPolynomialFreydBoundedComplex({
            terms: [zero, zero],
            differentials: [algebraPolynomialPresentationMorphismZero(zero, zero)]
        });
        const inclusion = algebraPolynomialFreydBoundedChainMapIdentity(subcomplex);
        const projection = algebraPolynomialFreydBoundedChainMap({
            source: otherMiddle, target: quotientComplex,
            components: [algebraPolynomialPresentationMorphismZero(object, zero),
                algebraPolynomialPresentationMorphismZero(object, zero)]
        });
        assert.equal(projection.isChainMap, true);
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({
            subcomplex, middleComplex, quotientComplex, inclusion, projection
        }), sequenceError('CHAIN_MAP_ENDPOINT_MISMATCH'));
    });

    it('reports the exact failing degree and retains the short-exact cause', () => {
        const input = fixture();
        const inclusion = algebraPolynomialFreydBoundedChainMap({
            source: input.subcomplex, target: input.middleComplex,
            components: [algebraPolynomialPresentationMorphismIdentity(input.free),
                algebraPolynomialPresentationMorphismIdentity(input.free)]
        });
        assert.equal(inclusion.isChainMap, true);
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({ ...input, inclusion }),
            (error: unknown) => {
                assert.ok(error instanceof AlgebraPolynomialFreydBoundedShortExactError);
                assert.equal(error.code, 'ROW_NOT_SHORT_EXACT');
                assert.equal(error.path, 'shortExactSequence.rows[0]');
                assert.equal((error.underlying as { code?: string }).code, 'ZERO_COMPOSITE_FAILED');
                return true;
            });
    });

    it('rejects invalid complexes, unequal ranges, and foreign polynomial rings', () => {
        const input = fixture();
        const invalid = algebraPolynomialFreydBoundedComplex({
            terms: [input.free, input.free, input.free],
            differentials: [input.multiplication, input.multiplication]
        });
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({ ...input, subcomplex: invalid }),
            sequenceError('INVALID_COMPLEX'));
        const shorter = algebraPolynomialFreydBoundedComplex({ terms: [input.free], differentials: [] });
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({ ...input, subcomplex: shorter }),
            sequenceError('RANGE_MISMATCH'));
        const foreign = fixture('y');
        assert.throws(() => algebraPolynomialFreydBoundedShortExactSequence({
            ...input, quotientComplex: foreign.quotientComplex
        }), sequenceError('FOREIGN_SEQUENCE_RING'));
    });

    it('supports a one-degree sequence', () => {
        const input = fixture();
        const subcomplex = algebraPolynomialFreydBoundedComplex({ terms: [input.free], differentials: [] });
        const middleComplex = algebraPolynomialFreydBoundedComplex({ terms: [input.free], differentials: [] });
        const quotientComplex = algebraPolynomialFreydBoundedComplex({ terms: [input.quotient.object], differentials: [] });
        const inclusion = algebraPolynomialFreydBoundedChainMap({
            source: subcomplex, target: middleComplex, components: [input.multiplication]
        });
        const projection = algebraPolynomialFreydBoundedChainMap({
            source: middleComplex, target: quotientComplex, components: [input.quotient.projection]
        });
        const result = algebraPolynomialFreydBoundedShortExactSequence({
            subcomplex, middleComplex, quotientComplex, inclusion, projection
        });
        assert.equal(result.rows.length, 1);
        assert.equal(result.length, 0);
        assert.equal(algebraPolynomialFreydBoundedShortExactExtendedAt(result, 1).triple, result.zeroRow);
    });

    it('serializes retained rows, chain squares, and zero extension deterministically', () => {
        const input = fixture();
        const first = algebraPolynomialFreydBoundedShortExactSequence(input);
        const second = algebraPolynomialFreydBoundedShortExactSequence(input);
        const serialized = serializeAlgebraPolynomialFreydBoundedShortExactSequence(first);
        assert.equal(serialized, serializeAlgebraPolynomialFreydBoundedShortExactSequence(second));
        const data = JSON.parse(serialized);
        assert.equal(data.rows.length, 2);
        assert.equal(data.inclusion.squares.length, 1);
        assert.equal(JSON.parse(data.rows[0].triple).shortExact, true);
        assert.equal(JSON.parse(data.zeroRow).shortExact, true);
        assert.equal(data.zeroObject.rank, 0);
        assert.equal(data.inclusion.source.kind, input.subcomplex.kind);
        assert.equal(data.projection.target.kind, input.quotientComplex.kind);
        assert.equal(serializeAlgebraPolynomialFreydBoundedComplex(input.subcomplex),
            serializeAlgebraPolynomialFreydBoundedComplex(input.middleComplex));
        assert.notEqual(serializeAlgebraPolynomialFreydBoundedChainMap(input.inclusion),
            serializeAlgebraPolynomialFreydBoundedChainMap(algebraPolynomialFreydBoundedChainMapIdentity(input.subcomplex)));
        const altered = {
            ...first,
            inclusion: {
                ...first.inclusion,
                squares: first.inclusion.squares.map(square => ({
                    ...square,
                    agreement: { ...square.agreement, reductionSteps: square.agreement.reductionSteps + 1 }
                }))
            }
        };
        assert.notEqual(serialized, serializeAlgebraPolynomialFreydBoundedShortExactSequence(altered));
    });

    it('retains the existing bounded-free provenance in canonical complex data', () => {
        const input = fixture();
        const free = algebraPolynomialBoundedFreeComplex({
            terms: [input.free.ambient, input.free.ambient],
            differentials: [input.multiplication.map]
        });
        const adapted = algebraPolynomialFreydBoundedComplexFromFree(free);
        const data = JSON.parse(serializeAlgebraPolynomialFreydBoundedComplex(adapted));
        assert.equal(data.freeSource.kind, 'algebra-polynomial-freyd-free-complex-source');
        assert.equal(JSON.parse(data.freeSource.complex).length, 1);
    });
});
