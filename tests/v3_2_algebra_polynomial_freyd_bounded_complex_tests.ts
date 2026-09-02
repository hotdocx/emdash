/** Focused bounded Freyd complexes, free adapter, and degreewise homology. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydBoundedComplexError,
    RATIONAL_DOMAIN,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydBoundedComplex,
    algebraPolynomialFreydBoundedComplexFromFree,
    algebraPolynomialFreydBoundedComplexHomology,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const boundedError = (
    code: AlgebraPolynomialFreydBoundedComplexError['code']
) => (error: unknown) => {
    assert.ok(error instanceof AlgebraPolynomialFreydBoundedComplexError);
    assert.equal(error.code, code);
    return true;
};

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const free = algebraPolynomialFreeModule(ring, 1);
    const one = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const multiplicationX = algebraPolynomialPresentationMorphism({
        source: one,
        target: one,
        map: algebraPolynomialModuleMap(free, free, [
            algebraPolynomialModuleVector(free, [x])
        ])
    });
    const quotient = algebraPolynomialFreydCokernel(multiplicationX);
    return { ring, x, free, one, multiplicationX, quotient };
};

describe('v3.2 bounded polynomial Freyd complexes', () => {
    it('computes degreewise homology of a nontrivial exact complex', () => {
        const value = fixture();
        const complex = algebraPolynomialFreydBoundedComplex({
            terms: [value.quotient.object, value.one, value.one],
            differentials: [
                value.quotient.projection,
                value.multiplicationX
            ]
        });
        const middle = algebraPolynomialFreydBoundedComplexHomology(complex, 1);
        const exactness = algebraPolynomialFreydExactnessAt(middle.homology);
        assert.equal(complex.conditions[0].agreement.agrees, true);
        assert.equal(complex.isComplex, true);
        assert.equal(middle.lowerEndpoint, false);
        assert.equal(middle.upperEndpoint, false);
        assert.equal(middle.homology.boundary.reconstructs, true);
        assert.equal(exactness.exact, true);

        const bottom = algebraPolynomialFreydBoundedComplexHomology(complex, 0);
        const top = algebraPolynomialFreydBoundedComplexHomology(complex, 2);
        assert.equal(bottom.lowerEndpoint, true);
        assert.equal(bottom.pair.isChainPair, true);
        assert.equal(top.upperEndpoint, true);
        assert.equal(top.pair.isChainPair, true);
    });

    it('retains an invalid adjacent agreement and gates degreewise homology', () => {
        const value = fixture();
        const complex = algebraPolynomialFreydBoundedComplex({
            terms: [value.one, value.one, value.one],
            differentials: [
                value.multiplicationX,
                algebraPolynomialPresentationMorphismIdentity(value.one)
            ]
        });
        assert.equal(complex.conditions[0].agreement.agrees, false);
        assert.equal(complex.isComplex, false);
        assert.throws(
            () => algebraPolynomialFreydBoundedComplexHomology(complex, 1),
            boundedError('CHAIN_CONDITION_FAILED')
        );
    });

    it('embeds direct bounded-free complexes as relation-free presentations',
        () => {
            const value = fixture();
            const freeComplex = algebraPolynomialBoundedFreeComplex({
                terms: [value.free, value.free, value.free],
                differentials: [
                    algebraPolynomialModuleMap(
                        value.free,
                        value.free,
                        [algebraPolynomialModuleVector(value.free, [value.x])]
                    ),
                    algebraPolynomialModuleMapZero(value.free, value.free)
                ]
            });
            const complex = algebraPolynomialFreydBoundedComplexFromFree(
                freeComplex
            );
            assert.equal(freeComplex.isComplex, true);
            assert.equal(complex.isComplex, true);
            assert.equal(complex.freeSource?.complex, freeComplex);
            assert.equal(complex.terms.every(term =>
                term.object.relations.generators.length === 0
            ), true);
            assert.equal(
                algebraPolynomialFreydBoundedComplexHomology(complex, 1)
                    .pair.isChainPair,
                true
            );
        });

    it('rejects bad endpoint data and out-of-range degrees', () => {
        const value = fixture();
        assert.throws(
            () => algebraPolynomialFreydBoundedComplex({
                terms: [value.one, value.quotient.object],
                differentials: [value.multiplicationX]
            }),
            boundedError('INVALID_DIFFERENTIALS')
        );
        const complex = algebraPolynomialFreydBoundedComplex({
            terms: [value.one],
            differentials: []
        });
        assert.throws(
            () => algebraPolynomialFreydBoundedComplexHomology(complex, 1),
            boundedError('DEGREE_OUT_OF_RANGE')
        );
    });

    it('is deterministic at the whole bounded-homology boundary', () => {
        const value = fixture();
        const make = () => algebraPolynomialFreydBoundedComplexHomology(
            algebraPolynomialFreydBoundedComplex({
                terms: [value.quotient.object, value.one, value.one],
                differentials: [
                    value.quotient.projection,
                    value.multiplicationX
                ]
            }),
            1
        );
        const first = make();
        const second = make();
        assert.deepEqual(first.homology.homologyObject,
            second.homology.homologyObject);
        assert.deepEqual(first.homology.boundaryMorphism.map,
            second.homology.boundaryMorphism.map);
    });
});
