/** Focused polynomial bounded-complex and whole chain-map tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedChainMapCompose,
    algebraPolynomialBoundedChainMapEquals,
    algebraPolynomialBoundedChainMapIdentity,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialBoundedFreeComplexFromSchreyer,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSchreyerResolution,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const zero = algebraPolynomialZero(ring);
    const one = algebraPolynomialOne(ring);
    const module = algebraPolynomialFreeModule(ring, 1);
    const map = (value: typeof x) => algebraPolynomialModuleMap(
        module,
        module,
        [algebraPolynomialModuleVector(module, [value])]
    );
    return { ring, x, y, zero, one, module, map };
};

describe('FBC polynomial bounded complexes and chain maps', () => {
    it('retains valid and nonzero adjacent composites', () => {
        const value = fixture();
        const valid = algebraPolynomialBoundedFreeComplex({
            terms: [value.module, value.module, value.module],
            differentials: [value.map(value.x), value.map(value.zero)]
        });
        const invalid = algebraPolynomialBoundedFreeComplex({
            terms: [value.module, value.module, value.module],
            differentials: [value.map(value.x), value.map(value.one)]
        });

        assert.equal(valid.isComplex, true);
        assert.equal(valid.conditions.length, 1);
        assert.equal(valid.conditions[0].zero, true);
        assert.equal(invalid.isComplex, false);
        assert.equal(invalid.conditions[0].zero, false);
        assert.equal(invalid.conditions[0].composite.columns[0]
            .components[0].terms.length > 0, true);
    });

    it('revalidates a Schreyer resolution without losing metadata', () => {
        const value = fixture();
        const ambient = algebraPolynomialFreeModule(
            value.ring,
            2,
            'position-over-term'
        );
        const relations = algebraPolynomialSubmodule(ambient, [
            algebraPolynomialModuleVector(ambient, [value.x, value.y]),
            algebraPolynomialModuleVector(ambient, [value.y, value.zero])
        ]);
        const resolution = algebraPolynomialSchreyerResolution(
            algebraPresentedPolynomialModule(relations),
            4
        );
        const complex = algebraPolynomialBoundedFreeComplexFromSchreyer(
            resolution
        );

        assert.equal(complex.isComplex, true);
        assert.equal(complex.length, resolution.length);
        assert.equal(complex.schreyerSource?.resolution, resolution);
        assert.equal(complex.schreyerSource?.complete, true);
    });

    it('validates identity, scalar, composition, and a changed component', () => {
        const value = fixture();
        const complex = algebraPolynomialBoundedFreeComplex({
            terms: [value.module, value.module],
            differentials: [value.map(value.x)]
        });
        const identity = algebraPolynomialBoundedChainMapIdentity(complex);
        const scalar = algebraPolynomialBoundedChainMap({
            source: complex,
            target: complex,
            components: [value.map(value.y), value.map(value.y)]
        });
        const composite = algebraPolynomialBoundedChainMapCompose(
            scalar,
            identity
        );
        const bad = algebraPolynomialBoundedChainMap({
            source: complex,
            target: complex,
            components: [value.map(value.one), value.map(value.y)]
        });

        assert.equal(identity.isChainMap, true);
        assert.equal(scalar.isChainMap, true);
        assert.equal(composite.isChainMap, true);
        assert.equal(algebraPolynomialBoundedChainMapEquals(composite, scalar), true);
        assert.equal(bad.isChainMap, false);
        assert.equal(bad.squares[0].commutes, false);
    });
});
