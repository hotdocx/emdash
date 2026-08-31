/** Focused whole relation-witness and representative-congruence tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialPresentationMorphismError,
    RATIONAL_DOMAIN,
    algebraPolynomialChainMapSquare,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapEquals,
    algebraPolynomialModuleVector,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedPolynomialModule,
    algebraPolynomialSubmodule
} from '../src/v3_2';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const zero = algebraPolynomialZero(ring);
    const one = algebraPolynomialOne(ring);
    const ambient = algebraPolynomialFreeModule(ring, 1);
    const source = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(ambient, [
            algebraPolynomialModuleVector(ambient, [x])
        ])
    );
    const target = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(ambient, [
            algebraPolynomialModuleVector(ambient, [x])
        ])
    );
    const stricterTarget = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(ambient, [
            algebraPolynomialModuleVector(ambient, [
                algebraPolynomialMultiply(x, x)
            ])
        ])
    );
    const map = (value: typeof x) => algebraPolynomialModuleMap(
        ambient,
        ambient,
        [algebraPolynomialModuleVector(ambient, [value])]
    );
    return { ring, x, y, zero, one, ambient, source, target, stricterTarget, map };
};

describe('FPMAP whole polynomial presentation morphisms', () => {
    it('computes an ordered relation witness and exact assembled equation', () => {
        const value = fixture();
        const result = algebraPolynomialPresentationMorphism({
            source: value.source,
            target: value.target,
            map: value.map(value.y)
        });

        assert.equal(result.preservesRelations, true);
        assert.equal(result.relationImages.length, 1);
        assert.equal(result.relationImages[0].membership.member, true);
        assert.equal(result.relationWitness.columns.length, 1);
        assert.equal(algebraPolynomialModuleMapEquals(
            result.targetAfterWitness,
            result.mapAfterSource
        ), true);
    });

    it('retains a nonzero remainder when a relation is not preserved', () => {
        const value = fixture();
        const result = algebraPolynomialPresentationMorphism({
            source: value.source,
            target: value.stricterTarget,
            map: value.map(value.one)
        });

        assert.equal(result.preservesRelations, false);
        assert.equal(result.relationImages[0].membership.member, false);
        assert.equal(
            result.relationImages[0].membership.remainder.components[0]
                .terms.length > 0,
            true
        );
    });

    it('computes valid and invalid representative agreement', () => {
        const value = fixture();
        const valid = algebraPolynomialPresentationMorphismAgreement({
            source: value.source,
            target: value.target,
            left: value.map(value.x),
            right: value.map(value.zero)
        });
        const invalid = algebraPolynomialPresentationMorphismAgreement({
            source: value.source,
            target: value.target,
            left: value.map(value.y),
            right: value.map(value.zero)
        });

        assert.equal(valid.agrees, true);
        assert.equal(algebraPolynomialModuleMapEquals(
            valid.targetAfterWitness,
            valid.difference
        ), true);
        assert.equal(invalid.agrees, false);
        assert.equal(invalid.columns[0].membership.member, false);
    });

    it('computes a chain square and rejects a changed component', () => {
        const value = fixture();
        const differential = value.map(value.x);
        const scalar = value.map(value.y);
        const good = algebraPolynomialChainMapSquare({
            differentialSource: differential,
            differentialTarget: differential,
            componentPrevious: scalar,
            componentNow: scalar
        });
        const bad = algebraPolynomialChainMapSquare({
            differentialSource: differential,
            differentialTarget: differential,
            componentPrevious: value.map(value.one),
            componentNow: scalar
        });

        assert.equal(good.commutes, true);
        assert.equal(bad.commutes, false);
    });

    it('rejects a candidate map with foreign endpoints', () => {
        const value = fixture();
        const rankTwo = algebraPolynomialFreeModule(value.ring, 2);
        const foreign = algebraPolynomialModuleMap(
            rankTwo,
            value.ambient,
            [
                algebraPolynomialModuleVector(value.ambient, [value.one]),
                algebraPolynomialModuleVector(value.ambient, [value.zero])
            ]
        );
        assert.throws(
            () => algebraPolynomialPresentationMorphism({
                source: value.source,
                target: value.target,
                map: foreign
            }),
            error => {
                assert.ok(error instanceof AlgebraPolynomialPresentationMorphismError);
                assert.equal(error.code, 'INVALID_MAP_ENDPOINTS');
                return true;
            }
        );
    });
});
