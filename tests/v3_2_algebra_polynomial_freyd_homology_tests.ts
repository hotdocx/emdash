/** Focused one-degree homology and exactness in polynomial Freyd. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydHomologyError,
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialFreydHomologyAt,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const homologyError = (code: AlgebraPolynomialFreydHomologyError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydHomologyError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const freeOne = algebraPolynomialFreeModule(ring, 1);
    const freeTwo = algebraPolynomialFreeModule(ring, 2);
    const one = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(freeOne, [])
    );
    const two = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(freeTwo, [])
    );
    const multiplicationX = algebraPolynomialPresentationMorphism({
        source: one,
        target: one,
        map: algebraPolynomialModuleMap(freeOne, freeOne, [
            algebraPolynomialModuleVector(freeOne, [x])
        ])
    });
    const rowXY = algebraPolynomialPresentationMorphism({
        source: two,
        target: one,
        map: algebraPolynomialModuleMap(freeTwo, freeOne, [
            algebraPolynomialModuleVector(freeOne, [x]),
            algebraPolynomialModuleVector(freeOne, [y])
        ])
    });
    const zero = algebraPolynomialPresentationMorphism({
        source: one,
        target: one,
        map: algebraPolynomialModuleMapZero(freeOne, freeOne)
    });
    return { ring, one, two, multiplicationX, rowXY, zero };
};

describe('v3.2 polynomial Freyd one-degree homology', () => {
    it('retains a negative chain agreement and gates homology', () => {
        const value = fixture();
        const pair = algebraPolynomialFreydChainPair(
            algebraPolynomialPresentationMorphismIdentity(value.one),
            value.multiplicationX
        );
        assert.equal(pair.chainAgreement.agrees, false);
        assert.equal(pair.isChainPair, false);
        assert.throws(
            () => algebraPolynomialFreydHomologyAt(pair),
            homologyError('CHAIN_CONDITION_FAILED')
        );
        assert.ok(Object.isFrozen(pair));
    });

    it('rejects different middle presentations before composition', () => {
        const value = fixture();
        assert.throws(
            () => algebraPolynomialFreydChainPair(
                value.multiplicationX,
                value.rowXY
            ),
            homologyError('INVALID_CHAIN_PAIR')
        );
    });

    it('computes the exact multiplication-and-quotient pair', () => {
        const value = fixture();
        const quotient = algebraPolynomialFreydCokernel(
            value.multiplicationX
        );
        const pair = algebraPolynomialFreydChainPair(
            value.multiplicationX,
            quotient.projection
        );
        const homology = algebraPolynomialFreydHomologyAt(pair);
        const exactness = algebraPolynomialFreydExactnessAt(homology);
        assert.equal(pair.chainAgreement.agrees, true);
        assert.equal(homology.boundary.reconstructs, true);
        assert.equal(homology.boundaryReconstruction.agrees, true);
        assert.equal(homology.homologyAnnihilation.agrees, true);
        assert.equal(exactness.projectionZeroAgreement.agrees, true);
        assert.equal(exactness.exact, true);
        assert.equal(exactness.epimorphism?.epic, true);
        assert.ok(Object.isFrozen(homology));
        assert.ok(Object.isFrozen(exactness));
    });

    it('retains nonexact zero-to-zero homology data', () => {
        const value = fixture();
        const pair = algebraPolynomialFreydChainPair(value.zero, value.zero);
        const homology = algebraPolynomialFreydHomologyAt(pair);
        const exactness = algebraPolynomialFreydExactnessAt(homology);
        assert.equal(pair.isChainPair, true);
        assert.equal(homology.boundaryReconstruction.agrees, true);
        assert.equal(exactness.exact, false);
        assert.equal(exactness.projectionZeroAgreement.agrees, false);
        assert.equal(exactness.epimorphism, undefined);
    });

    it('is deterministic on the selected nontrivial pair', () => {
        const value = fixture();
        const quotient = algebraPolynomialFreydCokernel(
            value.multiplicationX
        );
        const first = algebraPolynomialFreydHomologyAt(
            algebraPolynomialFreydChainPair(
                value.multiplicationX,
                quotient.projection
            )
        );
        const second = algebraPolynomialFreydHomologyAt(
            algebraPolynomialFreydChainPair(
                value.multiplicationX,
                quotient.projection
            )
        );
        assert.deepEqual(first.cycleObject, second.cycleObject);
        assert.deepEqual(first.boundaryMorphism.map, second.boundaryMorphism.map);
        assert.deepEqual(first.homologyObject, second.homologyObject);
    });
});
