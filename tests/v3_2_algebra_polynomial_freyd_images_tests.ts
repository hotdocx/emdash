/** Focused derived polynomial Freyd image/coimage isomorphism. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydImageCoimageComparison,
    algebraPolynomialFreydImageCoimageIsomorphism,
    algebraPolynomialFreydImages,
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
    return { ring, freeOne, one, multiplicationX, rowXY };
};

describe('v3.2 polynomial Freyd images and coimages', () => {
    it('constructs the canonical comparison and full factorization', () => {
        const value = fixture();
        const comparison = algebraPolynomialFreydImageCoimageComparison(
            value.multiplicationX
        );
        assert.equal(comparison.coastriction.reconstructs, true);
        assert.equal(comparison.comparisonLift.reconstructs, true);
        assert.equal(comparison.factorizationAgreement.agrees, true);
        assert.equal(comparison.factors, true);
        assert.ok(Object.isFrozen(comparison));
    });

    it('constructs both normality inverses and their quotient laws', () => {
        const value = fixture();
        const comparison = algebraPolynomialFreydImageCoimageComparison(
            value.multiplicationX
        );
        const iso = algebraPolynomialFreydImageCoimageIsomorphism(comparison);
        assert.equal(iso.monomorphism.monic, true);
        assert.equal(iso.epimorphism.epic, true);
        assert.equal(iso.inverseFromMonic.reconstructs, true);
        assert.equal(iso.inverseFromEpic.reconstructs, true);
        assert.equal(iso.inverseCandidatesAgreement.agrees, true);
        assert.equal(iso.rightInverseAgreement.agrees, true);
        assert.equal(iso.leftInverseAgreement.agrees, true);
        assert.equal(iso.isomorphism, true);
        assert.ok(Object.isFrozen(iso));
    });

    it('handles a nontrivial row map and zero/identity boundaries', () => {
        const value = fixture();
        const row = algebraPolynomialFreydImages(value.rowXY);
        assert.equal(row.comparison.factors, true);
        assert.equal(row.isomorphism, true);

        const identity = algebraPolynomialPresentationMorphismIdentity(value.one);
        const identityImages = algebraPolynomialFreydImages(identity);
        assert.equal(identityImages.isomorphism, true);

        const zero = algebraPolynomialPresentationMorphism({
            source: value.one,
            target: value.one,
            map: algebraPolynomialModuleMapZero(value.freeOne, value.freeOne)
        });
        const zeroImages = algebraPolynomialFreydImages(zero);
        assert.equal(zeroImages.comparison.factors, true);
        assert.equal(zeroImages.isomorphism, true);
    });

    it('retains deterministic selected image/coimage data', () => {
        const value = fixture();
        const first = algebraPolynomialFreydImages(value.multiplicationX);
        const second = algebraPolynomialFreydImages(value.multiplicationX);
        assert.deepEqual(first.comparison.image.object, second.comparison.image.object);
        assert.deepEqual(
            first.comparison.coimage.object,
            second.comparison.coimage.object
        );
        assert.deepEqual(first.inverse.map, second.inverse.map);
    });
});
