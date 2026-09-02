/** Non-authoritative field/Freyd comparison for constant homology pairs. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraFreeModule,
    algebraModuleHomology,
    algebraModuleIdentity,
    algebraModuleRealization,
    algebraModuleZeroMorphism,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialFreydHomologyAt,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const compare = (incomingIdentity: boolean) => {
    const fieldOne = algebraFreeModule(RATIONAL_DOMAIN, 1);
    const fieldIncoming = incomingIdentity
        ? algebraModuleIdentity(fieldOne)
        : algebraModuleZeroMorphism(fieldOne, fieldOne);
    const fieldOutgoing = algebraModuleZeroMorphism(fieldOne, fieldOne);
    const fieldHomology = algebraModuleHomology(
        fieldIncoming,
        fieldOutgoing
    );
    const fieldDimension = algebraModuleRealization(
        fieldHomology.object
    ).dimension;

    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const polynomialOne = algebraPolynomialFreeModule(ring, 1);
    const presentation = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(polynomialOne, [])
    );
    const freydIncoming = incomingIdentity
        ? algebraPolynomialPresentationMorphismIdentity(presentation)
        : algebraPolynomialPresentationMorphismZero(presentation, presentation);
    const freydOutgoing = algebraPolynomialPresentationMorphismZero(
        presentation,
        presentation
    );
    const freydHomology = algebraPolynomialFreydHomologyAt(
        algebraPolynomialFreydChainPair(freydIncoming, freydOutgoing)
    );
    const freydExactness = algebraPolynomialFreydExactnessAt(freydHomology);
    return {
        fieldDimension,
        fieldVanishes: fieldDimension === 0,
        freydExactness
    };
};

describe('v3.2 field/Freyd homology differential', () => {
    it('agrees on zero homology for identity followed by zero', () => {
        const value = compare(true);
        assert.equal(value.fieldDimension, 0);
        assert.equal(value.freydExactness.exact, true);
        assert.equal(value.fieldVanishes, value.freydExactness.exact);
    });

    it('agrees on nonzero homology for zero followed by zero', () => {
        const value = compare(false);
        assert.equal(value.fieldDimension, 1);
        assert.equal(value.freydExactness.exact, false);
        assert.equal(value.fieldVanishes, value.freydExactness.exact);
    });
});
