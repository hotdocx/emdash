/** Focused induced maps on polynomial Freyd homology. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydFunctorialHomologyError,
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydHomologyChainMap,
    algebraPolynomialFreydHomologyIdentityMap,
    algebraPolynomialFreydInducedHomologyMap,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const functorialError = (
    code: AlgebraPolynomialFreydFunctorialHomologyError['code']
) => (error: unknown) => {
    assert.ok(error instanceof AlgebraPolynomialFreydFunctorialHomologyError);
    assert.equal(error.code, code);
    return true;
};

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
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
    const multiplicationY = algebraPolynomialPresentationMorphism({
        source: one,
        target: one,
        map: algebraPolynomialModuleMap(free, free, [
            algebraPolynomialModuleVector(free, [y])
        ])
    });
    const zero = algebraPolynomialPresentationMorphismZero(one, one);
    const zeroHomology = algebraPolynomialFreydHomologyAt(
        algebraPolynomialFreydChainPair(zero, zero)
    );
    const quotient = algebraPolynomialFreydCokernel(multiplicationX);
    const exactHomology = algebraPolynomialFreydHomologyAt(
        algebraPolynomialFreydChainPair(
            multiplicationX,
            quotient.projection
        )
    );
    const scalarOn = (object: typeof one) => {
        const ambient = object.ambient;
        const zeroScalar = algebraPolynomialZero(ring);
        return algebraPolynomialPresentationMorphism({
            source: object,
            target: object,
            map: algebraPolynomialModuleMap(
                ambient,
                ambient,
                Array.from({ length: ambient.rank }, (_, column) =>
                    algebraPolynomialModuleVector(
                        ambient,
                        Array.from({ length: ambient.rank }, (_, row) =>
                            row === column ? y : zeroScalar
                        )
                    )
                )
            )
        });
    };
    return {
        one,
        multiplicationY,
        zeroHomology,
        exactHomology,
        quotient,
        scalarOn
    };
};

describe('v3.2 polynomial Freyd functorial homology', () => {
    it('computes the identity-induced map and its two factor equations', () => {
        const value = fixture();
        const induced = algebraPolynomialFreydHomologyIdentityMap(
            value.zeroHomology
        );
        const expected = algebraPolynomialPresentationMorphismIdentity(
            value.zeroHomology.homologyObject
        );
        assert.equal(induced.chainMap.isChainMap, true);
        assert.equal(induced.cyclesReconstruction.agrees, true);
        assert.equal(induced.boundaryCompatibility.agrees, true);
        assert.equal(induced.sourceBoundaryZeroAgreement.agrees, true);
        assert.equal(induced.homologyReconstruction.agrees, true);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(
            induced.homologyMap,
            expected
        ).agrees, true);
    });

    it('descends a nontrivial scalar chain map to the selected homology', () => {
        const value = fixture();
        const chainMap = algebraPolynomialFreydHomologyChainMap({
            source: value.zeroHomology,
            target: value.zeroHomology,
            fNext: value.multiplicationY,
            f: value.multiplicationY,
            fPrev: value.multiplicationY
        });
        const induced = algebraPolynomialFreydInducedHomologyMap(chainMap);
        const expected = value.scalarOn(value.zeroHomology.homologyObject);
        assert.equal(chainMap.upperAgreement.agrees, true);
        assert.equal(chainMap.lowerAgreement.agrees, true);
        assert.equal(induced.boundaryCompatibility.agrees, true);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(
            induced.homologyMap,
            expected
        ).agrees, true);
        assert.ok(Object.isFrozen(induced));
    });

    it('retains a failed square and gates the induced map', () => {
        const value = fixture();
        const chainMap = algebraPolynomialFreydHomologyChainMap({
            source: value.exactHomology,
            target: value.exactHomology,
            fNext: algebraPolynomialPresentationMorphismIdentity(value.one),
            f: algebraPolynomialPresentationMorphismIdentity(value.one),
            fPrev: algebraPolynomialPresentationMorphismZero(
                value.quotient.object,
                value.quotient.object
            )
        });
        assert.equal(chainMap.upperAgreement.agrees, true);
        assert.equal(chainMap.lowerAgreement.agrees, false);
        assert.equal(chainMap.isChainMap, false);
        assert.throws(
            () => algebraPolynomialFreydInducedHomologyMap(chainMap),
            functorialError('CHAIN_MAP_CONDITION_FAILED')
        );
    });

    it('rejects incompatible component endpoints', () => {
        const value = fixture();
        assert.throws(
            () => algebraPolynomialFreydHomologyChainMap({
                source: value.zeroHomology,
                target: value.zeroHomology,
                fNext: algebraPolynomialPresentationMorphismIdentity(
                    value.zeroHomology.homologyObject
                ),
                f: value.multiplicationY,
                fPrev: value.multiplicationY
            }),
            functorialError('INVALID_CHAIN_MAP')
        );
    });
});
