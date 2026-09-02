/** Focused genuine fiber products and pushouts in polynomial Freyd. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydFiberProductError,
    AlgebraPolynomialFreydPushoutError,
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydFiberProduct,
    algebraPolynomialFreydFiberProductFactor,
    algebraPolynomialFreydFiberProductFactorUnique,
    algebraPolynomialFreydPushout,
    algebraPolynomialFreydPushoutCofactor,
    algebraPolynomialFreydPushoutCofactorUnique,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const fiberError = (code: AlgebraPolynomialFreydFiberProductError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydFiberProductError);
        assert.equal(error.code, code);
        return true;
    };

const pushoutError = (code: AlgebraPolynomialFreydPushoutError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydPushoutError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const freeOne = algebraPolynomialFreeModule(ring, 1);
    const freeTwo = algebraPolynomialFreeModule(ring, 2);
    const one = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(freeOne, [])
    );
    const two = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(freeTwo, [])
    );
    return { one, two };
};

describe('v3.2 genuine polynomial Freyd fiber products', () => {
    it('constructs the diagonal fiber product with a unique factor', () => {
        const { one } = fixture();
        const identity = algebraPolynomialPresentationMorphismIdentity(one);
        const fiberProduct = algebraPolynomialFreydFiberProduct(
            identity,
            identity
        );
        const factor = algebraPolynomialFreydFiberProductFactor(
            fiberProduct,
            identity,
            identity
        );
        const uniqueness = algebraPolynomialFreydFiberProductFactorUnique(
            factor,
            factor.lift
        );
        assert.equal(fiberProduct.compatibilityAgreement.agrees, true);
        assert.equal(fiberProduct.claimsContractibleFactors, true);
        assert.equal(factor.kernelLift.zeroAgreement.agrees, true);
        assert.equal(factor.reconstructionCombinedAgreement.agrees, true);
        assert.equal(factor.reconstructionLeftAgreement.agrees, true);
        assert.equal(factor.reconstructionRightAgreement.agrees, true);
        assert.equal(factor.claimsUniqueFactor, true);
        assert.equal(uniqueness.uniquenessAgreement.agrees, true);
        assert.equal(uniqueness.uniqueInQuotient, true);
        assert.ok(Object.isFrozen(fiberProduct));
        assert.ok(Object.isFrozen(factor));
    });

    it('rejects malformed cospans and incompatible test pairs', () => {
        const { one, two } = fixture();
        const identityOne = algebraPolynomialPresentationMorphismIdentity(one);
        assert.throws(
            () => algebraPolynomialFreydFiberProduct(
                identityOne,
                algebraPolynomialPresentationMorphismIdentity(two)
            ),
            fiberError('INVALID_COSPAN')
        );
        const fiberProduct = algebraPolynomialFreydFiberProduct(
            identityOne,
            identityOne
        );
        assert.throws(
            () => algebraPolynomialFreydFiberProductFactor(
                fiberProduct,
                identityOne,
                algebraPolynomialPresentationMorphismZero(one, one)
            ),
            fiberError('INCOMPATIBLE_TEST_PAIR')
        );
    });

    it('is deterministic on the selected whole result', () => {
        const { one } = fixture();
        const identity = algebraPolynomialPresentationMorphismIdentity(one);
        const first = algebraPolynomialFreydFiberProduct(identity, identity);
        const second = algebraPolynomialFreydFiberProduct(identity, identity);
        assert.deepEqual(first.object, second.object);
        assert.deepEqual(first.projectionLeft, second.projectionLeft);
        assert.deepEqual(first.projectionRight, second.projectionRight);
    });
});

describe('v3.2 genuine polynomial Freyd pushouts', () => {
    it('constructs the identity-span pushout with a unique cofactor', () => {
        const { one } = fixture();
        const identity = algebraPolynomialPresentationMorphismIdentity(one);
        const pushout = algebraPolynomialFreydPushout(identity, identity);
        const cofactor = algebraPolynomialFreydPushoutCofactor(
            pushout,
            identity,
            identity
        );
        const uniqueness = algebraPolynomialFreydPushoutCofactorUnique(
            cofactor,
            cofactor.cofactor
        );
        assert.equal(pushout.compatibilityAgreement.agrees, true);
        assert.equal(pushout.claimsContractibleCofactors, true);
        assert.equal(cofactor.cokernelColift.zeroAgreement.agrees, true);
        assert.equal(cofactor.reconstructionCombinedAgreement.agrees, true);
        assert.equal(cofactor.reconstructionLeftAgreement.agrees, true);
        assert.equal(cofactor.reconstructionRightAgreement.agrees, true);
        assert.equal(cofactor.claimsUniqueCofactor, true);
        assert.equal(uniqueness.uniquenessAgreement.agrees, true);
        assert.equal(uniqueness.uniqueInQuotient, true);
        assert.ok(Object.isFrozen(pushout));
        assert.ok(Object.isFrozen(cofactor));
    });

    it('rejects malformed spans and incompatible test pairs', () => {
        const { one, two } = fixture();
        const identityOne = algebraPolynomialPresentationMorphismIdentity(one);
        assert.throws(
            () => algebraPolynomialFreydPushout(
                identityOne,
                algebraPolynomialPresentationMorphismIdentity(two)
            ),
            pushoutError('INVALID_SPAN')
        );
        const pushout = algebraPolynomialFreydPushout(identityOne, identityOne);
        assert.throws(
            () => algebraPolynomialFreydPushoutCofactor(
                pushout,
                identityOne,
                algebraPolynomialPresentationMorphismZero(one, one)
            ),
            pushoutError('INCOMPATIBLE_TEST_PAIR')
        );
    });

    it('is deterministic on the selected whole result', () => {
        const { one } = fixture();
        const identity = algebraPolynomialPresentationMorphismIdentity(one);
        const first = algebraPolynomialFreydPushout(identity, identity);
        const second = algebraPolynomialFreydPushout(identity, identity);
        assert.deepEqual(first.object, second.object);
        assert.deepEqual(first.injectionLeft, second.injectionLeft);
        assert.deepEqual(first.injectionRight, second.injectionRight);
    });
});
