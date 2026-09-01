/** Focused constructive cokernels in the polynomial Freyd category. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPresentedPolynomialModule,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapZero
} from '../src/v3_2/algebra_polynomial_presentation';
import {
    algebraPolynomialPresentationMorphism
} from '../src/v3_2/algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismIdentity
} from '../src/v3_2/algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydCokernelError,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydCokernelColiftUnique
} from '../src/v3_2/algebra_polynomial_freyd_cokernel';

const cokernelError = (code: AlgebraPolynomialFreydCokernelError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydCokernelError);
        assert.equal(error.code, code);
        return true;
    };

describe('v3.2 constructive polynomial Freyd cokernels', () => {
    it('adjoins morphism columns and computes a universal colift', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const one = algebraPolynomialOne(ring);
        const free = algebraPolynomialFreeModule(ring, 1);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const morphism = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: algebraPolynomialModuleMap(free, free, [
                algebraPolynomialModuleVector(free, [x])
            ])
        });
        const cokernel = algebraPolynomialFreydCokernel(morphism);
        assert.equal(cokernel.annihilates, true);
        assert.equal(cokernel.annihilationAgreement.agrees, true);
        assert.equal(cokernel.object.relations.generators.length, 1);

        const colift = algebraPolynomialFreydCokernelColift(
            cokernel,
            cokernel.projection
        );
        assert.equal(colift.zeroAgreement.agrees, true);
        assert.equal(colift.reconstructionAgreement.agrees, true);
        assert.equal(colift.reconstructs, true);

        const candidate = algebraPolynomialPresentationMorphism({
            source: cokernel.object,
            target: cokernel.object,
            map: algebraPolynomialModuleMap(free, free, [
                algebraPolynomialModuleVector(free, [
                    algebraPolynomialAdd(one, x)
                ])
            ])
        });
        assert.equal(candidate.preservesRelations, true);
        const uniqueness = algebraPolynomialFreydCokernelColiftUnique(
            colift,
            candidate
        );
        assert.equal(uniqueness.candidateReconstructionAgreement.agrees, true);
        assert.equal(uniqueness.uniquenessAgreement.agrees, true);
        assert.equal(uniqueness.uniqueInQuotient, true);
        assert.ok(Object.isFrozen(cokernel));
        assert.ok(Object.isFrozen(colift));
        assert.ok(Object.isFrozen(uniqueness));
    });

    it('handles a zero morphism without changing quotient semantics', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const free = algebraPolynomialFreeModule(ring, 2);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const zeroMorphism = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: algebraPolynomialModuleMapZero(free, free)
        });
        const cokernel = algebraPolynomialFreydCokernel(zeroMorphism);
        const identity = algebraPolynomialPresentationMorphismIdentity(target);
        const colift = algebraPolynomialFreydCokernelColift(cokernel, identity);
        assert.equal(colift.reconstructs, true);
        assert.equal(cokernel.object.relationBasis.basis.length, 0);
        assert.equal(algebraPresentedPolynomialModuleEquals(
            cokernel.object,
            target
        ), false);
    });

    it('rejects a test whose composite is nonzero in the quotient', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const free = algebraPolynomialFreeModule(ring, 1);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const identity = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: algebraPolynomialModuleMapIdentity(free)
        });
        const cokernel = algebraPolynomialFreydCokernel(identity);
        assert.throws(
            () => algebraPolynomialFreydCokernelColift(
                cokernel,
                algebraPolynomialPresentationMorphismIdentity(target)
            ),
            cokernelError('NON_ANNIHILATED_TEST')
        );
    });

    it('rejects invalid test and competing-colift endpoints', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const free = algebraPolynomialFreeModule(ring, 1);
        const otherFree = algebraPolynomialFreeModule(ring, 2);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(free, [])
        );
        const other = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(otherFree, [])
        );
        const zeroMorphism = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: algebraPolynomialModuleMapZero(free, free)
        });
        const cokernel = algebraPolynomialFreydCokernel(zeroMorphism);
        assert.throws(
            () => algebraPolynomialFreydCokernelColift(
                cokernel,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            cokernelError('INVALID_COLIFT')
        );
        const selected = algebraPolynomialFreydCokernelColift(
            cokernel,
            algebraPolynomialPresentationMorphismIdentity(target)
        );
        assert.throws(
            () => algebraPolynomialFreydCokernelColiftUnique(
                selected,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            cokernelError('INVALID_COMPETING_COLIFT')
        );
    });
});
