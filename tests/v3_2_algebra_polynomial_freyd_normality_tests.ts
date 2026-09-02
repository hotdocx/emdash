/** Focused witness-retaining Freyd normal-monomorphism computation. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraPolynomialFreydNormalityError,
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydColiftAlongEpimorphism,
    algebraPolynomialFreydColiftAlongEpimorphismUnique,
    algebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydLiftAlongMonomorphism,
    algebraPolynomialFreydLiftAlongMonomorphismUnique,
    algebraPolynomialFreydMonomorphismWitness,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapEquals,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapSplitRows,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule
} from '../src/v3_2';

const normalityError = (
    code: AlgebraPolynomialFreydNormalityError['code']
) => (error: unknown) => {
    assert.ok(error instanceof AlgebraPolynomialFreydNormalityError);
    assert.equal(error.code, code);
    return true;
};

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const free = algebraPolynomialFreeModule(ring, 1);
    const presentation = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const map = (value: typeof x) => algebraPolynomialModuleMap(
        free,
        free,
        [algebraPolynomialModuleVector(free, [value])]
    );
    const monomorphism = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: map(x)
    });
    const test = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: map(algebraPolynomialMultiply(x, y))
    });
    return { ring, x, y, free, presentation, map, monomorphism, test };
};

describe('v3.2 polynomial Freyd normality', () => {
    it('splits agreement matrices into representation-preserving row blocks', () => {
        const { ring } = fixture();
        const source = algebraPolynomialFreeModule(ring, 1);
        const target = algebraPolynomialFreeModule(ring, 3);
        const one = algebraPolynomialOne(ring);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [one, one, one])
        ]);
        const split = algebraPolynomialModuleMapSplitRows(map, 1);
        assert.equal(split.top.target.rank, 1);
        assert.equal(split.bottom.target.rank, 2);
        assert.equal(split.reconstructs, true);
        assert.throws(
            () => algebraPolynomialModuleMapSplitRows(map, 4),
            normalityError('INVALID_ROW_SPLIT')
        );
    });

    it('implements Construction 3.14 for multiplication by x', () => {
        const value = fixture();
        const monic = algebraPolynomialFreydMonomorphismWitness(
            value.monomorphism
        );
        const lift = algebraPolynomialFreydLiftAlongMonomorphism(
            monic,
            value.test
        );
        assert.equal(monic.kernelZeroAgreement.agrees, true);
        assert.equal(monic.monic, true);
        assert.equal(lift.testCokernelZeroAgreement.agrees, true);
        assert.equal(lift.agreementBlocks.topRows, 0);
        assert.equal(lift.agreementBlocks.bottomRows, 1);
        assert.equal(lift.relationFactorization.reconstructs, true);
        assert.equal(lift.expectedRelationWitnessEquation, true);
        assert.equal(lift.reconstructionAgreement.agrees, true);
        assert.equal(lift.reconstructs, true);
        assert.equal(algebraPolynomialModuleMapEquals(
            lift.lift.map,
            value.map(value.y)
        ), true);
        const uniqueness =
            algebraPolynomialFreydLiftAlongMonomorphismUnique(
                lift,
                lift.lift
            );
        assert.equal(uniqueness.uniquenessAgreement.agrees, true);
        assert.equal(uniqueness.uniqueInQuotient, true);
        assert.ok(Object.isFrozen(monic));
        assert.ok(Object.isFrozen(lift));
        assert.ok(Object.isFrozen(uniqueness));
    });

    it('rejects non-monomorphisms and non-annihilated tests', () => {
        const value = fixture();
        const zero = algebraPolynomialPresentationMorphism({
            source: value.presentation,
            target: value.presentation,
            map: algebraPolynomialModuleMapZero(value.free, value.free)
        });
        assert.throws(
            () => algebraPolynomialFreydMonomorphismWitness(zero),
            normalityError('NOT_MONOMORPHISM')
        );
        const monic = algebraPolynomialFreydMonomorphismWitness(
            value.monomorphism
        );
        assert.throws(
            () => algebraPolynomialFreydLiftAlongMonomorphism(
                monic,
                algebraPolynomialPresentationMorphismIdentity(value.presentation)
            ),
            normalityError('NON_ANNIHILATED_NORMAL_TEST')
        );
    });

    it('rejects invalid test and competing-lift endpoints', () => {
        const value = fixture();
        const monic = algebraPolynomialFreydMonomorphismWitness(
            value.monomorphism
        );
        const otherFree = algebraPolynomialFreeModule(value.ring, 2);
        const other = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(otherFree, [])
        );
        assert.throws(
            () => algebraPolynomialFreydLiftAlongMonomorphism(
                monic,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            normalityError('INVALID_NORMAL_TEST')
        );
        const selected = algebraPolynomialFreydLiftAlongMonomorphism(
            monic,
            value.test
        );
        assert.throws(
            () => algebraPolynomialFreydLiftAlongMonomorphismUnique(
                selected,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            normalityError('INVALID_COMPETING_NORMAL_FACTOR')
        );
    });

    it('implements Construction 3.15 for the quotient by x', () => {
        const value = fixture();
        const quotient = algebraPolynomialFreydCokernel(value.monomorphism);
        const epic = algebraPolynomialFreydEpimorphismWitness(
            quotient.projection
        );
        const colift = algebraPolynomialFreydColiftAlongEpimorphism(
            epic,
            quotient.projection
        );
        assert.equal(epic.cokernelZeroAgreement.agrees, true);
        assert.equal(epic.identityBlocks.topRows, 1);
        assert.equal(epic.identityBlocks.bottomRows, 1);
        assert.equal(epic.epic, true);
        assert.equal(colift.testKernelZeroAgreement.agrees, true);
        assert.equal(colift.relationFactorization.reconstructs, true);
        assert.equal(colift.expectedRelationWitnessEquation, true);
        assert.equal(colift.reconstructionAgreement.agrees, true);
        assert.equal(colift.reconstructs, true);
        assert.equal(algebraPolynomialModuleMapEquals(
            colift.colift.map,
            algebraPolynomialModuleMapIdentity(quotient.object.ambient)
        ), true);
        const uniqueness =
            algebraPolynomialFreydColiftAlongEpimorphismUnique(
                colift,
                colift.colift
            );
        assert.equal(uniqueness.uniquenessAgreement.agrees, true);
        assert.equal(uniqueness.uniqueInQuotient, true);
        assert.ok(Object.isFrozen(epic));
        assert.ok(Object.isFrozen(colift));
        assert.ok(Object.isFrozen(uniqueness));
    });

    it('rejects non-epimorphisms and non-annihilated epi tests', () => {
        const value = fixture();
        assert.throws(
            () => algebraPolynomialFreydEpimorphismWitness(value.monomorphism),
            normalityError('NOT_EPIMORPHISM')
        );
        const quotient = algebraPolynomialFreydCokernel(value.monomorphism);
        const epic = algebraPolynomialFreydEpimorphismWitness(
            quotient.projection
        );
        assert.throws(
            () => algebraPolynomialFreydColiftAlongEpimorphism(
                epic,
                algebraPolynomialPresentationMorphismIdentity(value.presentation)
            ),
            normalityError('NON_ANNIHILATED_NORMAL_TEST')
        );
    });

    it('rejects invalid epi-test and competing-colift endpoints', () => {
        const value = fixture();
        const quotient = algebraPolynomialFreydCokernel(value.monomorphism);
        const epic = algebraPolynomialFreydEpimorphismWitness(
            quotient.projection
        );
        const otherFree = algebraPolynomialFreeModule(value.ring, 2);
        const other = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(otherFree, [])
        );
        assert.throws(
            () => algebraPolynomialFreydColiftAlongEpimorphism(
                epic,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            normalityError('INVALID_NORMAL_TEST')
        );
        const selected = algebraPolynomialFreydColiftAlongEpimorphism(
            epic,
            quotient.projection
        );
        assert.throws(
            () => algebraPolynomialFreydColiftAlongEpimorphismUnique(
                selected,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            normalityError('INVALID_COMPETING_NORMAL_FACTOR')
        );
    });

    it('is deterministic on identity and selected polynomial cases', () => {
        const value = fixture();
        const first = algebraPolynomialFreydMonomorphismWitness(
            value.monomorphism
        );
        const second = algebraPolynomialFreydMonomorphismWitness(
            value.monomorphism
        );
        assert.deepEqual(first.kernel.object, second.kernel.object);
        assert.deepEqual(
            algebraPolynomialFreydLiftAlongMonomorphism(first, value.test).lift,
            algebraPolynomialFreydLiftAlongMonomorphism(second, value.test).lift
        );
        const identity = algebraPolynomialPresentationMorphism({
            source: value.presentation,
            target: value.presentation,
            map: algebraPolynomialModuleMapIdentity(value.free)
        });
        assert.equal(
            algebraPolynomialFreydMonomorphismWitness(identity).monic,
            true
        );
    });
});
