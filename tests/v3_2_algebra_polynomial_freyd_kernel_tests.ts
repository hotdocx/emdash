/** Focused constructive kernels in the polynomial Freyd category. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    algebraPolynomialZero
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
    algebraPolynomialPresentationMorphismIdentity
} from '../src/v3_2/algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydKernelError,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift,
    algebraPolynomialFreydKernelLiftUnique
} from '../src/v3_2/algebra_polynomial_freyd_kernel';

const kernelError = (code: AlgebraPolynomialFreydKernelError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialFreydKernelError);
        assert.equal(error.code, code);
        return true;
    };

describe('v3.2 constructive polynomial Freyd kernels', () => {
    it('uses two weak pullbacks and lifts a nontrivial syzygy', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const sourceAmbient = algebraPolynomialFreeModule(ring, 2);
        const targetAmbient = algebraPolynomialFreeModule(ring, 1);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(sourceAmbient, [])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(targetAmbient, [])
        );
        const morphism = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: algebraPolynomialModuleMap(sourceAmbient, targetAmbient, [
                algebraPolynomialModuleVector(targetAmbient, [x]),
                algebraPolynomialModuleVector(targetAmbient, [y])
            ])
        });
        const kernel = algebraPolynomialFreydKernel(morphism);
        assert.equal(kernel.annihilates, true);
        assert.equal(kernel.annihilationAgreement.agrees, true);
        assert.equal(kernel.expectedEmbeddingWitnessEquation, true);
        assert.ok(kernel.object.ambient.rank > 0);

        const testAmbient = algebraPolynomialFreeModule(ring, 1);
        const testSource = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(testAmbient, [])
        );
        const test = algebraPolynomialPresentationMorphism({
            source: testSource,
            target: source,
            map: algebraPolynomialModuleMap(testAmbient, sourceAmbient, [
                algebraPolynomialModuleVector(sourceAmbient, [
                    algebraPolynomialSubtract(zero, y),
                    x
                ])
            ])
        });
        const progress: string[] = [];
        const lift = algebraPolynomialFreydKernelLift(kernel, test, {
            context: { onProgress: event => progress.push(event.phase) }
        });
        assert.equal(lift.zeroAgreement.agrees, true);
        assert.equal(lift.expectedRelationWitnessEquation, true);
        assert.equal(lift.reconstructionAgreement.agrees, true);
        assert.equal(lift.reconstructs, true);
        assert.ok(progress.length >= 1);

        const uniqueness = algebraPolynomialFreydKernelLiftUnique(
            lift,
            lift.lift
        );
        assert.equal(uniqueness.candidateReconstructionAgreement.agrees, true);
        assert.equal(uniqueness.uniquenessAgreement.agrees, true);
        assert.equal(uniqueness.uniqueInQuotient, true);
        assert.ok(Object.isFrozen(kernel));
        assert.ok(Object.isFrozen(lift));
        assert.ok(Object.isFrozen(uniqueness));
    });

    it('handles identity and zero morphism boundaries', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const ambient = algebraPolynomialFreeModule(ring, 2);
        const presentation = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
        const identity = algebraPolynomialPresentationMorphismIdentity(
            presentation
        );
        const identityKernel = algebraPolynomialFreydKernel(identity);
        assert.equal(identityKernel.object.ambient.rank, 0);

        const zeroMorphism = algebraPolynomialPresentationMorphism({
            source: presentation,
            target: presentation,
            map: algebraPolynomialModuleMapZero(ambient, ambient)
        });
        const zeroKernel = algebraPolynomialFreydKernel(zeroMorphism);
        const identityLift = algebraPolynomialFreydKernelLift(
            zeroKernel,
            identity
        );
        assert.equal(identityLift.reconstructs, true);
    });

    it('rejects a non-annihilated test and invalid endpoints', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const otherAmbient = algebraPolynomialFreeModule(ring, 2);
        const presentation = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
        const other = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(otherAmbient, [])
        );
        const identity = algebraPolynomialPresentationMorphismIdentity(
            presentation
        );
        const kernel = algebraPolynomialFreydKernel(identity);
        assert.throws(
            () => algebraPolynomialFreydKernelLift(kernel, identity),
            kernelError('NON_ANNIHILATED_TEST')
        );

        const zeroMorphism = algebraPolynomialPresentationMorphism({
            source: presentation,
            target: presentation,
            map: algebraPolynomialModuleMapZero(ambient, ambient)
        });
        const zeroKernel = algebraPolynomialFreydKernel(zeroMorphism);
        assert.throws(
            () => algebraPolynomialFreydKernelLift(
                zeroKernel,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            kernelError('INVALID_TEST')
        );
        const selected = algebraPolynomialFreydKernelLift(
            zeroKernel,
            identity
        );
        assert.throws(
            () => algebraPolynomialFreydKernelLiftUnique(
                selected,
                algebraPolynomialPresentationMorphismIdentity(other)
            ),
            kernelError('INVALID_COMPETING_LIFT')
        );
    });

    it('retains deterministic selected kernel data', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const presentation = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
        const zeroMorphism = algebraPolynomialPresentationMorphism({
            source: presentation,
            target: presentation,
            map: algebraPolynomialModuleMapZero(ambient, ambient)
        });
        const first = algebraPolynomialFreydKernel(zeroMorphism);
        const second = algebraPolynomialFreydKernel(zeroMorphism);
        assert.deepEqual(first.object, second.object);
        assert.deepEqual(first.embedding.map, second.embedding.map);
        assert.deepEqual(
            first.firstWeakPullback.difference,
            second.firstWeakPullback.difference
        );
    });
});
