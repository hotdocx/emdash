/** Focused CAS-HOMOLOGICAL-7A5 field-resolution tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraMatrix,
    algebraMatrixSpace
} from '../src/v3_2/algebra_matrix';
import {
    algebraFreeModule,
    algebraModuleCompose,
    algebraModuleIdentity,
    algebraModuleMorphismEquivalent,
    algebraModuleMorphismIsZero,
    algebraModuleRealization,
    algebraPresentedModule,
    algebraPresentedModuleEquals
} from '../src/v3_2/algebra_module';
import {
    ALGEBRA_RESOLUTION_PROFILE,
    algebraModulePresentationResolution,
    algebraModuleSplitResolution
} from '../src/v3_2/algebra_resolution';

describe('v3.2 bounded free resolutions over a field', () => {
    it('retains relation syzygies in a presentation-derived resolution', () => {
        const module = algebraPresentedModule(
            RATIONAL_DOMAIN,
            2,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 2),
                [['1', '2'], ['0', '0']]
            )
        );
        const resolution = algebraModulePresentationResolution(module);
        assert.deepEqual(
            resolution.complex.terms.map(term => term.object.generators),
            [2, 2, 1]
        );
        assert.equal(resolution.projectiveLength, 2);
        assert.equal(resolution.syzygyKernel.object.generators, 1);
        assert.ok(algebraModuleMorphismIsZero(algebraModuleCompose(
            resolution.augmentation,
            resolution.relationMorphism
        )));
        assert.ok(algebraPresentedModuleEquals(
            resolution.homology[0].object,
            module
        ));
        assert.deepEqual(resolution.homology.map(value =>
            algebraModuleRealization(value.object).dimension
        ), [1, 0, 0]);
        assert.ok(Object.isFrozen(resolution));
    });

    it('shortens the presentation resolution when relations are independent', () => {
        const module = algebraPresentedModule(
            RATIONAL_DOMAIN,
            2,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
                [['1'], ['0']]
            )
        );
        const resolution = algebraModulePresentationResolution(module);
        assert.equal(resolution.projectiveLength, 1);
        assert.equal(resolution.syzygyKernel.object.generators, 0);

        const free = algebraFreeModule(RATIONAL_DOMAIN, 2);
        const freeResolution = algebraModulePresentationResolution(free);
        assert.equal(freeResolution.projectiveLength, 0);
        assert.deepEqual(
            freeResolution.complex.terms.map(term => term.object.generators),
            [2, 0, 0]
        );
    });

    it('also exposes the minimal split resolution specific to fields', () => {
        const module = algebraPresentedModule(
            RATIONAL_DOMAIN,
            2,
            algebraMatrix(
                algebraMatrixSpace(RATIONAL_DOMAIN, 2, 1),
                [['1'], ['0']]
            )
        );
        const resolution = algebraModuleSplitResolution(module);
        assert.equal(resolution.projectiveLength, 0);
        assert.equal(resolution.complex.terms.length, 1);
        assert.equal(resolution.complex.terms[0].object.generators, 1);
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                resolution.inverse,
                resolution.augmentation
            ),
            algebraModuleIdentity(resolution.complex.terms[0].object)
        ));
        assert.ok(algebraModuleMorphismEquivalent(
            algebraModuleCompose(
                resolution.augmentation,
                resolution.inverse
            ),
            algebraModuleIdentity(module)
        ));
        assert.equal(
            ALGEBRA_RESOLUTION_PROFILE.polynomialModuleResolution,
            false
        );
    });
});
