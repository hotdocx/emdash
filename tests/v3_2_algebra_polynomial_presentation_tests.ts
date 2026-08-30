/** Focused CAS-MODULE-4B2C presented polynomial-module resolution tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule
} from '../src/v3_2/algebra_polynomial_module';
import {
    ALGEBRA_POLYNOMIAL_PRESENTATION_PROFILE,
    AlgebraPolynomialPresentationError,
    algebraPolynomialModuleMapApply,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapIsZero,
    algebraPolynomialSchreyerResolution,
    algebraPresentedPolynomialModule,
    algebraPresentedPolynomialModuleNormalForm
} from '../src/v3_2/algebra_polynomial_presentation';

const presentationError = (code: AlgebraPolynomialPresentationError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialPresentationError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const zero = algebraPolynomialZero(ring);
    const ambient = algebraPolynomialFreeModule(
        ring,
        2,
        'position-over-term'
    );
    const first = algebraPolynomialModuleVector(ambient, [x, y]);
    const second = algebraPolynomialModuleVector(ambient, [y, zero]);
    const relations = algebraPolynomialSubmodule(ambient, [first, second]);
    const module = algebraPresentedPolynomialModule(relations);
    return { ring, x, y, zero, ambient, first, second, relations, module };
};

describe('v3.2 presented polynomial modules and Schreyer resolutions', () => {
    it('uses module Groebner remainders as quotient normal forms', () => {
        const { y, zero, ambient, module } = fixture();
        const relation = algebraPolynomialModuleVector(ambient, [
            zero,
            algebraPolynomialPower(y, 2n)
        ]);
        const member = algebraPresentedPolynomialModuleNormalForm(
            module,
            relation
        );
        assert.equal(member.member, true);
        const nonmember = algebraPresentedPolynomialModuleNormalForm(
            module,
            algebraPolynomialModuleVector(ambient, [zero, y])
        );
        assert.equal(nonmember.member, false);
        assert.equal(module.relationBasis.basis.length, 3);
        assert.ok(Object.isFrozen(module));
    });

    it('builds a complete bounded free resolution with zero composites', () => {
        const { first, module } = fixture();
        const resolution = algebraPolynomialSchreyerResolution(module, 4);
        assert.equal(resolution.complete, true);
        assert.equal(resolution.length, 2);
        assert.deepEqual(resolution.freeModules.map(value => value.rank), [
            2,
            3,
            1
        ]);
        assert.equal(resolution.stages[0].syzygies.generators.length, 1);
        assert.equal(resolution.stages[1].syzygies.generators.length, 0);
        assert.ok(algebraPolynomialModuleMapIsZero(
            algebraPolynomialModuleMapCompose(
                resolution.differentials[0],
                resolution.differentials[1]
            )
        ));
        const identity = algebraPolynomialModuleMapIdentity(first.parent);
        assert.ok(algebraPolynomialModuleEquals(
            algebraPolynomialModuleMapApply(identity, first),
            first
        ));
        assert.ok(Object.isFrozen(resolution));
        assert.ok(Object.isFrozen(resolution.freeModules));
    });

    it('retains truncation and handles a free quotient without fake stages', () => {
        const { ambient, module } = fixture();
        const truncated = algebraPolynomialSchreyerResolution(module, 1);
        assert.equal(truncated.length, 1);
        assert.equal(truncated.complete, false);
        const free = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
        const freeResolution = algebraPolynomialSchreyerResolution(free, 4);
        assert.equal(freeResolution.length, 0);
        assert.equal(freeResolution.complete, true);
        assert.deepEqual(freeResolution.freeModules.map(value => value.rank), [2]);
        assert.throws(
            () => algebraPolynomialSchreyerResolution(
                module,
                ALGEBRA_POLYNOMIAL_PRESENTATION_PROFILE.maximumLength + 1
            ),
            presentationError('INVALID_RESOLUTION_LIMIT')
        );
    });
});
