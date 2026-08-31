/** Focused PAM-MODULE-2A reduced polynomial-module basis tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN, algebraRational } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialMultiply,
    algebraPolynomialRing,
    algebraPolynomialText,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    AlgebraPolynomialModuleError,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleCombination,
    algebraPolynomialModuleDivide,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule,
    algebraReducedPolynomialModuleGroebnerBasis
} from '../src/v3_2/algebra_polynomial_module';

const moduleError = (code: AlgebraPolynomialModuleError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialModuleError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const two = algebraPolynomialConstant(ring, algebraRational(2n));
    const ambient = algebraPolynomialFreeModule(
        ring,
        1,
        'position-over-term'
    );
    const vector = (polynomial: typeof x) =>
        algebraPolynomialModuleVector(ambient, [polynomial]);
    const reduced = (generators: readonly ReturnType<typeof vector>[]) => {
        const submodule = algebraPolynomialSubmodule(ambient, generators);
        return algebraReducedPolynomialModuleGroebnerBasis(
            algebraPolynomialModuleGroebnerBasis(submodule)
        );
    };
    return { ring, x, y, two, ambient, vector, reduced };
};

const basisText = (basis: ReturnType<ReturnType<typeof fixture>['reduced']>) =>
    basis.basis.map(vector => vector.components.map(algebraPolynomialText));

describe('v3.2 reduced polynomial-module Groebner bases', () => {
    it('canonicalizes equivalent ordered relation presentations', () => {
        const value = fixture();
        const xy = value.reduced([value.vector(value.x), value.vector(value.y)]);
        const xThenSum = value.reduced([
            value.vector(value.x),
            value.vector(algebraPolynomialAdd(value.x, value.y))
        ]);
        const sumThenX = value.reduced([
            value.vector(algebraPolynomialAdd(value.x, value.y)),
            value.vector(value.x)
        ]);
        assert.deepEqual(basisText(xy), [['1*x'], ['1*y']]);
        assert.deepEqual(basisText(xThenSum), basisText(xy));
        assert.deepEqual(basisText(sumThenX), basisText(xy));
        assert.equal(xy.reduced, true);
    });

    it('retains transformations into every original generator family', () => {
        const value = fixture();
        const source = algebraPolynomialSubmodule(value.ambient, [
            value.vector(algebraPolynomialAdd(value.x, value.y)),
            value.vector(value.x)
        ]);
        const reduced = algebraReducedPolynomialModuleGroebnerBasis(
            algebraPolynomialModuleGroebnerBasis(source)
        );
        reduced.basis.forEach((basis, index) => assert.ok(
            algebraPolynomialModuleEquals(
                algebraPolynomialModuleCombination(
                    source.generators,
                    reduced.transformations[index]
                ),
                basis
            )
        ));
    });

    it('removes duplicates and scaled leading generators', () => {
        const value = fixture();
        const reduced = value.reduced([
            value.vector(value.x),
            value.vector(value.x),
            value.vector(algebraPolynomialMultiply(value.two, value.x))
        ]);
        assert.deepEqual(basisText(reduced), [['1*x']]);
        assert.equal(reduced.transformations[0].length, 3);
    });

    it('interreduces every retained vector against all the others', () => {
        const value = fixture();
        const reduced = value.reduced([
            value.vector(value.x),
            value.vector(algebraPolynomialAdd(value.x, value.y))
        ]);
        reduced.basis.forEach((basis, index) => {
            const division = algebraPolynomialModuleDivide(
                basis,
                reduced.basis.filter((_, other) => other !== index)
            );
            assert.ok(algebraPolynomialModuleEquals(division.remainder, basis));
        });
    });

    it('handles the zero submodule and rejects invalid limits', () => {
        const value = fixture();
        const source = algebraPolynomialSubmodule(value.ambient, []);
        const basis = algebraPolynomialModuleGroebnerBasis(source);
        const reduced = algebraReducedPolynomialModuleGroebnerBasis(basis);
        assert.equal(reduced.basis.length, 0);
        assert.equal(reduced.transformations.length, 0);
        assert.throws(
            () => algebraReducedPolynomialModuleGroebnerBasis(basis, 0),
            moduleError('MODULE_LIMIT_EXCEEDED')
        );
    });
});
