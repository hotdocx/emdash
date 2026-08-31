/** Focused PAM-MODULE-2A2 presented-algebra module and element tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialModuleAdd,
    algebraPolynomialModuleCombination,
    algebraPolynomialModuleEquals
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientAdd,
    algebraQuotientElement,
    algebraQuotientOne,
    algebraQuotientZero
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import {
    ALGEBRA_PRESENTED_MODULE_PROFILE,
    AlgebraPresentedModuleError,
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementAdd,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementIsZero,
    algebraPresentedAlgebraModuleElementNegate,
    algebraPresentedAlgebraModuleElementScale,
    algebraPresentedAlgebraModuleElementSchema,
    algebraPresentedAlgebraModuleIsZero,
    algebraPresentedAlgebraModuleNormalize,
    algebraPresentedAlgebraModuleVector,
    algebraPresentedAlgebraModuleVectorScale,
    serializeAlgebraPresentedAlgebraModule,
    serializeAlgebraPresentedAlgebraModuleElement
} from '../src/v3_2/algebra_presented_module';

const moduleError = (code: AlgebraPresentedModuleError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPresentedModuleError);
        assert.equal(error.code, code);
        return true;
    };

const polynomialAlgebra = (variables: readonly string[], relations = (
    values: ReturnType<typeof algebraPolynomialVariable>[]
) => [] as ReturnType<typeof algebraPolynomialVariable>[]) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const generators = variables.map((_, index) =>
        algebraPolynomialVariable(ring, index)
    );
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, relations(generators))
    );
    return {
        ring,
        generators,
        quotient,
        algebra: algebraPresentedAlgebra(quotient)
    };
};

describe('v3.2 modules over presented commutative algebras', () => {
    it('uses quotient relations as module-action relations', () => {
        const value = polynomialAlgebra(['x'], ([x]) => [
            algebraPolynomialPower(x, 2n)
        ]);
        const [x] = value.generators;
        const free = algebraPresentedAlgebraFreeModule(
            value.algebra,
            1,
            'position-over-term'
        );
        const module = algebraPresentedAlgebraModule(free, []);
        const xElement = algebraPresentedAlgebraModuleElement(
            module,
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(value.quotient, x)
            ])
        );
        const xSquared = algebraPresentedAlgebraModuleElement(
            module,
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(
                    value.quotient,
                    algebraPolynomialPower(x, 2n)
                )
            ])
        );
        assert.equal(module.algebraActionRelations.length, 1);
        assert.equal(module.relations.length, 0);
        assert.equal(module.relationBasis.reduced, true);
        assert.equal(algebraPresentedAlgebraModuleElementIsZero(xElement), false);
        assert.equal(algebraPresentedAlgebraModuleElementIsZero(xSquared), true);
    });

    it('normalizes A/(x) elements and retains the full decomposition', () => {
        const value = polynomialAlgebra(['x']);
        const [x] = value.generators;
        const free = algebraPresentedAlgebraFreeModule(value.algebra, 1);
        const relation = algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(value.quotient, x)
        ]);
        const module = algebraPresentedAlgebraModule(free, [relation]);
        const oneVector = algebraPresentedAlgebraModuleBasisVector(free, 0);
        const normalization = algebraPresentedAlgebraModuleNormalize(
            module,
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(
                    value.quotient,
                    algebraPolynomialAdd(x, algebraPolynomialOne(value.ring))
                )
            ])
        );
        const relationCombination = algebraPolynomialModuleCombination(
            module.combinedRelations.generators,
            normalization.membership.coefficients
        );
        assert.ok(algebraPolynomialModuleEquals(
            algebraPolynomialModuleAdd(
                relationCombination,
                normalization.membership.remainder
            ),
            normalization.lift
        ));
        assert.equal(normalization.algebraActionCoefficients.length, 0);
        assert.equal(normalization.relationCoefficients.length, 1);
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraPresentedAlgebraModuleElement(module, normalization.input),
            algebraPresentedAlgebraModuleElement(module, oneVector)
        ));
        assert.equal(algebraPresentedAlgebraModuleIsZero(module), false);
    });

    it('computes addition, negation, and scalar action canonically', () => {
        const value = polynomialAlgebra(['x']);
        const [x] = value.generators;
        const free = algebraPresentedAlgebraFreeModule(value.algebra, 1);
        const module = algebraPresentedAlgebraModule(free, [
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(value.quotient, x)
            ])
        ]);
        const one = algebraPresentedAlgebraModuleElement(
            module,
            algebraPresentedAlgebraModuleBasisVector(free, 0)
        );
        const negative = algebraPresentedAlgebraModuleElementNegate(one);
        assert.equal(algebraPresentedAlgebraModuleElementIsZero(
            algebraPresentedAlgebraModuleElementAdd(one, negative)
        ), true);
        assert.equal(algebraPresentedAlgebraModuleElementIsZero(
            algebraPresentedAlgebraModuleElementScale(
                algebraQuotientElement(value.quotient, x),
                one
            )
        ), true);
        assert.equal(algebraPresentedAlgebraModuleElementIsZero(one), false);
    });

    it('shares parent identity across equivalent relation presentations', () => {
        const value = polynomialAlgebra(['x', 'y']);
        const [x, y] = value.generators;
        const free = algebraPresentedAlgebraFreeModule(
            value.algebra,
            1,
            'position-over-term'
        );
        const vector = (polynomial: typeof x) =>
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(value.quotient, polynomial)
            ]);
        const first = algebraPresentedAlgebraModule(free, [vector(x), vector(y)]);
        const second = algebraPresentedAlgebraModule(free, [
            vector(x),
            vector(algebraPolynomialAdd(x, y))
        ]);
        const third = algebraPresentedAlgebraModule(free, [
            vector(algebraPolynomialAdd(x, y)),
            vector(x)
        ]);
        assert.deepEqual(first.identity, second.identity);
        assert.deepEqual(first.identity, third.identity);
        assert.deepEqual(
            first.relationBasis.basis.map(entry => entry.components),
            second.relationBasis.basis.map(entry => entry.components)
        );
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            algebraPresentedAlgebraModuleElement(
                first,
                algebraPresentedAlgebraModuleBasisVector(free, 0)
            ),
            algebraPresentedAlgebraModuleElement(
                second,
                algebraPresentedAlgebraModuleBasisVector(free, 0)
            )
        ));
    });

    it('uses canonical quotient representatives in relation acquisition', () => {
        const value = polynomialAlgebra(['x'], ([x]) => [
            algebraPolynomialPower(x, 2n)
        ]);
        const [x] = value.generators;
        const free = algebraPresentedAlgebraFreeModule(value.algebra, 1);
        const first = algebraPresentedAlgebraModule(free, [
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(value.quotient, x)
            ])
        ]);
        const second = algebraPresentedAlgebraModule(free, [
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(
                    value.quotient,
                    algebraPolynomialAdd(x, algebraPolynomialPower(x, 2n))
                )
            ])
        ]);
        assert.deepEqual(first.identity, second.identity);
        assert.deepEqual(first.relations, second.relations);
    });

    it('distinguishes module orders and detects zero modules', () => {
        const value = polynomialAlgebra(['x']);
        const freeTop = algebraPresentedAlgebraFreeModule(value.algebra, 1);
        const freePot = algebraPresentedAlgebraFreeModule(
            value.algebra,
            1,
            'position-over-term'
        );
        assert.notDeepEqual(freeTop.identity, freePot.identity);
        const zeroModule = algebraPresentedAlgebraModule(freeTop, [
            algebraPresentedAlgebraModuleVector(freeTop, [
                algebraQuotientOne(value.quotient)
            ])
        ]);
        const rankZero = algebraPresentedAlgebraModule(
            algebraPresentedAlgebraFreeModule(value.algebra, 0),
            []
        );
        assert.equal(algebraPresentedAlgebraModuleIsZero(zeroModule), true);
        assert.equal(algebraPresentedAlgebraModuleIsZero(rankZero), true);
        assert.equal(ALGEBRA_PRESENTED_MODULE_PROFILE.defaultTermOrder,
            'term-over-position');
    });

    it('roundtrips schemas and deterministic serialization', () => {
        const value = polynomialAlgebra(['x']);
        const free = algebraPresentedAlgebraFreeModule(value.algebra, 1);
        const module = algebraPresentedAlgebraModule(free, []);
        const element = algebraPresentedAlgebraModuleElement(
            module,
            algebraPresentedAlgebraModuleBasisVector(free, 0)
        );
        const schema = algebraPresentedAlgebraModuleElementSchema(module);
        assert.ok(algebraPresentedAlgebraModuleElementEquals(
            schema.normalize(element, 'element'),
            element
        ));
        assert.equal(
            serializeAlgebraPresentedAlgebraModule(module),
            serializeAlgebraPresentedAlgebraModule(module)
        );
        assert.equal(
            serializeAlgebraPresentedAlgebraModuleElement(element),
            serializeAlgebraPresentedAlgebraModuleElement(element)
        );
        assert.ok(Object.isFrozen(module));
        assert.ok(Object.isFrozen(element));
    });

    it('rejects wrong arity, positions, algebras, modules, and scalars', () => {
        const first = polynomialAlgebra(['x']);
        const second = polynomialAlgebra(['y']);
        const firstFree = algebraPresentedAlgebraFreeModule(first.algebra, 1);
        const secondFree = algebraPresentedAlgebraFreeModule(second.algebra, 1);
        assert.throws(
            () => algebraPresentedAlgebraModuleVector(firstFree, []),
            moduleError('INVALID_VECTOR')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleBasisVector(firstFree, 1),
            moduleError('INVALID_BASIS_POSITION')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleVector(firstFree, [
                algebraQuotientZero(second.quotient) as never
            ]),
            moduleError('FOREIGN_ALGEBRA')
        );
        assert.throws(
            () => algebraPresentedAlgebraModule(firstFree, [
                algebraPresentedAlgebraModuleVector(secondFree, [
                    algebraQuotientZero(second.quotient)
                ]) as never
            ]),
            moduleError('FOREIGN_FREE_MODULE')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleVectorScale(
                algebraQuotientZero(second.quotient) as never,
                algebraPresentedAlgebraModuleBasisVector(firstFree, 0)
            ),
            moduleError('FOREIGN_ALGEBRA')
        );
        const firstModule = algebraPresentedAlgebraModule(firstFree, []);
        const secondModule = algebraPresentedAlgebraModule(secondFree, []);
        assert.throws(
            () => algebraPresentedAlgebraModuleElementAdd(
                algebraPresentedAlgebraModuleElement(
                    firstModule,
                    algebraPresentedAlgebraModuleBasisVector(firstFree, 0)
                ),
                algebraPresentedAlgebraModuleElement(
                    secondModule,
                    algebraPresentedAlgebraModuleBasisVector(secondFree, 0)
                ) as never
            ),
            moduleError('FOREIGN_PRESENTED_MODULE')
        );
        assert.throws(
            () => algebraPresentedAlgebraModuleElementScale(
                algebraQuotientZero(second.quotient) as never,
                algebraPresentedAlgebraModuleElement(
                    firstModule,
                    algebraPresentedAlgebraModuleBasisVector(firstFree, 0)
                )
            ),
            moduleError('FOREIGN_ALGEBRA')
        );
    });
});
