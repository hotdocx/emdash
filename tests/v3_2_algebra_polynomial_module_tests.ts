/** Focused CAS-MODULE-4B2 polynomial free-module and Buchberger tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { INTEGER_DOMAIN, RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialText,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    ALGEBRA_POLYNOMIAL_MODULE_PROFILE,
    AlgebraPolynomialModuleError,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleAdd,
    algebraPolynomialModuleCombination,
    algebraPolynomialModuleDivide,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleLeadingTerm,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleOriginalSyzygies,
    algebraPolynomialModuleScale,
    algebraPolynomialModuleSchreyerSyzygies,
    algebraPolynomialModuleVector,
    algebraPolynomialModuleVectorSchema,
    algebraPolynomialModuleZero,
    algebraPolynomialSubmodule
} from '../src/v3_2/algebra_polynomial_module';

const moduleError = (code: AlgebraPolynomialModuleError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPolynomialModuleError);
        assert.equal(error.code, code);
        return true;
    };

const vectorText = (
    vector: ReturnType<typeof algebraPolynomialModuleVector>
): readonly string[] => vector.components.map(algebraPolynomialText);

describe('v3.2 polynomial free modules and module Buchberger', () => {
    it('distinguishes position-over-term from term-over-position', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'grlex');
        const x = algebraPolynomialVariable(ring, 0);
        const y2 = algebraPolynomialPower(algebraPolynomialVariable(ring, 1), 2n);
        const pot = algebraPolynomialFreeModule(ring, 2, 'position-over-term');
        const top = algebraPolynomialFreeModule(ring, 2, 'term-over-position');
        const potVector = algebraPolynomialModuleVector(pot, [x, y2]);
        const topVector = algebraPolynomialModuleVector(top, [x, y2]);
        assert.equal(algebraPolynomialModuleLeadingTerm(potVector)!.position, 0);
        assert.equal(algebraPolynomialModuleLeadingTerm(topVector)!.position, 1);
        assert.notEqual(pot.identity.id, top.identity.id);
        assert.equal(
            algebraPolynomialModuleVectorSchema(pot).normalize(
                potVector,
                'vector'
            ).kind,
            'algebra-polynomial-module-vector'
        );
        assert.equal(
            ALGEBRA_POLYNOMIAL_MODULE_PROFILE.positionTieBreak,
            'lower-index-first'
        );
    });

    it('divides module vectors only at matching basis positions', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const module = algebraPolynomialFreeModule(ring, 2, 'term-over-position');
        const zero = algebraPolynomialZero(ring);
        const first = algebraPolynomialModuleVector(module, [x, zero]);
        const second = algebraPolynomialModuleVector(module, [zero, y]);
        const dividend = algebraPolynomialModuleVector(module, [
            algebraPolynomialPower(x, 2n),
            algebraPolynomialAdd(algebraPolynomialPower(y, 2n), x)
        ]);
        const division = algebraPolynomialModuleDivide(
            dividend,
            [first, second]
        );
        assert.deepEqual(division.quotients.map(algebraPolynomialText), [
            '1*x',
            '1*y'
        ]);
        assert.deepEqual(vectorText(division.remainder), ['0', '1*x']);
        const reconstructed = algebraPolynomialModuleAdd(
            algebraPolynomialModuleAdd(
                algebraPolynomialModuleScale(division.quotients[0], first),
                algebraPolynomialModuleScale(division.quotients[1], second)
            ),
            division.remainder
        );
        assert.ok(algebraPolynomialModuleEquals(reconstructed, dividend));
    });

    it('computes module S-pairs and retains original-generator transformations', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const module = algebraPolynomialFreeModule(ring, 2, 'position-over-term');
        const first = algebraPolynomialModuleVector(module, [x, y]);
        const second = algebraPolynomialModuleVector(module, [y, zero]);
        const submodule = algebraPolynomialSubmodule(module, [first, second]);
        const progress: number[] = [];
        const basis = algebraPolynomialModuleGroebnerBasis(submodule, {
            context: { onProgress: event => progress.push(event.completed) }
        });
        assert.equal(basis.basis.length, 3);
        assert.equal(basis.pairsProcessed, 1);
        assert.deepEqual(
            vectorText(basis.basis[2]),
            ['0', '1*y^2']
        );
        basis.basis.forEach((vector, index) => {
            assert.ok(algebraPolynomialModuleEquals(
                algebraPolynomialModuleCombination(
                    submodule.generators,
                    basis.transformations[index]
                ),
                vector
            ));
        });
        assert.equal(progress.length, basis.pairsProcessed);

        const target = algebraPolynomialModuleVector(module, [
            zero,
            algebraPolynomialPower(y, 2n)
        ]);
        const membership = algebraPolynomialModuleMembership(target, basis);
        assert.equal(membership.member, true);
        assert.ok(algebraPolynomialModuleEquals(
            algebraPolynomialModuleAdd(
                algebraPolynomialModuleCombination(
                    submodule.generators,
                    membership.coefficients
                ),
                membership.remainder
            ),
            target
        ));
        const nonmember = algebraPolynomialModuleMembership(
            algebraPolynomialModuleVector(module, [zero, y]),
            basis
        );
        assert.equal(nonmember.member, false);
        assert.deepEqual(vectorText(nonmember.remainder), ['0', '1*y']);
        assert.ok(Object.isFrozen(basis));
        assert.ok(Object.isFrozen(basis.transformations));
    });

    it('computes verified syzygies in the induced Schreyer order', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const ambient = algebraPolynomialFreeModule(
            ring,
            2,
            'position-over-term'
        );
        const basis = algebraPolynomialModuleGroebnerBasis(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x, y]),
                algebraPolynomialModuleVector(ambient, [y, zero])
            ])
        );
        const syzygies = algebraPolynomialModuleSchreyerSyzygies(basis);
        assert.equal(syzygies.module.termOrder, 'schreyer');
        assert.equal(syzygies.generators.length, 1);
        assert.deepEqual(vectorText(syzygies.generators[0]), [
            '1*y',
            '-1*x',
            '-1'
        ]);
        assert.equal(
            algebraPolynomialModuleLeadingTerm(syzygies.generators[0])!
                .position,
            0
        );
        assert.deepEqual(syzygies.sourcePairs, [{ left: 0, right: 1 }]);
        assert.ok(algebraPolynomialModuleEquals(
            algebraPolynomialModuleCombination(
                basis.basis,
                syzygies.generators[0].components
            ),
            algebraPolynomialModuleZero(ambient)
        ));
        const syzygyBasis = algebraPolynomialModuleGroebnerBasis(
            algebraPolynomialSubmodule(
                syzygies.module,
                syzygies.generators
            )
        );
        assert.equal(syzygyBasis.basis.length, 1);
        assert.ok(Object.isFrozen(syzygies));
        assert.ok(Object.isFrozen(syzygies.module.schreyerData));
    });

    it('recovers complete syzygies in the original ordered columns', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const negativeOne = algebraPolynomialSubtract(zero, one);
        const target = algebraPolynomialFreeModule(ring, 1);
        const columns = [
            algebraPolynomialModuleVector(target, [x]),
            algebraPolynomialModuleVector(target, [y]),
            algebraPolynomialModuleVector(target, [algebraPolynomialAdd(x, y)])
        ];
        const syzygies = algebraPolynomialModuleOriginalSyzygies(
            algebraPolynomialSubmodule(target, columns)
        );
        assert.equal(syzygies.module.rank, 3);
        assert.equal(syzygies.module.termOrder, 'term-over-position');
        assert.ok(syzygies.pulledBackSchreyer.length > 0);
        assert.ok(syzygies.originalRewrites.length > 0);
        const expectedKoszul = algebraPolynomialModuleVector(
            syzygies.module,
            [algebraPolynomialSubtract(zero, y), x, zero]
        );
        const expectedRedundant = algebraPolynomialModuleVector(
            syzygies.module,
            [negativeOne, negativeOne, one]
        );
        assert.equal(
            algebraPolynomialModuleMembership(
                expectedKoszul,
                syzygies.basis
            ).member,
            true
        );
        assert.equal(
            algebraPolynomialModuleMembership(
                expectedRedundant,
                syzygies.basis
            ).member,
            true
        );
        syzygies.basis.basis.forEach(relation => assert.ok(
            algebraPolynomialModuleEquals(
                algebraPolynomialModuleCombination(
                    columns,
                    relation.components
                ),
                algebraPolynomialModuleZero(target)
            )
        ));
        assert.ok(Object.isFrozen(syzygies));
        assert.ok(Object.isFrozen(syzygies.rawGenerators));
    });

    it('retains zero and redundant original-column relations', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const negativeOne = algebraPolynomialSubtract(zero, one);
        const target = algebraPolynomialFreeModule(ring, 1);
        const syzygies = algebraPolynomialModuleOriginalSyzygies(
            algebraPolynomialSubmodule(target, [
                algebraPolynomialModuleVector(target, [x]),
                algebraPolynomialModuleVector(target, [x]),
                algebraPolynomialModuleVector(target, [zero])
            ])
        );
        const duplicate = algebraPolynomialModuleVector(
            syzygies.module,
            [one, negativeOne, zero]
        );
        const zeroColumn = algebraPolynomialModuleVector(
            syzygies.module,
            [zero, zero, one]
        );
        assert.equal(
            algebraPolynomialModuleMembership(duplicate, syzygies.basis).member,
            true
        );
        assert.equal(
            algebraPolynomialModuleMembership(zeroColumn, syzygies.basis).member,
            true
        );
    });

    it('returns rank-zero syzygies for independent and empty columns', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const target = algebraPolynomialFreeModule(ring, 2);
        const independent = algebraPolynomialModuleOriginalSyzygies(
            algebraPolynomialSubmodule(target, [
                algebraPolynomialModuleVector(target, [one, zero]),
                algebraPolynomialModuleVector(target, [zero, one])
            ])
        );
        assert.equal(independent.module.rank, 2);
        assert.equal(independent.basis.basis.length, 0);
        const empty = algebraPolynomialModuleOriginalSyzygies(
            algebraPolynomialSubmodule(target, [])
        );
        assert.equal(empty.module.rank, 0);
        assert.equal(empty.basis.basis.length, 0);
    });

    it('enforces field, module, divisor, basis, and cancellation gates', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const module = algebraPolynomialFreeModule(ring, 2, 'position-over-term');
        const first = algebraPolynomialModuleVector(module, [x, y]);
        const second = algebraPolynomialModuleVector(module, [y, zero]);
        const submodule = algebraPolynomialSubmodule(module, [first, second]);
        assert.throws(
            () => algebraPolynomialModuleGroebnerBasis(submodule, {
                maximumBasisSize: 2
            }),
            moduleError('MODULE_LIMIT_EXCEEDED')
        );
        assert.throws(
            () => algebraPolynomialModuleGroebnerBasis(submodule, {
                context: { cancellation: { requested: () => true } }
            }),
            moduleError('CANCELLED')
        );
        assert.throws(
            () => algebraPolynomialModuleOriginalSyzygies(submodule, {
                context: { cancellation: { requested: () => true } }
            }),
            moduleError('CANCELLED')
        );
        const incomplete = algebraPolynomialModuleGroebnerBasis(submodule);
        assert.throws(
            () => algebraPolynomialModuleSchreyerSyzygies({
                ...incomplete,
                basis: incomplete.basis.slice(0, 2),
                transformations: incomplete.transformations.slice(0, 2)
            }),
            moduleError('INVALID_GROEBNER_BASIS')
        );
        assert.throws(
            () => algebraPolynomialModuleDivide(first, [
                algebraPolynomialModuleZero(module)
            ]),
            moduleError('ZERO_DIVISOR')
        );
        const other = algebraPolynomialFreeModule(ring, 2, 'term-over-position');
        assert.throws(
            () => algebraPolynomialModuleAdd(
                first,
                algebraPolynomialModuleVector(other, [x, zero])
            ),
            moduleError('FOREIGN_FREE_MODULE')
        );

        const integerRing = algebraPolynomialRing(INTEGER_DOMAIN, ['x'], 'lex');
        const integerModule = algebraPolynomialFreeModule(integerRing, 1);
        const integerX = algebraPolynomialVariable(integerRing, 0);
        assert.throws(
            () => algebraPolynomialModuleGroebnerBasis(
                algebraPolynomialSubmodule(integerModule, [
                    algebraPolynomialModuleVector(integerModule, [integerX])
                ])
            ),
            moduleError('NON_FIELD_COEFFICIENTS')
        );
        assert.throws(
            () => algebraPolynomialModuleOriginalSyzygies(
                algebraPolynomialSubmodule(integerModule, [
                    algebraPolynomialModuleVector(integerModule, [integerX])
                ])
            ),
            moduleError('NON_FIELD_COEFFICIENTS')
        );
    });
});
