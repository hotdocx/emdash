/** Focused CAS-IDEAL-3A ideal and Buchberger tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraEngineError,
    computeAlgebraOperation
} from '../src/v3_2/algebra_engine';
import {
    INTEGER_DOMAIN,
    RATIONAL_DOMAIN,
    algebraRationalText
} from '../src/v3_2/algebra_exact';
import {
    ALGEBRA_IDEAL_PROFILE,
    AlgebraIdealError,
    algebraGroebnerBasis,
    algebraGroebnerBasisSchema,
    algebraIdealCombination,
    algebraIdealMembership,
    algebraIdealMembershipSchema,
    algebraPolynomialIdeal,
    algebraPolynomialIdealSchema,
    algebraPolynomialSPolynomial,
    algebraReducedGroebnerBasis,
    serializeAlgebraGroebnerBasis,
    serializeAlgebraPolynomialIdeal,
    validateAlgebraGroebnerBasis,
    validateAlgebraIdealMembership
} from '../src/v3_2/algebra_ideal';
import {
    algebraIdealReferenceOperations
} from '../src/v3_2/algebra_ideal_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import {
    algebraPolynomialAdd,
    algebraPolynomialConstant,
    algebraPolynomialDivide,
    algebraPolynomialEquals,
    algebraPolynomialLeadingTerm,
    algebraPolynomialMultiply,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialText,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    createAlgebraTypeScriptReferenceEngine
} from '../src/v3_2/algebra_reference_engine';

const idealError = (
    expected: AlgebraIdealError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraIdealError);
    assert.equal(error.code, expected);
    return true;
};

const fixture = () => {
    const ring = algebraPolynomialRing(
        RATIONAL_DOMAIN,
        ['x', 'y'],
        'lex'
    );
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const one = algebraPolynomialConstant(ring, '1');
    const f1 = algebraPolynomialSubtract(algebraPolynomialPower(x, 2n), y);
    const f2 = algebraPolynomialSubtract(algebraPolynomialMultiply(x, y), one);
    const ideal = algebraPolynomialIdeal(ring, [f1, f2]);
    return { ring, x, y, one, f1, f2, ideal };
};

const assertTransformations = (basis: ReturnType<typeof algebraGroebnerBasis>) => {
    basis.basis.forEach((polynomial, index) => {
        const reconstructed = algebraIdealCombination(
            basis.ideal,
            basis.transformations[index]
        );
        assert.ok(algebraPolynomialEquals(reconstructed, polynomial));
    });
};

const assertBuchbergerPairs = (basis: ReturnType<typeof algebraGroebnerBasis>) => {
    for (let right = 1; right < basis.basis.length; right++) {
        for (let left = 0; left < right; left++) {
            const s = algebraPolynomialSPolynomial(
                basis.basis[left],
                basis.basis[right]
            );
            const division = algebraPolynomialDivide(s, basis.basis);
            assert.equal(
                algebraPolynomialText(division.remainder),
                '0',
                `S-pair ${left},${right} did not reduce to zero`
            );
        }
    }
};

describe('v3.2 focused polynomial ideals and Buchberger reference', () => {
    it('retains ordered normalized generators and rejects foreign rings', () => {
        const { ring, f1, f2, ideal } = fixture();
        assert.deepEqual(ideal.generators, [f1, f2]);
        assert.ok(Object.isFrozen(ideal));
        assert.ok(Object.isFrozen(ideal.generators));
        const other = algebraPolynomialRing(
            RATIONAL_DOMAIN,
            ['x', 'y'],
            'grevlex'
        );
        assert.throws(
            () => algebraPolynomialIdeal(other, [f1 as never]),
            idealError('FOREIGN_POLYNOMIAL_RING')
        );
        assert.equal(
            algebraPolynomialIdealSchema(ring).normalize(ideal, 'ideal').kind,
            'algebra-polynomial-ideal'
        );
    });

    it('computes a monic Groebner basis and retained generator transformations', () => {
        const { ideal } = fixture();
        const progress: number[] = [];
        const basis = algebraGroebnerBasis(ideal, {
            context: {
                onProgress: event => progress.push(event.completed)
            }
        });
        assert.ok(basis.basis.length >= ideal.generators.length);
        assert.ok(basis.pairsProcessed > 0);
        assert.ok(basis.reductionSteps > 0);
        assert.equal(basis.reduced, false);
        basis.basis.forEach(polynomial => {
            assert.equal(
                algebraRationalText(
                    algebraPolynomialLeadingTerm(polynomial)!.coefficient
                ),
                '1'
            );
        });
        assert.equal(progress.length, basis.pairsProcessed);
        assertTransformations(basis);
        assertBuchbergerPairs(basis);
        assert.ok(Object.isFrozen(basis));
        assert.ok(Object.isFrozen(basis.basis));
        assert.ok(Object.isFrozen(basis.transformations));
    });

    it('interreduces the basis without losing transformation rows', () => {
        const { ideal } = fixture();
        const basis = algebraGroebnerBasis(ideal);
        const reduced = algebraReducedGroebnerBasis(basis);
        assert.equal(reduced.reduced, true);
        assert.ok(reduced.basis.length <= basis.basis.length);
        assertTransformations(reduced);
        assertBuchbergerPairs(reduced);
        reduced.basis.forEach(polynomial => {
            assert.equal(
                algebraRationalText(
                    algebraPolynomialLeadingTerm(polynomial)!.coefficient
                ),
                '1'
            );
        });
    });

    it('returns membership coefficients reconstructing a positive target', () => {
        const { ideal, x, y, f1, f2 } = fixture();
        const coefficient1 = algebraPolynomialAdd(x, y);
        const coefficient2 = y;
        const target = algebraPolynomialAdd(
            algebraPolynomialMultiply(coefficient1, f1),
            algebraPolynomialMultiply(coefficient2, f2)
        );
        const basis = algebraReducedGroebnerBasis(algebraGroebnerBasis(ideal));
        const membership = algebraIdealMembership(target, basis);
        assert.equal(membership.member, true);
        assert.equal(algebraPolynomialText(membership.remainder), '0');
        const reconstructed = algebraPolynomialAdd(
            algebraIdealCombination(ideal, membership.coefficients),
            membership.remainder
        );
        assert.ok(algebraPolynomialEquals(reconstructed, target));
        assert.equal(membership.coefficients.length, ideal.generators.length);
        assert.equal(membership.basisQuotients.length, basis.basis.length);
        assert.ok(Object.isFrozen(membership));
        assert.ok(Object.isFrozen(membership.coefficients));
    });

    it('returns a canonical nonzero remainder for nonmembership', () => {
        const { ideal, y } = fixture();
        const basis = algebraReducedGroebnerBasis(algebraGroebnerBasis(ideal));
        const membership = algebraIdealMembership(y, basis);
        assert.equal(membership.member, false);
        assert.notEqual(algebraPolynomialText(membership.remainder), '0');
        const reconstructed = algebraPolynomialAdd(
            algebraIdealCombination(ideal, membership.coefficients),
            membership.remainder
        );
        assert.ok(algebraPolynomialEquals(reconstructed, y));
    });

    it('handles the zero ideal and empty Groebner basis', () => {
        const { ring, x } = fixture();
        const ideal = algebraPolynomialIdeal(ring, []);
        const basis = algebraGroebnerBasis(ideal);
        assert.equal(basis.basis.length, 0);
        assert.equal(algebraIdealMembership(
            algebraPolynomialZero(ring),
            basis
        ).member, true);
        const nonzero = algebraIdealMembership(x, basis);
        assert.equal(nonzero.member, false);
        assert.ok(algebraPolynomialEquals(nonzero.remainder, x));
    });

    it('enforces field, pair, basis, total-reduction, and cancellation gates', () => {
        const { ideal } = fixture();
        assert.throws(
            () => algebraGroebnerBasis(ideal, { maximumPairs: 1 }),
            idealError('IDEAL_LIMIT_EXCEEDED')
        );
        assert.throws(
            () => algebraGroebnerBasis(ideal, { maximumBasisSize: 2 }),
            idealError('IDEAL_LIMIT_EXCEEDED')
        );
        assert.throws(
            () => algebraGroebnerBasis(ideal, {
                maximumTotalReductionSteps: 1
            }),
            idealError('IDEAL_LIMIT_EXCEEDED')
        );
        assert.throws(
            () => algebraGroebnerBasis(ideal, {
                context: {
                    cancellation: {
                        requested: () => true,
                        reason: () => 'cancelled by ideal test'
                    }
                }
            }),
            idealError('CANCELLED')
        );

        const integerRing = algebraPolynomialRing(
            INTEGER_DOMAIN,
            ['x'],
            'lex'
        );
        const integerIdeal = algebraPolynomialIdeal(integerRing, [
            algebraPolynomialVariable(integerRing, 0)
        ]);
        assert.throws(
            () => algebraGroebnerBasis(integerIdeal),
            idealError('NON_FIELD_COEFFICIENTS')
        );
    });

    it('normalizes result schemas and rejects transformation shape drift', () => {
        const { ring, ideal, x } = fixture();
        const basis = algebraGroebnerBasis(ideal);
        const basisSchema = algebraGroebnerBasisSchema(ring);
        const normalized = basisSchema.normalize(basis, 'basis');
        assertTransformations(normalized);
        assert.ok(validateAlgebraGroebnerBasis(ring, normalized));

        const membership = algebraIdealMembership(x, basis);
        const membershipSchema = algebraIdealMembershipSchema(ring);
        const normalizedMembership = membershipSchema.normalize(
            membership,
            'membership'
        );
        assert.ok(validateAlgebraIdealMembership(ring, normalizedMembership));

        assert.throws(
            () => basisSchema.normalize({
                ...basis,
                transformations: []
            }, 'basis'),
            error => {
                assert.ok(error instanceof Error);
                return true;
            }
        );
    });

    it('serializes generators, bases, and transformations deterministically', () => {
        const { ideal } = fixture();
        const basis = algebraReducedGroebnerBasis(algebraGroebnerBasis(ideal));
        const idealJson = JSON.parse(serializeAlgebraPolynomialIdeal(ideal));
        const basisText = serializeAlgebraGroebnerBasis(basis);
        const basisJson = JSON.parse(basisText);
        assert.equal(
            idealJson.serializationRevision,
            ALGEBRA_IDEAL_PROFILE.serializationRevision
        );
        assert.equal(idealJson.generators.length, 2);
        assert.equal(basisJson.basis.length, basis.basis.length);
        assert.equal(
            basisJson.transformations.length,
            basis.transformations.length
        );
        assert.equal(basisJson.reduced, true);
        assert.ok(basisText.endsWith('\n'));
    });

    it('executes Groebner, reduction, and membership through engine operations', async () => {
        const { ring, ideal, x, y, f1, f2 } = fixture();
        const operations = algebraIdealReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const basisResult = await computeAlgebraOperation({
            engine,
            operation: operations.groebner,
            input: ideal,
            context: {
                limits: {
                    fuel: 100,
                    maximumOutputItems: 20,
                    maximumIntermediateItems: 10_000
                }
            }
        });
        const reducedResult = await computeAlgebraOperation({
            engine,
            operation: operations.reduceBasis,
            input: basisResult.value,
            context: { limits: { fuel: 1_000, maximumOutputItems: 20 } }
        });
        const target = algebraPolynomialAdd(
            algebraPolynomialMultiply(x, f1),
            algebraPolynomialMultiply(y, f2)
        );
        const membership = await computeAlgebraOperation({
            engine,
            operation: operations.membership,
            input: {
                polynomial: target,
                basis: reducedResult.value
            },
            context: { limits: { fuel: 1_000 } }
        });
        assert.equal(membership.value.member, true);
        assert.ok(algebraPolynomialEquals(
            algebraIdealCombination(ideal, membership.value.coefficients),
            target
        ));
    });

    it('chains Groebner and reduced-basis nodes in a retained graph', async () => {
        const { ring, ideal } = fixture();
        const operations = algebraIdealReferenceOperations(ring);
        const engine = createAlgebraTypeScriptReferenceEngine({
            implementations: operations.implementations
        });
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.ideal.groebner-pipeline',
            'v1'
        );
        const input = builder.input('ideal', operations.idealSchema);
        const basis = builder.operation('basis', operations.groebner, input);
        const reduced = builder.operation(
            'reduced',
            operations.reduceBasis,
            basis
        );
        const graph = builder.build([{ id: 'result', value: reduced }]);
        const execution = await executeAlgebraComputationGraph({
            graph,
            engine,
            inputs: [{ id: 'ideal', value: ideal }]
        });
        const result = execution.outputs[0].value as ReturnType<
            typeof algebraGroebnerBasis
        >;
        assert.equal(result.reduced, true);
        assertTransformations(result);
        assertBuchbergerPairs(result);

        await assert.rejects(
            computeAlgebraOperation({
                engine,
                operation: operations.groebner,
                input: ideal,
                context: { limits: { fuel: 1 } }
            }),
            error => {
                assert.ok(error instanceof AlgebraEngineError);
                assert.equal(error.code, 'ENGINE_FAILURE');
                return true;
            }
        );
    });
});
