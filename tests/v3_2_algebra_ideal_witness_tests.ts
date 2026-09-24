import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraGroebnerBasis, algebraIdealMembership, algebraPolynomialIdeal
} from '../src/v3_2/algebra_ideal';
import {
    AlgebraMonomialOrder, algebraPolynomial, algebraPolynomialMultiply,
    algebraPolynomialNegate, algebraPolynomialOne, algebraPolynomialPower,
    algebraPolynomialRing, algebraPolynomialSubtract, algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraIdealWitnessSource, checkAlgebraIdealWitness
} from '../src/v3_2/algebra_ideal_witness';
import {
    computeSingularIdealWitness, parseSingularIdealWitness, singularIdealWitnessScript
} from '../src/v3_2/algebra_ideal_singular';
import { AlgebraOracleTransport } from '../src/v3_2/algebra_oracle';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';

const fixture = (order: AlgebraMonomialOrder = 'lex') => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], order);
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const one = algebraPolynomialOne(ring);
    return { ring, x, y, one, input: {
        ideal: algebraPolynomialIdeal(ring, [
            algebraPolynomialSubtract(y, algebraPolynomialPower(x, 2n)),
            algebraPolynomialSubtract(algebraPolynomialMultiply(x, y), one)
        ]),
        polynomial: algebraPolynomialSubtract(algebraPolynomialPower(x, 3n), one)
    } };
};

const output = (term = '-1') => [
    'EMDASH_WITNESS_V1', 'VERSION:4330', 'MEMBER:1', 'COEFFICIENT:0',
    `TERM:${term}:1,0`, 'END_COEFFICIENT', 'COEFFICIENT:1', 'TERM:1:0,0',
    'END_COEFFICIENT', 'END_WITNESS', ''
].join('\n');
const injected = (stdout = output()): AlgebraOracleTransport => ({
    async execute() { return { stdout, stderr: '', exitCode: 0 }; }
});

describe('source-bound ideal witnesses and Singular exchange', () => {
    it('checks native and independently supplied coefficients against original generators', () => {
        const { input, x, one } = fixture();
        const native = algebraIdealMembership(input.polynomial, algebraGroebnerBasis(input.ideal));
        assert.equal(native.member, true);
        const source = algebraIdealWitnessSource(input);
        checkAlgebraIdealWitness(input, { source, coefficients: native.coefficients });
        const checked = checkAlgebraIdealWitness(input, {
            source, coefficients: [algebraPolynomialNegate(x), one]
        });
        assert.equal(checked.authority, 'exact-polynomial-arithmetic');
        assert.ok(Object.isFrozen(checked.coefficients));
    });

    it('rejects changed queries, ordered generators, monomial orders and coefficients', () => {
        const { input, x, one } = fixture();
        const witness = { source: algebraIdealWitnessSource(input),
            coefficients: [algebraPolynomialNegate(x), one] };
        assert.throws(() => checkAlgebraIdealWitness({ ...input, polynomial: one }, witness),
            /exact ordered generators and query/u);
        assert.throws(() => checkAlgebraIdealWitness({ ...input,
            ideal: algebraPolynomialIdeal(input.ideal.ring, [...input.ideal.generators].reverse())
        }, witness), /exact ordered generators and query/u);
        assert.throws(() => checkAlgebraIdealWitness(fixture('grevlex').input, witness),
            /exact ordered generators and query/u);
        assert.throws(() => checkAlgebraIdealWitness(input, { ...witness, coefficients: [x, one] }),
            /does not equal/u);
        assert.throws(() => checkAlgebraIdealWitness(input, { ...witness, coefficients: [one] }),
            /One coefficient/u);
        const foreign = algebraPolynomialOne(algebraPolynomialRing(RATIONAL_DOMAIN, ['z']));
        assert.throws(() => checkAlgebraIdealWitness(input, {
            ...witness, coefficients: [foreign, one]
        }), /ring|parent/iu);
        assert.throws(() => singularIdealWitnessScript({ ...input, polynomial: foreign }),
            /ring|parent/iu);
    });

    it('rejects altered, truncated, ambiguous and malformed external replies', () => {
        const { input } = fixture();
        const parsed = parseSingularIdealWitness(input, output());
        assert.equal(parsed.kind, 'witness');
        for (const text of [output('1'), output().replace('END_WITNESS', ''),
            output() + 'MEMBER:0\n', output().replace('1,0', '1'),
            output().replace('1,0', '4097,0'), output().replace('TERM:1:', 'TERM:1/0:')]) {
            assert.throws(() => parseSingularIdealWitness(input, text));
        }
    });

    it('keeps a negative answer an uncertified observation', () => {
        const parsed = parseSingularIdealWitness(fixture().input,
            'EMDASH_WITNESS_V1\nVERSION:4330\nMEMBER:0\nEND_WITNESS\n');
        assert.equal(parsed.kind, 'nonmembership-observation');
        assert.equal('witness' in parsed, false);
    });

    it('retains bounded transport and rejects failure or cancellation before/after execution', async () => {
        const { input } = fixture();
        const result = await computeSingularIdealWitness(input, injected());
        assert.equal(result.kind, 'witness');
        assert.equal(result.request.timeoutMilliseconds, 30_000);
        assert.equal(result.request.maximumOutputBytes, 1_000_000);
        assert.deepEqual(result.request.args, ['-q', '--no-rc']);
        await assert.rejects(computeSingularIdealWitness(input, {
            async execute() { return { stdout: output(), stderr: 'failure', exitCode: 1 }; }
        }), /failure/u);
        let called = false;
        await assert.rejects(computeSingularIdealWitness(input, {
            async execute() { called = true; return injected().execute(result.request); }
        }, { context: { cancellation: { requested: () => true } } }), /cancelled/u);
        assert.equal(called, false);
        await assert.rejects(computeSingularIdealWitness(input, {
            async execute() { called = true; return injected().execute(result.request); }
        }, { context: { cancellation: { requested: () => called } } }), /cancelled/u);
    });

    it('renames even reserved variable names by position without changing the parent', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['ring', 'emdash_i'], 'grlex');
        const polynomial = algebraPolynomialVariable(ring, 0);
        const input = { ideal: algebraPolynomialIdeal(ring, [polynomial]), polynomial };
        const script = singularIdealWitnessScript(input);
        assert.match(script, /ring emdash_r=0,\(v1,v2\),Dp;/u);
        assert.doesNotMatch(script, /\(ring,emdash_i\)/u);
        assert.match(algebraIdealWitnessSource(input), /emdash_i/u);
    });

    it('enforces the reused Node transport timeout and output bound on real child processes', async () => {
        const transport = createAlgebraOracleNodeTransport();
        await assert.rejects(transport.execute({
            executable: process.execPath, args: ['-e', 'setTimeout(() => {}, 10000)'],
            stdin: '', timeoutMilliseconds: 100, maximumOutputBytes: 1024
        }), /timeout/u);
        await assert.rejects(transport.execute({
            executable: process.execPath, args: ['-e', 'process.stdout.write("x".repeat(4096))'],
            stdin: '', timeoutMilliseconds: 5000, maximumOutputBytes: 128
        }), /byte limit/u);
    });

    it('round-trips actual Singular witnesses, rational coefficients, zeros and negatives', {
        skip: process.env.EMDASH_RUN_SINGULAR_WORKBENCH !== '1'
    }, async () => {
        const transport = createAlgebraOracleNodeTransport();
        for (const order of ['lex', 'grlex', 'grevlex'] as const) {
            const { input } = fixture(order);
            const result = await computeSingularIdealWitness(input, transport);
            assert.equal(result.kind, 'witness');
            if (result.kind === 'witness') checkAlgebraIdealWitness(input, result.witness);
        }
        const { ring, x, one } = fixture();
        const halfX = algebraPolynomial(ring, [{ coefficient: '1/2', exponents: [1n, 0n] }]);
        const rational = await computeSingularIdealWitness({
            ideal: algebraPolynomialIdeal(ring, [x]), polynomial: halfX
        }, transport);
        assert.equal(rational.kind, 'witness');
        const zero = algebraPolynomialZero(ring);
        for (const generators of [[], [zero], [x, zero]]) {
            const result = await computeSingularIdealWitness({
                ideal: algebraPolynomialIdeal(ring, generators), polynomial: zero
            }, transport);
            assert.equal(result.kind, 'witness');
        }
        const negative = await computeSingularIdealWitness({
            ideal: algebraPolynomialIdeal(ring, [x]), polynomial: one
        }, transport);
        assert.equal(negative.kind, 'nonmembership-observation');
    });
});
