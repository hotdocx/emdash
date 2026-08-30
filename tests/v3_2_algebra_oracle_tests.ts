/** Focused CAS-ORACLE-9A differential-oracle tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    ALGEBRA_ORACLE_PROFILE,
    AlgebraOracleError,
    AlgebraOracleProcessRequest,
    AlgebraOracleTransport,
    algebraRadicalMembershipOperation,
    compareRadicalMembershipWithSingular,
    singularRadicalMembershipScript
} from '../src/v3_2/algebra_oracle';
import {
    ALGEBRA_ORACLE_NODE_PROFILE,
    createAlgebraOracleNodeTransport
} from '../src/v3_2/algebra_oracle_node';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const ideal = algebraPolynomialIdeal(ring, [algebraPolynomialPower(x, 2n)]);
    return {
        ring,
        x,
        input: { ideal, element: x },
        bundle: algebraRadicalMembershipOperation(ring)
    };
};

const transport = (
    output: string,
    capture?: (request: AlgebraOracleProcessRequest) => void
): AlgebraOracleTransport => ({
    async execute(request) {
        capture?.(request);
        return { exitCode: 0, stdout: output, stderr: '' };
    }
});

describe('v3.2 Singular differential oracle', () => {
    it('agrees with the native radical-membership consumer', async () => {
        const { input, bundle } = fixture();
        let request: AlgebraOracleProcessRequest | undefined;
        const comparison = await compareRadicalMembershipWithSingular(
            bundle,
            input,
            transport('noise\nEMDASH_RADICAL_MEMBER:1\n', value => {
                request = value;
            })
        );
        assert.equal(comparison.native.member, true);
        assert.equal(comparison.native.provider, 'native-typescript');
        assert.equal(comparison.oracle.member, true);
        assert.equal(comparison.oracle.provider, 'singular-oracle');
        assert.equal(comparison.agrees, true);
        assert.equal(request!.executable, 'Singular');
        assert.deepEqual(request!.args, ['-q']);
        assert.match(request!.stdin, /1-emdash_t\*imap\(emdash_r,emdash_f\)/u);
        assert.equal(ALGEBRA_ORACLE_PROFILE.authority,
            'non-authoritative-differential-comparison');
    });

    it('retains a disagreement rather than overriding the native result', async () => {
        const { input, bundle } = fixture();
        const comparison = await compareRadicalMembershipWithSingular(
            bundle,
            input,
            transport('EMDASH_RADICAL_MEMBER:0\n')
        );
        assert.equal(comparison.native.member, true);
        assert.equal(comparison.oracle.member, false);
        assert.equal(comparison.agrees, false);
    });

    it('rejects malformed and failed external results', async () => {
        const { input, bundle } = fixture();
        await assert.rejects(
            compareRadicalMembershipWithSingular(
                bundle,
                input,
                transport('no marker\n')
            )
        );
        await assert.rejects(
            compareRadicalMembershipWithSingular(bundle, input, {
                async execute() {
                    return { exitCode: 2, stdout: '', stderr: 'oracle failed' };
                }
            })
        );
    });

    it('builds deterministic scripts without invoking a process', () => {
        const { input } = fixture();
        const first = singularRadicalMembershipScript(input);
        const second = singularRadicalMembershipScript(input);
        assert.equal(first, second);
        assert.match(first, /ring emdash_e = 0,\(emdash_t,x\),lp;/u);
        assert.match(first, /EMDASH_RADICAL_MEMBER:1/u);
    });

    it('keeps Node process transport opt-in and shell-free', async () => {
        assert.equal(ALGEBRA_ORACLE_NODE_PROFILE.optIn, true);
        assert.equal(ALGEBRA_ORACLE_NODE_PROFILE.shell, false);
        await assert.rejects(
            createAlgebraOracleNodeTransport().execute({
                executable: 'emdash-definitely-missing-oracle-executable',
                args: [],
                stdin: '',
                timeoutMilliseconds: 1000,
                maximumOutputBytes: 1024
            }),
            (error: unknown) => {
                assert.ok(error instanceof AlgebraOracleError);
                assert.equal(error.code, 'PROCESS_FAILED');
                return true;
            }
        );
    });
});
