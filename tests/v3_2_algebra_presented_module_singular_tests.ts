/** Focused PAM-ORACLE-9A injected and real Singular module comparisons. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import {
    ALGEBRA_PRESENTED_MODULE_SINGULAR_PROFILE,
    algebraPresentedModuleZeroOperation,
    comparePresentedModuleZeroWithSingular,
    singularPresentedModuleZeroScript
} from '../src/v3_2/algebra_presented_module_singular';
import {
    AlgebraOracleProcessRequest,
    AlgebraOracleTransport
} from '../src/v3_2/algebra_oracle';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const free = algebraPresentedAlgebraFreeModule(algebra, 1);
    const module = algebraPresentedAlgebraModule(free, [
        algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(quotient, x)
        ])
    ]);
    const zeroVector = algebraPresentedAlgebraModuleVector(free, [
        algebraQuotientElement(quotient, x)
    ]);
    const nonzeroVector = algebraPresentedAlgebraModuleBasisVector(free, 0);
    return {
        ring,
        x,
        quotient,
        algebra,
        free,
        module,
        zeroVector,
        nonzeroVector,
        bundle: algebraPresentedModuleZeroOperation(module)
    };
};

const transport = (
    marker: 0 | 1,
    capture?: (request: AlgebraOracleProcessRequest) => void
): AlgebraOracleTransport => ({
    async execute(request) {
        capture?.(request);
        return {
            exitCode: 0,
            stdout: `noise\nEMDASH_MODULE_ZERO:${marker}\n`,
            stderr: ''
        };
    }
});

describe('v3.2 Singular presented-module differential comparison', () => {
    it('agrees with native zero and nonzero module reductions', async () => {
        const value = fixture();
        const zero = await comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.zeroVector,
            transport(1)
        );
        const nonzero = await comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.nonzeroVector,
            transport(0)
        );
        assert.equal(zero.native.zero, true);
        assert.equal(zero.oracle.zero, true);
        assert.equal(zero.agrees, true);
        assert.equal(nonzero.native.zero, false);
        assert.equal(nonzero.oracle.zero, false);
        assert.equal(nonzero.agrees, true);
        assert.equal(zero.native.provider, 'native-typescript');
        assert.equal(zero.oracle.provider, 'singular-oracle');
    });

    it('retains disagreement without replacing the native decision', async () => {
        const value = fixture();
        const comparison = await comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.zeroVector,
            transport(0)
        );
        assert.equal(comparison.native.zero, true);
        assert.equal(comparison.oracle.zero, false);
        assert.equal(comparison.agrees, false);
        assert.equal(ALGEBRA_PRESENTED_MODULE_SINGULAR_PROFILE.authority,
            'non-authoritative-differential-comparison');
    });

    it('builds one deterministic position-aware module script', () => {
        const value = fixture();
        const first = singularPresentedModuleZeroScript(
            value.module,
            value.zeroVector
        );
        const second = singularPresentedModuleZeroScript(
            value.module,
            value.zeroVector
        );
        assert.equal(first, second);
        assert.match(first, /module emdash_m = \[1\*x\];/u);
        assert.match(first, /vector emdash_v = \[1\*x\];/u);
        assert.match(first, /reduce\(emdash_v,emdash_g\)/u);
        assert.match(first, /EMDASH_MODULE_ZERO:1/u);
    });

    it('retains the exact bounded shell-free process request', async () => {
        const value = fixture();
        let request: AlgebraOracleProcessRequest | undefined;
        await comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.zeroVector,
            transport(1, candidate => {
                request = candidate;
            })
        );
        assert.equal(request!.executable, 'Singular');
        assert.deepEqual(request!.args, ['-q']);
        assert.equal(request!.timeoutMilliseconds, 30_000);
        assert.equal(request!.maximumOutputBytes, 1_000_000);
    });

    it('rejects malformed and failed external results', async () => {
        const value = fixture();
        await assert.rejects(comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.zeroVector,
            {
                async execute() {
                    return { exitCode: 0, stdout: 'missing marker', stderr: '' };
                }
            }
        ));
        await assert.rejects(comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.zeroVector,
            {
                async execute() {
                    return { exitCode: 2, stdout: '', stderr: 'oracle failed' };
                }
            }
        ));
    });

    it('checks both decisions against the installed Singular executable', {
        skip: process.env.EMDASH_RUN_SINGULAR_MODULE_ORACLE !== '1'
    }, async () => {
        const value = fixture();
        const node = createAlgebraOracleNodeTransport();
        const zero = await comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.zeroVector,
            node
        );
        const nonzero = await comparePresentedModuleZeroWithSingular(
            value.bundle,
            value.nonzeroVector,
            node
        );
        assert.equal(zero.agrees, true);
        assert.equal(nonzero.agrees, true);
    });

    it('serializes the rank-zero case as the unique zero vector', () => {
        const value = fixture();
        const free = algebraPresentedAlgebraFreeModule(value.algebra, 0);
        const module = algebraPresentedAlgebraModule(free, []);
        const vector = algebraPresentedAlgebraModuleVector(free, []);
        const script = singularPresentedModuleZeroScript(module, vector);
        assert.match(script, /EMDASH_MODULE_ZERO:1/u);
        assert.doesNotMatch(script, /module emdash_m/u);
    });
});
