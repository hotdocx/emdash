/** Focused injected and real Singular weak-kernel span comparisons. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialAdd,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapZero
} from '../src/v3_2/algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapWeakKernel
} from '../src/v3_2/algebra_polynomial_weak_kernel';
import {
    ALGEBRA_POLYNOMIAL_WEAK_KERNEL_SINGULAR_PROFILE,
    comparePolynomialWeakKernelWithSingular,
    singularPolynomialWeakKernelComparisonScript
} from '../src/v3_2/algebra_polynomial_weak_kernel_singular';
import {
    AlgebraOracleProcessRequest,
    AlgebraOracleTransport
} from '../src/v3_2/algebra_oracle';
import { createAlgebraOracleNodeTransport } from '../src/v3_2/algebra_oracle_node';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const source = algebraPolynomialFreeModule(ring, 3);
    const target = algebraPolynomialFreeModule(ring, 1);
    const map = algebraPolynomialModuleMap(source, target, [
        algebraPolynomialModuleVector(target, [x]),
        algebraPolynomialModuleVector(target, [y]),
        algebraPolynomialModuleVector(target, [algebraPolynomialAdd(x, y)])
    ]);
    return { ring, source, target, map,
        weakKernel: algebraPolynomialModuleMapWeakKernel(map) };
};

const transport = (
    nativeInOracle: 0 | 1,
    oracleInNative: 0 | 1,
    oracleCount: number,
    capture?: (request: AlgebraOracleProcessRequest) => void
): AlgebraOracleTransport => ({
    async execute(request) {
        capture?.(request);
        return {
            exitCode: 0,
            stdout: [
                `EMDASH_NATIVE_IN_ORACLE:${nativeInOracle}`,
                `EMDASH_ORACLE_IN_NATIVE:${oracleInNative}`,
                `EMDASH_ORACLE_COUNT:${oracleCount}`
            ].join('\n') + '\n',
            stderr: ''
        };
    }
});

describe('v3.2 Singular polynomial weak-kernel differential comparison', () => {
    it('retains bidirectional span agreement and disagreement', async () => {
        const value = fixture();
        const agreement = await comparePolynomialWeakKernelWithSingular(
            value.weakKernel,
            transport(1, 1, 2)
        );
        assert.equal(agreement.agrees, true);
        assert.equal(agreement.nativeInOracle, true);
        assert.equal(agreement.oracleInNative, true);
        assert.equal(agreement.oracleGeneratorCount, 2);
        const disagreement = await comparePolynomialWeakKernelWithSingular(
            value.weakKernel,
            transport(1, 0, 3)
        );
        assert.equal(disagreement.agrees, false);
        assert.equal(disagreement.nativeInOracle, true);
        assert.equal(disagreement.oracleInNative, false);
        assert.equal(
            ALGEBRA_POLYNOMIAL_WEAK_KERNEL_SINGULAR_PROFILE.authority,
            'non-authoritative-differential-comparison'
        );
    });

    it('builds a deterministic bidirectional module-span script', () => {
        const value = fixture();
        const first = singularPolynomialWeakKernelComparisonScript(
            value.weakKernel
        );
        const second = singularPolynomialWeakKernelComparisonScript(
            value.weakKernel
        );
        assert.equal(first, second);
        assert.match(first,
            /module emdash_f = \[1\*x\],\[1\*y\],\[1\*x \+ 1\*y\];/u);
        assert.match(first, /module emdash_s = syz\(emdash_f\);/u);
        assert.match(first, /reduce\(emdash_n\[emdash_i\],emdash_gs\)/u);
        assert.match(first, /reduce\(emdash_s\[emdash_i\],emdash_gn\)/u);
    });

    it('retains one bounded shell-free process request', async () => {
        const value = fixture();
        let request: AlgebraOracleProcessRequest | undefined;
        await comparePolynomialWeakKernelWithSingular(
            value.weakKernel,
            transport(1, 1, 2, candidate => {
                request = candidate;
            })
        );
        assert.equal(request!.executable, 'Singular');
        assert.deepEqual(request!.args, ['-q']);
        assert.equal(request!.timeoutMilliseconds, 30_000);
        assert.equal(request!.maximumOutputBytes, 1_000_000);
    });

    it('rejects malformed and failed oracle output', async () => {
        const value = fixture();
        await assert.rejects(comparePolynomialWeakKernelWithSingular(
            value.weakKernel,
            { async execute() {
                return { exitCode: 0, stdout: 'missing', stderr: '' };
            } }
        ));
        await assert.rejects(comparePolynomialWeakKernelWithSingular(
            value.weakKernel,
            { async execute() {
                return { exitCode: 2, stdout: '', stderr: 'failed' };
            } }
        ));
    });

    it('serializes source-rank-zero and target-rank-zero boundaries', () => {
        const value = fixture();
        const empty = algebraPolynomialFreeModule(value.ring, 0);
        const emptyMap = algebraPolynomialModuleMapZero(empty, value.target);
        const emptyScript = singularPolynomialWeakKernelComparisonScript(
            algebraPolynomialModuleMapWeakKernel(emptyMap)
        );
        assert.match(emptyScript, /EMDASH_ORACLE_COUNT:0/u);
        assert.doesNotMatch(emptyScript, /syz\(/u);
        const zeroTarget = algebraPolynomialFreeModule(value.ring, 0);
        const zeroTargetMap = algebraPolynomialModuleMapZero(
            value.source,
            zeroTarget
        );
        const zeroTargetScript = singularPolynomialWeakKernelComparisonScript(
            algebraPolynomialModuleMapWeakKernel(zeroTargetMap)
        );
        assert.match(zeroTargetScript, /module emdash_s = \[1,0,0\],\[0,1,0\],\[0,0,1\];/u);
        assert.doesNotMatch(zeroTargetScript, /syz\(/u);
        assert.equal(algebraPolynomialModuleMapIdentity(value.source).columns.length, 3);
    });

    it('agrees with the installed Singular executable', {
        skip: process.env.EMDASH_RUN_SINGULAR_WEAK_KERNEL_ORACLE !== '1'
    }, async () => {
        const value = fixture();
        const comparison = await comparePolynomialWeakKernelWithSingular(
            value.weakKernel,
            createAlgebraOracleNodeTransport()
        );
        assert.equal(comparison.agrees, true);
    });
});
