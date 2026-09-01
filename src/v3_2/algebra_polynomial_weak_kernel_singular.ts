/** Non-authoritative Singular span comparison for polynomial weak kernels. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialRing,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPolynomialModuleVector
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialWeakKernel
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraOracleError,
    AlgebraOracleTransport
} from './algebra_oracle';

export const ALGEBRA_POLYNOMIAL_WEAK_KERNEL_SINGULAR_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-weak-kernel-singular-v1' as const,
    authority: 'non-authoritative-differential-comparison' as const,
    comparison: 'bidirectional-syzygy-submodule-span' as const,
    executable: 'Singular' as const,
    nodeBuiltinDependency: false as const,
    performsIo: true as const
});

export interface AlgebraPolynomialWeakKernelSingularComparison {
    readonly kind: 'algebra-polynomial-weak-kernel-singular-comparison';
    readonly weakKernelKind: 'algebra-polynomial-weak-kernel';
    readonly nativeGeneratorCount: number;
    readonly oracleGeneratorCount: number;
    readonly nativeInOracle: boolean;
    readonly oracleInNative: boolean;
    readonly agrees: boolean;
    readonly provider: 'singular-oracle';
}

const singularOrder = (
    ring: AlgebraPolynomialRing<AlgebraParent, AlgebraElement, unknown>
): 'lp' | 'Dp' | 'dp' => ring.monomialOrder === 'lex'
    ? 'lp'
    : ring.monomialOrder === 'grlex' ? 'Dp' : 'dp';

const vectorText = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    vector: AlgebraPolynomialModuleVector<P, C, I>
): string => `[${vector.components.map(algebraPolynomialText).join(',')}]`;

const zeroVectorText = (rank: number): string =>
    `[${Array.from({ length: rank }, () => '0').join(',')}]`;

const identityModuleText = (rank: number): string => Array.from(
    { length: rank },
    (_, column) => `[${Array.from(
        { length: rank },
        (_, row) => row === column ? '1' : '0'
    ).join(',')}]`
).join(',');

/**
 * Compare generated submodules rather than literal bases: Singular and the
 * native engine may select different Groebner generators for the same kernel.
 */
export function singularPolynomialWeakKernelComparisonScript<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(weakKernel: AlgebraPolynomialWeakKernel<P, C, I>): string {
    const ring = weakKernel.map.source.ring;
    const variables = ring.variables.length === 0
        ? 'emdash_dummy'
        : ring.variables.join(',');
    const header = `ring emdash_r = 0,(${variables}),${singularOrder(ring as never)};`;
    const sourceRank = weakKernel.map.source.rank;
    if (sourceRank === 0) {
        return [
            header,
            'print("EMDASH_NATIVE_IN_ORACLE:1");',
            'print("EMDASH_ORACLE_IN_NATIVE:1");',
            'print("EMDASH_ORACLE_COUNT:0");',
            'quit;'
        ].join('\n') + '\n';
    }
    const nativeColumns = weakKernel.morphism.columns.length === 0
        ? zeroVectorText(sourceRank)
        : weakKernel.morphism.columns.map(vectorText).join(',');
    const oracleDefinition = weakKernel.map.target.rank === 0
        ? `module emdash_s = ${identityModuleText(sourceRank)};`
        : [
            `module emdash_f = ${weakKernel.map.columns.map(vectorText).join(',')};`,
            'module emdash_s = syz(emdash_f);'
        ].join('\n');
    return [
        header,
        oracleDefinition,
        `module emdash_n = ${nativeColumns};`,
        'module emdash_gs = std(emdash_s);',
        'module emdash_gn = std(emdash_n);',
        'int emdash_native_in_oracle = 1;',
        'int emdash_oracle_in_native = 1;',
        'int emdash_i;',
        'for (emdash_i=1; emdash_i<=size(emdash_n); emdash_i++)',
        '{ if (reduce(emdash_n[emdash_i],emdash_gs)!=0)',
        '  { emdash_native_in_oracle=0; } }',
        'for (emdash_i=1; emdash_i<=size(emdash_s); emdash_i++)',
        '{ if (reduce(emdash_s[emdash_i],emdash_gn)!=0)',
        '  { emdash_oracle_in_native=0; } }',
        'print("EMDASH_NATIVE_IN_ORACLE:"+string(emdash_native_in_oracle));',
        'print("EMDASH_ORACLE_IN_NATIVE:"+string(emdash_oracle_in_native));',
        'print("EMDASH_ORACLE_COUNT:"+string(size(emdash_s)));',
        'quit;'
    ].join('\n') + '\n';
}

const marker = (name: string, stdout: string): number => {
    const match = new RegExp(`(?:^|\\n)${name}:([0-9]+)(?:\\n|$)`, 'u')
        .exec(stdout);
    if (match === null) {
        throw new AlgebraOracleError(
            'MALFORMED_OUTPUT',
            `Singular output omitted ${name}`
        );
    }
    return Number(match[1]);
};

export async function comparePolynomialWeakKernelWithSingular<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    weakKernel: AlgebraPolynomialWeakKernel<P, C, I>,
    transport: AlgebraOracleTransport,
    executable = ALGEBRA_POLYNOMIAL_WEAK_KERNEL_SINGULAR_PROFILE.executable
): Promise<AlgebraPolynomialWeakKernelSingularComparison> {
    const result = await transport.execute({
        executable,
        args: ['-q'],
        stdin: singularPolynomialWeakKernelComparisonScript(weakKernel),
        timeoutMilliseconds: 30_000,
        maximumOutputBytes: 1_000_000
    });
    if (result.exitCode !== 0) {
        throw new AlgebraOracleError(
            'PROCESS_FAILED',
            result.stderr || `Singular exited with ${result.exitCode}`
        );
    }
    const nativeInOracle = marker(
        'EMDASH_NATIVE_IN_ORACLE',
        result.stdout
    ) === 1;
    const oracleInNative = marker(
        'EMDASH_ORACLE_IN_NATIVE',
        result.stdout
    ) === 1;
    const oracleGeneratorCount = marker(
        'EMDASH_ORACLE_COUNT',
        result.stdout
    );
    return Object.freeze({
        kind: 'algebra-polynomial-weak-kernel-singular-comparison',
        weakKernelKind: weakKernel.kind,
        nativeGeneratorCount: weakKernel.morphism.columns.length,
        oracleGeneratorCount,
        nativeInOracle,
        oracleInNative,
        agrees: nativeInOracle && oracleInNative,
        provider: 'singular-oracle'
    });
}
