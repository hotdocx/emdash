/** Source-aligned opaque interfaces and Core assembly for a two-step complex. */

import {
    KernelExpression, binderMode, kernelApplication, kernelBinder, kernelBound,
    kernelCall, kernelFree, kernelPi, provenance
} from './kernel';
import { CoreLfDeclarationEnvironment } from './lf_declarations';

export const FORMAL_BOUNDED_COMPLEX_ASSEMBLY_BINDINGS = Object.freeze({
    bridge_CommRingFreeChainTail: 'CommRingFreeChainTail',
    bridge_CommRingBoundedFreeComplex: 'CommRingBoundedFreeComplex',
    bridge_comm_ring_free_chain_tail_nil: 'comm_ring_free_chain_tail_nil',
    bridge_comm_ring_free_chain_tail_cons: 'comm_ring_free_chain_tail_cons',
    bridge_comm_ring_free_chain_tail_next_rank: 'comm_ring_free_chain_tail_next_rank',
    bridge_comm_ring_free_chain_tail_differential: 'comm_ring_free_chain_tail_differential',
    bridge_comm_ring_bounded_free_complex_succ: 'comm_ring_bounded_free_complex_succ',
    bridge_comm_ring_bounded_free_complex_rank0: 'comm_ring_bounded_free_complex_rank0',
    bridge_comm_ring_bounded_free_complex_rank1: 'comm_ring_bounded_free_complex_rank1',
    bridge_comm_ring_bounded_free_complex_d1: 'comm_ring_bounded_free_complex_d1',
    bridge_comm_ring_bounded_free_complex_tail: 'comm_ring_bounded_free_complex_tail'
});

export const FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE = Object.freeze({
    revision: 'emdash-formal-two-step-complex-assembly-v1',
    owner: 'emdash3_2_commutative_algebra_bounded_free_complexes.lp',
    sourceSha256: '7d4b137314c4293642a764d02cacb14dd1ad7ed1e0052a7c9ca7977f85851c35',
    declarationPolicy: 'exact-opaque-signature-mirrors',
    constructorPolicy: 'existing-successor-and-tail-cons',
    addsRuntimeRule: false,
    addsProofRule: false,
    addsCoreOwner: false,
    performsIo: false
} as const);

const p = provenance('derived', 'bounded free-complex Core assembly');
const free = (name: string) => kernelFree(name, p);
export const formalComplexCall = (
    name: string, values: readonly KernelExpression[], implicitCount = 0
): KernelExpression => kernelCall(free(name), values.map((value, index) => ({
    plicity: index < implicitCount ? 'implicit' as const : 'explicit' as const, value
})), p);
export const formalComplexTau = (classifier: KernelExpression) =>
    formalComplexCall('bridge_tau', [classifier]);
const carrier = (R: KernelExpression) => formalComplexCall('bridge_comm_ring_carrier', [R]);
const family = (A: KernelExpression, n: KernelExpression) =>
    formalComplexCall('bridge_FiniteFamily', [A, n]);
export const formalComplexVectorType = (R: KernelExpression, rank: KernelExpression) =>
    formalComplexTau(family(carrier(R), rank));
export const formalComplexMatrixType = (
    R: KernelExpression, rows: KernelExpression, columns: KernelExpression
) => formalComplexTau(family(family(carrier(R), rows), columns));
export const formalComplexNat = (n: number): KernelExpression => {
    if (!Number.isSafeInteger(n) || n < 0 || n > 1024) throw new Error('Invalid bounded formal rank');
    let result: KernelExpression = free('bridge_nat_zero');
    for (let i = 0; i < n; i++) result = formalComplexCall('bridge_nat_succ', [result]);
    return result;
};
const successor = (n: KernelExpression) => formalComplexCall('bridge_nat_succ', [n]);
const tailType = (R: KernelExpression, length: KernelExpression, below: KernelExpression,
    current: KernelExpression, boundary: KernelExpression) => formalComplexTau(
    formalComplexCall('bridge_CommRingFreeChainTail', [R, length, below, current, boundary]));
export const formalComplexType = (R: KernelExpression, length: KernelExpression) =>
    formalComplexTau(formalComplexCall('bridge_CommRingBoundedFreeComplex', [R, length]));

type Scope = Readonly<Record<string, KernelExpression>>;
type Parameter = readonly [string, (scope: Scope) => KernelExpression, boolean?];
/** Build dependent Pi types by names; each domain sees only earlier binders. */
const signature = (parameters: readonly Parameter[], result: (scope: Scope) => KernelExpression) => {
    const build = (depth: number): KernelExpression => {
        const scope = Object.fromEntries(parameters.slice(0, depth).map(([name], index) =>
            [name, kernelBound(depth - index - 1, p)]));
        if (depth === parameters.length) return result(scope);
        const [name, type, implicit] = parameters[depth];
        return kernelPi(kernelBinder(name, type(scope),
            binderMode(implicit ? 'implicit' : 'explicit', 'functorial'), p), build(depth + 1), p);
    };
    return build(0);
};

/** Extend the existing ring/matrix environment without changing its rules. */
export function extendFormalBoundedComplexAssemblySignatures(base: CoreLfDeclarationEnvironment) {
    let environment = base;
    const ring = () => formalComplexTau(free('bridge_CommRing'));
    const nat = () => formalComplexTau(free('bridge_Nat_grpd'));
    const grpd = () => kernelApplication('groupoid-universe', [], p);
    const add = (name: keyof typeof FORMAL_BOUNDED_COMPLEX_ASSEMBLY_BINDINGS,
        parameters: readonly Parameter[], result: (scope: Scope) => KernelExpression) => {
        environment = environment.extend({ name, type: signature(parameters, result),
            mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    add('bridge_CommRingFreeChainTail', [['R', ring], ['length', nat], ['below', nat],
        ['current', nat], ['boundary', s => formalComplexMatrixType(s.R, s.below, s.current)]], grpd);
    add('bridge_CommRingBoundedFreeComplex', [['R', ring], ['length', nat]], grpd);
    add('bridge_comm_ring_free_chain_tail_nil', [['R', ring, true], ['below', nat, true],
        ['current', nat, true], ['boundary', s => formalComplexMatrixType(s.R, s.below, s.current), true]],
    s => tailType(s.R, formalComplexNat(0), s.below, s.current, s.boundary));
    const tailParameters: readonly Parameter[] = [['R', ring, true], ['length', nat, true],
        ['below', nat, true], ['current', nat, true],
        ['boundary', s => formalComplexMatrixType(s.R, s.below, s.current), true]];
    add('bridge_comm_ring_free_chain_tail_cons', [...tailParameters, ['next', nat],
        ['differential', s => formalComplexMatrixType(s.R, s.current, s.next)],
        ['law', s => formalComplexTau(formalComplexCall('bridge_CommRingMatrixCompositeZero',
            [s.R, s.below, s.current, s.next, s.boundary, s.differential]))],
        ['rest', s => tailType(s.R, s.length, s.current, s.next, s.differential)]],
    s => tailType(s.R, successor(s.length), s.below, s.current, s.boundary));
    add('bridge_comm_ring_bounded_free_complex_succ', [['R', ring, true], ['tailLength', nat, true],
        ['rank0', nat], ['rank1', nat], ['d1', s => formalComplexMatrixType(s.R, s.rank0, s.rank1)],
        ['tail', s => tailType(s.R, s.tailLength, s.rank0, s.rank1, s.d1)]],
    s => formalComplexType(s.R, successor(s.tailLength)));
    const complexParameters: readonly Parameter[] = [['R', ring, true], ['tailLength', nat, true],
        ['C', s => formalComplexType(s.R, successor(s.tailLength))]];
    const rank = (s: Scope, index: 0 | 1) => formalComplexCall(
        `bridge_comm_ring_bounded_free_complex_rank${index}`, [s.R, s.tailLength, s.C], 2);
    const lower = (s: Scope) => formalComplexCall('bridge_comm_ring_bounded_free_complex_d1',
        [s.R, s.tailLength, s.C], 2);
    add('bridge_comm_ring_bounded_free_complex_rank0', complexParameters, nat);
    add('bridge_comm_ring_bounded_free_complex_rank1', complexParameters, nat);
    add('bridge_comm_ring_bounded_free_complex_d1', complexParameters,
        s => formalComplexMatrixType(s.R, rank(s, 0), rank(s, 1)));
    add('bridge_comm_ring_bounded_free_complex_tail', complexParameters,
        s => tailType(s.R, s.tailLength, rank(s, 0), rank(s, 1), lower(s)));
    const projectionParameters: readonly Parameter[] = [...tailParameters,
        ['tail', s => tailType(s.R, successor(s.length), s.below, s.current, s.boundary)]];
    add('bridge_comm_ring_free_chain_tail_next_rank', projectionParameters, nat);
    add('bridge_comm_ring_free_chain_tail_differential', projectionParameters, s =>
        formalComplexMatrixType(s.R, s.current, formalComplexCall('bridge_comm_ring_free_chain_tail_next_rank',
            [s.R, s.length, s.below, s.current, s.boundary, s.tail], 5)));
    return environment;
}

/** Assemble retained data and one supplied equation into the source's whole object. */
export function assembleFormalTwoStepComplex(input: {
    readonly formalRing: KernelExpression;
    readonly ranks: readonly [number, number, number];
    readonly lower: KernelExpression;
    readonly upper: KernelExpression;
    readonly law: KernelExpression;
}) {
    const R = input.formalRing;
    const [r0, r1, r2] = input.ranks.map(formalComplexNat);
    const rest = formalComplexCall('bridge_comm_ring_free_chain_tail_nil', [R, r1, r2, input.upper], 4);
    const tail = formalComplexCall('bridge_comm_ring_free_chain_tail_cons',
        [R, formalComplexNat(0), r0, r1, input.lower, r2, input.upper, input.law, rest], 5);
    const term = formalComplexCall('bridge_comm_ring_bounded_free_complex_succ',
        [R, formalComplexNat(1), r0, r1, input.lower, tail], 2);
    return Object.freeze({ term, type: formalComplexType(R, formalComplexNat(2)), tail });
}

/** Retain dependent ranks while exposing the actual upper differential for reuse. */
export function formalTwoStepUpperDifferential(R: KernelExpression, C: KernelExpression) {
    const prefix = [R, formalComplexNat(1), C];
    const below = formalComplexCall('bridge_comm_ring_bounded_free_complex_rank0', prefix, 2);
    const current = formalComplexCall('bridge_comm_ring_bounded_free_complex_rank1', prefix, 2);
    const boundary = formalComplexCall('bridge_comm_ring_bounded_free_complex_d1', prefix, 2);
    const tail = formalComplexCall('bridge_comm_ring_bounded_free_complex_tail', prefix, 2);
    const parameters = [R, formalComplexNat(0), below, current, boundary, tail];
    const next = formalComplexCall('bridge_comm_ring_free_chain_tail_next_rank', parameters, 5);
    const term = formalComplexCall('bridge_comm_ring_free_chain_tail_differential', parameters, 5);
    return Object.freeze({ term, type: formalComplexMatrixType(R, current, next),
        rows: current, columns: next });
}
