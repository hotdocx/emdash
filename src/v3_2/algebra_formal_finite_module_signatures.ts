/** Exact opaque LF mirrors for finite-vector and matrix proof goals. */

import {
    AffineFormalZariskiInputDeclaration
} from './algebra_formal_zariski_signatures';
import {
    createAffineFormalLocalizationProofEnvironment
} from './algebra_formal_localization_signatures';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    KernelExpression,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelPi,
    provenance,
    sourceSpan
} from './kernel';

export const FORMAL_FINITE_MODULE_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-finite-module-signatures-v1' as const,
    names: Object.freeze([
        'bridge_CommRingVector',
        'bridge_CommRingMatrix',
        'bridge_comm_ring_vector_zero',
        'bridge_comm_ring_matrix_apply',
        'bridge_comm_ring_matrix_zero',
        'bridge_comm_ring_matrix_comp',
        'bridge_CommRingPresentationAgreement',
        'bridge_CommRingMatrixSyzygy',
        'bridge_CommRingMatrixCompositeZero'
    ] as const),
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

const p = provenance('derived', 'formal finite module signature');
const explicit = binderMode('explicit', 'functorial');
const b = (index: number): KernelExpression => kernelBound(index, p);
const free = (name: string): KernelExpression => kernelFree(name, p);
const grpd = (): KernelExpression => kernelApplication('groupoid-universe', [], p);
const call = (
    name: string,
    values: readonly { plicity: 'explicit' | 'implicit'; value: KernelExpression }[]
) => kernelCall(free(name), values, p);
const pi = (
    name: string,
    type: KernelExpression,
    body: KernelExpression
) => kernelPi(kernelBinder(name, type, explicit, p), body, p);
const tau = (value: KernelExpression) => call('bridge_tau', [
    { plicity: 'explicit', value }
]);
const ring = () => tau(free('bridge_CommRing'));
const nat = () => tau(free('bridge_Nat_grpd'));
const carrier = (R: KernelExpression) => call('bridge_comm_ring_carrier', [
    { plicity: 'explicit', value: R }
]);
const vector = (R: KernelExpression, n: KernelExpression) =>
    call('bridge_FiniteFamily', [
        { plicity: 'explicit', value: carrier(R) },
        { plicity: 'explicit', value: n }
    ]);
const matrix = (
    R: KernelExpression,
    rows: KernelExpression,
    columns: KernelExpression
) => call('bridge_FiniteFamily', [
    { plicity: 'explicit', value: vector(R, rows) },
    { plicity: 'explicit', value: columns }
]);

export function createFormalFiniteModuleProofEnvironment(
    inputs: readonly AffineFormalZariskiInputDeclaration[]
): CoreLfDeclarationEnvironment {
    let environment = createAffineFormalLocalizationProofEnvironment([]);
    const add = (name: string, type: KernelExpression): void => {
        environment = environment.extend({ name, type, mode: explicit, provenance: p });
    };
    add('bridge_CommRingVector', pi('R', ring(), pi('n', nat(), grpd())));
    add('bridge_CommRingMatrix', pi('R', ring(),
        pi('rows', nat(), pi('columns', nat(), grpd()))));
    add('bridge_comm_ring_vector_zero', pi('R', ring(),
        pi('n', nat(), tau(vector(b(1), b(0))))));
    add('bridge_comm_ring_matrix_apply', pi('R', ring(),
        pi('rows', nat(), pi('columns', nat(),
            pi('A', tau(matrix(b(2), b(1), b(0))),
                pi('x', tau(vector(b(3), b(1))),
                    tau(vector(b(4), b(3)))))))));
    add('bridge_comm_ring_matrix_zero', pi('R', ring(),
        pi('rows', nat(), pi('columns', nat(),
            tau(matrix(b(2), b(1), b(0)))))));
    add('bridge_comm_ring_matrix_comp', pi('R', ring(),
        pi('rows', nat(), pi('middle', nat(), pi('columns', nat(),
            pi('A', tau(matrix(b(3), b(2), b(1))),
                pi('B', tau(matrix(b(4), b(2), b(1))),
                    tau(matrix(b(5), b(4), b(3))))))))));
    add('bridge_CommRingPresentationAgreement', pi('R', ring(),
        pi('generators', nat(), pi('relations', nat(),
            pi('A', tau(matrix(b(2), b(1), b(0))),
                pi('v', tau(vector(b(3), b(2))),
                    pi('w', tau(vector(b(4), b(3))), grpd())))))));
    add('bridge_CommRingMatrixSyzygy', pi('R', ring(),
        pi('rows', nat(), pi('columns', nat(),
            pi('A', tau(matrix(b(2), b(1), b(0))),
                pi('s', tau(vector(b(3), b(1))), grpd()))))));
    add('bridge_CommRingMatrixCompositeZero', pi('R', ring(),
        pi('rows', nat(), pi('middle', nat(), pi('columns', nat(),
            pi('A', tau(matrix(b(3), b(2), b(1))),
                pi('B', tau(matrix(b(4), b(2), b(1))), grpd())))))));
    inputs.forEach((input, index) => {
        environment = environment.extend({
            name: input.name,
            type: input.type,
            mode: input.mode ?? explicit,
            provenance: provenance('surface', `finite module input ${input.name}`,
                sourceSpan('generated/formal-finite-module-inputs.ts', index + 1, 1))
        });
    });
    return environment;
}
