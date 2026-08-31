/** Exact LF signature mirror for presentation-morphism equation targets. */

import {
    AffineFormalZariskiInputDeclaration
} from './algebra_formal_zariski_signatures';
import {
    createFormalFiniteModuleProofEnvironment
} from './algebra_formal_finite_module_signatures';
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

export const FORMAL_PRESENTATION_MORPHISM_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-presentation-morphism-signatures-v1' as const,
    names: Object.freeze(['bridge_comm_ring_matrix_sub'] as const),
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

const p = provenance('derived', 'formal presentation morphism signature');
const explicit = binderMode('explicit', 'functorial');
const b = (index: number): KernelExpression => kernelBound(index, p);
const free = (name: string): KernelExpression => kernelFree(name, p);
const call = (
    name: string,
    values: readonly { plicity: 'explicit' | 'implicit'; value: KernelExpression }[]
) => kernelCall(free(name), values, p);
const pi = (name: string, type: KernelExpression, body: KernelExpression) =>
    kernelPi(kernelBinder(name, type, explicit, p), body, p);
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

export function createFormalPresentationMorphismProofEnvironment(
    inputs: readonly AffineFormalZariskiInputDeclaration[]
): CoreLfDeclarationEnvironment {
    let environment = createFormalFiniteModuleProofEnvironment([]);
    environment = environment.extend({
        name: 'bridge_comm_ring_matrix_sub',
        type: pi('R', ring(), pi('rows', nat(), pi('columns', nat(),
            pi('A', tau(matrix(b(2), b(1), b(0))),
                pi('B', tau(matrix(b(3), b(2), b(1))),
                    tau(matrix(b(4), b(3), b(2)))))))),
        mode: explicit,
        provenance: p
    });
    inputs.forEach((input, index) => {
        environment = environment.extend({
            name: input.name,
            type: input.type,
            mode: input.mode ?? explicit,
            provenance: provenance(
                'surface',
                `presentation morphism input ${input.name}`,
                sourceSpan(
                    'generated/formal-presentation-morphism-inputs.ts',
                    index + 1,
                    1
                )
            )
        });
    });
    return environment;
}
