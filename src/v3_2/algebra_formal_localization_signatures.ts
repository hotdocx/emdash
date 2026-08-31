/** Exact opaque TypeScript LF mirrors needed by localization proof goals. */

import {
    AffineFormalZariskiInputDeclaration,
    createAffineFormalZariskiProofEnvironment
} from './algebra_formal_zariski_signatures';
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

export const AFFINE_FORMAL_LOCALIZATION_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-localization-signatures-v1' as const,
    additionalSignatures: Object.freeze([
        'bridge_CommRingHom',
        'bridge_comm_ring_hom_apply',
        'bridge_IsCommRingLocalizationAt'
    ] as const),
    declarationPolicy: 'exact-opaque-signature-mirrors' as const,
    addsCoreOwner: false as const,
    addsDefinition: false as const,
    addsRuntimeRule: false as const,
    addsProofRule: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export const AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS = Object.freeze({
    bridge_CommRingHom: 'CommRingHom',
    bridge_comm_ring_hom_apply: 'comm_ring_hom_apply',
    bridge_IsCommRingLocalizationAt: 'IsCommRingLocalizationAt'
});

const nodeProvenance = provenance(
    'derived',
    'affine formal localization goal signature mirror'
);
const explicit = binderMode('explicit', 'functorial');
const implicit = binderMode('implicit', 'functorial');
const bound = (index: number): KernelExpression => kernelBound(
    index,
    nodeProvenance
);
const free = (name: string): KernelExpression => kernelFree(
    name,
    nodeProvenance
);
const grpd = (): KernelExpression => kernelApplication(
    'groupoid-universe',
    [],
    nodeProvenance
);
const call = (
    name: string,
    values: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: KernelExpression;
    }[]
): KernelExpression => kernelCall(free(name), values, nodeProvenance);
const pi = (
    name: string,
    type: KernelExpression,
    mode: ReturnType<typeof binderMode>,
    body: KernelExpression
): KernelExpression => kernelPi(
    kernelBinder(name, type, mode, nodeProvenance),
    body,
    nodeProvenance
);
const tau = (classifier: KernelExpression): KernelExpression => call(
    'bridge_tau',
    [{ plicity: 'explicit', value: classifier }]
);
const ring = (): KernelExpression => tau(free('bridge_CommRing'));
const carrier = (value: KernelExpression): KernelExpression => call(
    'bridge_comm_ring_carrier',
    [{ plicity: 'explicit', value }]
);
const hom = (
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => call('bridge_CommRingHom', [
    { plicity: 'explicit', value: source },
    { plicity: 'explicit', value: target }
]);

export function createAffineFormalLocalizationProofEnvironment(
    inputs: readonly AffineFormalZariskiInputDeclaration[]
): CoreLfDeclarationEnvironment {
    let environment = createAffineFormalZariskiProofEnvironment([]);
    environment = environment.extend({
        name: 'bridge_CommRingHom',
        type: pi('R', ring(), explicit,
            pi('S', ring(), explicit, grpd())),
        mode: explicit,
        provenance: nodeProvenance
    });
    environment = environment.extend({
        name: 'bridge_comm_ring_hom_apply',
        type: pi('R', ring(), implicit,
            pi('S', ring(), implicit,
                pi('h', tau(hom(bound(1), bound(0))), explicit,
                    pi('x', tau(carrier(bound(2))), explicit,
                        tau(carrier(bound(2))))))),
        mode: explicit,
        provenance: nodeProvenance
    });
    environment = environment.extend({
        name: 'bridge_IsCommRingLocalizationAt',
        type: pi('R', ring(), implicit,
            pi('f', tau(carrier(bound(0))), explicit,
                pi('L', ring(), explicit,
                    pi('localization_map',
                        tau(hom(bound(2), bound(0))),
                        explicit,
                        grpd())))),
        mode: explicit,
        provenance: nodeProvenance
    });
    inputs.forEach((input, index) => {
        environment = environment.extend({
            name: input.name,
            type: input.type,
            mode: input.mode ?? explicit,
            provenance: provenance(
                'surface',
                `affine formal localization input ${index}: ${input.name}`,
                sourceSpan(
                    'generated/affine-formal-localization-inputs.ts',
                    index + 1,
                    1,
                    index + 1,
                    2
                )
            )
        });
    });
    return environment;
}
