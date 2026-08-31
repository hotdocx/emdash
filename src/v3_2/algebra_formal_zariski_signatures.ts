/** Exact opaque TypeScript LF mirrors for the portable formal Zariski surface. */

import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    BinderMode,
    KernelExpression,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelPi,
    kernelUniverse,
    provenance,
    sourceSpan
} from './kernel';

export const AFFINE_FORMAL_ZARISKI_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-zariski-signatures-v1' as const,
    signatureNames: Object.freeze([
        'bridge_tau',
        'bridge_eq',
        'bridge_CommRing',
        'bridge_Nat_grpd',
        'bridge_comm_ring_carrier',
        'bridge_comm_ring_zero',
        'bridge_comm_ring_one',
        'bridge_comm_ring_add',
        'bridge_comm_ring_neg',
        'bridge_comm_ring_mul',
        'bridge_FiniteFamily',
        'bridge_nat_zero',
        'bridge_nat_succ',
        'bridge_finite_family_nil',
        'bridge_finite_family_cons',
        'bridge_comm_ring_finite_dot',
        'bridge_CommRingUnimodularPresentation',
        'bridge_comm_ring_unimodular_intro',
        'bridge_CommRingZariskiCoverPresentation',
        'bridge_comm_ring_zariski_cover_intro'
    ] as const),
    declarationPolicy: 'exact-opaque-signature-mirrors' as const,
    addsCoreOwner: false as const,
    addsDefinition: false as const,
    addsRuntimeRule: false as const,
    addsProofRule: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export const AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS = Object.freeze({
    bridge_tau: 'τ',
    bridge_eq: '=',
    bridge_CommRing: 'CommRing',
    bridge_Nat_grpd: 'Nat_grpd',
    bridge_comm_ring_carrier: 'comm_ring_carrier',
    bridge_comm_ring_zero: 'comm_ring_zero',
    bridge_comm_ring_one: 'comm_ring_one',
    bridge_comm_ring_add: 'comm_ring_add',
    bridge_comm_ring_neg: 'comm_ring_neg',
    bridge_comm_ring_mul: 'comm_ring_mul',
    bridge_FiniteFamily: 'FiniteFamily',
    bridge_nat_zero: 'zero',
    bridge_nat_succ: 'succ',
    bridge_finite_family_nil: 'finite_family_nil',
    bridge_finite_family_cons: 'finite_family_cons',
    bridge_comm_ring_finite_dot: 'comm_ring_finite_dot',
    bridge_CommRingUnimodularPresentation:
        'CommRingUnimodularPresentation',
    bridge_comm_ring_unimodular_intro: 'comm_ring_unimodular_intro',
    bridge_CommRingZariskiCoverPresentation:
        'CommRingZariskiCoverPresentation',
    bridge_comm_ring_zariski_cover_intro: 'comm_ring_zariski_cover_intro'
});

export interface AffineFormalZariskiInputDeclaration {
    readonly name: string;
    readonly type: KernelExpression;
    readonly mode?: BinderMode;
}

const nodeProvenance = provenance(
    'derived',
    'affine formal Zariski signature mirror'
);
const explicit = binderMode('explicit', 'functorial');
const implicit = binderMode('implicit', 'functorial');

const grpd = (): KernelExpression => kernelApplication(
    'groupoid-universe',
    [],
    nodeProvenance
);
const bound = (index: number): KernelExpression => kernelBound(
    index,
    nodeProvenance
);
const free = (name: string): KernelExpression => kernelFree(
    name,
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
    mode: BinderMode,
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
const carrier = (ring: KernelExpression): KernelExpression => call(
    'bridge_comm_ring_carrier',
    [{ plicity: 'explicit', value: ring }]
);
const nat = (): KernelExpression => tau(free('bridge_Nat_grpd'));
const finiteFamily = (
    classifier: KernelExpression,
    length: KernelExpression
): KernelExpression => call('bridge_FiniteFamily', [
    { plicity: 'explicit', value: classifier },
    { plicity: 'explicit', value: length }
]);
const equality = (
    classifier: KernelExpression,
    left: KernelExpression,
    right: KernelExpression
): KernelExpression => call('bridge_eq', [
    { plicity: 'implicit', value: classifier },
    { plicity: 'explicit', value: left },
    { plicity: 'explicit', value: right }
]);

interface SignatureDeclaration {
    readonly name: string;
    readonly type: KernelExpression;
}

const signatures = (): readonly SignatureDeclaration[] => {
    const ringType = tau(free('bridge_CommRing'));
    const zero = free('bridge_nat_zero');
    const successor = (value: KernelExpression) => call('bridge_nat_succ', [
        { plicity: 'explicit', value }
    ]);
    const ringElement = (ring: KernelExpression) => tau(carrier(ring));
    const ringOperation = (arity: 1 | 2): KernelExpression => arity === 1
        ? pi('R', ringType, explicit,
            pi('x', ringElement(bound(0)), explicit,
                ringElement(bound(1))))
        : pi('R', ringType, explicit,
            pi('x', ringElement(bound(0)), explicit,
                pi('y', ringElement(bound(1)), explicit,
                    ringElement(bound(2)))));
    const familyAt = (
        ringIndex: number,
        lengthIndex: number
    ): KernelExpression => tau(finiteFamily(
        carrier(bound(ringIndex)),
        bound(lengthIndex)
    ));

    return Object.freeze([
        {
            name: 'bridge_tau',
            type: pi('A', grpd(), explicit, kernelUniverse(nodeProvenance))
        },
        {
            name: 'bridge_eq',
            type: pi('A', grpd(), implicit,
                pi('left', tau(bound(0)), explicit,
                    pi('right', tau(bound(1)), explicit, grpd())))
        },
        { name: 'bridge_CommRing', type: grpd() },
        { name: 'bridge_Nat_grpd', type: grpd() },
        {
            name: 'bridge_comm_ring_carrier',
            type: pi('R', ringType, explicit, grpd())
        },
        {
            name: 'bridge_comm_ring_zero',
            type: pi('R', ringType, explicit, ringElement(bound(0)))
        },
        {
            name: 'bridge_comm_ring_one',
            type: pi('R', ringType, explicit, ringElement(bound(0)))
        },
        { name: 'bridge_comm_ring_add', type: ringOperation(2) },
        { name: 'bridge_comm_ring_neg', type: ringOperation(1) },
        { name: 'bridge_comm_ring_mul', type: ringOperation(2) },
        {
            name: 'bridge_FiniteFamily',
            type: pi('A', grpd(), explicit,
                pi('n', nat(), explicit, grpd()))
        },
        { name: 'bridge_nat_zero', type: nat() },
        {
            name: 'bridge_nat_succ',
            type: pi('n', nat(), explicit, nat())
        },
        {
            name: 'bridge_finite_family_nil',
            type: pi('A', grpd(), implicit,
                tau(finiteFamily(bound(0), zero)))
        },
        {
            name: 'bridge_finite_family_cons',
            type: pi('A', grpd(), implicit,
                pi('n', nat(), implicit,
                    pi('head', tau(bound(1)), explicit,
                        pi('tail', tau(finiteFamily(bound(2), bound(1))),
                            explicit,
                            tau(finiteFamily(
                                bound(3),
                                successor(bound(2))
                            ))))))
        },
        {
            name: 'bridge_comm_ring_finite_dot',
            type: pi('R', ringType, explicit,
                pi('n', nat(), explicit,
                    pi('coefficients', familyAt(1, 0), explicit,
                        pi('generators', familyAt(2, 1), explicit,
                            ringElement(bound(3))))))
        },
        {
            name: 'bridge_CommRingUnimodularPresentation',
            type: pi('R', ringType, implicit,
                pi('n', nat(), explicit,
                    pi('generators', familyAt(1, 0), explicit, grpd())))
        },
        {
            name: 'bridge_comm_ring_unimodular_intro',
            type: pi('R', ringType, implicit,
                pi('n', nat(), implicit,
                    pi('generators', familyAt(1, 0), implicit,
                        pi('coefficients', familyAt(2, 1), explicit,
                            pi('law', tau(equality(
                                carrier(bound(3)),
                                call('bridge_comm_ring_finite_dot', [
                                    { plicity: 'explicit', value: bound(3) },
                                    { plicity: 'explicit', value: bound(2) },
                                    { plicity: 'explicit', value: bound(0) },
                                    { plicity: 'explicit', value: bound(1) }
                                ]),
                                call('bridge_comm_ring_one', [{
                                    plicity: 'explicit',
                                    value: bound(3)
                                }])
                            )), explicit,
                            tau(call(
                                'bridge_CommRingUnimodularPresentation',
                                [
                                    { plicity: 'implicit', value: bound(4) },
                                    { plicity: 'explicit', value: bound(3) },
                                    { plicity: 'explicit', value: bound(2) }
                                ]
                            )))))))
        },
        {
            name: 'bridge_CommRingZariskiCoverPresentation',
            type: pi('R', ringType, explicit, grpd())
        },
        {
            name: 'bridge_comm_ring_zariski_cover_intro',
            type: pi('R', ringType, implicit,
                pi('n', nat(), explicit,
                    pi('generators', familyAt(1, 0), explicit,
                        pi('unimodular', tau(call(
                            'bridge_CommRingUnimodularPresentation',
                            [
                                { plicity: 'implicit', value: bound(2) },
                                { plicity: 'explicit', value: bound(1) },
                                { plicity: 'explicit', value: bound(0) }
                            ]
                        )), explicit,
                        tau(call(
                            'bridge_CommRingZariskiCoverPresentation',
                            [{ plicity: 'explicit', value: bound(3) }]
                        ))))))
        }
    ]);
};

/**
 * Build the exact dependency-ordered opaque mirror plus caller formal inputs.
 */
export function createAffineFormalZariskiProofEnvironment(
    inputs: readonly AffineFormalZariskiInputDeclaration[]
): CoreLfDeclarationEnvironment {
    let environment = CoreLfDeclarationEnvironment.empty();
    signatures().forEach(signature => {
        environment = environment.extend({
            name: signature.name,
            type: signature.type,
            mode: explicit,
            provenance: nodeProvenance
        });
    });
    inputs.forEach((input, index) => {
        environment = environment.extend({
            name: input.name,
            type: input.type,
            mode: input.mode ?? explicit,
            provenance: provenance(
                'surface',
                `affine formal Zariski input ${index}: ${input.name}`,
                sourceSpan(
                    'generated/affine-formal-zariski-inputs.ts',
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
