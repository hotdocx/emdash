/** Explicit-Core reification and membership delegation for finite modules. */

import {
    AlgebraFormalComputationInterpretationInput,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    buildAffineFormalFamily
} from './algebra_formal_cover';
import {
    AlgebraAlgorithmIdentity,
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleGroebnerBasis,
    AlgebraPolynomialModuleMembership,
    AlgebraPolynomialModuleVector,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleVectorSchema
} from './algebra_polynomial_module';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    KernelExpression,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_FINITE_MODULE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-finite-module-v1' as const,
    orientation: 'formal-columns-cas-component-arrays' as const,
    membershipRevision: 'emdash-formal-module-membership-v1' as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_FINITE_MODULE_BINDINGS = Object.freeze({
    bridge_CommRingVector: 'CommRingVector',
    bridge_CommRingMatrix: 'CommRingMatrix',
    bridge_comm_ring_matrix_apply: 'comm_ring_matrix_apply',
    bridge_comm_ring_vector_zero: 'comm_ring_vector_zero',
    bridge_CommRingPresentationAgreement: 'CommRingPresentationAgreement',
    bridge_CommRingMatrixSyzygy: 'CommRingMatrixSyzygy',
    bridge_CommRingMatrixCompositeZero: 'CommRingMatrixCompositeZero'
});

const nodeProvenance = provenance('derived', 'formal finite module');
const call = (
    name: string,
    values: readonly { plicity: 'explicit' | 'implicit'; value: KernelExpression }[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    values,
    nodeProvenance
);
const nat = (value: number): KernelExpression => {
    let result: KernelExpression = kernelFree(
        'bridge_nat_zero',
        nodeProvenance
    );
    for (let index = 0; index < value; index++) {
        result = call('bridge_nat_succ', [{ plicity: 'explicit', value: result }]);
    }
    return result;
};
const tau = (value: KernelExpression): KernelExpression => call(
    'bridge_tau',
    [{ plicity: 'explicit', value }]
);

export interface AlgebraFormalModuleMembershipInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
}

export interface AlgebraFormalModuleMembershipRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.revision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly input: AlgebraFormalModuleMembershipInput<P, C, I>;
    readonly selected: AlgebraPolynomialModuleMembership<P, C, I>;
    readonly formalGenerators: KernelExpression;
    readonly formalCoefficients: KernelExpression;
    readonly formalVector: KernelExpression;
    readonly claimType: KernelExpression;
}

const vectorTerm = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): KernelExpression => buildAffineFormalFamily(
    call('bridge_comm_ring_carrier', [{
        plicity: 'explicit', value: reifier.formalRing
    }]),
    vector.components.map(reifier.reifyPolynomial)
).family;

export function defineAlgebraFormalModuleMembershipRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly selected: AlgebraPolynomialModuleMembership<P, C, I>;
}): AlgebraFormalModuleMembershipRealization<P, C, I> {
    const rank = input.vector.parent.rank;
    const columns = input.basis.submodule.generators.length;
    const vectorClassifier = call('bridge_CommRingVector', [
        { plicity: 'explicit', value: input.reifier.formalRing },
        { plicity: 'explicit', value: nat(rank) }
    ]);
    const formalColumns = input.basis.submodule.generators.map(generator =>
        vectorTerm(input.reifier, generator)
    );
    const formalGenerators = buildAffineFormalFamily(
        vectorClassifier,
        formalColumns
    ).family;
    const formalCoefficients = buildAffineFormalFamily(
        call('bridge_comm_ring_carrier', [{
            plicity: 'explicit', value: input.reifier.formalRing
        }]),
        input.selected.coefficients.map(input.reifier.reifyPolynomial)
    ).family;
    const formalVector = vectorTerm(input.reifier, input.vector);
    const applied = call('bridge_comm_ring_matrix_apply', [
        { plicity: 'explicit', value: input.reifier.formalRing },
        { plicity: 'explicit', value: nat(rank) },
        { plicity: 'explicit', value: nat(columns) },
        { plicity: 'explicit', value: formalGenerators },
        { plicity: 'explicit', value: formalCoefficients }
    ]);
    const claimType = tau(call('bridge_eq', [
        { plicity: 'implicit', value: vectorClassifier },
        { plicity: 'explicit', value: applied },
        { plicity: 'explicit', value: formalVector }
    ]));
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.revision,
        reifier: input.reifier,
        input: Object.freeze({ vector: input.vector, basis: input.basis }),
        selected: input.selected,
        formalGenerators,
        formalCoefficients,
        formalVector,
        claimType
    });
}

const serializeMembership = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialModuleMembership<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson({
    member: value.member,
    vector: value.vector.components.map(algebraPolynomialText),
    coefficients: value.coefficients.map(algebraPolynomialText),
    remainder: value.remainder.components.map(algebraPolynomialText),
    steps: value.reductionSteps
}, 'formalModuleMembership');

export function algebraFormalModuleMembershipBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(sample: AlgebraPolynomialModuleVector<P, C, I>) {
    const vectorSchema = algebraPolynomialModuleVectorSchema(sample.parent);
    const inputSchema: AlgebraRuntimeSchema<AlgebraFormalModuleMembershipInput<P, C, I>> =
        defineAlgebraRuntimeSchema({
            id: `algebra.formal-module-membership-input/${sample.parent.identity.id}`,
            revision: sample.parent.identity.revision,
            normalize(value, path) {
                if (value === null || typeof value !== 'object') {
                    throw new Error(`module membership input expected at ${path}`);
                }
                const input = value as AlgebraFormalModuleMembershipInput<P, C, I>;
                return Object.freeze({
                    vector: vectorSchema.normalize(input.vector, `${path}.vector`),
                    basis: input.basis
                });
            }
        });
    const outputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleMembership<P, C, I>
    >({
        id: `algebra.formal-module-membership/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        normalize(value) {
            return value as AlgebraPolynomialModuleMembership<P, C, I>;
        }
    });
    const operation: AlgebraOperation<
        AlgebraFormalModuleMembershipInput<P, C, I>,
        AlgebraPolynomialModuleMembership<P, C, I>
    > = defineAlgebraOperation({
        id: `algebra.module.membership/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        input: inputSchema,
        output: outputSchema
    });
    const algorithm: AlgebraAlgorithmIdentity = algebraAlgorithmIdentity(
        `algebra.typescript-reference/${operation.identity.id}`,
        'module-membership-v1'
    );
    const implementations: readonly AlgebraReferenceImplementation[] = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation,
            algorithm,
            execute: input => algebraPolynomialModuleMembership(
                input.vector,
                input.basis
            )
        })
    ]);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.module-membership/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        operation,
        normalizeRealization(value) {
            return value as AlgebraFormalModuleMembershipRealization<P, C, I>;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: serializeMembership(value.selected),
            claim: serializeCoreExpression(value.claimType)
        }, 'formalModuleMembershipRealization'),
        acquire: (_goal, value) => value.input,
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            vector: value.vector.components.map(algebraPolynomialText)
        }, 'formalModuleMembershipInput'),
        serializeOutput: serializeMembership,
        interpret: ({ goal, realization, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeMembership(computed.value) ===
                serializeMembership(realization.selected) && computed.value.member
                ? {
                    kind: 'claim',
                    summary: 'selected module linear combination equals vector',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'module vector has a nonzero or changed remainder'
                }
    });
    return Object.freeze({ inputSchema, outputSchema, operation, implementations, adapter });
}
