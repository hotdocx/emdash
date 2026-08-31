/** Computed face-product equations and formally derived face-unit evidence. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    affineFormalRingEqualityType
} from './algebra_formal_conformance';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    AFFINE_FORMAL_CECH_FACE_DERIVATION_BINDINGS
} from './algebra_formal_cech_face_bindings';
import {
    AffineFormalCechSimplexLocalization
} from './algebra_formal_overlap';
import {
    AlgebraCechFace
} from './algebra_cech';
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
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientMultiply,
    algebraQuotientText
} from './algebra_quotient';
import {
    KernelExpression,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_CECH_FACE_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-cech-face-delegation-v1' as const,
    realizationRevision:
        'emdash-algebra-formal-cech-face-realization-v1' as const,
    equationRevision: 'emdash-algebra-cech-face-product-equation-v1' as const,
    adapterRevision: 'emdash-algebra-formal-cech-face-adapter-v1' as const,
    classification: 'computed-equation' as const,
    faceUnit: 'derived-by-unit-transport-and-left-factor' as const,
    addsCoreOwner: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export interface AlgebraCechFaceProductInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly domainProduct: AlgebraQuotientElement<P, C, I>;
    readonly removedElement: AlgebraQuotientElement<P, C, I>;
    readonly codomainProduct: AlgebraQuotientElement<P, C, I>;
}

export interface AlgebraCechFaceProductEquation<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> extends AlgebraCechFaceProductInput<P, C, I> {
    readonly kind: 'algebra-cech-face-product-equation';
    readonly product: AlgebraQuotientElement<P, C, I>;
    readonly holds: boolean;
}

const faceInputSchema = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(sample: AlgebraQuotientElement<P, C, I>): AlgebraRuntimeSchema<
    AlgebraCechFaceProductInput<P, C, I>
> => defineAlgebraRuntimeSchema({
    id: `algebra.cech-face-product-input/${sample.parent.identity.id}`,
    revision: sample.parent.identity.revision,
    normalize(value, path) {
        if (value === null || typeof value !== 'object') {
            throw new Error(`face product input expected at ${path}`);
        }
        const input = value as AlgebraCechFaceProductInput<P, C, I>;
        [input.domainProduct, input.removedElement, input.codomainProduct]
            .forEach((element, index) => {
                if (!sameAlgebraParent(element.parent, sample.parent)) {
                    throw new Error(`foreign face product element ${index}`);
                }
            });
        return Object.freeze({ ...input });
    }
});

const faceOutputSchema = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(sample: AlgebraQuotientElement<P, C, I>): AlgebraRuntimeSchema<
    AlgebraCechFaceProductEquation<P, C, I>
> => defineAlgebraRuntimeSchema({
    id: `algebra.cech-face-product-equation/${sample.parent.identity.id}`,
    revision: sample.parent.identity.revision,
    normalize(value, path) {
        if (
            value === null || typeof value !== 'object' ||
            (value as { kind?: unknown }).kind !==
                'algebra-cech-face-product-equation'
        ) throw new Error(`face product equation expected at ${path}`);
        return value as AlgebraCechFaceProductEquation<P, C, I>;
    }
});

export interface AlgebraCechFaceProductOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly inputSchema: AlgebraRuntimeSchema<
        AlgebraCechFaceProductInput<P, C, I>
    >;
    readonly outputSchema: AlgebraRuntimeSchema<
        AlgebraCechFaceProductEquation<P, C, I>
    >;
    readonly operation: AlgebraOperation<
        AlgebraCechFaceProductInput<P, C, I>,
        AlgebraCechFaceProductEquation<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export function algebraCechFaceProductOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(sample: AlgebraQuotientElement<P, C, I>):
    AlgebraCechFaceProductOperations<P, C, I> {
    const inputSchema = faceInputSchema(sample);
    const outputSchema = faceOutputSchema(sample);
    const operation = defineAlgebraOperation({
        id: `algebra.cech.face-product/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        input: inputSchema,
        output: outputSchema
    });
    const algorithm: AlgebraAlgorithmIdentity = algebraAlgorithmIdentity(
        `algebra.typescript-reference/${operation.identity.id}`,
        'cech-face-product-v1'
    );
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation,
            algorithm,
            execute: input => {
                const product = algebraQuotientMultiply(
                    input.domainProduct,
                    input.removedElement
                );
                return Object.freeze({
                    kind: 'algebra-cech-face-product-equation' as const,
                    ...input,
                    product,
                    holds: algebraQuotientEquals(
                        product,
                        input.codomainProduct
                    )
                });
            }
        })
    ]);
    return Object.freeze({ inputSchema, outputSchema, operation, implementations });
}

export interface AlgebraFormalCechFaceDelegationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_CECH_FACE_DELEGATION_PROFILE.realizationRevision;
    readonly face: AlgebraCechFace<P, C, I>;
    readonly domain: AffineFormalCechSimplexLocalization<P, C, I>;
    readonly codomain: AffineFormalCechSimplexLocalization<P, C, I>;
    readonly input: AlgebraCechFaceProductInput<P, C, I>;
    readonly mappedDomain: KernelExpression;
    readonly mappedRemoved: KernelExpression;
    readonly mappedCodomain: KernelExpression;
    readonly product: KernelExpression;
    readonly claimType: KernelExpression;
}

const call = (
    name: keyof typeof AFFINE_FORMAL_CECH_FACE_DERIVATION_BINDINGS,
    values: readonly { plicity: 'explicit' | 'implicit'; value: KernelExpression }[]
): KernelExpression => kernelCall(
    kernelFree(name, provenance('derived', 'formal Cech face derivation')),
    values,
    provenance('derived', 'formal Cech face derivation')
);

export function defineAlgebraFormalCechFaceDelegationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly face: AlgebraCechFace<P, C, I>;
    readonly domain: AffineFormalCechSimplexLocalization<P, C, I>;
    readonly codomain: AffineFormalCechSimplexLocalization<P, C, I>;
}): AlgebraFormalCechFaceDelegationRealization<P, C, I> {
    if (!input.codomain.simplex.faces.includes(input.face)) {
        throw new AlgebraFormalDelegationError(
            'INVALID_REALIZATION',
            'cechFace.face',
            'Face does not belong to the selected codomain simplex'
        );
    }
    const cover = input.codomain.cover;
    const removedElement = cover.cover.elements[input.face.removedChart];
    const targetRing = input.codomain.localization.target.formalRing;
    const sourceRing = cover.algebra.formalRing;
    const map = input.codomain.localization.formalMap;
    const apply = (term: KernelExpression) => kernelCall(
        kernelFree('bridge_comm_ring_hom_apply', provenance('derived', 'face map')),
        [
            { plicity: 'implicit', value: sourceRing },
            { plicity: 'implicit', value: targetRing },
            { plicity: 'explicit', value: map },
            { plicity: 'explicit', value: term }
        ],
        provenance('derived', 'face map')
    );
    const mappedDomain = apply(input.domain.productTerm);
    const mappedRemoved = apply(cover.algebra.reifyElement(removedElement));
    const mappedCodomain = apply(input.codomain.productTerm);
    const product = kernelCall(
        kernelFree('bridge_comm_ring_mul', provenance('derived', 'face product')),
        [
            { plicity: 'explicit', value: targetRing },
            { plicity: 'explicit', value: mappedDomain },
            { plicity: 'explicit', value: mappedRemoved }
        ],
        provenance('derived', 'face product')
    );
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_CECH_FACE_DELEGATION_PROFILE.realizationRevision,
        face: input.face,
        domain: input.domain,
        codomain: input.codomain,
        input: Object.freeze({
            domainProduct: input.domain.simplex.product,
            removedElement,
            codomainProduct: input.codomain.simplex.product
        }),
        mappedDomain,
        mappedRemoved,
        mappedCodomain,
        product,
        claimType: affineFormalRingEqualityType(
            targetRing,
            product,
            mappedCodomain
        )
    });
}

const serializeEquation = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraCechFaceProductEquation<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson({
    domain: algebraQuotientText(value.domainProduct),
    removed: algebraQuotientText(value.removedElement),
    codomain: algebraQuotientText(value.codomainProduct),
    product: algebraQuotientText(value.product),
    holds: value.holds
}, 'algebraCechFaceProductEquation');

export function algebraFormalCechFaceDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(sample: AlgebraQuotientElement<P, C, I>) {
    const operations = algebraCechFaceProductOperations(sample);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.cech-face-product/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        operation: operations.operation,
        normalizeRealization(value, path) {
            if (
                value === null || typeof value !== 'object' ||
                (value as { profileRevision?: unknown }).profileRevision !==
                    ALGEBRA_FORMAL_CECH_FACE_DELEGATION_PROFILE.realizationRevision
            ) throw new Error(`face realization expected at ${path}`);
            return value as AlgebraFormalCechFaceDelegationRealization<P, C, I>;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            face: {
                removedPosition: value.face.removedPosition,
                removedChart: value.face.removedChart,
                targetIndices: value.face.targetIndices
            },
            claim: serializeCoreExpression(value.claimType)
        }, 'formalCechFaceRealization'),
        acquire: (goal, value) => {
            if (!kernelExpressionEquals(goal.target, value.claimType)) {
                throw new Error('face goal target mismatch');
            }
            return value.input;
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            domain: algebraQuotientText(value.domainProduct),
            removed: algebraQuotientText(value.removedElement),
            codomain: algebraQuotientText(value.codomainProduct)
        }, 'algebraCechFaceProductInput'),
        serializeOutput: serializeEquation,
        interpret: ({ goal, computed }): AlgebraFormalComputationInterpretationInput =>
            computed.value.holds ? {
                kind: 'claim',
                summary: 'Cech face product decomposes in the selected chart',
                claimType: goal.target
            } : {
                kind: 'observation',
                summary: 'Cech face product decomposition failed'
            }
    });
    return Object.freeze({ operations, adapter });
}

export function deriveAffineFormalCechFaceUnit<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AlgebraFormalCechFaceDelegationRealization<P, C, I>,
    decomposition: KernelExpression
): KernelExpression {
    const targetRing = realization.codomain.localization.target.formalRing;
    const property = realization.codomain.terms.property;
    const codomainUnit = call('bridge_comm_ring_localization_inverted_unit', [
        { plicity: 'implicit', value: realization.codomain.cover.algebra.formalRing },
        { plicity: 'implicit', value: realization.codomain.productTerm },
        { plicity: 'implicit', value: targetRing },
        { plicity: 'implicit', value: realization.codomain.localization.formalMap },
        { plicity: 'explicit', value: property }
    ]);
    const productUnit = call('bridge_comm_ring_unit_transport_backward', [
        { plicity: 'implicit', value: targetRing },
        { plicity: 'implicit', value: realization.product },
        { plicity: 'implicit', value: realization.mappedCodomain },
        { plicity: 'explicit', value: decomposition },
        { plicity: 'explicit', value: codomainUnit }
    ]);
    return call('bridge_comm_ring_unit_mul_left', [
        { plicity: 'implicit', value: targetRing },
        { plicity: 'implicit', value: realization.mappedDomain },
        { plicity: 'implicit', value: realization.mappedRemoved },
        { plicity: 'explicit', value: productUnit }
    ]);
}
