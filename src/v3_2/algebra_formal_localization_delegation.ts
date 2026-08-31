/** Proof–CAS delegation for selected principal-localization semantics. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    affineFormalInverseLawType,
    affineFormalLocalizationPropertyType,
    affineFormalLocalizationUniversalFromProperty,
    affineFormalRingElementType
} from './algebra_formal_conformance';
import {
    AffineFormalLocalizationRealization,
    defineAffineFormalLocalizationRealization
} from './algebra_formal_localization';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    AlgebraPrincipalLocalization
} from './algebra_localization';
import {
    AlgebraLocalizationReferenceOperations,
    algebraLocalizationReferenceOperations
} from './algebra_localization_reference_operations';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPresentedAlgebra
} from './algebra_presented_algebra';
import {
    AlgebraQuotientElement,
    algebraQuotientText
} from './algebra_quotient';
import {
    KernelExpression,
    kernelExpressionEquals
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-localization-delegation-v1' as const,
    realizationRevision:
        'emdash-algebra-formal-localization-delegation-realization-v1' as const,
    bundleRevision:
        'emdash-algebra-formal-localization-delegation-bundle-v1' as const,
    inverseClassification: 'computed-equation' as const,
    propertyClassification: 'trusted-presentation-semantics' as const,
    selectedOutputPolicy: 'exact-whole-localization' as const,
    addsCoreOwner: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

const sameIdentity = (
    left: { readonly id: string; readonly revision: string },
    right: { readonly id: string; readonly revision: string }
): boolean => left.id === right.id && left.revision === right.revision;

export const serializeAlgebraPrincipalLocalization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPrincipalLocalization<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        source: {
            id: value.source.quotient.identity.id,
            revision: value.source.quotient.identity.revision
        },
        element: algebraQuotientText(value.element),
        inverseVariable: value.inverseVariable,
        target: {
            id: value.algebra.quotient.identity.id,
            revision: value.algebra.quotient.identity.revision
        },
        canonicalMap: value.canonicalMap.generatorImages.map(
            algebraQuotientText
        ),
        inverse: algebraQuotientText(value.inverse),
        elementImage: algebraQuotientText(value.elementImage),
        inverseProduct: algebraQuotientText(value.inverseProduct),
        inverseEquation: value.inverseEquation
    }, 'algebraPrincipalLocalization');

export interface AlgebraFormalLocalizationDelegationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE.realizationRevision;
    readonly trusted: AffineFormalLocalizationRealization<P, C, I>;
    readonly inverseClaimType: KernelExpression;
    readonly propertyClaimType: KernelExpression;
    readonly selectedOutputData: string;
}

export function defineAlgebraFormalLocalizationDelegationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    trusted: AffineFormalLocalizationRealization<P, C, I>
): AlgebraFormalLocalizationDelegationRealization<P, C, I> {
    if (
        trusted.status !== 'trusted-computation' ||
        trusted.formalUnitAvailable ||
        trusted.formalLocalizationAvailable ||
        trusted.inverseLawTerm !== undefined ||
        trusted.universalTerm !== undefined
    ) {
        throw new AlgebraFormalDelegationError(
            'INVALID_REALIZATION',
            'localizationDelegation.trusted',
            'Localization delegation requires one trusted no-evidence realization'
        );
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE.realizationRevision,
        trusted,
        inverseClaimType: affineFormalInverseLawType(trusted),
        propertyClaimType: affineFormalLocalizationPropertyType(trusted),
        selectedOutputData: serializeAlgebraPrincipalLocalization(
            trusted.localization
        )
    });
}

const normalizeRealization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebra<P, C, I>,
    value: unknown,
    path: string
): AlgebraFormalLocalizationDelegationRealization<P, C, I> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        (value as { profileRevision?: unknown }).profileRevision !==
            ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE.realizationRevision
    ) {
        throw new AlgebraFormalDelegationError(
            'INVALID_REALIZATION',
            path,
            'Expected one current formal localization delegation realization'
        );
    }
    const realization = value as
        AlgebraFormalLocalizationDelegationRealization<P, C, I>;
    if (!sameIdentity(
        realization.trusted.localization.source.quotient.identity,
        source.quotient.identity
    )) {
        throw new AlgebraFormalDelegationError(
            'INVALID_REALIZATION',
            path,
            'Localization delegation realization has a foreign source algebra'
        );
    }
    return realization;
};

const serializeRealization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraFormalLocalizationDelegationRealization<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        serializationRevision:
            ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE.realizationRevision,
        selectedOutputData: value.selectedOutputData,
        formalSource: serializeCoreExpression(value.trusted.source.formalRing),
        formalTarget: serializeCoreExpression(value.trusted.target.formalRing),
        formalMap: serializeCoreExpression(value.trusted.formalMap),
        element: serializeCoreExpression(value.trusted.elementTerm),
        inverse: serializeCoreExpression(value.trusted.inverseTerm),
        inverseClaim: serializeCoreExpression(value.inverseClaimType),
        propertyClaim: serializeCoreExpression(value.propertyClaimType)
    }, 'algebraFormalLocalizationDelegationRealization');

const exactOutput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AlgebraFormalLocalizationDelegationRealization<P, C, I>,
    output: AlgebraPrincipalLocalization<P, C, I>
): boolean => output.inverseEquation &&
    serializeAlgebraPrincipalLocalization(output) ===
        realization.selectedOutputData;

export interface AlgebraFormalLocalizationDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE.bundleRevision;
    readonly operations: AlgebraLocalizationReferenceOperations<P, C, I>;
    readonly inverseAdapter: AlgebraFormalComputationAdapter<
        AlgebraFormalLocalizationDelegationRealization<P, C, I>,
        AlgebraQuotientElement<P, C, I>,
        AlgebraPrincipalLocalization<P, C, I>
    >;
    readonly propertyAdapter: AlgebraFormalComputationAdapter<
        AlgebraFormalLocalizationDelegationRealization<P, C, I>,
        AlgebraQuotientElement<P, C, I>,
        AlgebraPrincipalLocalization<P, C, I>
    >;
}

export function algebraFormalLocalizationDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    source: AlgebraPresentedAlgebra<P, C, I>
): AlgebraFormalLocalizationDelegationBundle<P, C, I> {
    const operations = algebraLocalizationReferenceOperations(source);
    const common = {
        operation: operations.localize,
        normalizeRealization: (value: unknown, path: string) =>
            normalizeRealization(source, value, path),
        serializeRealization,
        serializeInput: (value: AlgebraQuotientElement<P, C, I>) =>
            `${algebraQuotientText(value)}\n`,
        serializeOutput: serializeAlgebraPrincipalLocalization
    };
    const inverseAdapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.localization-inverse/${source.quotient.identity.id}`,
        revision: source.quotient.identity.revision,
        operation: operations.localize,
        normalizeRealization: common.normalizeRealization,
        serializeRealization,
        acquire: (goal, realization) => {
            if (!kernelExpressionEquals(
                goal.target,
                realization.inverseClaimType
            )) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'localizationInverse.goal',
                    'Goal differs from the selected localization inverse law'
                );
            }
            return realization.trusted.localization.element;
        },
        serializeInput: common.serializeInput,
        serializeOutput: serializeAlgebraPrincipalLocalization,
        interpret: ({ goal, realization, computed }):
            AlgebraFormalComputationInterpretationInput => exactOutput(
                realization,
                computed.value
            ) ? {
                kind: 'claim',
                summary: 'selected localization inverse equation holds',
                claimType: goal.target,
                data: [{
                    id: 'localization-inverse',
                    type: affineFormalRingElementType(
                        realization.trusted.target.formalRing
                    ),
                    term: realization.trusted.inverseTerm
                }]
            } : {
                kind: 'observation',
                summary: 'localization output differs from the selected presentation'
            }
    });
    const propertyAdapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.localization-property/${source.quotient.identity.id}`,
        revision: source.quotient.identity.revision,
        operation: operations.localize,
        normalizeRealization: common.normalizeRealization,
        serializeRealization,
        acquire: (goal, realization) => {
            if (!kernelExpressionEquals(
                goal.target,
                realization.propertyClaimType
            )) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'localizationProperty.goal',
                    'Goal differs from the selected localization property'
                );
            }
            return realization.trusted.localization.element;
        },
        serializeInput: common.serializeInput,
        serializeOutput: serializeAlgebraPrincipalLocalization,
        interpret: ({ goal, realization, computed }):
            AlgebraFormalComputationInterpretationInput => exactOutput(
                realization,
                computed.value
            ) ? {
                kind: 'claim',
                summary: 'selected adjoined-inverse presentation semantics',
                claimType: goal.target
            } : {
                kind: 'observation',
                summary: 'localization output differs from the selected presentation'
            }
    });
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_LOCALIZATION_DELEGATION_PROFILE.bundleRevision,
        operations,
        inverseAdapter,
        propertyAdapter
    });
}

export function realizeAdoptedAffineFormalLocalization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly realization:
        AlgebraFormalLocalizationDelegationRealization<P, C, I>;
    readonly inverseLaw: KernelExpression;
    readonly property: KernelExpression;
}): AffineFormalLocalizationRealization<P, C, I> {
    return defineAffineFormalLocalizationRealization({
        localization: input.realization.trusted.localization,
        source: input.realization.trusted.source,
        target: input.realization.trusted.target,
        formalMap: input.realization.trusted.formalMap,
        status: 'explicit-data',
        inverseLawTerm: input.inverseLaw,
        universalTerm: affineFormalLocalizationUniversalFromProperty(
            input.property
        )
    });
}
