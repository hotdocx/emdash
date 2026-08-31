/** Goal-aware ideal-membership delegation for selected formal equalities. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    affineFormalRingElementType,
    affineFormalRingEqualityType
} from './algebra_formal_conformance';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    AlgebraGroebnerBasis,
    AlgebraIdealMembership,
    algebraGroebnerBasisSchema,
    serializeAlgebraGroebnerBasis
} from './algebra_ideal';
import {
    AlgebraIdealMembershipInput,
    AlgebraIdealReferenceOperations,
    algebraIdealReferenceOperations
} from './algebra_ideal_reference_operations';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialEquals,
    algebraPolynomialSchema,
    algebraPolynomialSubtract,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    KernelExpression,
    kernelExpressionEquals
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-ideal-delegation-v1' as const,
    realizationRevision:
        'emdash-algebra-formal-ideal-equality-realization-v1' as const,
    adapterRevision: 'emdash-algebra-formal-ideal-equality-adapter-v1' as const,
    operation: 'algebra.ideal.membership' as const,
    claim: 'selected-formal-left-equals-right' as const,
    formalRelationPolicy: 'trusted-selected-ideal-relations' as const,
    negativePolicy: 'observation-with-remainder' as const,
    addsFormalQuotientOwner: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export type AlgebraFormalIdealDelegationErrorCode =
    | 'INVALID_REALIZATION'
    | 'FOREIGN_POLYNOMIAL_RING';

export class AlgebraFormalIdealDelegationError extends Error {
    constructor(
        public readonly code: AlgebraFormalIdealDelegationErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalIdealDelegationError';
    }
}

const fail = (
    code: AlgebraFormalIdealDelegationErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalIdealDelegationError(code, path, message);
};

const sameIdentity = (
    left: { readonly id: string; readonly revision: string },
    right: { readonly id: string; readonly revision: string }
): boolean => left.id === right.id && left.revision === right.revision;

export interface AlgebraFormalIdealEqualityRealizationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
    readonly left: AlgebraPolynomial<P, C, I>;
    readonly right: AlgebraPolynomial<P, C, I>;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
}

export interface AlgebraFormalIdealEqualityRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.realizationRevision;
    readonly relationPolicy:
        typeof ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.formalRelationPolicy;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
    readonly left: AlgebraPolynomial<P, C, I>;
    readonly right: AlgebraPolynomial<P, C, I>;
    readonly difference: AlgebraPolynomial<P, C, I>;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly formalLeft: KernelExpression;
    readonly formalRight: KernelExpression;
    readonly formalIdealGenerators: readonly KernelExpression[];
    readonly claimType: KernelExpression;
}

export function defineAlgebraFormalIdealEqualityRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AlgebraFormalIdealEqualityRealizationInput<P, C, I>
): AlgebraFormalIdealEqualityRealization<P, C, I> {
    const ring = input.basis.ideal.ring;
    if (!sameIdentity(
        ring.identity,
        input.reifier.algebra.quotient.polynomialRing.identity
    )) {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            'idealEqualityRealization.reifier',
            'Ideal basis and formal polynomial reifier use different rings'
        );
    }
    const polynomialSchema = algebraPolynomialSchema(ring);
    const left = polynomialSchema.normalize(
        input.left,
        'idealEqualityRealization.left'
    );
    const right = polynomialSchema.normalize(
        input.right,
        'idealEqualityRealization.right'
    );
    const difference = algebraPolynomialSubtract(left, right);
    const formalLeft = input.reifier.reifyPolynomial(left);
    const formalRight = input.reifier.reifyPolynomial(right);
    const formalIdealGenerators = Object.freeze(
        input.basis.ideal.generators.map(generator =>
            input.reifier.reifyPolynomial(generator)
        )
    );
    const claimType = affineFormalRingEqualityType(
        input.reifier.formalRing,
        formalLeft,
        formalRight
    );
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.realizationRevision,
        relationPolicy:
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.formalRelationPolicy,
        basis: input.basis,
        left,
        right,
        difference,
        reifier: input.reifier,
        formalLeft,
        formalRight,
        formalIdealGenerators,
        claimType
    });
}

const serializeMembershipInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: AlgebraIdealMembershipInput<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: 'algebra-ideal-membership-input',
        polynomial: algebraPolynomialText(input.polynomial),
        basis: serializeAlgebraGroebnerBasis(input.basis)
    }, 'algebraFormalIdealMembershipInput');

export const serializeAlgebraFormalIdealMembership = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(output: AlgebraIdealMembership<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: output.kind,
        polynomial: algebraPolynomialText(output.polynomial),
        basis: serializeAlgebraGroebnerBasis(output.basis),
        member: output.member,
        coefficients: output.coefficients.map(algebraPolynomialText),
        remainder: algebraPolynomialText(output.remainder),
        basisQuotients: output.basisQuotients.map(algebraPolynomialText),
        reductionSteps: output.reductionSteps
    }, 'algebraFormalIdealMembership');

const serializeRealization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(realization: AlgebraFormalIdealEqualityRealization<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        serializationRevision:
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.realizationRevision,
        relationPolicy: realization.relationPolicy,
        basis: serializeAlgebraGroebnerBasis(realization.basis),
        left: algebraPolynomialText(realization.left),
        right: algebraPolynomialText(realization.right),
        difference: algebraPolynomialText(realization.difference),
        formalRing: serializeCoreExpression(realization.reifier.formalRing),
        formalLeft: serializeCoreExpression(realization.formalLeft),
        formalRight: serializeCoreExpression(realization.formalRight),
        formalIdealGenerators: realization.formalIdealGenerators.map(term =>
            serializeCoreExpression(term)
        ),
        claimType: serializeCoreExpression(realization.claimType)
    }, 'algebraFormalIdealEqualityRealization');

const normalizeRealization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path: string
): AlgebraFormalIdealEqualityRealization<P, C, I> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        (value as { profileRevision?: unknown }).profileRevision !==
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.realizationRevision ||
        (value as { relationPolicy?: unknown }).relationPolicy !==
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.formalRelationPolicy
    ) {
        return fail(
            'INVALID_REALIZATION',
            path,
            'Expected one current formal ideal-equality realization'
        );
    }
    const realization = value as
        AlgebraFormalIdealEqualityRealization<P, C, I>;
    if (!sameIdentity(realization.basis.ideal.ring.identity, ring.identity)) {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            path,
            'Formal ideal-equality realization belongs to a foreign ring'
        );
    }
    algebraGroebnerBasisSchema(ring).normalize(
        realization.basis,
        `${path}.basis`
    );
    return realization;
};

export interface AlgebraFormalIdealEqualityDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.adapterRevision;
    readonly operations: AlgebraIdealReferenceOperations<P, C, I>;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalIdealEqualityRealization<P, C, I>,
        AlgebraIdealMembershipInput<P, C, I>,
        AlgebraIdealMembership<P, C, I>
    >;
}

export function algebraFormalIdealEqualityDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraFormalIdealEqualityDelegationBundle<P, C, I> {
    const operations = algebraIdealReferenceOperations(ring);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.ideal-equality/${ring.identity.id}`,
        revision: ring.identity.revision,
        operation: operations.membership,
        normalizeRealization: (value, path) =>
            normalizeRealization(ring, value, path),
        serializeRealization,
        acquire: (goal, realization) => {
            if (!kernelExpressionEquals(goal.target, realization.claimType)) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'idealEqualityAdapter.goal.target',
                    'Named proof goal differs from the selected quotient equality'
                );
            }
            return Object.freeze({
                polynomial: realization.difference,
                basis: realization.basis
            });
        },
        serializeInput: serializeMembershipInput,
        serializeOutput: serializeAlgebraFormalIdealMembership,
        interpret: ({ goal, realization, computed }):
            AlgebraFormalComputationInterpretationInput => {
            const output = computed.value;
            if (
                !algebraPolynomialEquals(
                    output.polynomial,
                    realization.difference
                ) ||
                serializeAlgebraGroebnerBasis(output.basis) !==
                    serializeAlgebraGroebnerBasis(realization.basis)
            ) {
                return {
                    kind: 'observation',
                    summary: 'membership output belongs to a different ' +
                        'polynomial or basis'
                };
            }
            if (!output.member) {
                return {
                    kind: 'observation',
                    summary: `selected quotient equality does not hold; ` +
                        `remainder ${algebraPolynomialText(output.remainder)}`
                };
            }
            const elementType = affineFormalRingElementType(
                realization.reifier.formalRing
            );
            const coefficientTerms = output.coefficients.map(coefficient =>
                realization.reifier.reifyPolynomial(coefficient)
            );
            return {
                kind: 'claim',
                summary: 'difference belongs to the selected ideal',
                claimType: goal.target,
                data: coefficientTerms.map((term, index) => ({
                    id: `membership-coefficient-${index}`,
                    type: elementType,
                    term
                }))
            };
        }
    });
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_IDEAL_DELEGATION_PROFILE.adapterRevision,
        operations,
        adapter
    });
}
