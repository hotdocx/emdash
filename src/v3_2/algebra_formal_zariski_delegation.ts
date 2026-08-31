/** Goal-aware delegation of exact unimodular computations to formal laws. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AffineFormalCoverRealization
} from './algebra_formal_realization';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    affineFormalRingElementType,
    affineFormalUnimodularLawType
} from './algebra_formal_conformance';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    AlgebraPolynomialIdeal,
    algebraPolynomialIdealSchema,
    serializeAlgebraPolynomialIdeal
} from './algebra_ideal';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialEquals,
    algebraPolynomialSchema,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraUnimodularCombination,
    serializeAlgebraUnimodularCombination
} from './algebra_zariski';
import {
    AlgebraZariskiReferenceOperations,
    algebraZariskiReferenceOperations
} from './algebra_zariski_reference_operations';
import {
    KernelExpression,
    kernelExpressionEquals
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-zariski-delegation-v1' as const,
    realizationRevision:
        'emdash-algebra-formal-zariski-realization-v1' as const,
    adapterRevision: 'emdash-algebra-formal-zariski-adapter-v1' as const,
    operation: 'algebra.zariski.unimodular' as const,
    positivePolicy: 'exact-selected-coefficients' as const,
    negativePolicy: 'observation-with-remainder' as const,
    relationfulCoverBridge: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export type AlgebraFormalZariskiDelegationErrorCode =
    | 'INVALID_REALIZATION'
    | 'FOREIGN_POLYNOMIAL_RING'
    | 'COEFFICIENT_ARITY_MISMATCH'
    | 'FORMAL_COVER_MISMATCH';

export class AlgebraFormalZariskiDelegationError extends Error {
    constructor(
        public readonly code: AlgebraFormalZariskiDelegationErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalZariskiDelegationError';
    }
}

const fail = (
    code: AlgebraFormalZariskiDelegationErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalZariskiDelegationError(code, path, message);
};

const sameIdentity = (
    left: { readonly id: string; readonly revision: string },
    right: { readonly id: string; readonly revision: string }
): boolean => left.id === right.id && left.revision === right.revision;

export interface AlgebraFormalZariskiDelegationRealizationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly candidateCoefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly formalCover?: AffineFormalCoverRealization<P, C, I>;
}

export interface AlgebraFormalZariskiDelegationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.realizationRevision;
    readonly ideal: AlgebraPolynomialIdeal<P, C, I>;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly candidateCoefficients: readonly AlgebraPolynomial<P, C, I>[];
    readonly formalGeneratorTerms: readonly KernelExpression[];
    readonly formalCoefficientTerms: readonly KernelExpression[];
    readonly claimType: KernelExpression;
    readonly formalCover?: AffineFormalCoverRealization<P, C, I>;
}

export function defineAlgebraFormalZariskiDelegationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AlgebraFormalZariskiDelegationRealizationInput<P, C, I>
): AlgebraFormalZariskiDelegationRealization<P, C, I> {
    const ring = input.ideal.ring;
    if (!sameIdentity(
        ring.identity,
        input.reifier.algebra.quotient.polynomialRing.identity
    )) {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            'zariskiRealization.reifier',
            'Ideal and formal polynomial reifier use different rings'
        );
    }
    if (input.candidateCoefficients.length !== input.ideal.generators.length) {
        return fail(
            'COEFFICIENT_ARITY_MISMATCH',
            'zariskiRealization.candidateCoefficients',
            `Expected ${input.ideal.generators.length} candidate coefficients`
        );
    }
    const polynomialSchema = algebraPolynomialSchema(ring);
    const candidateCoefficients = Object.freeze(
        input.candidateCoefficients.map((coefficient, index) =>
            polynomialSchema.normalize(
                coefficient,
                `zariskiRealization.candidateCoefficients[${index}]`
            )
        )
    );
    const formalGeneratorTerms = Object.freeze(input.ideal.generators.map(
        generator => input.reifier.reifyPolynomial(generator)
    ));
    const formalCoefficientTerms = Object.freeze(candidateCoefficients.map(
        coefficient => input.reifier.reifyPolynomial(coefficient)
    ));
    const claimType = affineFormalUnimodularLawType({
        formalRing: input.reifier.formalRing,
        generatorTerms: formalGeneratorTerms,
        coefficientTerms: formalCoefficientTerms
    });

    if (input.formalCover !== undefined) {
        const formalCover = input.formalCover;
        if (
            formalCover.status !== 'trusted-computation' ||
            formalCover.formalCoverAvailable ||
            formalCover.cover.relationGeneratorCount !== 0 ||
            !sameIdentity(
                formalCover.algebra.algebra.quotient.polynomialRing.identity,
                ring.identity
            ) ||
            serializeAlgebraPolynomialIdeal(formalCover.cover.unimodular.ideal) !==
                serializeAlgebraPolynomialIdeal(input.ideal) ||
            formalCover.generatorTerms.length !== formalGeneratorTerms.length ||
            formalCover.coefficientTerms.length !==
                formalCoefficientTerms.length ||
            formalCover.generatorTerms.some((term, index) =>
                serializeCoreExpression(term) !==
                    serializeCoreExpression(formalGeneratorTerms[index])
            ) ||
            formalCover.coefficientTerms.some((term, index) =>
                serializeCoreExpression(term) !==
                    serializeCoreExpression(formalCoefficientTerms[index])
            )
        ) {
            return fail(
                'FORMAL_COVER_MISMATCH',
                'zariskiRealization.formalCover',
                'Optional trusted formal cover does not match the selected ' +
                    'zero-relation ideal and candidate law'
            );
        }
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.realizationRevision,
        ideal: input.ideal,
        reifier: input.reifier,
        candidateCoefficients,
        formalGeneratorTerms,
        formalCoefficientTerms,
        claimType,
        ...(input.formalCover === undefined
            ? {}
            : { formalCover: input.formalCover })
    });
}

const serializeRealization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AlgebraFormalZariskiDelegationRealization<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson({
    serializationRevision:
        ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.realizationRevision,
    ideal: serializeAlgebraPolynomialIdeal(realization.ideal),
    formalRing: serializeCoreExpression(realization.reifier.formalRing),
    formalGenerators: realization.formalGeneratorTerms.map(term =>
        serializeCoreExpression(term)
    ),
    candidateCoefficients: realization.candidateCoefficients.map(
        algebraPolynomialText
    ),
    formalCoefficients: realization.formalCoefficientTerms.map(term =>
        serializeCoreExpression(term)
    ),
    claimType: serializeCoreExpression(realization.claimType),
    formalCover: realization.formalCover === undefined
        ? null
        : {
            quotientId: realization.formalCover.algebra.quotientId,
            status: realization.formalCover.status,
            generatorCount: realization.formalCover.generatorTerms.length
        }
}, 'algebraFormalZariskiRealization');

const normalizeRealization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    value: unknown,
    path: string
): AlgebraFormalZariskiDelegationRealization<P, C, I> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        (value as { profileRevision?: unknown }).profileRevision !==
            ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.realizationRevision
    ) {
        return fail(
            'INVALID_REALIZATION',
            path,
            'Expected one current formal Zariski realization'
        );
    }
    const realization = value as
        AlgebraFormalZariskiDelegationRealization<P, C, I>;
    if (!sameIdentity(realization.ideal.ring.identity, ring.identity)) {
        return fail(
            'FOREIGN_POLYNOMIAL_RING',
            path,
            'Formal Zariski realization belongs to a foreign ring'
        );
    }
    algebraPolynomialIdealSchema(ring).normalize(realization.ideal, `${path}.ideal`);
    return realization;
};

const coefficientsAgree = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    output: AlgebraUnimodularCombination<P, C, I>,
    realization: AlgebraFormalZariskiDelegationRealization<P, C, I>
): boolean => output.coefficients.length ===
    realization.candidateCoefficients.length &&
    output.coefficients.every((coefficient, index) =>
        algebraPolynomialEquals(
            coefficient,
            realization.candidateCoefficients[index]
        )
    );

export interface AlgebraFormalZariskiDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.adapterRevision;
    readonly operations: AlgebraZariskiReferenceOperations<P, C, I>;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalZariskiDelegationRealization<P, C, I>,
        AlgebraPolynomialIdeal<P, C, I>,
        AlgebraUnimodularCombination<P, C, I>
    >;
}

export function algebraFormalZariskiDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraFormalZariskiDelegationBundle<P, C, I> {
    const operations = algebraZariskiReferenceOperations(ring);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.zariski-unimodular/${ring.identity.id}`,
        revision: ring.identity.revision,
        operation: operations.unimodular,
        normalizeRealization: (value, path) =>
            normalizeRealization(ring, value, path),
        serializeRealization,
        acquire: (goal, realization) => {
            if (!kernelExpressionEquals(goal.target, realization.claimType)) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'zariskiAdapter.goal.target',
                    'Named proof goal differs from the selected unimodular law'
                );
            }
            return realization.ideal;
        },
        serializeInput: serializeAlgebraPolynomialIdeal,
        serializeOutput: serializeAlgebraUnimodularCombination,
        interpret: ({ goal, realization, computed }):
            AlgebraFormalComputationInterpretationInput => {
            const output = computed.value;
            if (!output.unimodular) {
                return {
                    kind: 'observation',
                    summary: `selected family is not unimodular; remainder ` +
                        algebraPolynomialText(output.remainder)
                };
            }
            if (
                serializeAlgebraPolynomialIdeal(output.ideal) !==
                    serializeAlgebraPolynomialIdeal(realization.ideal) ||
                !coefficientsAgree(output, realization)
            ) {
                return {
                    kind: 'observation',
                    summary: 'exact unimodular output uses coefficients ' +
                        'different from the selected formal goal'
                };
            }
            const elementType = affineFormalRingElementType(
                realization.reifier.formalRing
            );
            return {
                kind: 'claim',
                summary: 'exact selected coefficients have dot product one',
                claimType: goal.target,
                data: realization.formalCoefficientTerms.map((term, index) => ({
                    id: `coefficient-${index}`,
                    type: elementType,
                    term
                }))
            };
        }
    });
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.adapterRevision,
        operations,
        adapter
    });
}
