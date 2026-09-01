/** Selected proof–CAS equations for the operational polynomial Freyd universals. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AlgebraFormalPresentationAgreementRealization,
    AlgebraFormalPresentationMorphismRealization,
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraOperation
} from './algebra_engine';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    serializeAlgebraPolynomialPresentationAgreement,
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    AlgebraPolynomialFreydKernel,
    AlgebraPolynomialFreydKernelLift
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernel,
    AlgebraPolynomialFreydCokernelColift
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraPolynomialFreydCokernelColiftInput,
    AlgebraPolynomialFreydKernelLiftInput,
    algebraPolynomialFreydPreAbelianCategoryModel
} from './algebra_polynomial_freyd_preabelian_category';
import {
    AlgebraPolynomialWeakPullback,
    AlgebraPolynomialWeakPullbackFactorization
} from './algebra_polynomial_weak_pullback';
import {
    serializeAlgebraPolynomialWeakKernel,
    serializeAlgebraPolynomialWeakKernelFactorization
} from './algebra_formal_weak_kernel';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    KernelExpression,
    kernelExpressionEquals
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_PREABELIAN_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-freyd-preabelian-v1' as const,
    equationPolicy: 'selected-operation-output-plus-exact-equation' as const,
    operationReplay: 'native-preabelian-provider' as const,
    claimsRingWideFormalCapability: false as const,
    claimsQuotientPathDecoding: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const mapData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialModuleMap<P, C, I>
) => Object.freeze({
    sourceRank: value.source.rank,
    targetRank: value.target.rank,
    columns: value.columns.map(column =>
        column.components.map(algebraPolynomialText)
    )
});

const presentationData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPresentedPolynomialModule<P, C, I>) => Object.freeze({
    ambientRank: value.ambient.rank,
    relations: value.relations.generators.map(relation =>
        relation.components.map(algebraPolynomialText)
    )
});

const morphismData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialPresentationMorphism<P, C, I>) => Object.freeze({
    source: presentationData(value.source),
    target: presentationData(value.target),
    realization: serializeAlgebraPolynomialPresentationMorphism(value)
});

const weakPullbackData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialWeakPullback<P, C, I>) => Object.freeze({
    left: mapData(value.left),
    right: mapData(value.right),
    difference: mapData(value.difference),
    weakKernel: serializeAlgebraPolynomialWeakKernel(value.weakKernel),
    combinedMorphism: mapData(value.combinedMorphism),
    projectionLeft: mapData(value.projectionLeft),
    projectionRight: mapData(value.projectionRight),
    compatibilityLeft: mapData(value.compatibilityLeft),
    compatibilityRight: mapData(value.compatibilityRight),
    compatible: value.compatible,
    claimsUniqueLifts: value.claimsUniqueLifts
});

const weakPullbackFactorData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialWeakPullbackFactorization<P, C, I>) =>
    Object.freeze({
        weakPullback: weakPullbackData(value.weakPullback),
        testLeft: mapData(value.testLeft),
        testRight: mapData(value.testRight),
        pairedTest: mapData(value.pairedTest),
        weakKernelFactorization:
            serializeAlgebraPolynomialWeakKernelFactorization(
                value.weakKernelFactorization
            ),
        lift: mapData(value.lift),
        reconstructionCombined: mapData(value.reconstructionCombined),
        reconstructionLeft: mapData(value.reconstructionLeft),
        reconstructionRight: mapData(value.reconstructionRight),
        reconstructs: value.reconstructs,
        claimsUniqueLift: value.claimsUniqueLift
    });

export const serializeAlgebraPolynomialFreydKernel = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydKernel<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        morphism: morphismData(value.morphism),
        firstWeakPullback: weakPullbackData(value.firstWeakPullback),
        secondWeakPullback: weakPullbackData(value.secondWeakPullback),
        object: presentationData(value.object),
        embedding: serializeAlgebraPolynomialPresentationMorphism(value.embedding),
        expectedEmbeddingWitness: mapData(value.expectedEmbeddingWitness),
        annihilation:
            serializeAlgebraPolynomialPresentationMorphism(value.annihilation),
        zero: serializeAlgebraPolynomialPresentationMorphism(value.zero),
        annihilationAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.annihilationAgreement
            ),
        annihilates: value.annihilates
    }, 'polynomialFreydKernel');

export const serializeAlgebraPolynomialFreydKernelLift = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydKernelLift<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        kernel: serializeAlgebraPolynomialFreydKernel(value.kernel),
        test: morphismData(value.test),
        zeroComposite:
            serializeAlgebraPolynomialPresentationMorphism(value.zeroComposite),
        zero: serializeAlgebraPolynomialPresentationMorphism(value.zero),
        zeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(value.zeroAgreement),
        zeroWitness: mapData(value.zeroWitness),
        firstFactorization: weakPullbackFactorData(value.firstFactorization),
        sourceRelationsAfterFirstLift:
            mapData(value.sourceRelationsAfterFirstLift),
        secondFactorization: weakPullbackFactorData(value.secondFactorization),
        expectedRelationWitness: mapData(value.expectedRelationWitness),
        lift: serializeAlgebraPolynomialPresentationMorphism(value.lift),
        reconstruction:
            serializeAlgebraPolynomialPresentationMorphism(value.reconstruction),
        reconstructionAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.reconstructionAgreement
            ),
        reconstructs: value.reconstructs
    }, 'polynomialFreydKernelLift');

export const serializeAlgebraPolynomialFreydCokernel = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydCokernel<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        morphism: morphismData(value.morphism),
        object: presentationData(value.object),
        projection:
            serializeAlgebraPolynomialPresentationMorphism(value.projection),
        annihilation:
            serializeAlgebraPolynomialPresentationMorphism(value.annihilation),
        zero: serializeAlgebraPolynomialPresentationMorphism(value.zero),
        annihilationAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.annihilationAgreement
            ),
        annihilates: value.annihilates
    }, 'polynomialFreydCokernel');

export const serializeAlgebraPolynomialFreydCokernelColift = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydCokernelColift<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        cokernel: serializeAlgebraPolynomialFreydCokernel(value.cokernel),
        test: morphismData(value.test),
        zeroComposite:
            serializeAlgebraPolynomialPresentationMorphism(value.zeroComposite),
        zero: serializeAlgebraPolynomialPresentationMorphism(value.zero),
        zeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(value.zeroAgreement),
        colift: serializeAlgebraPolynomialPresentationMorphism(value.colift),
        reconstruction:
            serializeAlgebraPolynomialPresentationMorphism(value.reconstruction),
        reconstructionAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.reconstructionAgreement
            ),
        reconstructs: value.reconstructs
    }, 'polynomialFreydCokernelColift');

type EquationRealization = {
    readonly profileRevision: string;
    readonly selectedOutputData: string;
    readonly claimType: KernelExpression;
};

export interface AlgebraFormalFreydOperationEquationBundle<
    Realization extends EquationRealization,
    Input,
    Output
> {
    readonly realization: Realization;
    readonly adapter: AlgebraFormalComputationAdapter<Realization, Input, Output>;
}

const exactTarget = (
    goal: { readonly target: KernelExpression },
    target: KernelExpression,
    path: string
): void => {
    if (!kernelExpressionEquals(goal.target, target)) {
        throw new AlgebraFormalDelegationError(
            'CLAIM_TARGET_MISMATCH',
            path,
            'Goal differs from the selected Freyd universal equation'
        );
    }
};

const operationEquationBundle = <
    Realization extends EquationRealization,
    Input,
    Output
>(input: {
    readonly id: string;
    readonly operation: AlgebraOperation<Input, Output>;
    readonly operationInput: Input;
    readonly selectedOutputData: string;
    readonly realization: Realization;
    readonly serializeInput: (value: Input) => string;
    readonly serializeOutput: (value: Output) => string;
    readonly summary: string;
}): AlgebraFormalFreydOperationEquationBundle<Realization, Input, Output> => {
    const adapter = defineAlgebraFormalComputationAdapter({
        id: input.id,
        revision: ALGEBRA_FORMAL_FREYD_PREABELIAN_PROFILE.revision,
        operation: input.operation,
        normalizeRealization(value, path) {
            if (!record(value)) {
                throw new AlgebraFormalDelegationError(
                    'INVALID_REALIZATION', path,
                    'Expected one selected Freyd equation realization'
                );
            }
            const candidate = value as unknown as Realization;
            if (
                candidate.profileRevision !== input.realization.profileRevision ||
                candidate.selectedOutputData !==
                    input.realization.selectedOutputData ||
                !kernelExpressionEquals(
                    candidate.claimType,
                    input.realization.claimType
                )
            ) {
                throw new AlgebraFormalDelegationError(
                    'INVALID_REALIZATION', path,
                    'Selected Freyd equation realization has drifted'
                );
            }
            return candidate;
        },
        serializeRealization: value =>
            serializeCoreLfWorkspaceCanonicalJson({
                operationOutput: input.selectedOutputData,
                equationData: value.selectedOutputData,
                claim: serializeCoreExpression(value.claimType)
            }, 'formalFreydOperationEquation'),
        acquire: (goal, value) => {
            exactTarget(goal, value.claimType, 'formalFreydUniversal.goal');
            return input.operationInput;
        },
        serializeInput: input.serializeInput,
        serializeOutput: input.serializeOutput,
        interpret: ({ goal, computed }):
            AlgebraFormalComputationInterpretationInput =>
            input.serializeOutput(computed.value) === input.selectedOutputData
                ? { kind: 'claim', summary: input.summary,
                    claimType: goal.target }
                : { kind: 'observation',
                    summary: 'computed Freyd universal differs from selected data' }
    });
    return Object.freeze({ realization: input.realization, adapter });
};

const serializeMorphismInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialPresentationMorphism<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        morphism: morphismData(value)
    }, 'formalFreydMorphismInput');

const serializeKernelLiftInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydKernelLiftInput<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        morphism: morphismData(value.morphism),
        test: morphismData(value.test),
        maximumReductionSteps: value.maximumReductionSteps ?? null
    }, 'formalFreydKernelLiftInput');

const serializeCokernelColiftInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydCokernelColiftInput<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        morphism: morphismData(value.morphism),
        test: morphismData(value.test)
    }, 'formalFreydCokernelColiftInput');

export function algebraFormalFreydKernelDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydKernel<P, C, I>;
}) {
    const model = algebraPolynomialFreydPreAbelianCategoryModel(
        input.selected.morphism.source.ambient.ring
    );
    const selectedOutputData = serializeAlgebraPolynomialFreydKernel(
        input.selected
    );
    const operation = model.native.operations.kernel;
    const structuralRealization =
        defineAlgebraFormalPresentationMorphismRealization({
            reifier: input.reifier,
            selected: input.selected.embedding
        });
    const annihilationRealization =
        defineAlgebraFormalPresentationAgreementRealization({
            reifier: input.reifier,
            selected: input.selected.annihilationAgreement
        });
    const common = {
        operation,
        operationInput: input.selected.morphism,
        selectedOutputData,
        serializeInput: serializeMorphismInput,
        serializeOutput: serializeAlgebraPolynomialFreydKernel
    };
    return Object.freeze({
        model,
        structural: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-kernel-embedding/` +
                input.selected.morphism.source.ambient.ring.identity.id,
            realization: structuralRealization,
            summary: 'selected Freyd kernel embedding preserves relations'
        }),
        annihilation: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-kernel-annihilation/` +
                input.selected.morphism.source.ambient.ring.identity.id,
            realization: annihilationRealization,
            summary: 'selected Freyd kernel composite agrees with zero'
        })
    });
}

export function algebraFormalFreydKernelLiftDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydKernelLift<P, C, I>;
    readonly maximumReductionSteps?: number;
}) {
    const model = algebraPolynomialFreydPreAbelianCategoryModel(
        input.selected.kernel.morphism.source.ambient.ring
    );
    const selectedOutputData = serializeAlgebraPolynomialFreydKernelLift(
        input.selected
    );
    const operationInput = Object.freeze({
        morphism: input.selected.kernel.morphism,
        test: input.selected.test,
        ...(input.maximumReductionSteps === undefined
            ? {}
            : { maximumReductionSteps: input.maximumReductionSteps })
    });
    const common = {
        operation: model.native.operations.kernelLift,
        operationInput,
        selectedOutputData,
        serializeInput: serializeKernelLiftInput,
        serializeOutput: serializeAlgebraPolynomialFreydKernelLift
    };
    const ringId = input.selected.kernel.morphism.source.ambient.ring.identity.id;
    return Object.freeze({
        model,
        structural: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-kernel-lift/` + ringId,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: input.selected.lift
            }),
            summary: 'selected Freyd kernel lift preserves relations'
        }),
        reconstruction: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-kernel-reconstruction/` + ringId,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.reconstructionAgreement
            }),
            summary: 'selected Freyd kernel lift reconstructs the test morphism'
        })
    });
}

export function algebraFormalFreydCokernelDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydCokernel<P, C, I>;
}) {
    const model = algebraPolynomialFreydPreAbelianCategoryModel(
        input.selected.morphism.source.ambient.ring
    );
    const selectedOutputData = serializeAlgebraPolynomialFreydCokernel(
        input.selected
    );
    const common = {
        operation: model.native.operations.cokernel,
        operationInput: input.selected.morphism,
        selectedOutputData,
        serializeInput: serializeMorphismInput,
        serializeOutput: serializeAlgebraPolynomialFreydCokernel
    };
    const ringId = input.selected.morphism.source.ambient.ring.identity.id;
    return Object.freeze({
        model,
        structural: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-cokernel-projection/` + ringId,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: input.selected.projection
            }),
            summary: 'selected Freyd cokernel projection preserves relations'
        }),
        annihilation: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-cokernel-annihilation/` + ringId,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.annihilationAgreement
            }),
            summary: 'selected Freyd cokernel composite agrees with zero'
        })
    });
}

export function algebraFormalFreydCokernelColiftDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydCokernelColift<P, C, I>;
}) {
    const model = algebraPolynomialFreydPreAbelianCategoryModel(
        input.selected.cokernel.morphism.source.ambient.ring
    );
    const selectedOutputData = serializeAlgebraPolynomialFreydCokernelColift(
        input.selected
    );
    const operationInput = Object.freeze({
        morphism: input.selected.cokernel.morphism,
        test: input.selected.test
    });
    const common = {
        operation: model.native.operations.cokernelColift,
        operationInput,
        selectedOutputData,
        serializeInput: serializeCokernelColiftInput,
        serializeOutput: serializeAlgebraPolynomialFreydCokernelColift
    };
    const ringId = input.selected.cokernel.morphism.source.ambient.ring.identity.id;
    return Object.freeze({
        model,
        structural: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-cokernel-colift/` + ringId,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: input.selected.colift
            }),
            summary: 'selected Freyd cokernel colift preserves relations'
        }),
        reconstruction: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-cokernel-reconstruction/` + ringId,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.reconstructionAgreement
            }),
            summary: 'selected Freyd cokernel colift reconstructs the test morphism'
        })
    });
}

export type AlgebraFormalFreydStructuralRealization<P extends AlgebraParent,
    C extends AlgebraElement<P>, I> =
    AlgebraFormalPresentationMorphismRealization<P, C, I>;

export type AlgebraFormalFreydAgreementRealization<P extends AlgebraParent,
    C extends AlgebraElement<P>, I> =
    AlgebraFormalPresentationAgreementRealization<P, C, I>;
