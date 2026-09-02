/** Selected proof–CAS equations for constructive polynomial Freyd normality. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    serializeAlgebraPolynomialFreydCokernel,
    serializeAlgebraPolynomialFreydCokernelColift,
    serializeAlgebraPolynomialFreydKernel,
    serializeAlgebraPolynomialFreydKernelLift
} from './algebra_formal_freyd_preabelian';
import {
    serializeAlgebraPolynomialWeakKernelFactorization
} from './algebra_formal_weak_kernel';
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
    AlgebraPolynomialModuleMapRowSplit,
    AlgebraPolynomialFreydColiftAlongEpimorphism,
    AlgebraPolynomialFreydEpimorphismWitness,
    AlgebraPolynomialFreydLiftAlongMonomorphism,
    AlgebraPolynomialFreydMonomorphismWitness
} from './algebra_polynomial_freyd_normality';
import {
    AlgebraPolynomialFreydImageCoimageComparison,
    AlgebraPolynomialFreydImageCoimageIsomorphism
} from './algebra_polynomial_freyd_images';
import {
    AlgebraPolynomialFreydNormalFactorInput,
    algebraPolynomialFreydAbelianCategoryModel
} from './algebra_polynomial_freyd_abelian_category';
import {
    AlgebraPolynomialWeakPullbackFactorization
} from './algebra_polynomial_weak_pullback';
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

export const ALGEBRA_FORMAL_FREYD_ABELIAN_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-freyd-abelian-v1' as const,
    equationPolicy: 'selected-whole-output-plus-exact-equations' as const,
    operationReplay: 'native-abelian-provider' as const,
    claimsRingWideFormalCapability: false as const,
    claimsQuotientPathDecoding: false as const,
    claimsPrimitiveIsomorphism: false as const,
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

const rowSplitData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialModuleMapRowSplit<P, C, I>) => Object.freeze({
    map: mapData(value.map),
    topRows: value.topRows,
    bottomRows: value.bottomRows,
    top: mapData(value.top),
    bottom: mapData(value.bottom),
    reconstructs: value.reconstructs
});

const factorData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialWeakPullbackFactorization<P, C, I>
) => Object.freeze({
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

export const serializeAlgebraPolynomialFreydMonomorphismWitness = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydMonomorphismWitness<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        morphism: morphismData(value.morphism),
        kernel: serializeAlgebraPolynomialFreydKernel(value.kernel),
        zeroEmbedding:
            serializeAlgebraPolynomialPresentationMorphism(value.zeroEmbedding),
        kernelZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.kernelZeroAgreement
            ),
        kernelZeroWitness: mapData(value.kernelZeroWitness),
        monic: value.monic
    }, 'polynomialFreydMonomorphismWitness');

export const serializeAlgebraPolynomialFreydEpimorphismWitness = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydEpimorphismWitness<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        morphism: morphismData(value.morphism),
        cokernel: serializeAlgebraPolynomialFreydCokernel(value.cokernel),
        zeroProjection:
            serializeAlgebraPolynomialPresentationMorphism(value.zeroProjection),
        cokernelZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.cokernelZeroAgreement
            ),
        identityBlocks: rowSplitData(value.identityBlocks),
        targetRelationComponent: mapData(value.targetRelationComponent),
        sourceGeneratorComponent: mapData(value.sourceGeneratorComponent),
        epic: value.epic
    }, 'polynomialFreydEpimorphismWitness');

export const serializeAlgebraPolynomialFreydNormalMonoLift = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        monomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.monomorphism
            ),
        test: morphismData(value.test),
        cokernel: serializeAlgebraPolynomialFreydCokernel(value.cokernel),
        testCokernelComposite:
            serializeAlgebraPolynomialPresentationMorphism(
                value.testCokernelComposite
            ),
        testCokernelZero:
            serializeAlgebraPolynomialPresentationMorphism(
                value.testCokernelZero
            ),
        testCokernelZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.testCokernelZeroAgreement
            ),
        agreementBlocks: rowSplitData(value.agreementBlocks),
        targetRelationComponent: mapData(value.targetRelationComponent),
        liftMap: mapData(value.liftMap),
        liftAfterSourceRelations: mapData(value.liftAfterSourceRelations),
        targetComponentAfterSourceRelations:
            mapData(value.targetComponentAfterSourceRelations),
        weakPullbackRightComponent: mapData(value.weakPullbackRightComponent),
        relationFactorization: factorData(value.relationFactorization),
        expectedRelationWitness: mapData(value.expectedRelationWitness),
        expectedRelationWitnessEquation: value.expectedRelationWitnessEquation,
        lift: serializeAlgebraPolynomialPresentationMorphism(value.lift),
        reconstruction:
            serializeAlgebraPolynomialPresentationMorphism(value.reconstruction),
        reconstructionAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.reconstructionAgreement
            ),
        reconstructs: value.reconstructs
    }, 'polynomialFreydNormalMonoLift');

export const serializeAlgebraPolynomialFreydNormalEpiColift = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        epimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.epimorphism
            ),
        test: morphismData(value.test),
        kernel: serializeAlgebraPolynomialFreydKernel(value.kernel),
        testKernelComposite:
            serializeAlgebraPolynomialPresentationMorphism(
                value.testKernelComposite
            ),
        testKernelZero:
            serializeAlgebraPolynomialPresentationMorphism(value.testKernelZero),
        testKernelZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.testKernelZeroAgreement
            ),
        sourceComponentAfterTargetRelations:
            mapData(value.sourceComponentAfterTargetRelations),
        targetComponentAfterTargetRelations:
            mapData(value.targetComponentAfterTargetRelations),
        weakPullbackRightComponent: mapData(value.weakPullbackRightComponent),
        relationFactorization: factorData(value.relationFactorization),
        coliftMap: mapData(value.coliftMap),
        expectedRelationWitness: mapData(value.expectedRelationWitness),
        expectedRelationWitnessEquation: value.expectedRelationWitnessEquation,
        colift: serializeAlgebraPolynomialPresentationMorphism(value.colift),
        reconstruction:
            serializeAlgebraPolynomialPresentationMorphism(value.reconstruction),
        reconstructionAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.reconstructionAgreement
            ),
        reconstructs: value.reconstructs
    }, 'polynomialFreydNormalEpiColift');

const comparisonData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydImageCoimageComparison<P, C, I>) =>
    Object.freeze({
        kind: value.kind,
        morphism: morphismData(value.morphism),
        kernel: serializeAlgebraPolynomialFreydKernel(value.kernel),
        coimage: serializeAlgebraPolynomialFreydCokernel(value.coimage),
        cokernel: serializeAlgebraPolynomialFreydCokernel(value.cokernel),
        image: serializeAlgebraPolynomialFreydKernel(value.image),
        coastriction:
            serializeAlgebraPolynomialFreydCokernelColift(value.coastriction),
        comparisonLift:
            serializeAlgebraPolynomialFreydKernelLift(value.comparisonLift),
        comparison:
            serializeAlgebraPolynomialPresentationMorphism(value.comparison),
        coastrictionToImage:
            serializeAlgebraPolynomialPresentationMorphism(
                value.coastrictionToImage
            ),
        astrictionFromCoimage:
            serializeAlgebraPolynomialPresentationMorphism(
                value.astrictionFromCoimage
            ),
        factorization:
            serializeAlgebraPolynomialPresentationMorphism(value.factorization),
        factorizationAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.factorizationAgreement
            ),
        factors: value.factors
    });

export const serializeAlgebraPolynomialFreydImageIsomorphism = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydImageCoimageIsomorphism<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        comparison: comparisonData(value.comparison),
        monomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.monomorphism
            ),
        epimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.epimorphism
            ),
        identityImage:
            serializeAlgebraPolynomialPresentationMorphism(value.identityImage),
        identityCoimage:
            serializeAlgebraPolynomialPresentationMorphism(value.identityCoimage),
        inverseFromMonic:
            serializeAlgebraPolynomialFreydNormalMonoLift(
                value.inverseFromMonic
            ),
        inverseFromEpic:
            serializeAlgebraPolynomialFreydNormalEpiColift(
                value.inverseFromEpic
            ),
        inverseCandidatesAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.inverseCandidatesAgreement
            ),
        inverse: serializeAlgebraPolynomialPresentationMorphism(value.inverse),
        comparisonAfterInverse:
            serializeAlgebraPolynomialPresentationMorphism(
                value.comparisonAfterInverse
            ),
        inverseAfterComparison:
            serializeAlgebraPolynomialPresentationMorphism(
                value.inverseAfterComparison
            ),
        rightInverseAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.rightInverseAgreement
            ),
        leftInverseAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.leftInverseAgreement
            ),
        isomorphism: value.isomorphism
    }, 'polynomialFreydImageIsomorphism');

type EquationRealization = {
    readonly profileRevision: string;
    readonly selectedOutputData: string;
    readonly claimType: KernelExpression;
};

export interface AlgebraFormalFreydAbelianEquationBundle<
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
            'Goal differs from the selected Freyd Abelian equation'
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
}): AlgebraFormalFreydAbelianEquationBundle<Realization, Input, Output> => {
    const adapter = defineAlgebraFormalComputationAdapter({
        id: input.id,
        revision: ALGEBRA_FORMAL_FREYD_ABELIAN_PROFILE.revision,
        operation: input.operation,
        normalizeRealization(value, path) {
            if (!record(value)) {
                throw new AlgebraFormalDelegationError(
                    'INVALID_REALIZATION', path,
                    'Expected one selected Freyd Abelian realization'
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
                    'Selected Freyd Abelian realization has drifted'
                );
            }
            return candidate;
        },
        serializeRealization: value =>
            serializeCoreLfWorkspaceCanonicalJson({
                operationOutput: input.selectedOutputData,
                equationData: value.selectedOutputData,
                claim: serializeCoreExpression(value.claimType)
            }, 'formalFreydAbelianOperationEquation'),
        acquire: (goal, value) => {
            exactTarget(goal, value.claimType, 'formalFreydAbelian.goal');
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
                    summary: 'computed Freyd Abelian data differs from selected' }
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
    }, 'formalFreydAbelianMorphismInput');

const serializeNormalFactorInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydNormalFactorInput<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        morphism: morphismData(value.morphism),
        test: morphismData(value.test),
        maximumReductionSteps: value.maximumReductionSteps ?? null
    }, 'formalFreydAbelianFactorInput');

export function algebraFormalFreydMonomorphismDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
}) {
    const model = algebraPolynomialFreydAbelianCategoryModel(
        input.selected.morphism.source.ambient.ring
    );
    const selectedOutputData =
        serializeAlgebraPolynomialFreydMonomorphismWitness(input.selected);
    const ringId = input.selected.morphism.source.ambient.ring.identity.id;
    return Object.freeze({
        model,
        kernelZero: operationEquationBundle({
            id: `proof-cas.freyd-monomorphism-kernel-zero/${ringId}`,
            operation: model.native.operations.monomorphismWitness,
            operationInput: input.selected.morphism,
            selectedOutputData,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.kernelZeroAgreement
            }),
            serializeInput: serializeMorphismInput,
            serializeOutput:
                serializeAlgebraPolynomialFreydMonomorphismWitness,
            summary: 'selected Freyd kernel embedding agrees with zero'
        })
    });
}

export function algebraFormalFreydEpimorphismDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
}) {
    const model = algebraPolynomialFreydAbelianCategoryModel(
        input.selected.morphism.source.ambient.ring
    );
    const selectedOutputData =
        serializeAlgebraPolynomialFreydEpimorphismWitness(input.selected);
    const ringId = input.selected.morphism.source.ambient.ring.identity.id;
    return Object.freeze({
        model,
        cokernelZero: operationEquationBundle({
            id: `proof-cas.freyd-epimorphism-cokernel-zero/${ringId}`,
            operation: model.native.operations.epimorphismWitness,
            operationInput: input.selected.morphism,
            selectedOutputData,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.cokernelZeroAgreement
            }),
            serializeInput: serializeMorphismInput,
            serializeOutput:
                serializeAlgebraPolynomialFreydEpimorphismWitness,
            summary: 'selected Freyd cokernel projection agrees with zero'
        })
    });
}

export function algebraFormalFreydNormalMonoDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>;
    readonly maximumReductionSteps?: number;
}) {
    const model = algebraPolynomialFreydAbelianCategoryModel(
        input.selected.monomorphism.morphism.source.ambient.ring
    );
    const operationInput = Object.freeze({
        morphism: input.selected.monomorphism.morphism,
        test: input.selected.test,
        ...(input.maximumReductionSteps === undefined
            ? {}
            : { maximumReductionSteps: input.maximumReductionSteps })
    });
    const selectedOutputData =
        serializeAlgebraPolynomialFreydNormalMonoLift(input.selected);
    const common = {
        operation: model.native.operations.liftAlongMonomorphism,
        operationInput,
        selectedOutputData,
        serializeInput: serializeNormalFactorInput,
        serializeOutput: serializeAlgebraPolynomialFreydNormalMonoLift
    };
    const ringId = input.selected.monomorphism.morphism.source.ambient.ring
        .identity.id;
    return Object.freeze({
        model,
        structural: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-normal-mono-lift/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: input.selected.lift
            }),
            summary: 'selected Freyd normal-mono lift preserves relations'
        }),
        reconstruction: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-normal-mono-reconstruction/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.reconstructionAgreement
            }),
            summary: 'selected Freyd normal-mono lift reconstructs the test'
        })
    });
}

export function algebraFormalFreydNormalEpiDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>;
    readonly maximumReductionSteps?: number;
}) {
    const model = algebraPolynomialFreydAbelianCategoryModel(
        input.selected.epimorphism.morphism.source.ambient.ring
    );
    const operationInput = Object.freeze({
        morphism: input.selected.epimorphism.morphism,
        test: input.selected.test,
        ...(input.maximumReductionSteps === undefined
            ? {}
            : { maximumReductionSteps: input.maximumReductionSteps })
    });
    const selectedOutputData =
        serializeAlgebraPolynomialFreydNormalEpiColift(input.selected);
    const common = {
        operation: model.native.operations.coliftAlongEpimorphism,
        operationInput,
        selectedOutputData,
        serializeInput: serializeNormalFactorInput,
        serializeOutput: serializeAlgebraPolynomialFreydNormalEpiColift
    };
    const ringId = input.selected.epimorphism.morphism.source.ambient.ring
        .identity.id;
    return Object.freeze({
        model,
        structural: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-normal-epi-colift/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: input.selected.colift
            }),
            summary: 'selected Freyd normal-epi colift preserves relations'
        }),
        reconstruction: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-normal-epi-reconstruction/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.reconstructionAgreement
            }),
            summary: 'selected Freyd normal-epi colift reconstructs the test'
        })
    });
}

export function algebraFormalFreydImageDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydImageCoimageIsomorphism<P, C, I>;
}) {
    const model = algebraPolynomialFreydAbelianCategoryModel(
        input.selected.comparison.morphism.source.ambient.ring
    );
    const selectedOutputData =
        serializeAlgebraPolynomialFreydImageIsomorphism(input.selected);
    const common = {
        operation: model.native.operations.coimageImageIsomorphism,
        operationInput: input.selected.comparison.morphism,
        selectedOutputData,
        serializeInput: serializeMorphismInput,
        serializeOutput: serializeAlgebraPolynomialFreydImageIsomorphism
    };
    const ringId = input.selected.comparison.morphism.source.ambient.ring
        .identity.id;
    const agreement = (
        id: string,
        selected: Parameters<
            typeof defineAlgebraFormalPresentationAgreementRealization<
                P, C, I
            >
        >[0]['selected'],
        summary: string
    ) => operationEquationBundle({
        ...common,
        id: `proof-cas.${id}/${ringId}`,
        realization: defineAlgebraFormalPresentationAgreementRealization({
            reifier: input.reifier,
            selected
        }),
        summary
    });
    return Object.freeze({
        model,
        comparison: operationEquationBundle({
            ...common,
            id: `proof-cas.freyd-image-comparison/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: input.selected.comparison.comparison
            }),
            summary: 'selected coimage-image comparison preserves relations'
        }),
        factorization: agreement(
            'freyd-image-factorization',
            input.selected.comparison.factorizationAgreement,
            'selected comparison factors the original Freyd morphism'
        ),
        comparisonMonic: agreement(
            'freyd-comparison-kernel-zero',
            input.selected.monomorphism.kernelZeroAgreement,
            'selected comparison kernel embedding agrees with zero'
        ),
        comparisonEpic: agreement(
            'freyd-comparison-cokernel-zero',
            input.selected.epimorphism.cokernelZeroAgreement,
            'selected comparison cokernel projection agrees with zero'
        ),
        inverseCandidates: agreement(
            'freyd-comparison-inverse-candidates',
            input.selected.inverseCandidatesAgreement,
            'normal mono and epi comparison inverses agree'
        ),
        leftInverse: agreement(
            'freyd-comparison-left-inverse',
            input.selected.leftInverseAgreement,
            'selected comparison inverse is a left inverse'
        ),
        rightInverse: agreement(
            'freyd-comparison-right-inverse',
            input.selected.rightInverseAgreement,
            'selected comparison inverse is a right inverse'
        )
    });
}
