/** Selected proof–CAS equations for the polynomial Freyd snake construction. */

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
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    AlgebraOperation
} from './algebra_engine';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialFreydSnakeConnecting
} from './algebra_polynomial_freyd_snake';
import {
    algebraPolynomialFreydSnakeCategoryModel
} from './algebra_polynomial_freyd_snake_category';
import {
    serializeAlgebraPolynomialFreydSnakeConnecting,
    serializeAlgebraPolynomialFreydSnakeTriple
} from './algebra_polynomial_freyd_snake_reference_operations';
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

export const ALGEBRA_FORMAL_FREYD_SNAKE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-freyd-snake-v1' as const,
    equationPolicy: 'selected-whole-output-plus-exact-equations' as const,
    operationReplay: 'native-freyd-snake-provider' as const,
    exactEquationCount: 25 as const,
    claimsRingWideFormalCapability: false as const,
    claimsQuotientPathDecoding: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

type EquationRealization = {
    readonly profileRevision: string;
    readonly selectedOutputData: string;
    readonly claimType: KernelExpression;
};

export interface AlgebraFormalFreydSnakeEquationBundle<
    Realization extends EquationRealization,
    Input,
    Output
> {
    readonly realization: Realization;
    readonly adapter: AlgebraFormalComputationAdapter<Realization, Input, Output>;
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const exactTarget = (
    goal: { readonly target: KernelExpression },
    target: KernelExpression,
    path: string
): void => {
    if (!kernelExpressionEquals(goal.target, target)) {
        throw new AlgebraFormalDelegationError(
            'CLAIM_TARGET_MISMATCH',
            path,
            'Goal differs from the selected Freyd snake equation'
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
}): AlgebraFormalFreydSnakeEquationBundle<Realization, Input, Output> => {
    const adapter = defineAlgebraFormalComputationAdapter({
        id: input.id,
        revision: ALGEBRA_FORMAL_FREYD_SNAKE_PROFILE.revision,
        operation: input.operation,
        normalizeRealization(value, path) {
            if (!record(value)) {
                throw new AlgebraFormalDelegationError(
                    'INVALID_REALIZATION',
                    path,
                    'Expected one selected Freyd snake realization'
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
                    'INVALID_REALIZATION',
                    path,
                    'Selected Freyd snake realization has drifted'
                );
            }
            return candidate;
        },
        serializeRealization: value =>
            serializeCoreLfWorkspaceCanonicalJson({
                operationOutput: input.selectedOutputData,
                equationData: value.selectedOutputData,
                claim: serializeCoreExpression(value.claimType)
            }, 'formalFreydSnakeOperationEquation'),
        acquire: (goal, value) => {
            exactTarget(goal, value.claimType, 'formalFreydSnake.goal');
            return input.operationInput;
        },
        serializeInput: input.serializeInput,
        serializeOutput: input.serializeOutput,
        interpret: ({ goal, computed }):
            AlgebraFormalComputationInterpretationInput =>
            input.serializeOutput(computed.value) === input.selectedOutputData
                ? {
                    kind: 'claim',
                    summary: input.summary,
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'computed Freyd snake data differs from selected'
                }
    });
    return Object.freeze({ realization: input.realization, adapter });
};

export function algebraFormalFreydSnakeDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydSnakeConnecting<P, C, I>;
}) {
    const selected = input.selected;
    const ring = selected.triple.delta.source.ambient.ring;
    const model = algebraPolynomialFreydSnakeCategoryModel(ring);
    const ringId = ring.identity.id;
    const common = {
        operation: model.native.connecting,
        operationInput: selected.triple,
        selectedOutputData:
            serializeAlgebraPolynomialFreydSnakeConnecting(selected),
        serializeInput: serializeAlgebraPolynomialFreydSnakeTriple,
        serializeOutput: serializeAlgebraPolynomialFreydSnakeConnecting
    };
    const agreement = (
        id: string,
        value: Parameters<
            typeof defineAlgebraFormalPresentationAgreementRealization<P, C, I>
        >[0]['selected'],
        summary: string
    ) => operationEquationBundle({
        ...common,
        id: `proof-cas.freyd-snake-${id}/${ringId}`,
        realization: defineAlgebraFormalPresentationAgreementRealization({
            reifier: input.reifier,
            selected: value
        }),
        summary
    });
    const morphism = (
        id: string,
        value: Parameters<
            typeof defineAlgebraFormalPresentationMorphismRealization<P, C, I>
        >[0]['selected'],
        summary: string
    ) => operationEquationBundle({
        ...common,
        id: `proof-cas.freyd-snake-${id}/${ringId}`,
        realization: defineAlgebraFormalPresentationMorphismRealization({
            reifier: input.reifier,
            selected: value
        }),
        summary
    });
    return Object.freeze({
        model,
        tripleZero: agreement(
            'triple-zero',
            selected.triple.tripleZeroAgreement,
            'selected lambda-beta-delta composite agrees with zero'
        ),
        deltaCokernelAnnihilation: agreement(
            'delta-cokernel-annihilation',
            selected.deltaCokernel.annihilationAgreement,
            'selected epsilon annihilates delta'
        ),
        gammaTestZero: agreement(
            'gamma-test-zero',
            selected.gammaColift.zeroAgreement,
            'lambda-beta is a valid delta-cokernel test'
        ),
        gammaReconstruction: agreement(
            'gamma-reconstruction',
            selected.gammaColift.reconstructionAgreement,
            'gamma after epsilon reconstructs lambda-beta'
        ),
        gammaKernelAnnihilation: agreement(
            'gamma-kernel-annihilation',
            selected.gammaKernel.annihilationAgreement,
            'gamma annihilates iota'
        ),
        lambdaKernelAnnihilation: agreement(
            'lambda-kernel-annihilation',
            selected.lambdaKernel.annihilationAgreement,
            'lambda annihilates mu'
        ),
        alphaTestZero: agreement(
            'alpha-test-zero',
            selected.alphaLift.zeroAgreement,
            'beta-delta is a valid lambda-kernel test'
        ),
        alphaReconstruction: agreement(
            'alpha-reconstruction',
            selected.alphaLift.reconstructionAgreement,
            'mu after alpha reconstructs beta-delta'
        ),
        alphaCokernelAnnihilation: agreement(
            'alpha-cokernel-annihilation',
            selected.alphaCokernel.annihilationAgreement,
            'pi annihilates alpha'
        ),
        fiberCompatibility: agreement(
            'fiber-compatibility',
            selected.fiberProduct.compatibilityAgreement,
            'selected fiber-product projections equalize iota and epsilon'
        ),
        fiberProjectionLeftReconstruction: agreement(
            'fiber-projection-left-reconstruction',
            selected.fiberProductIdentityFactor.reconstructionLeftAgreement,
            'selected fiber factor reconstructs the first projection'
        ),
        fiberProjectionRightReconstruction: agreement(
            'fiber-projection-right-reconstruction',
            selected.fiberProductIdentityFactor.reconstructionRightAgreement,
            'selected fiber factor reconstructs the second projection'
        ),
        epsilonEpicity: agreement(
            'epsilon-epicity',
            selected.epsilonEpimorphism.cokernelZeroAgreement,
            'epsilon has zero selected cokernel projection'
        ),
        p1Epicity: agreement(
            'p1-epicity',
            selected.p1Epimorphism.cokernelZeroAgreement,
            'p1 has zero selected cokernel projection'
        ),
        muMonicity: agreement(
            'mu-monicity',
            selected.muMonomorphism.kernelZeroAgreement,
            'mu has zero selected kernel embedding'
        ),
        pushoutCompatibility: agreement(
            'pushout-compatibility',
            selected.pushout.compatibilityAgreement,
            'selected pushout injections coequalize mu and pi'
        ),
        pushoutInjectionLeftReconstruction: agreement(
            'pushout-injection-left-reconstruction',
            selected.pushoutIdentityCofactor.reconstructionLeftAgreement,
            'selected pushout cofactor reconstructs the first injection'
        ),
        pushoutInjectionRightReconstruction: agreement(
            'pushout-injection-right-reconstruction',
            selected.pushoutIdentityCofactor.reconstructionRightAgreement,
            'selected pushout cofactor reconstructs the second injection'
        ),
        q2Monicity: agreement(
            'q2-monicity',
            selected.q2Monomorphism.kernelZeroAgreement,
            'q2 has zero selected kernel embedding'
        ),
        normalEpiTest: agreement(
            'normal-epi-test',
            selected.uColift.testKernelZeroAgreement,
            'q1-beta-p2 annihilates the selected kernel of p1'
        ),
        u: morphism(
            'u',
            selected.u,
            'selected normal-epi colift u preserves relations'
        ),
        uReconstruction: agreement(
            'u-reconstruction',
            selected.uColift.reconstructionAgreement,
            'u after p1 reconstructs q1-beta-p2'
        ),
        normalMonoTest: agreement(
            'normal-mono-test',
            selected.connectingLift.testCokernelZeroAgreement,
            'u is annihilated by the selected cokernel of q2'
        ),
        connecting: morphism(
            'connecting',
            selected.connecting,
            'selected snake connecting morphism preserves relations'
        ),
        connectingReconstruction: agreement(
            'connecting-reconstruction',
            selected.connectingLift.reconstructionAgreement,
            'q2 after the connecting morphism reconstructs u'
        )
    });
}
