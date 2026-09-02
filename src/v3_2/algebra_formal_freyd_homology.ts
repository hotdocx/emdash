/** Selected proof–CAS equations for polynomial Freyd homology. */

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
    AlgebraPolynomialFreydExactnessAt,
    AlgebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_functorial_homology';
import {
    algebraPolynomialFreydHomologyCategoryModel
} from './algebra_polynomial_freyd_homology_category';
import {
    AlgebraPolynomialFreydChainPairInput,
    AlgebraPolynomialFreydHomologyChainMapInput,
    serializeAlgebraPolynomialFreydChainPair,
    serializeAlgebraPolynomialFreydExactnessAt,
    serializeAlgebraPolynomialFreydHomologyAt,
    serializeAlgebraPolynomialFreydHomologyChainMap,
    serializeAlgebraPolynomialFreydInducedHomologyMap
} from './algebra_polynomial_freyd_homology_reference_operations';
import {
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
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

export const ALGEBRA_FORMAL_FREYD_HOMOLOGY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-freyd-homology-v1' as const,
    equationPolicy: 'selected-whole-output-plus-exact-equations' as const,
    operationReplay: 'native-freyd-homology-provider' as const,
    exactEquationCount: 14 as const,
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

export interface AlgebraFormalFreydHomologyEquationBundle<
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
            'Goal differs from the selected Freyd homology equation'
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
}): AlgebraFormalFreydHomologyEquationBundle<Realization, Input, Output> => {
    const adapter = defineAlgebraFormalComputationAdapter({
        id: input.id,
        revision: ALGEBRA_FORMAL_FREYD_HOMOLOGY_PROFILE.revision,
        operation: input.operation,
        normalizeRealization(value, path) {
            if (!record(value)) {
                throw new AlgebraFormalDelegationError(
                    'INVALID_REALIZATION',
                    path,
                    'Expected one selected Freyd homology realization'
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
                    'Selected Freyd homology realization has drifted'
                );
            }
            return candidate;
        },
        serializeRealization: value =>
            serializeCoreLfWorkspaceCanonicalJson({
                operationOutput: input.selectedOutputData,
                equationData: value.selectedOutputData,
                claim: serializeCoreExpression(value.claimType)
            }, 'formalFreydHomologyOperationEquation'),
        acquire: (goal, value) => {
            exactTarget(goal, value.claimType, 'formalFreydHomology.goal');
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
                    summary: 'computed Freyd homology data differs from selected'
                }
    });
    return Object.freeze({ realization: input.realization, adapter });
};

const serializePairInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydChainPairInput<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        dNext: serializeAlgebraPolynomialPresentationMorphism(value.dNext),
        d: serializeAlgebraPolynomialPresentationMorphism(value.d)
    }, 'formalFreydHomologyPairInput');

const serializeChainMapInput = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydHomologyChainMapInput<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        source: serializeAlgebraPolynomialFreydHomologyAt(value.source),
        target: serializeAlgebraPolynomialFreydHomologyAt(value.target),
        fNext: serializeAlgebraPolynomialPresentationMorphism(value.fNext),
        f: serializeAlgebraPolynomialPresentationMorphism(value.f),
        fPrev: serializeAlgebraPolynomialPresentationMorphism(value.fPrev)
    }, 'formalFreydHomologyChainMapInput');

export function algebraFormalFreydHomologyDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydHomologyAt<P, C, I>;
}) {
    const selected = input.selected;
    const ring = selected.pair.dNext.source.ambient.ring;
    const model = algebraPolynomialFreydHomologyCategoryModel(ring);
    const ringId = ring.identity.id;
    const pairInput = Object.freeze({
        dNext: selected.pair.dNext,
        d: selected.pair.d
    });
    const pairCommon = {
        operation: model.native.chainPair,
        operationInput: pairInput,
        selectedOutputData: serializeAlgebraPolynomialFreydChainPair(
            selected.pair
        ),
        serializeInput: serializePairInput,
        serializeOutput: serializeAlgebraPolynomialFreydChainPair
    };
    const homologyCommon = {
        operation: model.native.homologyAt,
        operationInput: selected.pair,
        selectedOutputData: serializeAlgebraPolynomialFreydHomologyAt(selected),
        serializeInput: serializeAlgebraPolynomialFreydChainPair,
        serializeOutput: serializeAlgebraPolynomialFreydHomologyAt
    };
    return Object.freeze({
        model,
        chain: operationEquationBundle({
            ...pairCommon,
            id: `proof-cas.freyd-homology-chain/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: selected.pair.chainAgreement
            }),
            summary: 'selected adjacent Freyd composite agrees with zero'
        }),
        boundary: operationEquationBundle({
            ...homologyCommon,
            id: `proof-cas.freyd-homology-boundary/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: selected.boundaryMorphism
            }),
            summary: 'selected Freyd homology boundary preserves relations'
        }),
        boundaryReconstruction: operationEquationBundle({
            ...homologyCommon,
            id: `proof-cas.freyd-homology-boundary-reconstruction/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: selected.boundaryReconstruction
            }),
            summary: 'cycle embedding reconstructs the selected boundary'
        }),
        projection: operationEquationBundle({
            ...homologyCommon,
            id: `proof-cas.freyd-homology-projection/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: selected.homologyProjection
            }),
            summary: 'selected Freyd homology projection preserves relations'
        }),
        annihilation: operationEquationBundle({
            ...homologyCommon,
            id: `proof-cas.freyd-homology-annihilation/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: selected.homologyAnnihilation
            }),
            summary: 'homology projection annihilates the selected boundary'
        })
    });
}

export function algebraFormalFreydExactnessDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydExactnessAt<P, C, I>;
}) {
    if (!input.selected.exact || input.selected.epimorphism === undefined) {
        throw new Error('Formal exactness claims require a positive witness');
    }
    const ring = input.selected.homology.pair.dNext.source.ambient.ring;
    const model = algebraPolynomialFreydHomologyCategoryModel(ring);
    const selectedOutputData = serializeAlgebraPolynomialFreydExactnessAt(
        input.selected
    );
    return Object.freeze({
        model,
        projectionZero: operationEquationBundle({
            id: `proof-cas.freyd-homology-exactness/${ring.identity.id}`,
            operation: model.native.exactnessAt,
            operationInput: input.selected.homology,
            selectedOutputData,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: input.selected.projectionZeroAgreement
            }),
            serializeInput: serializeAlgebraPolynomialFreydHomologyAt,
            serializeOutput: serializeAlgebraPolynomialFreydExactnessAt,
            summary: 'exact boundary has zero selected homology projection'
        })
    });
}

export function algebraFormalFreydInducedHomologyDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>;
}) {
    const selected = input.selected;
    const ring = selected.chainMap.source.pair.dNext.source.ambient.ring;
    const model = algebraPolynomialFreydHomologyCategoryModel(ring);
    const ringId = ring.identity.id;
    const chainMapInput = Object.freeze({
        source: selected.chainMap.source,
        target: selected.chainMap.target,
        fNext: selected.chainMap.fNext,
        f: selected.chainMap.f,
        fPrev: selected.chainMap.fPrev
    });
    const chainCommon = {
        operation: model.native.chainMap,
        operationInput: chainMapInput,
        selectedOutputData: serializeAlgebraPolynomialFreydHomologyChainMap(
            selected.chainMap
        ),
        serializeInput: serializeChainMapInput,
        serializeOutput: serializeAlgebraPolynomialFreydHomologyChainMap
    };
    const inducedCommon = {
        operation: model.native.inducedHomologyMap,
        operationInput: selected.chainMap,
        selectedOutputData:
            serializeAlgebraPolynomialFreydInducedHomologyMap(selected),
        serializeInput: serializeAlgebraPolynomialFreydHomologyChainMap,
        serializeOutput: serializeAlgebraPolynomialFreydInducedHomologyMap
    };
    const agreement = (
        id: string,
        value: Parameters<
            typeof defineAlgebraFormalPresentationAgreementRealization<
                P, C, I
            >
        >[0]['selected'],
        summary: string
    ) => operationEquationBundle({
        ...inducedCommon,
        id: `proof-cas.${id}/${ringId}`,
        realization: defineAlgebraFormalPresentationAgreementRealization({
            reifier: input.reifier,
            selected: value
        }),
        summary
    });
    return Object.freeze({
        model,
        upperSquare: operationEquationBundle({
            ...chainCommon,
            id: `proof-cas.freyd-homology-upper-square/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: selected.chainMap.upperAgreement
            }),
            summary: 'selected upper chain square agrees'
        }),
        lowerSquare: operationEquationBundle({
            ...chainCommon,
            id: `proof-cas.freyd-homology-lower-square/${ringId}`,
            realization: defineAlgebraFormalPresentationAgreementRealization({
                reifier: input.reifier,
                selected: selected.chainMap.lowerAgreement
            }),
            summary: 'selected lower chain square agrees'
        }),
        cyclesMap: operationEquationBundle({
            ...inducedCommon,
            id: `proof-cas.freyd-homology-cycles-map/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: selected.cyclesMorphism
            }),
            summary: 'selected cycles map preserves relations'
        }),
        cyclesReconstruction: agreement(
            'freyd-homology-cycles-reconstruction',
            selected.cyclesReconstruction,
            'target cycle embedding reconstructs the cycles map'
        ),
        boundaryCompatibility: agreement(
            'freyd-homology-boundary-compatibility',
            selected.boundaryCompatibility,
            'selected cycles map preserves boundaries'
        ),
        sourceBoundaryZero: agreement(
            'freyd-homology-source-boundary-zero',
            selected.sourceBoundaryZeroAgreement,
            'target homology projection annihilates the source boundary'
        ),
        homologyMap: operationEquationBundle({
            ...inducedCommon,
            id: `proof-cas.freyd-induced-homology-map/${ringId}`,
            realization: defineAlgebraFormalPresentationMorphismRealization({
                reifier: input.reifier,
                selected: selected.homologyMap
            }),
            summary: 'selected induced homology map preserves relations'
        }),
        homologyReconstruction: agreement(
            'freyd-induced-homology-reconstruction',
            selected.homologyReconstruction,
            'source homology projection reconstructs the induced map'
        )
    });
}
