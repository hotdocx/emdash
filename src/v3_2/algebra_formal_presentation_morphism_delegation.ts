/** Proof–CAS adapters for presentation morphism, agreement, and chain laws. */

import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE,
    AlgebraFormalChainMapSquareRealization,
    AlgebraFormalPresentationAgreementRealization,
    AlgebraFormalPresentationMorphismRealization,
    defineAlgebraFormalChainMapSquareRealization,
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialChainMapSquare,
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialChainMapSquareInput,
    AlgebraPolynomialPresentationAgreementInput,
    AlgebraPolynomialPresentationMorphismInput,
    AlgebraPolynomialPresentationMorphismReferenceOperations,
    algebraPolynomialPresentationMorphismReferenceOperations,
    serializeAlgebraPolynomialChainMapSquare,
    serializeAlgebraPolynomialPresentationAgreement,
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    kernelExpressionEquals
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_PRESENTATION_MORPHISM_DELEGATION_PROFILE =
    Object.freeze({
        revision: 'emdash-formal-presentation-morphism-delegation-v1' as const,
        exactWholeOutput: true as const,
        classifications: 'computed-equation' as const,
        addsCoreOwner: false as const,
        performsIo: false as const,
        productionLambdapiDependency: false as const
    });

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const invalid = (path: string, message: string): never => {
    throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, message);
};

const mapData = (value: {
    readonly source: { readonly rank: number };
    readonly target: { readonly rank: number };
    readonly columns: readonly {
        readonly components: readonly Parameters<typeof algebraPolynomialText>[0][];
    }[];
}) => Object.freeze({
    sourceRank: value.source.rank,
    targetRank: value.target.rank,
    columns: value.columns.map(column =>
        column.components.map(algebraPolynomialText)
    )
});

const goalTarget = (
    target: Parameters<typeof kernelExpressionEquals>[0],
    expected: Parameters<typeof kernelExpressionEquals>[1],
    path: string
): void => {
    if (!kernelExpressionEquals(target, expected)) {
        throw new AlgebraFormalDelegationError(
            'CLAIM_TARGET_MISMATCH',
            path,
            'Goal differs from the selected formal matrix equation'
        );
    }
};

export interface AlgebraFormalPresentationMorphismDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations:
        AlgebraPolynomialPresentationMorphismReferenceOperations<P, C, I>;
    readonly realization: AlgebraFormalPresentationMorphismRealization<P, C, I>;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalPresentationMorphismRealization<P, C, I>,
        AlgebraPolynomialPresentationMorphismInput<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
}

export function algebraFormalPresentationMorphismDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialPresentationMorphism<P, C, I>;
}): AlgebraFormalPresentationMorphismDelegationBundle<P, C, I> {
    const operations =
        algebraPolynomialPresentationMorphismReferenceOperations<P, C, I>();
    const realization = defineAlgebraFormalPresentationMorphismRealization(input);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.presentation-morphism/` +
            input.selected.source.ambient.ring.identity.id,
        revision: input.selected.source.ambient.ring.identity.revision,
        operation: operations.morphism,
        normalizeRealization(value, path) {
            if (
                !record(value) ||
                value.profileRevision !==
                    ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.morphismRevision
            ) return invalid(path, 'Expected one current morphism realization');
            const candidate = value as unknown as typeof realization;
            const expected = defineAlgebraFormalPresentationMorphismRealization({
                reifier: candidate.reifier,
                selected: candidate.selected
            });
            if (
                candidate.selectedOutputData !== expected.selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, expected.claimType)
            ) return invalid(path, 'Morphism realization differs from its equation');
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            map: serializeCoreExpression(value.formalMap),
            witness: serializeCoreExpression(value.formalRelationWitness),
            claim: serializeCoreExpression(value.claimType)
        }, 'formalPresentationMorphismRealization'),
        acquire: (goal, value) => {
            goalTarget(goal.target, value.claimType, 'presentationMorphism.goal');
            return Object.freeze({
                source: value.selected.source,
                target: value.selected.target,
                map: value.selected.map
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            sourceRelations: value.source.relations.generators.map(relation =>
                relation.components.map(algebraPolynomialText)
            ),
            targetRelations: value.target.relations.generators.map(relation =>
                relation.components.map(algebraPolynomialText)
            ),
            map: mapData(value.map)
        }, 'formalPresentationMorphismInput'),
        serializeOutput: serializeAlgebraPolynomialPresentationMorphism,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialPresentationMorphism(computed.value) ===
                value.selectedOutputData && computed.value.preservesRelations
                ? {
                    kind: 'claim',
                    summary: 'selected generator map preserves every relation',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'candidate map has a changed or nonzero relation remainder'
                }
    });
    return Object.freeze({ operations, realization, adapter });
}

export interface AlgebraFormalPresentationAgreementDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations:
        AlgebraPolynomialPresentationMorphismReferenceOperations<P, C, I>;
    readonly realization: AlgebraFormalPresentationAgreementRealization<P, C, I>;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalPresentationAgreementRealization<P, C, I>,
        AlgebraPolynomialPresentationAgreementInput<P, C, I>,
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>
    >;
}

export function algebraFormalPresentationAgreementDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
}): AlgebraFormalPresentationAgreementDelegationBundle<P, C, I> {
    const operations =
        algebraPolynomialPresentationMorphismReferenceOperations<P, C, I>();
    const realization = defineAlgebraFormalPresentationAgreementRealization(input);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.presentation-agreement/` +
            input.selected.source.ambient.ring.identity.id,
        revision: input.selected.source.ambient.ring.identity.revision,
        operation: operations.agreement,
        normalizeRealization(value, path) {
            if (
                !record(value) ||
                value.profileRevision !==
                    ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.agreementRevision
            ) return invalid(path, 'Expected one current agreement realization');
            const candidate = value as unknown as typeof realization;
            const expected = defineAlgebraFormalPresentationAgreementRealization({
                reifier: candidate.reifier,
                selected: candidate.selected
            });
            if (
                candidate.selectedOutputData !== expected.selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, expected.claimType)
            ) return invalid(path, 'Agreement realization differs from its equation');
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            witness: serializeCoreExpression(value.formalAgreementWitness),
            claim: serializeCoreExpression(value.claimType)
        }, 'formalPresentationAgreementRealization'),
        acquire: (goal, value) => {
            goalTarget(goal.target, value.claimType, 'presentationAgreement.goal');
            return Object.freeze({
                source: value.selected.source,
                target: value.selected.target,
                left: value.selected.left,
                right: value.selected.right
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            left: mapData(value.left),
            right: mapData(value.right)
        }, 'formalPresentationAgreementInput'),
        serializeOutput: serializeAlgebraPolynomialPresentationAgreement,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialPresentationAgreement(computed.value) ===
                value.selectedOutputData && computed.value.agrees
                ? {
                    kind: 'claim',
                    summary: 'selected map representatives agree modulo relations',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'map difference has a changed or nonzero remainder'
                }
    });
    return Object.freeze({ operations, realization, adapter });
}

export interface AlgebraFormalChainMapSquareDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly operations:
        AlgebraPolynomialPresentationMorphismReferenceOperations<P, C, I>;
    readonly realization: AlgebraFormalChainMapSquareRealization<P, C, I>;
    readonly adapter: AlgebraFormalComputationAdapter<
        AlgebraFormalChainMapSquareRealization<P, C, I>,
        AlgebraPolynomialChainMapSquareInput<P, C, I>,
        AlgebraPolynomialChainMapSquare<P, C, I>
    >;
}

export function algebraFormalChainMapSquareDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialChainMapSquare<P, C, I>;
}): AlgebraFormalChainMapSquareDelegationBundle<P, C, I> {
    const operations =
        algebraPolynomialPresentationMorphismReferenceOperations<P, C, I>();
    const realization = defineAlgebraFormalChainMapSquareRealization(input);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.chain-map-square/` +
            input.selected.differentialSource.source.ring.identity.id,
        revision: input.selected.differentialSource.source.ring.identity.revision,
        operation: operations.chainSquare,
        normalizeRealization(value, path) {
            if (
                !record(value) ||
                value.profileRevision !==
                    ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.chainSquareRevision
            ) return invalid(path, 'Expected one current chain-square realization');
            const candidate = value as unknown as typeof realization;
            const expected = defineAlgebraFormalChainMapSquareRealization({
                reifier: candidate.reifier,
                selected: candidate.selected
            });
            if (
                candidate.selectedOutputData !== expected.selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, expected.claimType)
            ) return invalid(path, 'Chain-square realization differs from its equation');
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            claim: serializeCoreExpression(value.claimType)
        }, 'formalChainMapSquareRealization'),
        acquire: (goal, value) => {
            goalTarget(goal.target, value.claimType, 'chainMapSquare.goal');
            return Object.freeze({
                differentialSource: value.selected.differentialSource,
                differentialTarget: value.selected.differentialTarget,
                componentPrevious: value.selected.componentPrevious,
                componentNow: value.selected.componentNow
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            differentialSource: mapData(value.differentialSource),
            differentialTarget: mapData(value.differentialTarget),
            componentPrevious: mapData(value.componentPrevious),
            componentNow: mapData(value.componentNow)
        }, 'formalChainMapSquareInput'),
        serializeOutput: serializeAlgebraPolynomialChainMapSquare,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialChainMapSquare(computed.value) ===
                value.selectedOutputData && computed.value.commutes
                ? {
                    kind: 'claim',
                    summary: 'selected chain-map component square commutes',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'chain-map component square does not commute'
                }
    });
    return Object.freeze({ operations, realization, adapter });
}
