/** Batch adoption and portable artifact for presentation-morphism equations. */

import {
    AlgebraFormalAssumptionSource,
    appendAlgebraFormalAssumption,
    serializeAlgebraFormalAssumptionSource
} from './algebra_formal_assumption_source';
import {
    AlgebraFormalChainMapSquareRealization,
    AlgebraFormalPresentationAgreementRealization,
    AlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    algebraFormalChainMapSquareDelegationBundle,
    algebraFormalPresentationAgreementDelegationBundle,
    algebraFormalPresentationMorphismDelegationBundle
} from './algebra_formal_presentation_morphism_delegation';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';
import {
    AlgebraPolynomialChainMapSquare,
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    KernelExpression,
    provenance
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreProofArtifactFingerprint
} from './proof_document';
import {
    coreProofPlanHole
} from './proof_plan';
import {
    runAlgebraFormalWorkflow,
    trustAlgebraFormalWorkflow
} from './algebra_formal_workflow';

export const ALGEBRA_FORMAL_PRESENTATION_MORPHISM_BATCH_PROFILE = Object.freeze({
    revision: 'emdash-formal-presentation-morphism-batch-v1' as const,
    order: 'morphisms-then-agreements-then-chain-squares' as const,
    classification: 'computed-equation' as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export interface AlgebraFormalPresentationMorphismBatchResult<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_PRESENTATION_MORPHISM_BATCH_PROFILE.revision;
    readonly source: AlgebraFormalAssumptionSource;
    readonly morphisms:
        readonly AlgebraFormalPresentationMorphismRealization<P, C, I>[];
    readonly agreements:
        readonly AlgebraFormalPresentationAgreementRealization<P, C, I>[];
    readonly chainSquares:
        readonly AlgebraFormalChainMapSquareRealization<P, C, I>[];
}

export const serializeAlgebraFormalPresentationMorphismBatchResult = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraFormalPresentationMorphismBatchResult<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        profileRevision: value.profileRevision,
        source: serializeAlgebraFormalAssumptionSource(value.source),
        morphisms: value.morphisms.map(realization => Object.freeze({
            selected: realization.selectedOutputData,
            claim: serializeCoreExpression(realization.claimType)
        })),
        agreements: value.agreements.map(realization => Object.freeze({
            selected: realization.selectedOutputData,
            claim: serializeCoreExpression(realization.claimType)
        })),
        chainSquares: value.chainSquares.map(realization => Object.freeze({
            selected: realization.selectedOutputData,
            claim: serializeCoreExpression(realization.claimType)
        }))
    }, 'formalPresentationMorphismBatchResult');

const assumptionStem = (value: string): string => {
    const normalized = value.replace(/[^A-Za-z0-9_]/gu, '_');
    if (/^[A-Za-z][A-Za-z0-9_]*$/u.test(normalized)) return normalized;
    throw new Error('Presentation-morphism artifact ID must begin with a letter');
};

export async function delegateAlgebraFormalPresentationMorphismEquations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly artifactId: string;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly morphisms:
        readonly AlgebraPolynomialPresentationMorphism<P, C, I>[];
    readonly agreements:
        readonly AlgebraPolynomialPresentationMorphismAgreement<P, C, I>[];
    readonly chainSquares: readonly AlgebraPolynomialChainMapSquare<P, C, I>[];
    readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}): Promise<AlgebraFormalPresentationMorphismBatchResult<P, C, I>> {
    let source = input.source;
    const stem = assumptionStem(input.artifactId);
    const morphisms: AlgebraFormalPresentationMorphismRealization<P, C, I>[] = [];
    const agreements: AlgebraFormalPresentationAgreementRealization<P, C, I>[] = [];
    const chainSquares: AlgebraFormalChainMapSquareRealization<P, C, I>[] = [];
    const document = (goalId: string, target: KernelExpression) => Object.freeze({
        moduleId: `${input.artifactId}.assumptions`,
        declarationId: goalId,
        environment: source.environment,
        type: target,
        plan: coreProofPlanHole(goalId, {
            provenance: provenance('derived', `generated goal ${goalId}`),
            expectation: { contextDepth: 0, target }
        }),
        provenance: provenance('derived', `generated root ${goalId}`),
        fingerprint: input.fingerprint(goalId)
    });
    const adopt = async <R, Input, Output>(args: {
        readonly goalId: string;
        readonly assumptionName: string;
        readonly target: KernelExpression;
        readonly adapter: AlgebraFormalComputationAdapter<R, Input, Output>;
        readonly realization: R;
        readonly implementations: readonly AlgebraReferenceImplementation[];
    }): Promise<void> => {
        const engine = createAlgebraTypeScriptReferenceEngine({
            id: `${input.artifactId}.reference`,
            revision: 'v1',
            implementations: args.implementations
        });
        const run = await runAlgebraFormalWorkflow({
            document: document(args.goalId, args.target),
            goalId: args.goalId,
            adapter: args.adapter,
            realization: args.realization,
            engine
        });
        const adoption = trustAlgebraFormalWorkflow({
            run,
            assumptionName: args.assumptionName,
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: input.decisionEvidence(args.goalId)
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption,
            classification: 'computed-equation'
        });
    };

    for (let index = 0; index < input.morphisms.length; index++) {
        const bundle = algebraFormalPresentationMorphismDelegationBundle({
            reifier: input.reifier,
            selected: input.morphisms[index]
        });
        morphisms.push(bundle.realization);
        await adopt({
            goalId: `${input.artifactId}-morphism-${index}`,
            assumptionName: `${stem}_morphism_${index}`,
            target: bundle.realization.claimType,
            adapter: bundle.adapter,
            realization: bundle.realization,
            implementations: bundle.operations.implementations
        });
    }
    for (let index = 0; index < input.agreements.length; index++) {
        const bundle = algebraFormalPresentationAgreementDelegationBundle({
            reifier: input.reifier,
            selected: input.agreements[index]
        });
        agreements.push(bundle.realization);
        await adopt({
            goalId: `${input.artifactId}-agreement-${index}`,
            assumptionName: `${stem}_agreement_${index}`,
            target: bundle.realization.claimType,
            adapter: bundle.adapter,
            realization: bundle.realization,
            implementations: bundle.operations.implementations
        });
    }
    for (let index = 0; index < input.chainSquares.length; index++) {
        const bundle = algebraFormalChainMapSquareDelegationBundle({
            reifier: input.reifier,
            selected: input.chainSquares[index]
        });
        chainSquares.push(bundle.realization);
        await adopt({
            goalId: `${input.artifactId}-chain-${index}`,
            assumptionName: `${stem}_chain_${index}`,
            target: bundle.realization.claimType,
            adapter: bundle.adapter,
            realization: bundle.realization,
            implementations: bundle.operations.implementations
        });
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_PRESENTATION_MORPHISM_BATCH_PROFILE.revision,
        source,
        morphisms: Object.freeze(morphisms),
        agreements: Object.freeze(agreements),
        chainSquares: Object.freeze(chainSquares)
    });
}
