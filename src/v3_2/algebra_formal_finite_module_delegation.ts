/** Batch proof–CAS delegation for finite-module equations. */

import {
    AlgebraFormalAssumptionSource,
    appendAlgebraFormalAssumption
} from './algebra_formal_assumption_source';
import {
    AlgebraFormalModuleResolutionRealization,
    AlgebraFormalModuleSyzygyRealization,
    algebraFormalResolutionDelegationBundle,
    algebraFormalSyzygyDelegationBundle
} from './algebra_formal_finite_module';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleGroebnerBasis,
    AlgebraPolynomialModuleSchreyerSyzygies,
    AlgebraPolynomialSubmodule
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialSchreyerResolution
} from './algebra_polynomial_presentation';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';
import {
    KernelExpression,
    provenance
} from './kernel';
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

export const ALGEBRA_FORMAL_FINITE_MODULE_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-finite-module-delegation-v1' as const,
    order: 'syzygies-then-adjacent-resolution-composites' as const,
    classification: 'computed-equation' as const,
    addsCoreOwner: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export interface AlgebraFormalFiniteModuleDelegationResult<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_FINITE_MODULE_DELEGATION_PROFILE.revision;
    readonly source: AlgebraFormalAssumptionSource;
    readonly syzygies:
        readonly AlgebraFormalModuleSyzygyRealization<P, C, I>[];
    readonly composites:
        readonly AlgebraFormalModuleResolutionRealization<P, C, I>[];
}

const assumptionStem = (value: string): string => {
    const normalized = value.replace(/[^A-Za-z0-9_]/gu, '_');
    if (/^[A-Za-z][A-Za-z0-9_]*$/u.test(normalized)) return normalized;
    throw new Error('Finite-module artifact ID must begin with a letter');
};

export async function delegateAlgebraFormalFiniteModuleEquations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly artifactId: string;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly selectedSyzygies:
        AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>;
    readonly relations: AlgebraPolynomialSubmodule<P, C, I>;
    readonly maximumLength: number;
    readonly selectedResolution: AlgebraPolynomialSchreyerResolution<P, C, I>;
    readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}): Promise<AlgebraFormalFiniteModuleDelegationResult<P, C, I>> {
    let source = input.source;
    const stem = assumptionStem(input.artifactId);
    const syzygyRealizations: AlgebraFormalModuleSyzygyRealization<P, C, I>[] = [];
    const compositeRealizations:
        AlgebraFormalModuleResolutionRealization<P, C, I>[] = [];
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

    for (
        let index = 0;
        index < input.selectedSyzygies.generators.length;
        index++
    ) {
        const bundle = algebraFormalSyzygyDelegationBundle({
            reifier: input.reifier,
            basis: input.basis,
            selected: input.selectedSyzygies,
            index
        });
        syzygyRealizations.push(bundle.realization);
        const engine = createAlgebraTypeScriptReferenceEngine({
            id: `${input.artifactId}.syzygy-reference`,
            revision: 'v1',
            implementations: bundle.operations.implementations
        });
        const goalId = `${input.artifactId}-syzygy-${index}`;
        const run = await runAlgebraFormalWorkflow({
            document: document(goalId, bundle.realization.claimType),
            goalId,
            adapter: bundle.adapter,
            realization: bundle.realization,
            engine
        });
        const adoption = trustAlgebraFormalWorkflow({
            run,
            assumptionName: `${stem}_syzygy_${index}`,
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: input.decisionEvidence(goalId)
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption,
            classification: 'computed-equation'
        });
    }

    for (
        let index = 0;
        index + 1 < input.selectedResolution.differentials.length;
        index++
    ) {
        const bundle = algebraFormalResolutionDelegationBundle({
            reifier: input.reifier,
            relations: input.relations,
            maximumLength: input.maximumLength,
            selected: input.selectedResolution,
            adjacentIndex: index
        });
        compositeRealizations.push(bundle.realization);
        const engine = createAlgebraTypeScriptReferenceEngine({
            id: `${input.artifactId}.resolution-reference`,
            revision: 'v1',
            implementations: bundle.operations.implementations
        });
        const goalId = `${input.artifactId}-composite-${index}`;
        const run = await runAlgebraFormalWorkflow({
            document: document(goalId, bundle.realization.claimType),
            goalId,
            adapter: bundle.adapter,
            realization: bundle.realization,
            engine
        });
        const adoption = trustAlgebraFormalWorkflow({
            run,
            assumptionName: `${stem}_composite_${index}`,
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: input.decisionEvidence(goalId)
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption,
            classification: 'computed-equation'
        });
    }

    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_FINITE_MODULE_DELEGATION_PROFILE.revision,
        source,
        syzygies: Object.freeze(syzygyRealizations),
        composites: Object.freeze(compositeRealizations)
    });
}
