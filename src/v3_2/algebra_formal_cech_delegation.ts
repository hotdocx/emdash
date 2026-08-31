/** Uniform whole-cover localization and face delegation pipeline. */

import {
    AlgebraFormalAssumptionSource,
    appendAlgebraFormalAssumption
} from './algebra_formal_assumption_source';
import {
    AlgebraFormalCechFaceDelegationRealization,
    algebraFormalCechFaceDelegationBundle,
    defineAlgebraFormalCechFaceDelegationRealization,
    deriveAffineFormalCechFaceUnit
} from './algebra_formal_cech_face_delegation';
import {
    AlgebraFormalLocalizationDelegationRealization,
    algebraFormalLocalizationDelegationBundle,
    defineAlgebraFormalLocalizationDelegationRealization,
    realizeAdoptedAffineFormalLocalization
} from './algebra_formal_localization_delegation';
import {
    AffineFormalBridgeArtifact,
    buildAffineFormalBridgeArtifact
} from './algebra_formal_artifact';
import {
    AffineFormalCechPresentation,
    buildAffineFormalCechPresentation
} from './algebra_formal_cech';
import {
    AffineFormalCoverRealization
} from './algebra_formal_realization';
import {
    AffineFormalLocalizationRealization
} from './algebra_formal_localization';
import {
    AffineFormalCechOverlapTerms,
    AffineFormalCechSimplexLocalization,
    buildAffineFormalCechOverlapTerms,
    defineAffineFormalCechSimplexLocalization
} from './algebra_formal_overlap';
import {
    AlgebraEngine
} from './algebra_engine';
import {
    createAlgebraTypeScriptReferenceEngine
} from './algebra_reference_engine';
import {
    CoreProofArtifactFingerprint
} from './proof_document';
import {
    coreProofPlanHole
} from './proof_plan';
import {
    KernelExpression,
    provenance
} from './kernel';
import {
    runAlgebraFormalWorkflow,
    trustAlgebraFormalWorkflow
} from './algebra_formal_workflow';

export const ALGEBRA_FORMAL_CECH_DELEGATION_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-cech-delegation-v1' as const,
    assumptionOrder:
        'simplex-inverse-property-then-face-decomposition' as const,
    faceUnitSource: 'formal-transport-and-left-factor' as const,
    handwrittenFaceEvidence: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export interface AlgebraFormalCechDelegationResult<
    P extends import('./algebra_parent').AlgebraParent,
    C extends import('./algebra_parent').AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_CECH_DELEGATION_PROFILE.revision;
    readonly source: AlgebraFormalAssumptionSource;
    readonly localizationRealizations:
        readonly AlgebraFormalLocalizationDelegationRealization<P, C, I>[];
    readonly explicitLocalizations:
        readonly AffineFormalLocalizationRealization<P, C, I>[];
    readonly simplices:
        readonly AffineFormalCechSimplexLocalization<P, C, I>[];
    readonly faceRealizations:
        readonly AlgebraFormalCechFaceDelegationRealization<P, C, I>[];
    readonly faceUnits: readonly (readonly KernelExpression[])[];
    readonly overlap: AffineFormalCechOverlapTerms<P, C, I>;
    readonly presentation: AffineFormalCechPresentation<P, C, I>;
    readonly artifact: AffineFormalBridgeArtifact<P, C, I>;
}

export async function delegateAffineFormalCechCover<
    P extends import('./algebra_parent').AlgebraParent,
    C extends import('./algebra_parent').AlgebraElement<P>,
    I
>(input: {
    readonly artifactId: string;
    readonly cover: AffineFormalCoverRealization<P, C, I>;
    readonly trustedLocalizations:
        readonly AffineFormalLocalizationRealization<P, C, I>[];
    readonly source: AlgebraFormalAssumptionSource;
    readonly localizationEngine: AlgebraEngine;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}): Promise<AlgebraFormalCechDelegationResult<P, C, I>> {
    if (!input.cover.formalCoverAvailable) {
        throw new Error('Formal Cech delegation requires a law-bearing cover');
    }
    if (
        input.trustedLocalizations.length !== input.cover.cover.simplices.length
    ) {
        throw new Error('Trusted localization count differs from simplices');
    }
    let source = input.source;
    const localizationBundle = algebraFormalLocalizationDelegationBundle(
        input.cover.cover.ambient.coordinateAlgebra
    );
    const selected: AlgebraFormalLocalizationDelegationRealization<P, C, I>[] = [];
    const explicit: AffineFormalLocalizationRealization<P, C, I>[] = [];
    const simplices: AffineFormalCechSimplexLocalization<P, C, I>[] = [];
    const document = (
        goalId: string,
        target: KernelExpression
    ) => Object.freeze({
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

    for (let index = 0; index < input.trustedLocalizations.length; index++) {
        const realization =
            defineAlgebraFormalLocalizationDelegationRealization(
                input.trustedLocalizations[index]
            );
        selected.push(realization);
        const inverseId = `${input.artifactId}-simplex-${index}-inverse`;
        const inverseRun = await runAlgebraFormalWorkflow({
            document: document(inverseId, realization.inverseClaimType),
            goalId: inverseId,
            adapter: localizationBundle.inverseAdapter,
            realization,
            engine: input.localizationEngine
        });
        const inverse = trustAlgebraFormalWorkflow({
            run: inverseRun,
            assumptionName: `${input.artifactId}_simplex_${index}_inverse_law`,
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: input.decisionEvidence(inverseId)
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption: inverse,
            classification: 'computed-equation'
        });
        const propertyId = `${input.artifactId}-simplex-${index}-property`;
        const propertyRun = await runAlgebraFormalWorkflow({
            document: document(propertyId, realization.propertyClaimType),
            goalId: propertyId,
            adapter: localizationBundle.propertyAdapter,
            realization,
            engine: input.localizationEngine
        });
        const property = trustAlgebraFormalWorkflow({
            run: propertyRun,
            assumptionName: `${input.artifactId}_simplex_${index}_property`,
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: input.decisionEvidence(propertyId)
            }
        });
        source = appendAlgebraFormalAssumption({
            source,
            adoption: property,
            classification: 'trusted-presentation-semantics'
        });
        const localization = realizeAdoptedAffineFormalLocalization({
            realization,
            inverseLaw: source.entries[source.entries.length - 2].reference,
            property: source.entries[source.entries.length - 1].reference
        });
        explicit.push(localization);
        simplices.push(defineAffineFormalCechSimplexLocalization(
            input.cover,
            input.cover.cover.simplices[index],
            localization
        ));
    }

    const faceRealizations: AlgebraFormalCechFaceDelegationRealization<P, C, I>[] = [];
    const faceUnits: KernelExpression[][] = simplices.map(() => []);
    for (let simplexIndex = 0; simplexIndex < simplices.length; simplexIndex++) {
        const codomain = simplices[simplexIndex];
        for (let faceIndex = 0; faceIndex < codomain.simplex.faces.length; faceIndex++) {
            const face = codomain.simplex.faces[faceIndex];
            const domain = simplices.find(value =>
                value.simplex.indices.join(',') === face.targetIndices.join(',')
            );
            if (domain === undefined) throw new Error('Missing face domain');
            const realization = defineAlgebraFormalCechFaceDelegationRealization({
                face,
                domain,
                codomain
            });
            faceRealizations.push(realization);
            const bundle = algebraFormalCechFaceDelegationBundle(
                realization.input.domainProduct
            );
            const engine = createAlgebraTypeScriptReferenceEngine({
                id: `${input.artifactId}.face-reference`,
                revision: 'v1',
                implementations: bundle.operations.implementations
            });
            const goalId = `${input.artifactId}-simplex-${simplexIndex}-face-${faceIndex}`;
            const run = await runAlgebraFormalWorkflow({
                document: document(goalId, realization.claimType),
                goalId,
                adapter: bundle.adapter,
                realization,
                engine
            });
            const adoption = trustAlgebraFormalWorkflow({
                run,
                assumptionName:
                    `${input.artifactId}_simplex_${simplexIndex}_face_${faceIndex}_product`,
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
            faceUnits[simplexIndex].push(deriveAffineFormalCechFaceUnit(
                realization,
                source.entries[source.entries.length - 1].reference
            ));
        }
    }
    const overlap = buildAffineFormalCechOverlapTerms(
        input.cover,
        simplices,
        faceUnits
    );
    const presentation = buildAffineFormalCechPresentation(overlap);
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_CECH_DELEGATION_PROFILE.revision,
        source,
        localizationRealizations: Object.freeze(selected),
        explicitLocalizations: Object.freeze(explicit),
        simplices: Object.freeze(simplices),
        faceRealizations: Object.freeze(faceRealizations),
        faceUnits: Object.freeze(faceUnits.map(row => Object.freeze(row))),
        overlap,
        presentation,
        artifact: buildAffineFormalBridgeArtifact(input.artifactId, presentation)
    });
}
