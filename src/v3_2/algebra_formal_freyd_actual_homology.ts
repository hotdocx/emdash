/** Actual selected homology/epicity terms, retaining the native raw boundary. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { AlgebraPolynomialFreydHomologyAt } from './algebra_polynomial_freyd_homology';
import { serializeAlgebraPolynomialFreydHomologyAt } from './algebra_polynomial_freyd_homology_reference_operations';
import { algebraPolynomialModuleMapCompose } from './algebra_polynomial_presentation';
import { algebraPolynomialModuleMapEquals } from './algebra_polynomial_presentation_morphism';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import { defineAlgebraFormalPresentationAgreementRealization, defineAlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { algebraFormalPresentationAgreementDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { algebraFormalFreydMorphismTerm, defineAlgebraFormalFreydChainPairRealization } from './algebra_formal_freyd_chain_pair';
import { AlgebraFormalFreydKernelChoiceProvidersPreparation, trustAlgebraFormalFreydKernelChoiceProviders } from './algebra_formal_freyd_kernel_choice_providers';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import { CoreLfScopedBuilder } from './lf_builder';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_ACTUAL_HOMOLOGY_PROFILE = Object.freeze({
    revision: 'emdash-formal-actual-selected-homology-v1' as const,
    boundary: 'original-native-raw-morphism' as const,
    reconstruction: 'source-relations-times-witness-equals-formal-kernel-boundary-composite-minus-incoming' as const,
    exactness: 'existing-epimorphism-witness-at-the-same-boundary' as const,
    reselectsHomology: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

/** Reify the semantic composite k B, not just its already-computed matrix value. */
export function defineAlgebraFormalFreydActualHomologyRealization<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydHomologyAt<P, C, I>;
    readonly providers: AlgebraFormalFreydKernelChoiceProvidersPreparation<P, C, I>;
}) {
    const { reifier, selected, providers } = input;
    providers.selected.assertCurrent();
    if (providers.reifier !== reifier || providers.selected.kernel !== selected.cycles ||
        selected.cycles.morphism !== selected.pair.d || selected.cycleObject !== selected.cycles.object ||
        selected.cycleEmbedding !== selected.cycles.embedding || selected.boundary.kernel !== selected.cycles ||
        selected.boundary.test !== selected.pair.dNext || selected.boundaryMorphism !== selected.boundary.lift ||
        selected.boundaryReconstruction !== selected.boundary.reconstructionAgreement ||
        selected.homology.morphism !== selected.boundaryMorphism || selected.homologyObject !== selected.homology.object ||
        selected.homologyProjection !== selected.homology.projection || !selected.boundaryReconstruction.agrees) {
        throw new Error('Actual homology must retain its original pair, kernel choices, boundary and cokernel');
    }
    const agreement = selected.boundaryReconstruction;
    if (agreement.source !== selected.pair.dNext.source || agreement.target !== selected.pair.dNext.target ||
        !algebraPolynomialModuleMapEquals(agreement.left, algebraPolynomialModuleMapCompose(selected.cycleEmbedding.map, selected.boundaryMorphism.map)) ||
        !algebraPolynomialModuleMapEquals(agreement.right, selected.pair.dNext.map)) {
        throw new Error('Boundary reconstruction must concern the actual kernel embedding and incoming arrow');
    }
    const chain = defineAlgebraFormalFreydChainPairRealization({ reifier, selected: selected.pair });
    const boundary = defineAlgebraFormalPresentationMorphismRealization({ reifier, selected: selected.boundaryMorphism });
    const rawAgreement = defineAlgebraFormalPresentationAgreementRealization({ reifier, selected: agreement });
    if (!kernelExpressionEquals(boundary.formalSourceRelations, chain.above.formalSourceRelations) ||
        !kernelExpressionEquals(boundary.formalTargetRelations, providers.second.matrices[2]) ||
        !kernelExpressionEquals(providers.first.matrices[0], chain.below.formalMap)) {
        throw new Error('Selected provider matrices and the actual homology presentations disagree');
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'actual homology reconstruction'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(reifier.formalRing);
    const [n2, , n1, r1] = chain.ranks.map(L.nat);
    const k1 = L.nat(selected.cycleObject.ambient.rank);
    const formalWitness = algebraFormalMatrixTerm(reifier, agreement.agreementWitness.columns, agreement.agreementWitness.target.rank);
    const left = L.comp(R, n1, r1, n2, b.embed(chain.above.formalTargetRelations), b.embed(formalWitness));
    const right = L.call('bridge_comm_ring_matrix_sub', [R, n1, n2,
        L.comp(R, n1, k1, n2, b.embed(providers.first.matrices[2]), b.embed(boundary.formalMap)), b.embed(chain.above.formalMap)]);
    const claimType = b.lower(L.equality(L.matrix(R, n1, n2), left, right));
    const selectedOutputData = serializeAlgebraPolynomialFreydHomologyAt(selected);
    const formalData = serializeCoreLfWorkspaceCanonicalJson({ selected: selectedOutputData,
        providers: [providers.first.formalData, providers.second.formalData],
        expressions: [reifier.formalRing, chain.above.claimType, chain.below.claimType, chain.claimType,
            boundary.claimType, formalWitness, claimType].map(term => serializeCoreExpression(term))
    }, 'actualFreydHomology');
    return Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_ACTUAL_HOMOLOGY_PROFILE.revision,
        reifier, selected, providers, chain, boundary, rawAgreement, formalWitness, claimType, selectedOutputData, formalData });
}

export type AlgebraFormalFreydActualHomologyRealization<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof defineAlgebraFormalFreydActualHomologyRealization<P, C, I>>;

/** Replay only the existing relation-agreement operation; no kernel or homology selection. */
export function algebraFormalFreydActualHomologyReconstructionBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: Parameters<typeof defineAlgebraFormalFreydActualHomologyRealization<P, C, I>>[0]
) {
    const realization = defineAlgebraFormalFreydActualHomologyRealization(input);
    const base = algebraFormalPresentationAgreementDelegationBundle({ reifier: input.reifier, selected: input.selected.boundaryReconstruction });
    const current = (value: typeof realization) => {
        const rebuilt = defineAlgebraFormalFreydActualHomologyRealization(value);
        if (rebuilt.formalData !== value.formalData || rebuilt.formalData !== realization.formalData) {
            throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'actualHomology.reconstruction', 'Actual boundary or provider bindings have drifted');
        }
        return rebuilt;
    };
    const id = 'proof-cas.actual-homology-reconstruction/' + input.selected.pair.d.source.ambient.ring.identity.id;
    const adapter = defineAlgebraFormalComputationAdapter({
        id,
        revision: realization.profileRevision, operation: base.operations.agreement,
        normalizeRealization(value: unknown) {
            const candidate = value as typeof realization;
            if (!candidate || candidate.profileRevision !== realization.profileRevision || candidate.providers !== input.providers) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'actualHomology.reconstruction', 'Expected the actual homology preparation');
            }
            return current(candidate);
        },
        serializeRealization: value => value.formalData,
        acquire(goal, value) {
            current(value);
            if (!kernelExpressionEquals(goal.target, value.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'actualHomology.goal', 'Goal differs from the actual boundary reconstruction');
            const selected = value.selected.boundaryReconstruction;
            return { source: selected.source, target: selected.target, left: selected.left, right: selected.right };
        },
        serializeInput: base.adapter.serializeInput,
        serializeOutput: base.adapter.serializeOutput,
        interpret: ({ goal, realization: value, computed }) => computed.value.agrees &&
            base.adapter.serializeOutput(computed.value) === value.rawAgreement.selectedOutputData
            ? { kind: 'claim' as const, claimType: goal.target, summary: 'the original boundary reconstructs the incoming arrow through its selected cycles' }
            : { kind: 'observation' as const, summary: 'the replayed boundary agreement differs from its selected witness' }
    });
    return Object.freeze({ realization, adapter, engine: createAlgebraTypeScriptReferenceEngine({
        id: id + '/engine', revision: realization.profileRevision, implementations: base.operations.implementations }) });
}

type ProviderAdoption<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    Awaited<ReturnType<typeof trustAlgebraFormalFreydKernelChoiceProviders<P, C, I>>>;

/** Pure constructor applications; the caller checks them in the final adopted source. */
export function algebraFormalFreydActualHomologyTerm<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraFormalFreydActualHomologyRealization<P, C, I>, evidence: {
        readonly providers: ProviderAdoption<P, C, I>;
        readonly aboveLaw: KernelExpression; readonly belowLaw: KernelExpression; readonly chain: KernelExpression;
        readonly boundaryLaw: KernelExpression; readonly reconstructionLaw: KernelExpression; readonly epic: KernelExpression;
    }
) {
    const current = defineAlgebraFormalFreydActualHomologyRealization(value);
    if (current.formalData !== value.formalData || evidence.providers.prepared !== value.providers ||
        evidence.providers.native !== value.selected.cycles) throw new Error('Actual homology constructor received foreign or stale kernel choices');
    const b = new CoreLfScopedBuilder(provenance('derived', 'actual homology and exactness introduction'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(value.reifier.formalRing);
    const embed = (terms: readonly KernelExpression[]) => terms.map(term => b.embed(term));
    const stages = [value.providers.first, value.providers.second].flatMap((stage, index) => [L.nat(stage.ranks[3]),
        ...embed([stage.matrices[2], stage.matrices[3], evidence.providers.bindings[index].compatibility,
            evidence.providers.bindings[index].provider])]);
    const args = [R, ...value.chain.ranks.map(L.nat), ...embed([
        value.chain.above.formalSourceRelations, value.chain.above.formalTargetRelations, value.chain.below.formalTargetRelations,
        value.chain.above.formalMap, value.chain.above.formalRelationWitness, evidence.aboveLaw,
        value.chain.below.formalMap, value.chain.below.formalRelationWitness, evidence.belowLaw, evidence.chain]),
    ...stages, ...embed([value.boundary.formalMap, value.boundary.formalRelationWitness, evidence.boundaryLaw,
        value.formalWitness, evidence.reconstructionLaw])];
    const above = algebraFormalFreydMorphismTerm(value.chain.above, evidence.aboveLaw);
    const below = algebraFormalFreydMorphismTerm(value.chain.below, evidence.belowLaw);
    const boundary = algebraFormalFreydMorphismTerm(value.boundary, evidence.boundaryLaw);
    // Reuse both adopted providers; rebuilding their transparent package makes no native choice.
    const choices = L.call('bridge_comm_ring_freyd_kernel_choices_from_matrix_providers', [R,
        ...value.chain.ranks.slice(2).map(L.nat), ...embed([value.chain.below.formalSourceRelations,
            value.chain.below.formalTargetRelations, value.chain.below.formalMap, value.chain.below.formalRelationWitness,
            evidence.belowLaw]), ...stages]);
    const homologyArgs = [R, ...embed(value.chain.presentations), ...embed([above, below]), choices, b.embed(evidence.chain)];
    const term = L.call('bridge_comm_ring_freyd_homology_from_matrix_providers', args);
    const exactness = L.call('bridge_comm_ring_freyd_exactness_from_matrix_providers', [...args, b.embed(evidence.epic)]);
    return Object.freeze({ selected: value.selected, boundary, above, below, choices: b.lower(choices),
        term: b.lower(term), type: b.lower(L.tau(L.call('bridge_CommRingFreydSelectedHomologyAt', homologyArgs, 4))),
        exactness: b.lower(exactness), exactnessType: b.lower(L.tau(L.call('bridge_CommRingFreydSelectedExactnessAt', [...homologyArgs, term], 8))) });
}
