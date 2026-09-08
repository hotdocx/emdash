/** Actual presentation-morphism/chain constructors from selected matrix equations. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import {
    AlgebraFormalPresentationMorphismRealization, defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import { AlgebraPolynomialFreydChainPair } from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialFreydChainPairInput, serializeAlgebraPolynomialFreydChainPair
} from './algebra_polynomial_freyd_homology_reference_operations';
import { serializeAlgebraPolynomialPresentationMorphism } from './algebra_polynomial_presentation_morphism_reference_operations';
import { algebraPolynomialFreydHomologyCategoryModel } from './algebra_polynomial_freyd_homology_category';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_CHAIN_PAIR_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-semantic-chain-pair-v1' as const,
    equation: 'target-relations-times-witness-equals-formal-composite-minus-formal-zero' as const,
    constructsExistingOwners: true as const,
    addsCoreOwner: false as const,
    claimsExactness: false as const,
    performsIo: false as const
});

/** A morphism result is an application of the checked transparent introduction. */
export function algebraFormalFreydMorphismTerm<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraFormalPresentationMorphismRealization<P, C, I>, law: KernelExpression
): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'formal Freyd morphism introduction'));
    const L = formalFreydSpineLanguage(b);
    return b.lower(L.morphism([
        b.embed(value.reifier.formalRing),
        ...[value.selected.source.ambient.rank, value.selected.source.relations.generators.length,
            value.selected.target.ambient.rank, value.selected.target.relations.generators.length].map(L.nat),
        ...[value.formalSourceRelations, value.formalTargetRelations, value.formalMap, value.formalRelationWitness, law].map(term => b.embed(term))
    ]));
}

/** Unlike the earlier literal agreement, this claim contains the formal G ∘ F. */
export function defineAlgebraFormalFreydChainPairRealization<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(input: { readonly reifier: AffineFormalPolynomialReifier<P, C, I>; readonly selected: AlgebraPolynomialFreydChainPair<P, C, I> }) {
    const { reifier, selected } = input;
    if (!selected.isChainPair || !selected.chainAgreement.agrees) throw new Error('A positive selected chain agreement is required');
    const above = defineAlgebraFormalPresentationMorphismRealization({ reifier, selected: selected.dNext });
    const below = defineAlgebraFormalPresentationMorphismRealization({ reifier, selected: selected.d });
    const b = new CoreLfScopedBuilder(provenance('derived', 'formal Freyd semantic chain equation'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(reifier.formalRing);
    const ranks = [selected.dNext.source.ambient.rank, selected.dNext.source.relations.generators.length,
        selected.dNext.target.ambient.rank, selected.dNext.target.relations.generators.length,
        selected.d.target.ambient.rank, selected.d.target.relations.generators.length] as const;
    const [p2, r2, p1, r1, p0, r0] = ranks.map(L.nat);
    const P2 = b.embed(above.formalSourceRelations);
    const P1 = b.embed(above.formalTargetRelations);
    const P0 = b.embed(below.formalTargetRelations);
    if (!kernelExpressionEquals(above.formalTargetRelations, below.formalSourceRelations) ||
        selected.dNext.target.ambient.rank !== selected.d.source.ambient.rank) {
        throw new Error('Formal chain maps must have the same selected middle presentation');
    }
    const formalWitness = algebraFormalMatrixTerm(reifier, selected.chainAgreement.agreementWitness.columns,
        selected.chainAgreement.agreementWitness.target.rank);
    const left = L.comp(R, p0, r0, p2, P0, b.embed(formalWitness));
    const composite = L.comp(R, p0, p1, p2, b.embed(below.formalMap), b.embed(above.formalMap));
    const right = L.call('bridge_comm_ring_matrix_sub', [R, p0, p2, composite,
        L.call('bridge_comm_ring_matrix_zero', [R, p0, p2])]);
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_CHAIN_PAIR_PROFILE.revision,
        reifier, selected, above, below, ranks: Object.freeze(ranks), formalWitness,
        presentations: Object.freeze([L.presentation(R, p2, r2, P2), L.presentation(R, p1, r1, P1),
            L.presentation(R, p0, r0, P0)].map(term => b.lower(term))),
        selectedOutputData: serializeAlgebraPolynomialFreydChainPair(selected),
        left: b.lower(left), right: b.lower(right),
        claimType: b.lower(L.equality(L.matrix(R, p0, p2), left, right))
    });
}

export type AlgebraFormalFreydChainPairRealization<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof defineAlgebraFormalFreydChainPairRealization<P, C, I>>;

/** Return the actual original chain-pair type and constructor term. */
export function algebraFormalFreydChainPairTerm<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraFormalFreydChainPairRealization<P, C, I>,
    aboveLaw: KernelExpression, belowLaw: KernelExpression, chainLaw: KernelExpression
) {
    const b = new CoreLfScopedBuilder(provenance('derived', 'formal Freyd chain-pair introduction'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(value.reifier.formalRing);
    const above = algebraFormalFreydMorphismTerm(value.above, aboveLaw);
    const below = algebraFormalFreydMorphismTerm(value.below, belowLaw);
    const term = L.call('bridge_comm_ring_freyd_chain_pair_from_matrices', [R, ...value.ranks.map(L.nat),
        ...[value.above.formalSourceRelations, value.above.formalTargetRelations, value.below.formalTargetRelations,
            value.above.formalMap, value.above.formalRelationWitness, aboveLaw,
            value.below.formalMap, value.below.formalRelationWitness, belowLaw,
            value.formalWitness, chainLaw].map(expression => b.embed(expression))]);
    const [P2, P1, P0] = value.presentations.map(expression => b.embed(expression));
    return Object.freeze({
        term: b.lower(term), above, below,
        type: b.lower(L.chainType(R, P2, P1, P0, b.embed(above), b.embed(below)))
    });
}

/** Replay just the raw pair calculation, not any homology/universal construction. */
export function algebraFormalFreydChainPairDelegationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: { readonly reifier: AffineFormalPolynomialReifier<P, C, I>; readonly selected: AlgebraPolynomialFreydChainPair<P, C, I> }
) {
    const realization = defineAlgebraFormalFreydChainPairRealization(input);
    const model = algebraPolynomialFreydHomologyCategoryModel(input.selected.d.source.ambient.ring);
    const adapter = defineAlgebraFormalComputationAdapter<
        typeof realization, AlgebraPolynomialFreydChainPairInput<P, C, I>, AlgebraPolynomialFreydChainPair<P, C, I>
    >({
        id: 'proof-cas.freyd-semantic-chain/' + input.selected.d.source.ambient.ring.identity.id,
        revision: realization.profileRevision, operation: model.native.chainPair,
        normalizeRealization(value, path) {
            const candidate = value as typeof realization;
            if (!candidate || candidate.profileRevision !== realization.profileRevision) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, 'Expected a semantic chain-pair realization');
            }
            const current = defineAlgebraFormalFreydChainPairRealization(candidate);
            if (current.selectedOutputData !== candidate.selectedOutputData || !kernelExpressionEquals(current.claimType, candidate.claimType)) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, 'Semantic chain-pair data has drifted');
            }
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            profileRevision: value.profileRevision, selected: value.selectedOutputData, claim: serializeCoreExpression(value.claimType)
        }, 'formalFreydSemanticChain'),
        acquire(goal, value) {
            if (!kernelExpressionEquals(goal.target, value.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'freydChain.goal', 'Goal differs from the semantic composition equation');
            return { dNext: value.selected.dNext, d: value.selected.d };
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            dNext: serializeAlgebraPolynomialPresentationMorphism(value.dNext), d: serializeAlgebraPolynomialPresentationMorphism(value.d)
        }, 'formalFreydSemanticChainInput'),
        serializeOutput: serializeAlgebraPolynomialFreydChainPair,
        interpret: ({ goal, realization: value, computed }) => computed.value.isChainPair &&
            serializeAlgebraPolynomialFreydChainPair(computed.value) === value.selectedOutputData
            ? { kind: 'claim', claimType: goal.target, summary: 'formal differential composition has the selected zero witness' }
            : { kind: 'observation', summary: 'computed chain pair differs from the selected one' }
    });
    return Object.freeze({ realization, adapter, model });
}
