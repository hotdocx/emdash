/** Construct existing formal boundary-epicity witnesses from adopted block equations. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import { defineAlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { AlgebraPolynomialFreydEpimorphismWitness, algebraPolynomialModuleMapSplitRows } from './algebra_polynomial_freyd_normality';
import { algebraPolynomialModuleMapEquals, algebraPolynomialPresentationRelationMap } from './algebra_polynomial_presentation_morphism';
import { algebraPolynomialModuleMapAdd, algebraPolynomialModuleMapCompose, algebraPolynomialModuleMapIdentity } from './algebra_polynomial_presentation';
import { algebraPolynomialFreydAbelianCategoryModel } from './algebra_polynomial_freyd_abelian_category';
import { serializeAlgebraPolynomialFreydEpimorphismWitness } from './algebra_formal_freyd_abelian';
import { serializeAlgebraPolynomialPresentationMorphism } from './algebra_polynomial_presentation_morphism_reference_operations';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_EPIMORPHISM_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-epimorphism-block-v1' as const,
    equation: 'target-relations-times-U-plus-morphism-times-V-equals-identity' as const,
    constructsExistingWitness: true as const,
    claimsChainExactness: false as const,
    suppliesWeakKernelCapability: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

/** Check retained block sharing and the native identity without rerunning epicity. */
const validateBlocks = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(selected: AlgebraPolynomialFreydEpimorphismWitness<P, C, I>) => {
    if (!selected?.epic || !selected.cokernelZeroAgreement?.agrees || selected.cokernel.morphism !== selected.morphism) {
        throw new Error('An existing positive epimorphism with its original morphism is required');
    }
    const qr = selected.morphism.target.relations.generators.length;
    const split = algebraPolynomialModuleMapSplitRows(selected.cokernelZeroAgreement.agreementWitness, qr);
    if (selected.identityBlocks.map !== selected.cokernelZeroAgreement.agreementWitness ||
        selected.identityBlocks.topRows !== qr || selected.identityBlocks.bottomRows !== selected.morphism.source.ambient.rank ||
        !algebraPolynomialModuleMapEquals(split.top, selected.identityBlocks.top) ||
        !algebraPolynomialModuleMapEquals(split.bottom, selected.identityBlocks.bottom) ||
        !algebraPolynomialModuleMapEquals(split.top, selected.targetRelationComponent) ||
        !algebraPolynomialModuleMapEquals(split.bottom, selected.sourceGeneratorComponent)) {
        throw new Error('Epimorphism blocks differ from the original selected coefficient witness');
    }
    const composite = algebraPolynomialModuleMapAdd(
        algebraPolynomialModuleMapCompose(algebraPolynomialPresentationRelationMap(selected.morphism.target), selected.targetRelationComponent),
        algebraPolynomialModuleMapCompose(selected.morphism.map, selected.sourceGeneratorComponent));
    if (!algebraPolynomialModuleMapEquals(composite, algebraPolynomialModuleMapIdentity(selected.morphism.target.ambient))) {
        throw new Error('Selected epimorphism blocks do not reconstruct the identity');
    }
};

/** The claim contains formal composition/addition/identity, preserving native blocks. */
export function defineAlgebraFormalFreydEpimorphismBlockRealization<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: { readonly reifier: AffineFormalPolynomialReifier<P, C, I>; readonly selected: AlgebraPolynomialFreydEpimorphismWitness<P, C, I> }
) {
    const { reifier, selected } = input;
    validateBlocks(selected);
    const morphism = defineAlgebraFormalPresentationMorphismRealization({ reifier, selected: selected.morphism });
    const b = new CoreLfScopedBuilder(provenance('derived', 'formal Freyd epimorphism block equation'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(reifier.formalRing);
    const ranks = [selected.morphism.source.ambient.rank, selected.morphism.source.relations.generators.length,
        selected.morphism.target.ambient.rank, selected.morphism.target.relations.generators.length] as const;
    const [p, pr, q, qr] = ranks.map(L.nat);
    const U = algebraFormalMatrixTerm(reifier, selected.targetRelationComponent.columns, selected.targetRelationComponent.target.rank);
    const V = algebraFormalMatrixTerm(reifier, selected.sourceGeneratorComponent.columns, selected.sourceGeneratorComponent.target.rank);
    const left = b.lower(L.call('bridge_comm_ring_matrix_add', [R, q, q,
        L.comp(R, q, qr, q, b.embed(morphism.formalTargetRelations), b.embed(U)),
        L.comp(R, q, p, q, b.embed(morphism.formalMap), b.embed(V))]));
    const right = b.lower(L.call('bridge_comm_ring_finite_free_id_matrix', [R, q]));
    const claimType = b.lower(L.equality(L.matrix(R, q, q), b.embed(left), b.embed(right)));
    const presentations = Object.freeze([
        L.presentation(R, p, pr, b.embed(morphism.formalSourceRelations)),
        L.presentation(R, q, qr, b.embed(morphism.formalTargetRelations))
    ].map(term => b.lower(term)));
    const selectedOutputData = serializeAlgebraPolynomialFreydEpimorphismWitness(selected);
    const formalData = serializeCoreLfWorkspaceCanonicalJson({ selected: selectedOutputData, ranks,
        expressions: [reifier.formalRing, morphism.formalSourceRelations, morphism.formalTargetRelations,
            morphism.formalMap, morphism.formalRelationWitness, morphism.claimType, U, V, left, right, claimType,
            ...presentations].map(expression => serializeCoreExpression(expression)) }, 'formalFreydEpimorphismBlock');
    return Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_EPIMORPHISM_PROFILE.revision,
        reifier, selected, morphism, ranks: Object.freeze(ranks), U, V, left, right, claimType, presentations,
        selectedOutputData, formalData });
}

export type AlgebraFormalFreydEpimorphismBlockRealization<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof defineAlgebraFormalFreydEpimorphismBlockRealization<P, C, I>>;

/** A constructor term, checked by the caller using the two adopted law references. */
export function algebraFormalFreydEpimorphismTerm<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraFormalFreydEpimorphismBlockRealization<P, C, I>, morphismLaw: KernelExpression, epicityLaw: KernelExpression
) {
    const current = defineAlgebraFormalFreydEpimorphismBlockRealization(value);
    if (current.formalData !== value.formalData || !kernelExpressionEquals(current.claimType, value.claimType)) {
        throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'freydEpimorphism.term', 'The selected block realization has drifted');
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'formal Freyd epimorphism introduction'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(current.reifier.formalRing);
    const morphism = algebraFormalFreydMorphismTerm(current.morphism, morphismLaw);
    const [P, Q] = current.presentations.map(term => b.embed(term));
    const term = b.lower(L.call('bridge_comm_ring_freyd_epimorphism_from_matrices', [R, ...current.ranks.map(L.nat),
        ...[current.morphism.formalSourceRelations, current.morphism.formalTargetRelations, current.morphism.formalMap,
            current.morphism.formalRelationWitness, morphismLaw, current.U, current.V, epicityLaw].map(expression => b.embed(expression))]));
    const type = b.lower(L.tau(L.call('bridge_CommRingFreydEpimorphismWitness', [R, P, Q, b.embed(morphism)], 3)));
    return Object.freeze({ term, type, morphism, presentations: current.presentations, selected: current.selected });
}

/** Replay the existing native epicity operation; only explicit trust can adopt its equation. */
export function algebraFormalFreydEpimorphismBlockDelegationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: { readonly reifier: AffineFormalPolynomialReifier<P, C, I>; readonly selected: AlgebraPolynomialFreydEpimorphismWitness<P, C, I> }
) {
    const realization = defineAlgebraFormalFreydEpimorphismBlockRealization(input);
    const model = algebraPolynomialFreydAbelianCategoryModel(input.selected.morphism.source.ambient.ring);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: 'proof-cas.freyd-epimorphism-block/' + input.selected.morphism.source.ambient.ring.identity.id,
        revision: realization.profileRevision, operation: model.native.operations.epimorphismWitness,
        normalizeRealization(value: unknown, path: string) {
            const candidate = value as typeof realization;
            if (!candidate || candidate.profileRevision !== realization.profileRevision || candidate.reifier !== input.reifier) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, 'Expected the prepared epimorphism block realization');
            }
            const current = defineAlgebraFormalFreydEpimorphismBlockRealization(candidate);
            if (current.formalData !== candidate.formalData || current.formalData !== realization.formalData ||
                !kernelExpressionEquals(current.claimType, candidate.claimType)) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, 'Selected epimorphism blocks, output, or claim have drifted');
            }
            return current;
        },
        serializeRealization: value => value.formalData,
        acquire(goal, value) {
            if (!kernelExpressionEquals(goal.target, value.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'freydEpimorphism.goal', 'Goal differs from the semantic block identity');
            return value.selected.morphism;
        },
        serializeInput: serializeAlgebraPolynomialPresentationMorphism,
        serializeOutput: serializeAlgebraPolynomialFreydEpimorphismWitness,
        interpret: ({ goal, realization: value, computed }) => serializeAlgebraPolynomialFreydEpimorphismWitness(computed.value) === value.selectedOutputData
            ? { kind: 'claim' as const, claimType: goal.target, summary: 'the selected boundary blocks reconstruct the formal identity' }
            : { kind: 'observation' as const, summary: 'computed epimorphism differs from the selected whole witness' }
    });
    return Object.freeze({ realization, model, adapter });
}
