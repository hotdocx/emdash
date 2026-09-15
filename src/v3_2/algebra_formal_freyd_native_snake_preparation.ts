/** Retained snake matrices and the semantic triple-zero equation; no universals are recomputed. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { AlgebraPolynomialFreydSnakeExactSequence } from './algebra_polynomial_freyd_snake_exact';
import { serializeAlgebraPolynomialFreydSnakeExactSequence } from './algebra_polynomial_freyd_snake_exact_serialization';
import { defineAlgebraFormalPresentationAgreementRealization, defineAlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { algebraFormalPresentationAgreementDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { algebraPolynomialModuleMapCompose, algebraPolynomialModuleMapZero } from './algebra_polynomial_presentation';
import { algebraPolynomialModuleMapEquals } from './algebra_polynomial_presentation_morphism';
import { algebraPresentedPolynomialModuleEquals } from './algebra_polynomial_freyd_category';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import { CoreLfScopedBuilder } from './lf_builder';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

const preparations = new WeakMap<object, () => void>();

export function prepareAlgebraFormalFreydNativeSnake<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydSnakeExactSequence<P, C, I>;
}) {
    const { reifier, selected } = input, triple = selected.connecting.triple;
    const selectedData = serializeAlgebraPolynomialFreydSnakeExactSequence(selected);
    if (!selected.isExact || !triple.isSnakeTriple || !triple.tripleZeroAgreement.agrees) throw new Error('A valid retained six-term snake is required');
    const maps = Object.freeze([triple.delta, triple.beta, triple.lambda].map(selected =>
        defineAlgebraFormalPresentationMorphismRealization({ reifier, selected })));
    const outputs = Object.freeze(selected.arrows.map(selected => defineAlgebraFormalPresentationMorphismRealization({ reifier, selected })));
    const objects = [triple.delta.source, triple.delta.target, triple.beta.target, triple.lambda.target];
    const ranks = Object.freeze(objects.flatMap(o => [o.ambient.rank, o.relations.generators.length]));
    const relations = Object.freeze([maps[0].formalSourceRelations, maps[0].formalTargetRelations,
        maps[1].formalTargetRelations, maps[2].formalTargetRelations]);
    maps.forEach((m, i) => {
        if (!algebraPresentedPolynomialModuleEquals(m.selected.source, objects[i]) ||
            !algebraPresentedPolynomialModuleEquals(m.selected.target, objects[i + 1]) ||
            !kernelExpressionEquals(m.formalSourceRelations, relations[i]) ||
            !kernelExpressionEquals(m.formalTargetRelations, relations[i + 1])) throw new Error('Snake input presentations disagree');
    });
    outputs.forEach((m, i) => {
        if (!algebraPresentedPolynomialModuleEquals(m.selected.source, selected.objects[i]) ||
            !algebraPresentedPolynomialModuleEquals(m.selected.target, selected.objects[i + 1])) throw new Error('Snake result endpoints changed');
    });
    const agreement = triple.tripleZeroAgreement;
    if (!algebraPresentedPolynomialModuleEquals(agreement.source, objects[0]) ||
        !algebraPresentedPolynomialModuleEquals(agreement.target, objects[3]) ||
        !algebraPolynomialModuleMapEquals(agreement.left, algebraPolynomialModuleMapCompose(triple.lambda.map,
            algebraPolynomialModuleMapCompose(triple.beta.map, triple.delta.map))) ||
        !algebraPolynomialModuleMapEquals(agreement.right, algebraPolynomialModuleMapZero(objects[0].ambient, objects[3].ambient))) {
        throw new Error('The zero witness must concern the original c∘(b∘a)');
    }
    const raw = defineAlgebraFormalPresentationAgreementRealization({ reifier, selected: agreement });
    const b = new CoreLfScopedBuilder(provenance('derived', 'native snake matrix preparation')), L = formalFreydSpineLanguage(b);
    const R = b.embed(reifier.formalRing), [pa, , pb, , px, , pd, rd] = ranks.map(L.nat);
    const left = L.comp(R, pd, rd, pa, b.embed(relations[3]), b.embed(raw.formalAgreementWitness));
    const right = L.call('bridge_comm_ring_matrix_sub', [R, pd, pa,
        L.comp(R, pd, px, pa, b.embed(maps[2].formalMap), L.comp(R, px, pb, pa, b.embed(maps[1].formalMap), b.embed(maps[0].formalMap))),
        L.call('bridge_comm_ring_matrix_zero', [R, pd, pa])]);
    const zero = Object.freeze({ raw, claimType: b.lower(L.equality(L.matrix(R, pd, pa), left, right)) });
    const presentations = Object.freeze(objects.map((_, i) => b.lower(L.presentation(R, L.nat(ranks[2 * i]),
        L.nat(ranks[2 * i + 1]), b.embed(relations[i])))));
    const serialize = () => serializeCoreLfWorkspaceCanonicalJson({ selected: selectedData, ranks,
        expressions: [reifier.formalRing, ...relations, ...presentations, zero.claimType, raw.formalAgreementWitness,
            ...[...maps, ...outputs].flatMap(m => [m.formalSourceRelations, m.formalTargetRelations, m.formalMap,
                m.formalRelationWitness, m.claimType])].map(x => serializeCoreExpression(x)) }, 'nativeSnakePreparation');
    const formalData = serialize();
    const prepared = Object.freeze({ reifier, selected, maps, outputs, ranks, relations, presentations, zero, selectedData, formalData });
    preparations.set(prepared, () => {
        if (serializeAlgebraPolynomialFreydSnakeExactSequence(selected) !== selectedData || serialize() !== formalData ||
            prepareAlgebraFormalFreydNativeSnake(input).formalData !== formalData) throw new Error('Stale native snake preparation');
    });
    return prepared;
}

export type AlgebraFormalFreydNativeSnakePreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydNativeSnake<P, C, I>>;

export function assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared: object): void {
    const current = preparations.get(prepared);
    if (!current) throw new Error('Use an issued native snake preparation');
    current();
}

/** Replay the coefficient agreement at its original symbolic matrix product. */
export function algebraFormalFreydNativeSnakeZeroBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: AlgebraFormalFreydNativeSnakePreparation<P, C, I>
) {
    assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared);
    const zero = prepared.zero, base = algebraFormalPresentationAgreementDelegationBundle({ reifier: prepared.reifier, selected: zero.raw.selected });
    const current = () => assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared);
    const realization = Object.freeze({ prepared, claimType: zero.claimType });
    const id = 'proof-cas.native-snake-zero/' + prepared.selected.connecting.triple.delta.source.ambient.ring.identity.id;
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: 'v1', operation: base.operations.agreement,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new Error('Foreign native snake zero realization');
            current(); return realization;
        },
        serializeRealization: () => serializeCoreLfWorkspaceCanonicalJson({ prepared: prepared.formalData,
            claim: serializeCoreExpression(zero.claimType) }, 'nativeSnakeZero'),
        acquire(goal) {
            current();
            if (!kernelExpressionEquals(goal.target, zero.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'nativeSnake.zero', 'Goal differs from the original triple-zero equation');
            return { source: zero.raw.selected.source, target: zero.raw.selected.target,
                left: zero.raw.selected.left, right: zero.raw.selected.right };
        },
        serializeInput: base.adapter.serializeInput, serializeOutput: base.adapter.serializeOutput,
        interpret: ({ goal, computed }) => {
            current();
            return computed.value.agrees && base.adapter.serializeOutput(computed.value) === zero.raw.selectedOutputData
                ? { kind: 'claim' as const, claimType: goal.target, summary: 'the original triple-zero witness satisfies c∘(b∘a)=0' }
                : { kind: 'observation' as const, summary: 'the retained triple-zero agreement changed' };
        }
    });
    return Object.freeze({ realization, adapter, engine: createAlgebraTypeScriptReferenceEngine({ id: id + '/engine',
        revision: 'v1', implementations: base.operations.implementations }) });
}

export function algebraFormalFreydNativeSnakeInputTerms<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: AlgebraFormalFreydNativeSnakePreparation<P, C, I>, morphismLaws: readonly KernelExpression[], zeroLaw: KernelExpression
) {
    assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared);
    if (morphismLaws.length !== 3) throw new Error('Three original morphism laws are required');
    const b = new CoreLfScopedBuilder(provenance('derived', 'native snake matrix introduction')), L = formalFreydSpineLanguage(b);
    const R = b.embed(prepared.reifier.formalRing);
    const morphisms = Object.freeze(prepared.maps.map((m, i) => algebraFormalFreydMorphismTerm(m, morphismLaws[i])));
    const zero = b.lower(L.call('bridge_comm_ring_freyd_snake_zero_from_matrices', [R, ...prepared.ranks.map(L.nat),
        ...prepared.relations.map(x => b.embed(x)), ...prepared.maps.flatMap((m, i) =>
            [m.formalMap, m.formalRelationWitness, morphismLaws[i]].map(x => b.embed(x))),
        b.embed(prepared.zero.raw.formalAgreementWitness), b.embed(zeroLaw)]));
    const [A, B, X, D] = prepared.presentations.map(x => b.embed(x));
    const type = b.lower(L.chainType(R, A, X, D, L.call('bridge_comm_ring_presentation_morphism_comp',
        [R, A, B, X, b.embed(morphisms[1]), b.embed(morphisms[0])], 4), b.embed(morphisms[2])));
    return Object.freeze({ morphisms, zero, zeroType: type, presentations: prepared.presentations });
}
