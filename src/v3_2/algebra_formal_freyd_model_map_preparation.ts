/** Original map data and semantic matrix equations for whole-H map observation. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { AlgebraPolynomialFreydInducedHomologyMap } from './algebra_polynomial_freyd_functorial_homology';
import { serializeAlgebraPolynomialFreydInducedHomologyMap } from './algebra_polynomial_freyd_homology_reference_operations';
import { defineAlgebraFormalPresentationAgreementRealization, defineAlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { algebraFormalFreydMorphismTerm, defineAlgebraFormalFreydChainPairRealization } from './algebra_formal_freyd_chain_pair';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import { CoreLfScopedBuilder } from './lf_builder';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { FREYD_CHAIN_MAP_MATRIX_ROLES } from './algebra_formal_freyd_raw_map_signatures';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { algebraPolynomialModuleMapCompose } from './algebra_polynomial_presentation';
import { algebraPolynomialModuleMapEquals } from './algebra_polynomial_presentation_morphism';
import { algebraPresentedPolynomialModuleEquals } from './algebra_polynomial_freyd_category';
import { algebraFormalPresentationAgreementDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';

const preparations = new WeakMap<object, () => void>();

export function prepareAlgebraFormalFreydModelMap<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydInducedHomologyMap<P, C, I>;
}) {
    const { selected, reifier } = input, chain = selected.chainMap;
    if (!chain.isChainMap || !chain.upperAgreement.agrees || !chain.lowerAgreement.agrees ||
        selected.cyclesMap.kernel !== chain.target.cycles || selected.cyclesMorphism !== selected.cyclesMap.lift ||
        selected.induced.cokernel !== chain.source.homology || selected.homologyMap !== selected.induced.colift ||
        selected.homologyMap.source !== chain.source.homologyObject || selected.homologyMap.target !== chain.target.homologyObject) {
        throw new Error('Model map must retain its original source/target homologies, kernels and colift');
    }
    const nativeMaps = [chain.source.pair.dNext, chain.source.pair.d, chain.target.pair.dNext, chain.target.pair.d,
        chain.fNext, chain.f, chain.fPrev] as const;
    const objects = [nativeMaps[0].source, nativeMaps[0].target, nativeMaps[1].target,
        nativeMaps[2].source, nativeMaps[2].target, nativeMaps[3].target] as const;
    const maps = Object.freeze(nativeMaps.map(selected => defineAlgebraFormalPresentationMorphismRealization({ reifier, selected })));
    const source = defineAlgebraFormalFreydChainPairRealization({ reifier, selected: chain.source.pair });
    const target = defineAlgebraFormalFreydChainPairRealization({ reifier, selected: chain.target.pair });
    const ranks = Object.freeze(objects.flatMap(o => [o.ambient.rank, o.relations.generators.length]));
    const relations = Object.freeze([maps[0].formalSourceRelations, maps[0].formalTargetRelations, maps[1].formalTargetRelations,
        maps[2].formalSourceRelations, maps[2].formalTargetRelations, maps[3].formalTargetRelations]);
    for (const [i, [, from, to]] of FREYD_CHAIN_MAP_MATRIX_ROLES.entries()) {
        if (!algebraPresentedPolynomialModuleEquals(nativeMaps[i].source, objects[from]) ||
            !algebraPresentedPolynomialModuleEquals(nativeMaps[i].target, objects[to]) ||
            !kernelExpressionEquals(maps[i].formalSourceRelations, relations[from]) ||
            !kernelExpressionEquals(maps[i].formalTargetRelations, relations[to])) throw new Error('Shared map presentation data disagree');
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'model map semantic squares')), L = formalFreydSpineLanguage(b);
    const R = b.embed(reifier.formalRing);
    const square = (which: 'upper' | 'lower') => {
        const [from, to, leftMid, leftAfter, leftBefore, rightMid, rightAfter, rightBefore] = which === 'upper'
            ? [0, 4, 3, 2, 4, 1, 5, 0] : [1, 5, 4, 3, 5, 2, 6, 1];
        const agreement = which === 'upper' ? chain.upperAgreement : chain.lowerAgreement;
        if (!algebraPresentedPolynomialModuleEquals(agreement.source, objects[from]) ||
            !algebraPresentedPolynomialModuleEquals(agreement.target, objects[to]) ||
            !algebraPolynomialModuleMapEquals(agreement.left, algebraPolynomialModuleMapCompose(nativeMaps[leftAfter].map, nativeMaps[leftBefore].map)) ||
            !algebraPolynomialModuleMapEquals(agreement.right, algebraPolynomialModuleMapCompose(nativeMaps[rightAfter].map, nativeMaps[rightBefore].map))) {
            throw new Error('Raw square agreement does not concern the original semantic products');
        }
        const raw = defineAlgebraFormalPresentationAgreementRealization({ reifier, selected: agreement });
        const rows = L.nat(ranks[2 * to]), columns = L.nat(ranks[2 * from]), rels = L.nat(ranks[2 * to + 1]);
        const left = L.comp(R, rows, L.nat(ranks[2 * leftMid]), columns, b.embed(maps[leftAfter].formalMap), b.embed(maps[leftBefore].formalMap));
        const right = L.comp(R, rows, L.nat(ranks[2 * rightMid]), columns, b.embed(maps[rightAfter].formalMap), b.embed(maps[rightBefore].formalMap));
        const claimType = b.lower(L.equality(L.matrix(R, rows, columns),
            L.comp(R, rows, rels, columns, b.embed(relations[to]), b.embed(raw.formalAgreementWitness)),
            L.call('bridge_comm_ring_matrix_sub', [R, rows, columns, left, right])));
        return Object.freeze({ which, raw, claimType });
    };
    const upper = square('upper'), lower = square('lower');
    const result = defineAlgebraFormalPresentationMorphismRealization({ reifier, selected: selected.homologyMap });
    // Include output coefficients before the caller closes the environment.
    algebraFormalMatrixTerm(reifier, selected.homologyMap.source.relations.generators, selected.homologyMap.source.ambient.rank);
    const selectedData = serializeAlgebraPolynomialFreydInducedHomologyMap(selected);
    const serialize = () => serializeCoreLfWorkspaceCanonicalJson({ selected: selectedData, source: source.selectedOutputData,
        target: target.selectedOutputData, ranks, expressions: [reifier.formalRing, ...relations,
            ...source.presentations, ...target.presentations,
            ...[...maps, result].flatMap(m => [m.formalMap, m.formalSourceRelations, m.formalTargetRelations, m.formalRelationWitness, m.claimType]),
            upper.raw.formalAgreementWitness, lower.raw.formalAgreementWitness, upper.claimType, lower.claimType]
            .map(x => serializeCoreExpression(x)) }, 'modelMapPreparation');
    const formalData = serialize();
    const prepared = Object.freeze({ reifier, selected, source, target, maps, ranks, relations, upper, lower, result, selectedData, formalData });
    preparations.set(prepared, () => {
        if (serialize() !== formalData || prepareAlgebraFormalFreydModelMap(input).formalData !== formalData) {
            throw new Error('Stale model map preparation');
        }
    });
    return prepared;
}

export type AlgebraFormalFreydModelMapPreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydModelMap<P, C, I>>;

export function assertAlgebraFormalFreydModelMapPreparationCurrent(prepared: object): void {
    const current = preparations.get(prepared);
    if (!current) throw new Error('Use the issued model map preparation');
    current();
}

/** Replay the original agreement at the semantic-product equation; no universal selection. */
export function algebraFormalFreydModelMapSquareBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: AlgebraFormalFreydModelMapPreparation<P, C, I>, which: 'upper' | 'lower'
) {
    assertAlgebraFormalFreydModelMapPreparationCurrent(prepared);
    const square = prepared[which];
    const base = algebraFormalPresentationAgreementDelegationBundle({ reifier: prepared.reifier, selected: square.raw.selected });
    const current = () => assertAlgebraFormalFreydModelMapPreparationCurrent(prepared);
    const realization = Object.freeze({ prepared, which, claimType: square.claimType });
    const id = 'proof-cas.model-map-square/' + which + '/' + prepared.selected.chainMap.source.pair.d.source.ambient.ring.identity.id;
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: 'v1', operation: base.operations.agreement,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'modelMap.square', 'Foreign square realization');
            current(); return realization;
        },
        serializeRealization: () => serializeCoreLfWorkspaceCanonicalJson({ prepared: prepared.formalData, which,
            claim: serializeCoreExpression(square.claimType) }, 'modelMapSemanticSquare'),
        acquire(goal) {
            current();
            if (!kernelExpressionEquals(goal.target, square.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'modelMap.squareGoal', 'Goal differs from the original semantic chain square');
            return { source: square.raw.selected.source, target: square.raw.selected.target,
                left: square.raw.selected.left, right: square.raw.selected.right };
        },
        serializeInput: base.adapter.serializeInput, serializeOutput: base.adapter.serializeOutput,
        interpret: ({ goal, computed }) => {
            current();
            return computed.value.agrees && base.adapter.serializeOutput(computed.value) === square.raw.selectedOutputData
                ? { kind: 'claim' as const, claimType: goal.target, summary: 'the original raw chain-map coefficient witness satisfies its semantic matrix products' }
                : { kind: 'observation' as const, summary: 'semantic chain-square witness changed' };
        }
    });
    return Object.freeze({ realization, adapter, engine: createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1',
        implementations: base.operations.implementations }) });
}

export function algebraFormalFreydModelChainMapTerm<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: AlgebraFormalFreydModelMapPreparation<P, C, I>, laws: {
        readonly morphisms: readonly KernelExpression[]; readonly upper: KernelExpression; readonly lower: KernelExpression;
    }
) {
    if (laws.morphisms.length !== 7) throw new Error('Seven original morphism laws are required');
    assertAlgebraFormalFreydModelMapPreparationCurrent(prepared);
    const b = new CoreLfScopedBuilder(provenance('derived', 'original formal chain map introduction')), L = formalFreydSpineLanguage(b);
    const R = b.embed(prepared.reifier.formalRing);
    const values = [R, ...prepared.ranks.map(L.nat), ...prepared.relations.map(x => b.embed(x)),
        ...prepared.maps.flatMap((m, i) => [m.formalMap, m.formalRelationWitness, laws.morphisms[i]].map(x => b.embed(x))),
        ...[prepared.upper.raw.formalAgreementWitness, laws.upper, prepared.lower.raw.formalAgreementWitness, laws.lower].map(x => b.embed(x))];
    const morphisms = Object.freeze(prepared.maps.map((m, i) => algebraFormalFreydMorphismTerm(m, laws.morphisms[i])));
    const presentations = Object.freeze([...prepared.source.presentations, ...prepared.target.presentations]);
    const term = b.lower(L.call('bridge_comm_ring_freyd_chain_map_from_matrices', values));
    const type = b.lower(L.tau(L.call('bridge_CommRingFreydHomologyChainMap',
        [R, ...presentations.map(x => b.embed(x)), ...morphisms.map(x => b.embed(x))], 7)));
    return Object.freeze({ prepared, term, type, morphisms, presentations });
}
