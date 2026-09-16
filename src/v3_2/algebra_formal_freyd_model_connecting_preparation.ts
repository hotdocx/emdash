/** Retained window inputs for the already-computed homology connecting map. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { AlgebraPolynomialFreydHomologyConnecting } from './algebra_polynomial_freyd_homology_connecting';
import { serializeAlgebraPolynomialFreydHomologyConnecting } from './algebra_polynomial_freyd_homology_connecting_serialization';
import { algebraPolynomialFreydBoundedShortExactExtendedAt } from './algebra_polynomial_freyd_bounded_short_exact';
import { algebraPolynomialFreydHomologyContext, algebraPolynomialFreydSameHomologicalArrow } from './algebra_polynomial_freyd_homology_context';
import { AlgebraPolynomialFreydHomologyChainMap, algebraPolynomialFreydHomologyChainMap } from './algebra_polynomial_freyd_functorial_homology';
import { algebraPolynomialFreydChainPair } from './algebra_polynomial_freyd_homology';
import { defineAlgebraFormalFreydChainPairRealization, algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { defineAlgebraFormalPresentationAgreementRealization, defineAlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { FREYD_CHAIN_MAP_MATRIX_ROLES } from './algebra_formal_freyd_raw_map_signatures';
import { algebraPolynomialModuleMapCompose } from './algebra_polynomial_presentation';
import { algebraPolynomialModuleMapEquals } from './algebra_polynomial_presentation_morphism';
import { algebraPresentedPolynomialModuleEquals } from './algebra_polynomial_freyd_category';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { algebraFormalPresentationAgreementDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';

export const ALGEBRA_FORMAL_FREYD_MODEL_CONNECTING_PREPARATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-connecting-preparation-v1' as const,
    operation: 'observe-retained-connecting-window' as const,
    replaysConnecting: false as const, reselectsUniversals: false as const,
    replaysHomology: false as const, performsIo: false as const
});

const preparations = new WeakMap<object, () => void>();

function prepareRowMap<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>, chain: AlgebraPolynomialFreydHomologyChainMap<P, C, I>
) {
    if (!chain.isChainMap || !chain.upperAgreement.agrees || !chain.lowerAgreement.agrees) {
        throw new Error('The original row map must satisfy both raw agreements');
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
    return Object.freeze({ chain, source, target, maps, ranks, relations, upper, lower });
}

export function prepareAlgebraFormalFreydModelConnecting<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydHomologyConnecting<P, C, I>;
}) {
    const { selected, reifier } = input, sequence = selected.sequence;
    const fail = (_code: string, path: string, message: string): never => { throw new Error(message + ' (' + path + ')'); };
    const context = algebraPolynomialFreydHomologyContext(sequence, selected.degree, 'modelConnecting', fail);
    if (!context.matchesHomologyAt(selected.source, sequence.quotientComplex, selected.degree) ||
        !context.matchesHomologyAt(selected.target, sequence.subcomplex, selected.degree - 1) ||
        selected.homologyMap.source !== selected.source.homologyObject ||
        selected.homologyMap.target !== selected.target.homologyObject ||
        !selected.reconstruction.agreement.agrees || selected.assumesSplitEpimorphisms) {
        throw new Error('Connecting must retain its original H points, arrow endpoints and reconstruction');
    }
    if (selected.kind !== 'algebra-polynomial-freyd-homology-connecting' ||
        selected.trace.kind !== 'snake-homology-connecting-v1' ||
        selected.homologyMap !== selected.trace.homologyMap || selected.homologyMap !== selected.trace.descent.colift ||
        selected.reconstruction.sourceProjection !== selected.source.homologyProjection ||
        selected.reconstruction.targetInclusion !== selected.trace.homologyEmbedding.colift ||
        selected.reconstruction.comparedMap !== selected.trace.comparedSnake) {
        throw new Error('Connecting result and its retained method reconstruction disagree');
    }
    const rows = Object.freeze([1, 0, -1, -2].map(offset =>
        algebraPolynomialFreydBoundedShortExactExtendedAt(sequence, selected.degree + offset)));
    rows.forEach(row => {
        if (!row.triple.shortExact || !row.triple.exactness.exact || !row.triple.pair.chainAgreement.agrees ||
            row.triple.homology.pair !== row.triple.pair || row.triple.exactness.homology !== row.triple.homology) {
            throw new Error('A connecting row lost its original short-exact data');
        }
    });
    const vertical = [selected.degree + 1, selected.degree, selected.degree - 1].map(n =>
        [sequence.subcomplex, sequence.middleComplex, sequence.quotientComplex].map(c => context.differential(c, n)));
    // Use the retained representatives at the two H inputs, including outside support.
    for (const [i, j, value] of [[0, 2, selected.source.pair.dNext], [1, 2, selected.source.pair.d],
        [1, 0, selected.target.pair.dNext], [2, 0, selected.target.pair.d]] as const) {
        if (!algebraPolynomialFreydSameHomologicalArrow(vertical[i][j], value)) throw new Error('Changed connecting differential');
        vertical[i][j] = value;
    }
    const rowPairs = Object.freeze(rows.map(row => defineAlgebraFormalFreydChainPairRealization({ reifier, selected: row.triple.pair })));
    const rowMaps = Object.freeze(vertical.map((arrows, i) => prepareRowMap(reifier,
        algebraPolynomialFreydHomologyChainMap({ source: rows[i].triple.homology, target: rows[i + 1].triple.homology,
            fNext: arrows[0], f: arrows[1], fPrev: arrows[2] }))));
    const upper = defineAlgebraFormalFreydChainPairRealization({ reifier,
        selected: algebraPolynomialFreydChainPair(vertical[0][1], vertical[1][1]) });
    const lower = defineAlgebraFormalFreydChainPairRealization({ reifier,
        selected: algebraPolynomialFreydChainPair(vertical[1][1], vertical[2][1]) });
    const source = defineAlgebraFormalFreydChainPairRealization({ reifier, selected: selected.source.pair });
    const target = defineAlgebraFormalFreydChainPairRealization({ reifier, selected: selected.target.pair });
    const result = defineAlgebraFormalPresentationMorphismRealization({ reifier, selected: selected.homologyMap });
    const selectedData = serializeAlgebraPolynomialFreydHomologyConnecting(selected);
    const expressions = [...rowPairs, upper, lower, source, target].flatMap(pair =>
        [pair.claimType, pair.formalWitness, ...pair.presentations, pair.above.claimType, pair.below.claimType]);
    const formalData = serializeCoreLfWorkspaceCanonicalJson({ selected: selectedData,
        expressions: [...expressions, result.claimType, ...rowMaps.flatMap(map =>
            [map.upper.claimType, map.lower.claimType, ...map.maps.flatMap(m => [m.formalMap, m.formalRelationWitness, m.claimType])])]
            .map(value => serializeCoreExpression(value)) }, 'modelConnectingPreparation');
    const prepared = Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_MODEL_CONNECTING_PREPARATION_PROFILE,
        reifier, selected, rows, rowPairs, rowMaps, upper, lower, source, target, result, selectedData, formalData });
    preparations.set(prepared, () => {
        if (serializeAlgebraPolynomialFreydHomologyConnecting(selected) !== selectedData ||
            prepareAlgebraFormalFreydModelConnecting(input).formalData !== formalData) throw new Error('Stale model connecting preparation');
    });
    return prepared;
}

export type AlgebraFormalFreydModelConnectingPreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydModelConnecting<P, C, I>>;

export function assertAlgebraFormalFreydModelConnectingPreparationCurrent(value: object): void {
    const current = preparations.get(value);
    if (!current) throw new Error('Use the issued model connecting preparation');
    current();
}

export function algebraFormalFreydConnectingRowMapTerm<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: AlgebraFormalFreydModelConnectingPreparation<P, C, I>, index: 0 | 1 | 2,
    laws: { readonly morphisms: readonly KernelExpression[]; readonly upper: KernelExpression; readonly lower: KernelExpression }
) {
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    if (!Number.isInteger(index) || index < 0 || index > 2) throw new Error('Invalid connecting row-map index');
    if (laws.morphisms.length !== 7) throw new Error('Seven row-map morphism laws are required');
    const map = prepared.rowMaps[index];
    const b = new CoreLfScopedBuilder(provenance('derived', 'connecting raw row map')), L = formalFreydSpineLanguage(b);
    const R = b.embed(prepared.reifier.formalRing);
    const values = [R, ...map.ranks.map(L.nat), ...map.relations.map(t => b.embed(t)),
        ...map.maps.flatMap((m, i) => [m.formalMap, m.formalRelationWitness, laws.morphisms[i]].map(t => b.embed(t))),
        ...[map.upper.raw.formalAgreementWitness, laws.upper, map.lower.raw.formalAgreementWitness, laws.lower].map(t => b.embed(t))];
    const morphisms = Object.freeze(map.maps.map((m, i) => algebraFormalFreydMorphismTerm(m, laws.morphisms[i])));
    const presentations = Object.freeze([...map.source.presentations, ...map.target.presentations]);
    return Object.freeze({ term: b.lower(L.call('bridge_comm_ring_freyd_chain_map_from_matrices', values)),
        type: b.lower(L.tau(L.call('bridge_CommRingFreydHomologyChainMap',
            [R, ...presentations.map(t => b.embed(t)), ...morphisms.map(t => b.embed(t))], 7))), morphisms, presentations });
}

/** Replay only the fixed raw square agreement at its semantic-product claim. */
export function algebraFormalFreydConnectingSquareBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: AlgebraFormalFreydModelConnectingPreparation<P, C, I>, index: 0 | 1 | 2, which: 'upper' | 'lower'
) {
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    if (!Number.isInteger(index) || index < 0 || index > 2 || !['upper', 'lower'].includes(which)) {
        throw new Error('Invalid connecting square');
    }
    const square = prepared.rowMaps[index][which];
    const base = algebraFormalPresentationAgreementDelegationBundle({ reifier: prepared.reifier, selected: square.raw.selected });
    const current = () => assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    const realization = Object.freeze({ prepared, index, which, claimType: square.claimType });
    const id = 'proof-cas.model-connecting-square/' + prepared.selected.degree + '/' + index + '/' + which;
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: 'v1', operation: base.operations.agreement,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new Error('Foreign connecting square realization');
            current(); return realization;
        }, serializeRealization: () => serializeCoreLfWorkspaceCanonicalJson({ prepared: prepared.formalData, index, which,
            claim: serializeCoreExpression(square.claimType) }, 'modelConnectingSquare'),
        acquire(goal) {
            current();
            if (!kernelExpressionEquals(goal.target, square.claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'modelConnecting.square', 'Goal differs from the retained semantic matrix square');
            return { source: square.raw.selected.source, target: square.raw.selected.target,
                left: square.raw.selected.left, right: square.raw.selected.right };
        }, serializeInput: base.adapter.serializeInput, serializeOutput: base.adapter.serializeOutput,
        interpret: ({ goal, computed }) => {
            current();
            return computed.value.agrees && base.adapter.serializeOutput(computed.value) === square.raw.selectedOutputData
                ? { kind: 'claim' as const, claimType: goal.target, summary: 'the retained row-map witness satisfies its semantic matrix products' }
                : { kind: 'observation' as const, summary: 'the row-map witness changed' };
        }
    });
    return Object.freeze({ realization, adapter, engine: createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1',
        implementations: base.operations.implementations }) });
}
