/** Read-only typed raw values for the retained whole proof-CAS equation inventory. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactAdoption, AlgebraFormalFreydLongExactDelegationBundle, ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE } from './algebra_formal_freyd_long_exact';
import { algebraFormalFreydLongExactEquations, serializeAlgebraFormalFreydLongExactEquations } from './algebra_formal_freyd_long_exact_equations';
import { createFormalFreydActualHomologyProofEnvironment } from './algebra_formal_freyd_actual_homology_signatures';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { AlgebraFormalAssumptionSource, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { AlgebraFormalDelegationError } from './algebra_formal_delegation';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import { algebraPolynomialPresentationRelationMap } from './algebra_polynomial_presentation_morphism';
import { algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { KernelExpression, binderMode, kernelExpressionEquals, provenance, sourceSpan } from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { createCoreProofChecker } from './proof_checker';

export const FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS = Object.freeze({
    bridge_CommRingPresentationAgreementAtMatrices: 'CommRingPresentationAgreementAtMatrices',
    bridge_comm_ring_presentation_agreement_from_matrices: 'comm_ring_presentation_agreement_from_matrices'
});

/** One source environment for raw witnesses and the actual-homology bridge. */
export function createFormalFreydRawWitnessProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydActualHomologyProofEnvironment([]);
    const p = provenance('derived', 'raw Freyd witness signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term];
    const fields: Field[] = [['R', () => L.tau(b.free('bridge_CommRing'))],
        ...['p', 'pr', 'q', 'qr'].map(name => [name, () => L.tau(b.free('bridge_Nat_grpd'))] as Field),
        ['P', s => L.tau(L.matrix(s.R, s.p, s.pr))], ['Q', s => L.tau(L.matrix(s.R, s.q, s.qr))],
        ['F', s => L.tau(L.matrix(s.R, s.q, s.p))], ['G', s => L.tau(L.matrix(s.R, s.q, s.p))]];
    const args = (s: Scope) => fields.map(field => s[field[0]]);
    const add = (name: string, fs: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fs.length ? result(s) :
            b.pi(fs[i][0], fs[i][1](s), value => visit(i + 1, { ...s, [fs[i][0]]: value }), binderMode('explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    add('bridge_CommRingPresentationAgreementAtMatrices', fields, () => b.application('groupoid-universe', []));
    add('bridge_comm_ring_presentation_agreement_from_matrices', [...fields,
        ['H', s => L.tau(L.matrix(s.R, s.qr, s.p))],
        ['law', s => L.equality(L.matrix(s.R, s.q, s.p), L.comp(s.R, s.q, s.qr, s.p, s.Q, s.H),
            L.call('bridge_comm_ring_matrix_sub', [s.R, s.q, s.p, s.F, s.G]))]],
    s => L.tau(L.call('bridge_CommRingPresentationAgreementAtMatrices', args(s))));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'raw witness input ' + input.name, sourceSpan('generated/raw-witness-inputs.ts', index + 1, 1)) });
    });
    return environment;
}

const shapeEntries = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>,
    equations: ReturnType<typeof algebraFormalFreydLongExactEquations<P, C, I>>) => Object.freeze(equations.entries.map(entry => {
    const value = entry.realization, selected = value.selected;
    const b = new CoreLfScopedBuilder(provenance('derived', 'raw witness shape ' + entry.id)), L = formalFreydSpineLanguage(b);
    const R = b.embed(bundle.reifier.formalRing);
    const ranks = [selected.source.ambient.rank, selected.source.relations.generators.length,
        selected.target.ambient.rank, selected.target.relations.generators.length] as const;
    const sourceRelations = entry.kind === 'morphism' ? entry.realization.formalSourceRelations :
        algebraFormalMatrixTerm(bundle.reifier, algebraPolynomialPresentationRelationMap(selected.source).columns, selected.source.ambient.rank);
    const targetRelations = value.formalTargetRelations;
    const prefix = [R, ...ranks.map(L.nat), b.embed(sourceRelations), b.embed(targetRelations)];
    const type = entry.kind === 'morphism'
        ? L.morphismType(R, L.presentation(R, L.nat(ranks[0]), L.nat(ranks[1]), b.embed(sourceRelations)),
            L.presentation(R, L.nat(ranks[2]), L.nat(ranks[3]), b.embed(targetRelations)))
        : L.tau(L.call('bridge_CommRingPresentationAgreementAtMatrices', [...prefix,
            b.embed(entry.realization.formalLeftMap), b.embed(entry.realization.formalRightMap)]));
    return Object.freeze({ entry, ranks: Object.freeze(ranks), sourceRelations, type: b.lower(type) });
}));

const shapeData = (entries: readonly { readonly entry: { readonly id: string; readonly kind: string }; readonly type: KernelExpression }[]) =>
    serializeCoreLfWorkspaceCanonicalJson(entries.map(e => ({ id: e.entry.id, kind: e.entry.kind, type: serializeCoreExpression(e.type) })), 'rawWitnessShapes');

/** Source-presentation coefficients can be absent from an agreement's equation. */
export function prepareAlgebraFormalFreydRawWitnesses<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>
) {
    const entries = shapeEntries(bundle, bundle.equations);
    return Object.freeze({ bundle, equationsData: bundle.equationsData, entries, shapeData: shapeData(entries) });
}

/** Construct values from already adopted laws; this adds no assumption or CAS replay. */
export function constructAlgebraFormalFreydRawWitnesses<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly prepared: ReturnType<typeof prepareAlgebraFormalFreydRawWitnesses<P, C, I>>;
    readonly adopted: AlgebraFormalFreydLongExactAdoption<P, C, I>;
    readonly source?: AlgebraFormalAssumptionSource;
}) {
    if (input.adopted.profileRevision !== ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision) throw new Error('Foreign whole-adoption profile');
    const { bundle } = input.prepared;
    const upstream = input.adopted.adoption.result;
    if (upstream.request.adapter !== bundle.adapter) throw new Error('Raw witnesses belong to another whole replay');
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    const source = validateAlgebraFormalAssumptionSource(input.source ?? input.adopted.source);
    if (!source.entries.some(entry => entry.adoption === input.adopted.adoption)) throw new Error('Raw witness source is missing its parent adoption');
    const expected = createFormalFreydRawWitnessProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS)) {
        const actual = source.environment.lookup(name);
        if (!actual || actual.body !== undefined || actual.transparency !== 'opaque' ||
            !kernelExpressionEquals(actual.type, expected.lookup(name)!.type)) throw new Error('Missing or changed raw witness signature ' + name);
    }
    const equations = algebraFormalFreydLongExactEquations({ reifier: bundle.reifier, selected: upstream.computed.value });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== input.prepared.equationsData ||
        input.prepared.equationsData !== bundle.equationsData ||
        serializeAlgebraFormalFreydLongExactEquations(input.adopted.equations) !== bundle.equationsData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'rawWitnesses.equations', 'The whole equation inventory has drifted');
    }
    const shapes = shapeEntries(bundle, equations);
    if (shapeData(shapes) !== input.prepared.shapeData || shapeData(input.prepared.entries) !== input.prepared.shapeData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'rawWitnesses.shapes', 'Raw witness labels or endpoint presentations have changed');
    }
    const checker = createCoreProofChecker(source.environment);
    const unique = new Map<string, { readonly term: KernelExpression; readonly type: KernelExpression; readonly labels: string[] }>();
    const entries = shapes.map(shape => {
        const { entry } = shape;
        const binding = input.adopted.bindings.find(value => value.labels.includes(entry.id));
        if (!binding || !source.entries[binding.sourceIndex]) throw new Error('Missing adopted raw witness equation ' + entry.id);
        const proof = source.entries[binding.sourceIndex].reference;
        checker.check(checker.rootContext, proof, entry.realization.claimType);
        let term: KernelExpression;
        if (entry.kind === 'morphism') term = algebraFormalFreydMorphismTerm(entry.realization, proof);
        else {
            const b = new CoreLfScopedBuilder(provenance('derived', 'raw agreement ' + entry.id)), L = formalFreydSpineLanguage(b);
            term = b.lower(L.call('bridge_comm_ring_presentation_agreement_from_matrices', [b.embed(bundle.reifier.formalRing),
                ...shape.ranks.map(L.nat), ...[shape.sourceRelations, entry.realization.formalTargetRelations,
                    entry.realization.formalLeftMap, entry.realization.formalRightMap, entry.realization.formalAgreementWitness, proof].map(value => b.embed(value))]));
        }
        const key = serializeCoreExpression(shape.type) + '\n' + serializeCoreExpression(term);
        let shared = unique.get(key);
        if (!shared) {
            checker.check(checker.rootContext, term, shape.type);
            shared = { term, type: shape.type, labels: [] };
            unique.set(key, shared);
        }
        shared.labels.push(entry.id);
        return Object.freeze({ id: entry.id, kind: entry.kind, selected: entry.realization.selected,
            term: shared.term, type: shared.type, proof, sourceIndex: binding.sourceIndex });
    });
    return Object.freeze({ source, native: upstream.computed.value, entries: Object.freeze(entries),
        unique: Object.freeze([...unique.values()].map(entry => Object.freeze({ ...entry, labels: Object.freeze(entry.labels) }))),
        assumptionsAdded: 0 as const, replays: 0 as const });
}
