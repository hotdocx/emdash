/** Exact private mirrors for derived finite-diagram paths and endpoint β views. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { KernelBinder, KernelExpression, binderMode, kernelBound, kernelCall, kernelFree, kernelPi, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydNativeExactnessProofEnvironment } from './algebra_formal_freyd_native_exactness_signatures';
import { FREYD_MODEL_CONNECTING_ARGUMENTS } from './algebra_formal_freyd_model_connecting_signatures';

const arrowOwners = ['bridge_freyd_raw_arrow_observation', 'bridge_freyd_adjunction_model_arrow_observation',
    'bridge_freyd_adjunction_model_connecting_observation'] as const;
const sides = ['source', 'target'] as const;
const names = ['eq_refl', 'eq_sym', 'eq_trans', 'finite_family_cons_path',
    'freyd_arrow_observation_source', 'freyd_arrow_observation_target', 'FreydArrowMatchingTail',
    'freyd_arrow_matching_nil', 'freyd_arrow_matching_cons', 'FreydArrowObservationDiagram',
    'freyd_arrow_diagram_intro', 'freyd_arrow_diagram_arrows', 'freyd_arrow_diagram_path'];
export const FORMAL_FREYD_DIAGRAM_STRUCTURE_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(
    Object.fromEntries(names.map(name => ['bridge_' + name, name])));
export const FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(Object.fromEntries([
    ...names.map(name => ['bridge_' + name, name]),
    ...arrowOwners.flatMap(owner => sides.map(side => [owner + '_' + side + '_beta', owner.slice(7) + '_' + side + '_beta']))
]));

export function extendFormalFreydDiagramStructureSignatures(environment: CoreLfDeclarationEnvironment) {
    const p = provenance('derived', 'finite native diagram proof signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: string, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), v => visit(i + 1, { ...s, [fields[i][0]]: v }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const grpd = () => b.application('groupoid-universe', []);
    const nat = () => L.tau(b.free('bridge_Nat_grpd'));
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const obs = (s: Scope) => L.call('bridge_FreydArrowObservation', [s.R]);
    const family = (A: Term, n: Term) => L.call('bridge_FiniteFamily', [A, n]);
    const cons = (A: Term, n: Term, a: Term, xs: Term) => L.call('bridge_finite_family_cons', [A, n, a, xs], 2);
    const matching = (s: Scope, a: Term, n: Term, xs: Term) => L.call('bridge_FreydArrowMatchingTail', [s.R, a, n, xs], 1);
    const diagram = (s: Scope) => L.call('bridge_FreydArrowObservationDiagram', [s.R, s.n]);
    const intro = (s: Scope, a: Term, xs: Term, m: Term) => L.call('bridge_freyd_arrow_diagram_intro', [s.R, s.n, a, xs, m], 2);
    const endpoint = (s: Scope, side: string, a: Term) => L.call('bridge_freyd_arrow_observation_' + side, [s.R, a], 1);
    const implicit = (fields: readonly Field[]): Field[] => fields.map(([name, type]) => [name, type, 'implicit']);
    const points: Field[] = [['A', grpd, 'implicit'], ...['x', 'y', 'z'].map(name => [name, (s: Scope) => L.tau(s.A), 'implicit'] as Field)];
    add('bridge_eq_refl', [points[0], ['x', s => L.tau(s.A)]], s => L.equality(s.A, s.x, s.x));
    add('bridge_eq_sym', [...points.slice(0, 3), ['p', s => L.equality(s.A, s.x, s.y)]], s => L.equality(s.A, s.y, s.x));
    add('bridge_eq_trans', [...points, ['p', s => L.equality(s.A, s.x, s.y)], ['q', s => L.equality(s.A, s.y, s.z)]],
        s => L.equality(s.A, s.x, s.z));
    add('bridge_finite_family_cons_path', [['A', grpd, 'implicit'], ['n', nat, 'implicit'],
        ...implicit(['x', 'y'].map(name => [name, (s: Scope) => L.tau(s.A)] as Field)),
        ...implicit(['xs', 'ys'].map(name => [name, (s: Scope) => L.tau(family(s.A, s.n))] as Field)),
        ['p', s => L.equality(s.A, s.x, s.y)], ['q', s => L.equality(family(s.A, s.n), s.xs, s.ys)]],
    s => L.equality(family(s.A, L.call('bridge_nat_succ', [s.n])), cons(s.A, s.n, s.x, s.xs), cons(s.A, s.n, s.y, s.ys)));
    for (const side of sides) add('bridge_freyd_arrow_observation_' + side,
        [['R', ring, 'implicit'], ['u', s => L.tau(obs(s))]], s => L.presentationType(s.R));
    add('bridge_FreydArrowMatchingTail', [['R', ring, 'implicit'], ['a', s => L.tau(obs(s))], ['n', nat],
        ['xs', s => L.tau(family(obs(s), s.n))]], grpd);
    add('bridge_freyd_arrow_matching_nil', [['R', ring, 'implicit'], ['a', s => L.tau(obs(s))]],
        s => L.tau(matching(s, s.a, L.nat(0), L.call('bridge_finite_family_nil', [obs(s)], 1))));
    add('bridge_freyd_arrow_matching_cons', [['R', ring, 'implicit'], ['n', nat, 'implicit'],
        ...implicit(['a', 'b'].map(name => [name, (s: Scope) => L.tau(obs(s))] as Field)),
        ['xs', s => L.tau(family(obs(s), s.n)), 'implicit'],
        ['e', s => L.equality(L.call('bridge_CommRingPresentation', [s.R]), endpoint(s, 'target', s.a), endpoint(s, 'source', s.b))],
        ['rest', s => L.tau(matching(s, s.b, s.n, s.xs))]],
    s => L.tau(matching(s, s.a, L.call('bridge_nat_succ', [s.n]), cons(obs(s), s.n, s.b, s.xs))));
    add('bridge_FreydArrowObservationDiagram', [['R', ring], ['n', nat]], grpd);
    add('bridge_freyd_arrow_diagram_intro', [['R', ring, 'implicit'], ['n', nat, 'implicit'],
        ['a', s => L.tau(obs(s))], ['xs', s => L.tau(family(obs(s), s.n))],
        ['matching', s => L.tau(matching(s, s.a, s.n, s.xs))]], s => L.tau(diagram(s)));
    add('bridge_freyd_arrow_diagram_arrows', [['R', ring, 'implicit'], ['n', nat, 'implicit'], ['d', s => L.tau(diagram(s))]],
        s => L.tau(family(obs(s), L.call('bridge_nat_succ', [s.n]))));
    add('bridge_freyd_arrow_diagram_path', [['R', ring, 'implicit'], ['n', nat, 'implicit'],
        ...implicit(['a', 'b'].map(name => [name, (s: Scope) => L.tau(obs(s))] as Field)),
        ...implicit(['xs', 'ys'].map(name => [name, (s: Scope) => L.tau(family(obs(s), s.n))] as Field)),
        ['mx', s => L.tau(matching(s, s.a, s.n, s.xs))], ['my', s => L.tau(matching(s, s.b, s.n, s.ys))],
        ['p', s => L.equality(obs(s), s.a, s.b)], ['q', s => L.equality(family(obs(s), s.n), s.xs, s.ys)]],
    s => L.equality(diagram(s), intro(s, s.a, s.xs, s.mx), intro(s, s.b, s.ys, s.my)));

    return environment;
}

export function createFormalFreydDiagramProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = extendFormalFreydDiagramStructureSignatures(createFormalFreydNativeExactnessProofEnvironment([]));
    const p = provenance('derived', 'finite native diagram proof signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    // Preserve each original observer telescope verbatim; only replace its result
    // by the corresponding defined endpoint β theorem's exact result type.
    for (const owner of arrowOwners) for (const side of sides) {
        const signature = environment.lookup(owner)!;
        const visit = (type: KernelExpression, fields: readonly KernelBinder[]): KernelExpression => {
            if (type.tag === 'pi') return kernelPi(type.binder, visit(type.body, [...fields, type.binder]), type.provenance);
            const argumentNames = owner === 'bridge_freyd_raw_arrow_observation' ? ['R', 'A', 'B', 'f'] :
                owner === 'bridge_freyd_adjunction_model_arrow_observation' ?
                    ['R', 'M', 'S2', 'S1', 'S0', 'T2', 'T1', 'T0', 'sdNext', 'sd', 'tdNext', 'td', 'f2', 'f1', 'f0', 'chainS', 'chainT', 'm'] :
                    FREYD_MODEL_CONNECTING_ARGUMENTS.map(field => field.name);
            if (fields.length !== argumentNames.length) throw new Error('Changed native observer telescope ' + owner);
            // Positional owner ABI, never the diagnostic names of LF binders.
            const values = fields.map((_, i) => kernelBound(fields.length - i - 1, p));
            const s = Object.fromEntries(argumentNames.map((name, i) => [name, values[i]]));
            const call = (name: string, values: readonly KernelExpression[], implicitIndices: readonly number[] = []) =>
                kernelCall(kernelFree(name, p), values.map((value, i) => ({ value, plicity: implicitIndices.includes(i) ? 'implicit' : 'explicit' })), p);
            const arrow = call(owner, values, fields.flatMap((field, i) => field.mode.plicity === 'implicit' ? [i] : []));
            const point = owner === 'bridge_freyd_raw_arrow_observation' ? s[side === 'source' ? 'A' : 'B'] :
                call('bridge_freyd_adjunction_model_object', [s.R, s.M, ...(
                    owner === 'bridge_freyd_adjunction_model_arrow_observation' ?
                        (side === 'source' ? ['S2', 'S1', 'S0', 'sdNext', 'sd', 'chainS'] : ['T2', 'T1', 'T0', 'tdNext', 'td', 'chainT']) :
                        (side === 'source' ? ['Dm', 'D0', 'D1', 'dm', 'd0', 'source_chain'] : ['A0', 'A1', 'A2', 'a0', 'a1', 'target_chain'])
                ).map(name => s[name])], [0, 2, 3, 4]);
            return call('bridge_tau', [call('bridge_eq', [call('bridge_CommRingPresentation', [s.R]),
                call('bridge_freyd_arrow_observation_' + side, [s.R, arrow], [0]), point], [0])]);
        };
        environment = environment.extend({ name: owner + '_' + side + '_beta', type: visit(signature.type, []),
            mode: binderMode('explicit', 'functorial'), provenance: p });
    }
    inputs.forEach((input, i) => { environment = environment.extend({ ...input,
        mode: input.mode ?? binderMode('explicit', 'functorial'),
        provenance: provenance('surface', 'native diagram input ' + input.name,
            sourceSpan('generated/native-diagram-inputs.ts', i + 1, 1)) }); });
    return environment;
}
