/** Shared exact mirrors of the existing Freyd arrow/equivalence carrier. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { binderMode, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FORMAL_FREYD_OMEGA_ARROW_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(Object.fromEntries(
    ['FreydOmegaArrowObservation', 'FreydArrowOmegaEvidence', 'freyd_omega_arrow_observation', 'freyd_omega_arrow_evidence']
        .map(name => ['bridge_' + name, name])));

export function extendFormalFreydOmegaArrowSignatures(environment: CoreLfDeclarationEnvironment) {
    const p = provenance('derived', 'native exactness point observation signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: string, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), value => visit(i + 1, { ...s, [fields[i][0]]: value }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const grpd = () => b.application('groupoid-universe', []), ring = () => L.tau(b.free('bridge_CommRing'));
    const observation = (s: Scope) => L.call('bridge_FreydOmegaArrowObservation', [s.R]);
    add('bridge_FreydOmegaArrowObservation', [['R', ring]], grpd);
    add('bridge_FreydArrowOmegaEvidence', [['R', ring], ['a', s => L.tau(L.call('bridge_FreydArrowObservation', [s.R]))]], grpd);
    for (const name of ['observation', 'evidence']) add('bridge_freyd_omega_arrow_' + name,
        [['R', ring, 'implicit'], ['d', s => L.tau(observation(s))]], s => name === 'observation' ?
            L.tau(L.call('bridge_FreydArrowObservation', [s.R])) :
            L.tau(L.call('bridge_FreydArrowOmegaEvidence', [s.R, L.call('bridge_freyd_omega_arrow_observation', [s.R, s.d], 1)])));
    return environment;
}
