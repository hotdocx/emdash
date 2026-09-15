/** Observe the original native whole exactness proofs at the concrete index. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { constructAlgebraFormalFreydNativeExactness } from './algebra_formal_freyd_native_exactness';
import { createFormalFreydExactnessPointProofEnvironment, FORMAL_FREYD_EXACTNESS_POINT_SIGNATURE_BINDINGS,
    algebraFormalFreydExactnessPointExpressions } from './algebra_formal_freyd_exactness_point_signatures';
import { createCoreProofChecker } from './proof_checker';
import { binderMode, kernelExpressionEquals, kernelFree, provenance, sourceSpan } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { CoreLfDeclarationInput } from './lf_declarations';

export function observeAlgebraFormalFreydNativeExactness<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: Parameters<typeof constructAlgebraFormalFreydNativeExactness<P, C, I>>[0]
) {
    const whole = constructAlgebraFormalFreydNativeExactness(input);
    const expected = createFormalFreydExactnessPointProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_EXACTNESS_POINT_SIGNATURE_BINDINGS)) {
        const declaration = whole.source.environment.lookup(name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, expected.lookup(name)!.type)) {
            throw new Error('Missing or changed exactness observation signature ' + name);
        }
    }
    let environment = whole.source.environment;
    const definitions: CoreLfDeclarationInput[] = [];
    const observations = algebraFormalFreydExactnessPointExpressions(whole.evidence).map((item, index) => {
        let suffix = 0, name = 'native_exactness_point_' + item.position;
        while (environment.lookup(name)) name = 'native_exactness_point_' + item.position + '_' + (++suffix);
        const p = provenance('derived', 'original ' + item.position + ' point exactness',
            sourceSpan('generated/native-exactness-points.ts', index + 1, 1));
        const definition: CoreLfDeclarationInput = { name, type: item.dataType, body: item.data, transparency: 'transparent',
            mode: binderMode('explicit', 'functorial'), provenance: p };
        environment = environment.extend(definition);
        definitions.push(definition);
        const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
        if (item.whole.term.tag !== 'call') throw new Error('Expected the checked whole exactness application');
        const R = b.embed(item.whole.term.arguments[0].value), data = kernelFree(name, p);
        const arrow = L.call('bridge_freyd_omega_arrow_observation', [R, b.embed(data)], 1);
        const evidence = L.call('bridge_freyd_omega_arrow_evidence', [R, b.embed(data)], 1);
        const type = L.tau(L.call('bridge_FreydArrowOmegaEvidence', [R, arrow]));
        const result = Object.freeze({ ...item, data, arrow: b.lower(arrow), evidence: b.lower(evidence), type: b.lower(type) });
        const checker = createCoreProofChecker(environment);
        checker.check(checker.rootContext, result.data, result.dataType);
        checker.check(checker.rootContext, result.arrow, result.arrowType);
        checker.check(checker.rootContext, result.evidence, result.type);
        return result;
    });
    return Object.freeze({ source: whole.source, environment, definitions: Object.freeze(definitions),
        prepared: whole.prepared, whole, observations: Object.freeze(observations),
        assumptionsAdded: 0 as const, trustDecisions: 0 as const, observesOriginalComparison: true as const,
        provesDisplayedCasExactness: false as const });
}
