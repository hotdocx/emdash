/** A checked exactness certificate indexed by the original displayed CAS diagram. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { trustAlgebraFormalFreydNativeSnake } from './algebra_formal_freyd_native_snake_workflow';
import { constructAlgebraFormalFreydNativeSnakeExactness } from './algebra_formal_freyd_native_snake_exactness';
import { constructAlgebraFormalFreydNativeSnakeDiagram } from './algebra_formal_freyd_native_snake_diagram';
import { createFormalFreydNativeSnakeCertificateProofEnvironment, FORMAL_FREYD_NATIVE_SNAKE_CERTIFICATE_SIGNATURE_BINDINGS,
    FREYD_NATIVE_SNAKE_CERTIFICATE_POSITIONS } from './algebra_formal_freyd_native_snake_certificate_signatures';
import { CoreLfScopedBuilder } from './lf_builder';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createCoreProofChecker } from './proof_checker';

export function constructAlgebraFormalFreydNativeSnakeDisplayedExactness<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    snake: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeSnake<P, C, I>>>
) {
    const whole = constructAlgebraFormalFreydNativeSnakeExactness(snake);
    const diagram = constructAlgebraFormalFreydNativeSnakeDiagram(snake);
    if (whole.source !== diagram.source || whole.prepared !== diagram.prepared) throw new Error('Retain one snake source and selection');
    const source = whole.source, expected = createFormalFreydNativeSnakeCertificateProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_NATIVE_SNAKE_CERTIFICATE_SIGNATURE_BINDINGS)) {
        const actual = source.environment.lookup(name);
        if (!actual || actual.body !== undefined || !kernelExpressionEquals(actual.type, expected.lookup(name)!.type)) throw new Error('Missing or changed native snake certificate signature ' + name);
    }
    const first = whole.evidence[0].term;
    if (first.tag !== 'call') throw new Error('Retain the original whole exactness constructor');
    const b = new CoreLfScopedBuilder(provenance('derived', 'native snake displayed exactness')), L = formalFreydSpineLanguage(b);
    const args = first.arguments.map(a => ({ ...a, value: b.embed(a.value) }));
    const checker = createCoreProofChecker(source.environment);
    const pairs: { readonly position: string; readonly term: KernelExpression; readonly type: KernelExpression }[] = [];
    for (const [i, position] of FREYD_NATIVE_SNAKE_CERTIFICATE_POSITIONS.entries()) {
        const a = b.embed(snake.observations[i].observation.realization.nativeArrow);
        const c = b.embed(snake.observations[i + 1].observation.realization.nativeArrow);
        const term = b.call(b.free('bridge_freyd_native_snake_' + position + '_exact_at'), [...args,
            { value: b.embed(whole.evidence[i].term), plicity: 'explicit' },
            { value: a, plicity: 'implicit' }, { value: c, plicity: 'implicit' },
            { value: b.embed(snake.observations[i].proof), plicity: 'explicit' },
            { value: b.embed(snake.observations[i + 1].proof), plicity: 'explicit' }]);
        const type = L.tau(b.call(b.free('bridge_FreydNativeSnake' + position[0].toUpperCase() + position.slice(1) + 'ExactAt'),
            [...args, { value: a, plicity: 'explicit' }, { value: c, plicity: 'explicit' }]));
        const lowered = b.lower(term), loweredType = b.lower(type);
        checker.check(checker.rootContext, lowered, loweredType);
        pairs.push(Object.freeze({ position, term: lowered, type: loweredType }));
    }
    const term = b.call(b.free('bridge_freyd_native_snake_exact_diagram_intro'), [...args,
        ...snake.observations.map(o => ({ value: b.embed(o.observation.realization.nativeArrow), plicity: 'explicit' as const })),
        { value: b.embed(diagram.nativeMatching), plicity: 'explicit' },
        ...pairs.map(p => ({ value: b.embed(p.term), plicity: 'explicit' as const }))]);
    const type = L.tau(b.call(b.free('bridge_FreydNativeSnakeDiagramExactness'),
        [...args, { value: b.embed(diagram.nativeDiagram), plicity: 'explicit' }]));
    const proof = b.lower(term), proofType = b.lower(type);
    checker.check(checker.rootContext, proof, proofType);
    return Object.freeze({ source, prepared: whole.prepared, whole, diagram, pairs: Object.freeze(pairs), proof, type: proofType,
        assumptionsAdded: 0 as const, trustDecisions: 0 as const, provesDisplayedCasExactness: true as const });
}
