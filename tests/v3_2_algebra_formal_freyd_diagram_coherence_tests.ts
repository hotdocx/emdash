/** Whole finite diagram proof construction from arbitrary supplied arrow paths. */
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { describe, it } from 'node:test';
import { CoreLfScopedBuilder } from '../src/v3_2/lf_builder';
import { CoreLfDeclarationEnvironment } from '../src/v3_2/lf_declarations';
import { KernelBinder, KernelExpression, kernelBound, kernelCall, kernelFree, kernelLambda, provenance, sourceSpan } from '../src/v3_2/kernel';
import { formalFreydSpineLanguage } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { createFormalFreydDiagramProofEnvironment, FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_diagram_signatures';
import { createAlgebraFormalAssumptionSource } from '../src/v3_2/algebra_formal_assumption_source';
import { constructAlgebraFormalFreydDiagramCoherence } from '../src/v3_2/algebra_formal_freyd_diagram_coherence';
import { freydNativeModelProbe } from './v3_2_algebra_formal_freyd_native_model_fixtures';

const p = provenance('surface', 'generic finite diagram', sourceSpan('tests/native-diagram-path.ts', 1, 1));
// Fully apply imported implicit binders inside an eta expansion; a bare LP
// reference would insert its implicits before the signature assertion.
const signatureTerm = (name: string, type: KernelExpression): KernelExpression => {
    const visit = (t: KernelExpression, fields: readonly KernelBinder[]): KernelExpression => t.tag === 'pi' ?
        kernelLambda(t.binder, visit(t.body, [...fields, t.binder]), p) :
        kernelCall(kernelFree(name, p), fields.map((field, i) => ({ value: kernelBound(fields.length - i - 1, p),
            plicity: field.mode.plicity })), p);
    return visit(type, []);
};
const prepare = () => {
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b), R = b.free('R');
    const inputs = [{ name: 'R', type: b.lower(L.tau(b.free('bridge_CommRing'))) }];
    for (const name of ['A0', 'A1', 'A2', 'B0', 'B1', 'B2']) inputs.push({ name, type: b.lower(L.presentationType(R)) });
    const arrows = [0, 1].map(i => {
        for (const [f, a] of [['f', 'A'], ['g', 'B']]) inputs.push({ name: f + i,
            type: b.lower(L.morphismType(R, b.free(a + i), b.free(a + (i + 1)))) });
        const formal = L.call('bridge_freyd_raw_arrow_observation', [R, b.free('A' + i), b.free('A' + (i + 1)), b.free('f' + i)], 3);
        const native = L.call('bridge_freyd_raw_arrow_observation', [R, b.free('B' + i), b.free('B' + (i + 1)), b.free('g' + i)], 3);
        inputs.push({ name: 'p' + i, type: b.lower(L.equality(L.call('bridge_FreydArrowObservation', [R]), formal, native)) });
        return { formalArrow: b.lower(formal), nativeArrow: b.lower(native), proof: b.lower(b.free('p' + i)),
            formalSource: b.lower(b.free('A' + i)), formalTarget: b.lower(b.free('A' + (i + 1))),
            nativeSource: b.lower(b.free('B' + i)), nativeTarget: b.lower(b.free('B' + (i + 1))) };
    });
    const environment = createFormalFreydDiagramProofEnvironment(inputs);
    const source = createAlgebraFormalAssumptionSource({ moduleId: 'native.diagram.symbolic', sourceId: 'tests/native-diagram-symbolic', baseEnvironment: environment });
    return { source, formalRing: b.lower(R), arrows };
};

describe('v3.2 native finite diagram path', () => {
    it('constructs the whole path from arbitrary non-reflexive arrow agreements', () => {
        const input = prepare(), result = constructAlgebraFormalFreydDiagramCoherence(input);
        assert.equal(result.source, input.source);
        assert.equal(result.assumptionsAdded, 0);
        assert.equal(result.trustDecisions, 0);
        assert.equal(result.wholeFiniteObservationPath, true);
        assert.equal(result.provesDisplayedExactness, false);
        assert.equal(result.endpointPaths.length, 1);
        const emitted = freydNativeModelProbe(result.source.environment, [
            ...Object.keys(FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS).map(name => ({
                label: name + ' exact signature', term: signatureTerm(name, result.source.environment.lookup(name)!.type),
                type: result.source.environment.lookup(name)!.type, span: p.span!
            })),
            { label: 'formal diagram', term: result.formalDiagram, type: result.diagramType, span: p.span! },
            { label: 'CAS diagram', term: result.nativeDiagram, type: result.diagramType, span: p.span! },
            { label: 'whole diagram path', term: result.path, type: result.pathType, span: p.span! }
        ]);
        if (process.env.EMDASH_NATIVE_DIAGRAM_SYMBOLIC_PROBE) writeFileSync(process.env.EMDASH_NATIVE_DIAGRAM_SYMBOLIC_PROBE, emitted);
    });

    it('rejects changed endpoints, missing computation views and empty diagrams', () => {
        const input = prepare();
        assert.throws(() => constructAlgebraFormalFreydDiagramCoherence({ ...input, arrows: [] }), /nonempty/);
        const arrows = [...input.arrows];
        arrows[1] = { ...arrows[1], formalSource: arrows[1].formalTarget };
        assert.throws(() => constructAlgebraFormalFreydDiagramCoherence({ ...input, arrows }), /shared endpoint/);
        const environment = CoreLfDeclarationEnvironment.empty().extendOpaqueBatch(input.source.environment.declarations.filter(
            d => d.name !== 'bridge_freyd_raw_arrow_observation_target_beta'));
        const source = createAlgebraFormalAssumptionSource({ moduleId: 'native.diagram.missing', sourceId: 'tests/native-diagram-missing', baseEnvironment: environment });
        assert.throws(() => constructAlgebraFormalFreydDiagramCoherence({ ...input, source }), /Missing or changed native diagram signature/);
    });
});
