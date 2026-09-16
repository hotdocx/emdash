/** Complete native H/map/delta observation assembly over the original CAS result. */
import assert from 'node:assert/strict';
import { appendFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { describe, it, mock } from 'node:test';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { kernelExpressionEquals, provenance, sourceSpan } from '../src/v3_2/kernel';
import { runAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { defineAlgebraFormalFreydNativeRationalBackend, prepareAlgebraFormalFreydNativeRationalModelContext } from '../src/v3_2/algebra_formal_freyd_native_rational_model_context';
import { trustAlgebraFormalFreydNativeDiagram } from '../src/v3_2/algebra_formal_freyd_native_diagram';
import { constructAlgebraFormalFreydDiagramCoherence } from '../src/v3_2/algebra_formal_freyd_diagram_coherence';
import { constructAlgebraFormalFreydNativeDisplayedExactness } from '../src/v3_2/algebra_formal_freyd_native_displayed_exactness';
import { polynomialFreydHomologyFixture, isPolynomialFreydMorphismZero } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { freydNativeModelProbe } from './v3_2_algebra_formal_freyd_native_model_fixtures';
import { freydNativeExactnessProbe, freydNativeLesCertificateProbe } from './v3_2_algebra_formal_freyd_native_exactness_fixtures';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as nativeConnecting from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';

const traceStart = Date.now();
const trace = (phase: string) => {
    if (process.env.EMDASH_PROOF_CAS_NATIVE_DIAGRAM_TRACE) appendFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_DIAGRAM_TRACE,
        JSON.stringify({ phase, elapsedMs: Date.now() - traceStart }) + '\n');
};
const p = provenance('surface', 'native diagram', sourceSpan('tests/native-connecting-windows.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({ id: 'tests.native-connecting-windows', revision: 'v1',
    coefficientContract: 'Interpret the ring and coefficient names in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native whole P/Q; selected-arrow realization is separately explicit.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality of that native model.' });
const prepare = () => prepareAlgebraFormalFreydNativeRationalModelContext({ backend, namePrefix: 'native_diagram',
    selected: algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(
        polynomialFreydHomologyFixture('two'))) });
let setup: ReturnType<typeof prepare>;
const context = () => setup ??= prepare();
const adoptEquations = async () => {
    const v = context(), goalId = 'native-diagram-replay', type = v.bundle.realization.claimType;
    const run = await runAlgebraFormalWorkflow({ goalId, adapter: v.bundle.adapter, realization: v.bundle.realization,
        engine: v.bundle.engine, document: { moduleId: v.initialSource.moduleId, declarationId: goalId,
            environment: v.environment, type, provenance: p, fingerprint: fingerprint(goalId),
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: type } }) } });
    return trustAlgebraFormalFreydLongExact({ artifactId: 'native-diagram-equations', bundle: v.bundle, run,
        source: v.initialSource, fingerprint, decisionEvidence: id => 'Explicitly adopt the original matrix equation ' + id });
};
let equationsPromise: ReturnType<typeof adoptEquations>;
const equations = () => equationsPromise ??= adoptEquations();
const realize = async () => {
    const v = context(), adopted = await equations();
    const input = { artifactId: 'native-diagram-model', modelId: 'native-window-model', formalModel: v.formalModel,
        normality: v.normality, prepared: v.preparedModel, adopted, fingerprint,
        decisionEvidence: (id: string) => { trace('claim ' + id); return 'Explicit native window interpretation or computed matrix equation: ' + id; } };
    trace('assembly-start');
    const result = await trustAlgebraFormalFreydNativeDiagram(input);
    trace('assembly-finish');
    return { v, adopted, input, result };
};
let realizationPromise: ReturnType<typeof realize>;
const consumer = () => realizationPromise ??= realize();

describe('v3.2 complete native bounded diagram', () => {
    it('assembles every degree H/map, delta window and displayed arrow with shared endpoints', async t => {
        await equations();
        trace('CAS-equations-ready');
        const forbid = () => { throw new Error('Native diagram assembly must retain all original CAS selections'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { v, adopted, result } = await consumer();
            assert.equal(result.native, adopted.adoption.result.computed.value.result);
            assert.equal(result.inventoryData, v.preparedModel.inventory.data);
            assert.deepEqual([result.counts.points, result.counts.maps, result.counts.windows,
                result.counts.displayedPoints, result.counts.displayedArrows, result.counts.exactness], [12, 8, 3, 8, 7, 9]);
            assert.deepEqual(result.displayed.map(x => x.entry.position), [0, 1, 2, 3, 4, 5, 6]);
            assert.deepEqual(result.displayed.map(x => x.kind), ['connecting', 'map', 'map', 'connecting', 'map', 'map', 'connecting']);
            assert.deepEqual(result.windows.map(w => isPolynomialFreydMorphismZero(w.entry.prepared.selected.homologyMap)), [true, false, true]);
            for (const [i, arrow] of result.displayed.entries()) {
                const r = arrow.result.observation.realization;
                assert.ok(kernelExpressionEquals(r.source.formalPoint, result.displayedPoints[i].realization.formalPoint));
                assert.ok(kernelExpressionEquals(r.target.formalPoint, result.displayedPoints[i + 1].realization.formalPoint));
                assert.equal(r.prepared.selected.homologyMap, result.native.arrows[i]);
            }
            assert.equal(result.profile.provesDisplayedDiagramCoherence, true);
            assert.equal(result.profile.provesDisplayedExactness, true);
            assert.equal(result.coherence.source, result.source);
            assert.equal(result.coherence.assumptionsAdded, 0);
            assert.equal(result.coherence.endpointPaths.length, 6);
            assert.equal(result.displayedExactness.source, result.source);
            assert.equal(result.displayedExactness.assumptionsAdded, 0);
            assert.equal(result.displayedExactness.trustDecisions, 0);
            assert.equal(result.displayedExactness.provesDisplayedCasExactness, true);
            assert.ok(kernelExpressionEquals(result.displayedExactness.diagram, result.coherence.nativeDiagram));
            assert.deepEqual(result.displayedExactness.pairs.map(pair => [pair.position, pair.kind, pair.degree]),
                [[1, 'target', 2], [2, 'middle', 1], [3, 'source', 1], [4, 'target', 1], [5, 'middle', 0], [6, 'source', 0]]);
            const certificateInput = { source: result.source, formalRing: v.formalRing, formalModel: v.formalModel,
                normality: v.normality, maps: result.maps, windows: result.windows, displayed: result.displayed,
                coherence: result.coherence };
            assert.throws(() => constructAlgebraFormalFreydNativeDisplayedExactness({ ...certificateInput,
                displayed: result.displayed.slice(1) }), /original nonempty coherent LES diagram/i);
            assert.throws(() => constructAlgebraFormalFreydNativeDisplayedExactness({ ...certificateInput,
                maps: result.maps.filter(map => map.entry.degree !== 1 || map.entry.role !== 'inclusion') }), /retained LES map/i);
            const changed = [...result.coherence.arrows];
            const different = result.points.map(point => point.realization.formalPoint).find(
                point => !kernelExpressionEquals(point, changed[1].formalSource));
            assert.ok(different, 'The fixture must supply a distinct H endpoint');
            changed[1] = { ...changed[1], formalSource: different };
            assert.throws(() => constructAlgebraFormalFreydDiagramCoherence({ source: result.source,
                formalRing: v.formalRing, arrows: changed }), /shared endpoint|type|mismatch/i);
            assert.ok(result.exactness.every(e => e.evidence.assumptionsAdded === 0));
            assert.equal(result.counts.homologyReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            assert.equal(result.counts.connectingReplays, 0);
            assert.equal(result.source.environment.lookup('bridge_FreydHomologyModel'), undefined);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
            t.diagnostic(JSON.stringify(result.counts));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('reuses the complete diagram without further decisions or source changes', async () => {
        const { input, result } = await consumer();
        trace('reuse-start');
        const again = await trustAlgebraFormalFreydNativeDiagram({ ...input, source: result.source,
            artifactId: 'native-diagram-reuse', decisionEvidence: () => { assert.fail('Every existing diagram claim must be reused'); } });
        trace('reuse-finish');
        assert.equal(again.source, result.source);
        assert.equal(again.counts.newAssumptions, 0);
        assert.equal(again.counts.reused, 215);
        assert.ok(kernelExpressionEquals(again.coherence.path, result.coherence.path));
        assert.ok(kernelExpressionEquals(again.displayedExactness.proof, result.displayedExactness.proof));
        assert.ok(kernelExpressionEquals(again.displayedExactness.inputs, result.displayedExactness.inputs));
        again.displayed.forEach((a, i) => assert.ok(kernelExpressionEquals(a.result.proof, result.displayed[i].result.proof)));
    });

    it('emits all native diagram observations and the separate whole exactness proofs', async () => {
        const { result } = await consumer();
        trace('emission-start');
        const directory = process.env.EMDASH_PROOF_CAS_NATIVE_DIAGRAM_PROBE_DIR;
        if (directory) mkdirSync(directory, { recursive: true });
        const checker = createCoreProofChecker(result.source.environment);
        const manifest = [];
        // Keep proof artifacts local to their actual module dependencies.
        const terms = result.points.flatMap(point => [
            { label: point.entry.key + ' native H', term: point.realization.formalPoint, type: point.realization.pointType, span: p.span! },
            { label: point.entry.key + ' CAS H', term: point.realization.nativePoint, type: point.realization.pointType, span: p.span! }
        ]);
        const assertions = result.displayed.flatMap((a, i) => {
            const r = a.result.observation.realization;
            checker.check(checker.rootContext, a.result.proof, r.claimType);
            return [{ label: 'displayed arrow ' + i, term: r.formalArrow, type: r.observationType, span: p.span! },
                { label: 'displayed CAS arrow ' + i, term: r.nativeArrow, type: r.observationType, span: p.span! },
                { label: 'displayed interpretation ' + i, term: a.result.proof, type: r.claimType, span: p.span! }];
        });
        // Emit a single observation artifact for the entire shared diagram.
        const coherent = [
            { label: 'whole native observation diagram', term: result.coherence.formalDiagram, type: result.coherence.diagramType, span: p.span! },
            { label: 'whole CAS observation diagram', term: result.coherence.nativeDiagram, type: result.coherence.diagramType, span: p.span! },
            { label: 'derived whole diagram path', term: result.coherence.path, type: result.coherence.pathType, span: p.span! }
        ];
        const observation = freydNativeModelProbe(result.source.environment, [...terms, ...assertions, ...coherent]);
        if (directory) writeFileSync(join(directory, 'diagram.lp'), observation);
        manifest.push({ file: 'diagram.lp', assertions: terms.length + assertions.length + coherent.length });
        const displayedExactness = [...result.displayedExactness.pairs.map(pair => ({
            label: 'displayed pair ' + pair.position + ' canonical exactness', term: pair.term, type: pair.type, span: p.span!
        })), { label: 'whole displayed CAS LES exactness', term: result.displayedExactness.proof,
            type: result.displayedExactness.type, span: p.span! }];
        displayedExactness.forEach(assertion => checker.check(checker.rootContext, assertion.term, assertion.type));
        const certificate = freydNativeLesCertificateProbe(result.source.environment, displayedExactness);
        if (directory) writeFileSync(join(directory, 'displayed_exactness.lp'), certificate.source);
        manifest.push({ file: 'displayed_exactness.lp', assertions: displayedExactness.length });
        for (const exact of result.exactness) {
            const probe = freydNativeExactnessProbe(exact.evidence.source.environment, exact.evidence.evidence.map(e => ({
                label: 'window ' + exact.degree + ' ' + e.position + ' exactness', term: e.term, type: e.type, span: p.span!
            })));
            const file = 'exactness_' + exact.degree + '.lp';
            if (directory) writeFileSync(join(directory, file), probe.source);
            manifest.push({ file, assertions: 3 });
        }
        if (directory) writeFileSync(join(directory, 'manifest.json'), JSON.stringify({ files: manifest, counts: result.counts }, null, 2) + '\n');
        trace('emission-finish');
    });
});
