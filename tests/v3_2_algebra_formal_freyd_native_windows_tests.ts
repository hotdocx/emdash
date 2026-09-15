/** All three original native δ windows under one model and source. */
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
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
import { trustAlgebraFormalFreydNativeConnectingWindows } from '../src/v3_2/algebra_formal_freyd_native_connecting_windows';
import { polynomialFreydHomologyFixture, isPolynomialFreydMorphismZero } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { freydNativeModelProbe } from './v3_2_algebra_formal_freyd_native_model_fixtures';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as nativeConnecting from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';

const p = provenance('surface', 'native connecting windows', sourceSpan('tests/native-connecting-windows.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({ id: 'tests.native-connecting-windows', revision: 'v1',
    coefficientContract: 'Interpret the ring and coefficient names in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native whole P/Q; selected-arrow realization is separately explicit.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality of that native model.' });
const prepare = () => prepareAlgebraFormalFreydNativeRationalModelContext({ backend, namePrefix: 'native_windows',
    selected: algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(
        polynomialFreydHomologyFixture('two'))) });
let setup: ReturnType<typeof prepare>;
const context = () => setup ??= prepare();
const adoptEquations = async () => {
    const v = context(), goalId = 'native-windows-replay', type = v.bundle.realization.claimType;
    const run = await runAlgebraFormalWorkflow({ goalId, adapter: v.bundle.adapter, realization: v.bundle.realization,
        engine: v.bundle.engine, document: { moduleId: v.initialSource.moduleId, declarationId: goalId,
            environment: v.environment, type, provenance: p, fingerprint: fingerprint(goalId),
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: type } }) } });
    return trustAlgebraFormalFreydLongExact({ artifactId: 'native-windows-equations', bundle: v.bundle, run,
        source: v.initialSource, fingerprint, decisionEvidence: id => 'Explicitly adopt the original matrix equation ' + id });
};
let equationsPromise: ReturnType<typeof adoptEquations>;
const equations = () => equationsPromise ??= adoptEquations();
const realize = async () => {
    const v = context(), adopted = await equations();
    const input = { artifactId: 'native-windows-model', modelId: 'native-window-model', formalModel: v.formalModel,
        normality: v.normality, prepared: v.preparedModel, adopted, fingerprint,
        decisionEvidence: (id: string) => 'Explicit native window interpretation or computed matrix equation: ' + id };
    const result = await trustAlgebraFormalFreydNativeConnectingWindows(input);
    return { v, adopted, input, result };
};
let realizationPromise: ReturnType<typeof realize>;
const consumer = () => realizationPromise ??= realize();

describe('v3.2 bounded native connecting windows', () => {
    it('realizes both zero endpoints and the middle delta in one native model without reselection', async t => {
        await equations();
        const forbid = () => { throw new Error('Bounded realization must retain the original H, delta and universals'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { v, adopted, result } = await consumer();
            assert.equal(result.native, adopted.adoption.result.computed.value.result);
            assert.equal(result.upstreamAdoption, adopted);
            assert.equal(result.inventoryData, v.preparedModel.inventory.data);
            assert.deepEqual(result.windows.map(w => [w.entry.degree, w.entry.position]), [[0, 6], [1, 3], [2, 0]]);
            assert.deepEqual(result.windows.map(w => isPolynomialFreydMorphismZero(w.entry.prepared.selected.homologyMap)), [true, false, true]);
            assert.equal(result.counts.windows, 3);
            assert.equal(result.counts.homologyReplays, 0);
            assert.equal(result.counts.connectingReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            assert.equal(result.profile.provesWholeDiagramCoherence, false);
            assert.equal(result.profile.assumesOutputExactness, false);
            assert.equal(result.source.environment.lookup('bridge_FreydHomologyModel'), undefined);
            const checker = createCoreProofChecker(result.source.environment);
            let previous = adopted.source;
            for (const window of result.windows) {
                const observed = window.result.observation.realization;
                assert.equal(window.entry.prepared.selected, result.native.windows[window.entry.degree].connecting);
                assert.equal(observed.source.actual.selected, window.entry.prepared.selected.source);
                assert.equal(observed.target.actual.selected, window.entry.prepared.selected.target);
                assert.ok(kernelExpressionEquals(observed.values.M, v.formalModel));
                assert.ok(kernelExpressionEquals(observed.values.N, v.normality));
                assert.deepEqual(window.result.source.entries.slice(0, previous.entries.length), previous.entries);
                checker.check(checker.rootContext, window.result.proof, observed.claimType);
                previous = window.result.source;
            }
            assert.equal(previous, result.source);
            assert.equal(adopted.source.entries.length, v.bundle.equations.claims.length);
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
            t.diagnostic(JSON.stringify(result.counts));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('reuses all three complete windows without any new decision or source change', async () => {
        const { input, result } = await consumer();
        const again = await trustAlgebraFormalFreydNativeConnectingWindows({ ...input, source: result.source,
            artifactId: 'native-windows-reuse', decisionEvidence: () => { assert.fail('Every existing window claim must be reused'); } });
        assert.equal(again.source, result.source);
        assert.equal(again.counts.reused, 111);
        assert.equal(again.counts.newAssumptions, 0);
        assert.equal(again.counts.interpretationClaims, 0);
        again.windows.forEach((w, i) => assert.ok(kernelExpressionEquals(w.result.proof, result.windows[i].result.proof)));
    });

    it('rejects foreign inventories, wrong normality and missing whole adoption before decisions', async () => {
        const { v, input } = await consumer();
        const base = { ...input, decisionEvidence: () => { assert.fail('Reject invalid bounded inputs before further decisions'); } };
        await assert.rejects(trustAlgebraFormalFreydNativeConnectingWindows({ ...base, prepared: { ...input.prepared } }), /issued/iu);
        await assert.rejects(trustAlgebraFormalFreydNativeConnectingWindows({ ...base, source: v.initialSource }), /original whole adoption/iu);
        await assert.rejects(trustAlgebraFormalFreydNativeConnectingWindows({ ...base, normality: v.formalModel }));
        const other = prepareAlgebraFormalFreydNativeRationalModelContext({ backend, namePrefix: 'other_windows', selected: v.selected });
        await assert.rejects(trustAlgebraFormalFreydNativeConnectingWindows({ ...base, prepared: other.preparedModel }), /another whole CAS replay/iu);
    });

    it('emits all native endpoint and middle windows for Lambdapi conformance', async () => {
        const { result } = await consumer();
        const directory = process.env.EMDASH_PROOF_CAS_NATIVE_WINDOWS_PROBE_DIR;
        if (directory) mkdirSync(directory, { recursive: true });
        const manifest = [];
        for (const { entry, result: window } of result.windows) {
            const r = window.observation.realization;
            const source = freydNativeModelProbe(window.source.environment, [
                { label: 'native delta degree ' + entry.degree, term: r.formalArrow, type: r.observationType, span: p.span! },
                { label: 'original CAS delta degree ' + entry.degree, term: r.nativeArrow, type: r.observationType, span: p.span! },
                { label: 'explicit native delta realization ' + entry.degree, term: window.proof, type: r.claimType, span: p.span! }
            ]);
            assert.doesNotMatch(source, /FreydHomologyModel|freyd_homology_model/u);
            const file = 'connecting_' + entry.degree + '.lp';
            manifest.push({ degree: entry.degree, position: entry.position, file, assertions: 3,
                zero: isPolynomialFreydMorphismZero(entry.prepared.selected.homologyMap) });
            if (directory) writeFileSync(join(directory, file), source);
        }
        if (directory) writeFileSync(join(directory, 'manifest.json'), JSON.stringify({ windows: manifest, counts: result.counts }, null, 2) + '\n');
    });
});
