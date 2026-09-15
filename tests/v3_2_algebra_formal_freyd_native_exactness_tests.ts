/** Derived whole exactness at the actual native window, with no output assumption. */
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { describe, it } from 'node:test';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { binderMode, kernelFree, kernelInstantiate, kernelExpressionEquals, KernelExpression, provenance, sourceSpan } from '../src/v3_2/kernel';
import { runAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { defineAlgebraFormalFreydNativeRationalBackend, prepareAlgebraFormalFreydNativeRationalModelContext } from '../src/v3_2/algebra_formal_freyd_native_rational_model_context';
import { trustAlgebraFormalFreydNativeConnecting } from '../src/v3_2/algebra_formal_freyd_native_connecting_workflow';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';

import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { freydNativeExactnessProbe, freydNativeExactnessPointProbe } from './v3_2_algebra_formal_freyd_native_exactness_fixtures';
import { constructAlgebraFormalFreydNativeExactness } from '../src/v3_2/algebra_formal_freyd_native_exactness';
import { algebraFormalFreydNativeExactnessExpressions,
    FREYD_NATIVE_EXACTNESS_ARGUMENTS } from '../src/v3_2/algebra_formal_freyd_native_exactness_signatures';
import { createFormalFreydExactnessPointProofEnvironment, algebraFormalFreydExactnessPointExpressions } from '../src/v3_2/algebra_formal_freyd_exactness_point_signatures';
import { observeAlgebraFormalFreydNativeExactness } from '../src/v3_2/algebra_formal_freyd_exactness_points';

const p = provenance('surface', 'native categorical exactness', sourceSpan('tests/native-exactness.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({ id: 'tests.native-exactness', revision: 'v1',
    coefficientContract: 'Interpret the ring and coefficient names in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native whole P/Q; selected-arrow realization is separately explicit.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality of that native model.' });
const prepare = () => prepareAlgebraFormalFreydNativeRationalModelContext({ backend, namePrefix: 'native_exactness',
    selected: algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(
        polynomialFreydHomologyFixture('two'))) });
let setup: ReturnType<typeof prepare>;
const context = () => setup ??= prepare();
const adoptEquations = async () => {
    const v = context(), goalId = 'native-exactness-replay', type = v.bundle.realization.claimType;
    const run = await runAlgebraFormalWorkflow({ goalId, adapter: v.bundle.adapter, realization: v.bundle.realization,
        engine: v.bundle.engine, document: { moduleId: v.initialSource.moduleId, declarationId: goalId,
            environment: v.environment, type, provenance: p, fingerprint: fingerprint(goalId),
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: type } }) } });
    return trustAlgebraFormalFreydLongExact({ artifactId: 'native-exactness-equations', bundle: v.bundle, run,
        source: v.initialSource, fingerprint, decisionEvidence: id => 'Explicitly adopt the original matrix equation ' + id });
};
let equationsPromise: ReturnType<typeof adoptEquations>;
const equations = () => equationsPromise ??= adoptEquations();
const realize = async () => {
    const v = context(), adopted = await equations();
    const entry = v.preparedModel.inventory.connectings.find(x => x.key === 'degree/1/connecting')!;
    const decisions: string[] = [];
    const input = { artifactId: 'native-exactness-model', modelId: 'native-scalar-model', observationId: 'degree/1/connecting',
        formalModel: v.formalModel, normality: v.normality, prepared: entry.prepared, source: adopted.source, fingerprint,
        decisionEvidence: (id: string) => { decisions.push(id); return 'Explicit matrix computation or complete native arrow interpretation: ' + id; } };
    const result = await trustAlgebraFormalFreydNativeConnecting(input);
    return { v, adopted, entry, input, result, decisions };
};
let realizationPromise: ReturnType<typeof realize>;
const consumer = () => realizationPromise ??= realize();

const symbolic = () => {
    let environment = createFormalFreydExactnessPointProofEnvironment([]);
    let type = environment.lookup('bridge_freyd_adjunction_model_middle_exact_evidence')!.type;
    const values: Record<string, KernelExpression> = {};
    for (const field of FREYD_NATIVE_EXACTNESS_ARGUMENTS) {
        if (type.tag !== 'pi') throw new Error('Exactness telescope ended early');
        assert.equal(type.binder.mode.plicity, field.implicit ? 'implicit' : 'explicit');
        const term = kernelFree('exactness_input_' + field.name, p);
        environment = environment.extend({ name: term.name, type: type.binder.type,
            mode: binderMode('explicit', 'functorial'), provenance: p });
        values[field.name] = term;
        type = kernelInstantiate(type.body, term);
    }
    return { environment, values };
};

describe('v3.2 native whole categorical exactness', () => {
    it('checks the three derived constructors at the exact whole window telescope', () => {
        const { environment, values } = symbolic();
        assert.equal(FREYD_NATIVE_EXACTNESS_ARGUMENTS.length, 45);
        const checker = createCoreProofChecker(environment);
        const evidence = algebraFormalFreydNativeExactnessExpressions(values);
        assert.deepEqual(evidence.map(e => e.position), ['middle', 'source', 'target']);
        evidence.forEach(e => checker.check(checker.rootContext, e.term, e.type));
        const points = algebraFormalFreydExactnessPointExpressions(evidence);
        const pointAssertions = points.flatMap(e => [
            { label: e.position + ' point data', term: e.data, type: e.dataType, span: p.span! },
            { label: e.position + ' original comparison', term: e.arrow, type: e.arrowType, span: p.span! },
            { label: e.position + ' observed evidence', term: e.evidence, type: e.type, span: p.span! }
        ]);
        pointAssertions.forEach(e => checker.check(checker.rootContext, e.term, e.type));
        if (process.env.EMDASH_NATIVE_EXACTNESS_POINT_SYMBOLIC_OUTPUT) writeFileSync(process.env.EMDASH_NATIVE_EXACTNESS_POINT_SYMBOLIC_OUTPUT,
            freydNativeExactnessPointProbe(environment, pointAssertions).source);
        const probe = freydNativeExactnessProbe(environment, evidence.map(e => ({ label: e.position + ' whole exactness',
            term: e.term, type: e.type, span: p.span! })));
        if (process.env.EMDASH_PROOF_CAS_NATIVE_EXACTNESS_SYMBOLIC_OUTPUT) {
            writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_EXACTNESS_SYMBOLIC_OUTPUT, probe.source);
        }
    });

    it('rejects missing inputs and raw chain evidence in place of categorical row shortness', () => {
        const { environment, values } = symbolic(), checker = createCoreProofChecker(environment);
        const { N, ...missing } = values;
        assert.throws(() => algebraFormalFreydNativeExactnessExpressions(missing), /exact native window/iu);
        assert.throws(() => algebraFormalFreydNativeExactnessExpressions({ ...values, extra: N }), /exact native window/iu);
        for (const bad of [{ ...values, N: values.M }, { ...values, xm: values.cm }]) {
            const e = algebraFormalFreydNativeExactnessExpressions(bad)[0];
            assert.throws(() => checker.check(checker.rootContext, e.term, e.type));
        }
        const original = algebraFormalFreydNativeExactnessExpressions(values);
        assert.throws(() => algebraFormalFreydExactnessPointExpressions(original.map((e, i) => i ? e :
            { ...e, term: kernelFree('unrelated_proof', p) })), /original whole exactness constructor/);
    });

    it('constructs exactness on the actual CAS window without adding an assumption or using the delta agreement', async t => {
        const { result } = await consumer();
        const source = result.source, before = source.entries.length;
        assert.throws(() => constructAlgebraFormalFreydNativeExactness({ ...result, prepared: { ...result.prepared } }),
            /original window preparation/iu);
        const exactness = constructAlgebraFormalFreydNativeExactness(result);
        const points = observeAlgebraFormalFreydNativeExactness(result);
        assert.equal(points.source, source);
        assert.equal(points.assumptionsAdded, 0);
        assert.equal(points.trustDecisions, 0);
        assert.equal(points.provesDisplayedCasExactness, false);
        assert.equal(points.definitions.length, 3);
        assert.ok(points.definitions.every(d => d.body !== undefined && d.transparency === 'transparent'));
        points.observations.forEach((e, i) => assert.equal(e.whole, points.whole.evidence[i]));
        assert.equal(exactness.source, source);
        assert.equal(exactness.assumptionsAdded, 0);
        assert.equal(exactness.trustDecisions, 0);
        assert.equal(exactness.wholeCategoricalEvidence, true);
        assert.equal(exactness.provesDisplayedCasExactness, false);
        assert.equal(source.entries.length, before);
        const probe = freydNativeExactnessProbe(source.environment, exactness.evidence.map(e => ({
            label: 'native concrete ' + e.position + ' exactness', term: e.term, type: e.type, span: p.span!
        })));
        if (result.proof.tag !== 'reference') throw new Error('The test expects the issued delta interpretation reference');
        assert.equal(probe.environment.lookup(result.proof.name), undefined, 'The delta agreement is not an exactness premise');
        assert.ok(probe.environment.lookup(result.observation.realization.values.M.tag === 'reference'
            ? result.observation.realization.values.M.name : 'missing'));
        const checked = createCoreProofChecker(probe.environment);
        exactness.evidence.forEach(e => checked.check(checked.rootContext, e.term, e.type));
        assert.doesNotMatch(probe.source, /freyd_adjunction_model_connecting_observation|FreydHomologyModel/u);
        const pointProbe = freydNativeExactnessPointProbe(points.environment, points.observations.flatMap(e => [
            { label: e.position + ' native point data', term: e.data, type: e.dataType, span: p.span! },
            { label: e.position + ' native point comparison', term: e.arrow, type: e.arrowType, span: p.span! },
            { label: e.position + ' native point evidence', term: e.evidence, type: e.type, span: p.span! }
        ]));
        assert.equal(pointProbe.environment.lookup(result.proof.name), undefined);
        points.definitions.forEach(d => assert.ok(pointProbe.environment.lookup(d.name)?.body));
        assert.doesNotMatch(pointProbe.source, /freyd_adjunction_model_connecting_observation|FreydHomologyModel/u);
        if (process.env.EMDASH_NATIVE_EXACTNESS_POINT_OUTPUT) writeFileSync(process.env.EMDASH_NATIVE_EXACTNESS_POINT_OUTPUT, pointProbe.source);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_EXACTNESS_OUTPUT) {
            writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_EXACTNESS_OUTPUT, probe.source);
        }
        t.diagnostic(before + ' unchanged source assumptions; ' + probe.declarations + ' declarations in the checked dependency closure');
    });
});
