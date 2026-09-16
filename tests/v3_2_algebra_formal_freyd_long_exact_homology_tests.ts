/** Every retained interior becomes a formal selected homology/exactness pair. */

import { prepareAlgebraFormalFreydRationalInputs } from '../src/v3_2/algebra_formal_freyd_rational_preparation';
import { createAlgebraFormalAssumptionSource } from '../src/v3_2/algebra_formal_assumption_source';
import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it, mock } from 'node:test';
import { AFFINE_FORMAL_FINITE_MODULE_BINDINGS } from '../src/v3_2/algebra_formal_finite_module';
import { AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS } from '../src/v3_2/algebra_formal_localization_signatures';
import { AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS } from '../src/v3_2/algebra_formal_presentation_morphism';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';
import { affineFormalCommRingType, affineFormalRingElementType } from '../src/v3_2/algebra_formal_conformance';
import { binderMode, kernelExpressionEquals, kernelFree, provenance, sourceSpan } from '../src/v3_2/kernel';
import { checkLambdapiProbe } from '../src/v3_2/probe';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { runAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';
import { KernelExpression } from '../src/v3_2/kernel';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeWindow from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_actual_homology_signatures';
import { createFormalFreydRawWitnessProofEnvironment, constructAlgebraFormalFreydRawWitnesses, FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_raw_witnesses';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_kernel_choice_provider_signatures';
import {
    ALGEBRA_FORMAL_FREYD_LONG_EXACT_HOMOLOGY_PROFILE,
    prepareAlgebraFormalFreydLongExactHomology, trustAlgebraFormalFreydLongExactHomology
} from '../src/v3_2/algebra_formal_freyd_long_exact_homology';

const p = provenance('surface', 'whole actual formal homology', sourceSpan('tests/whole-actual-homology.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});

const backend = { id: 'tests.retained-raw-polynomial-freyd', revision: 'v1' };
let retainedSelection: ReturnType<typeof selectResult> | undefined;
const selectResult = () => {
    const sequence = polynomialFreydHomologyFixture('two');
    return algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(sequence));
};
const selectedResult = () => retainedSelection ??= selectResult();
let preparedContext: ReturnType<typeof prepareRawContext>;
const prepareRawContext = () => {
    const inputs = prepareAlgebraFormalFreydRationalInputs({ backend, selected: selectedResult(), namePrefix: 'whole_actual' });
    const environment = createFormalFreydRawWitnessProofEnvironment([
        { name: inputs.formalRing.name, type: affineFormalCommRingType() },
        ...[...inputs.generatorTerms, ...inputs.coefficients.map(c => c.term)].map(term => ({
            name: term.name, type: affineFormalRingElementType(inputs.formalRing)
        }))
    ]);
    const initialSource = createAlgebraFormalAssumptionSource({ moduleId: 'proof.cas.whole-actual-homology',
        sourceId: 'tests/whole-actual-homology.assumptions', baseEnvironment: environment });
    return { ...inputs, environment, initialSource };
};
const rawContext = () => preparedContext ??= prepareRawContext();

const construct = async () => {
    const setup = rawContext();
    const { bundle, preparedHomology: prepared, preparedRaw: rawPreparation,
        environment, initialSource: initial } = setup;
    const target = bundle.realization.claimType, goalId = 'whole-actual-homology-replay';
    const run = await runAlgebraFormalWorkflow({ document: { moduleId: initial.moduleId, declarationId: goalId,
        environment, type: target, plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
        provenance: p, fingerprint: fingerprint(goalId) }, goalId, adapter: bundle.adapter, realization: bundle.realization, engine: bundle.engine });
    const adopted = await trustAlgebraFormalFreydLongExact({ artifactId: 'whole-actual-upstream', bundle, run,
        source: initial, fingerprint, decisionEvidence: id => 'Explicitly adopt original whole equation ' + id });
    const decisions: string[] = [];
    const input = { artifactId: 'whole-actual-homology', prepared, adopted, fingerprint,
        decisionEvidence: (id: string) => { decisions.push(id); return 'Explicit equation/provider trust ' + id; } };
    const forbid = () => { throw new Error('Downstream actual homology must reuse the whole replay and selected kernels'); };
    const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
        mock.method(nativeWindow, 'algebraPolynomialFreydHomologyWindow', forbid),
        mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
        mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
        mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
    try {
        const result = await trustAlgebraFormalFreydLongExactHomology(input);
        const raw = constructAlgebraFormalFreydRawWitnesses({ prepared: rawPreparation, adopted, source: result.source });
        spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        return { bundle, prepared, rawPreparation, raw, initial, adopted, input, result, decisions };
    } finally { spies.forEach(spy => spy.mock.restore()); }
};
let resultPromise: ReturnType<typeof construct> | undefined;
const consumer = () => resultPromise ??= construct();

const bindings = {
    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
    ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
    ...FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS
};
const imports = 'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;\n' +
    'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;';

describe('v3.2 whole long-exact actual formal homologies', () => {
    it('constructs all six homologies and exactness witnesses over the actual formal spine', async () => {
        const v = await consumer();
        assert.equal(v.result.native, v.adopted.adoption.result.computed.value.result);
        assert.equal(v.result.spine.native, v.result.native);
        assert.equal(v.result.epicities.native, v.result.native);
        assert.equal(v.result.interiors.length, 6);
        assert.equal(v.result.counts.positions, 6);
        assert.equal(v.result.counts.wholeHomologyReplays, 0);
        assert.equal(v.result.counts.weakKernelReselections, 0);
        assert.equal(v.result.counts.newAssumptions, v.result.source.entries.length - v.adopted.source.entries.length);
        assert.equal(v.result.source.entries.filter(entry => entry.classification === 'trusted-presentation-semantics').length, 12);
        assert.equal(v.initial.entries.length, 0);
        assert.deepEqual(v.result.interiors.map(entry => [entry.position, entry.degree, entry.role]),
            [[1, 1, 'A'], [2, 1, 'B'], [3, 1, 'C'], [4, 0, 'A'], [5, 0, 'B'], [6, 0, 'C']]);
        const checker = createCoreProofChecker(v.result.source.environment);
        checker.check(checker.rootContext, v.result.spine.spine.term, v.result.spine.spine.type);
        v.result.interiors.forEach((entry, index) => {
            assert.equal(entry.point, v.result.native.interior[index]);
            assert.equal(entry.constructed.selected, entry.point.exactness.homology);
            assert.equal(entry.providers.native, entry.point.exactness.homology.cycles);
            assert.ok(kernelExpressionEquals(entry.constructed.above, v.result.spine.arrows[index]));
            assert.ok(kernelExpressionEquals(entry.constructed.below, v.result.spine.arrows[index + 1]));
            assert.ok(kernelExpressionEquals(entry.constructed.boundary, v.result.epicities.witnesses[index].constructed.morphism));
            checker.check(checker.rootContext, entry.constructed.term, entry.constructed.type);
            checker.check(checker.rootContext, entry.constructed.exactness, entry.constructed.exactnessType);
        });
        assert.equal(ALGEBRA_FORMAL_FREYD_LONG_EXACT_HOMOLOGY_PROFILE.claimsGenericLongExactTheorem, false);
    });

    it('constructs every labelled raw witness without further assumptions or replay', async () => {
        const v = await consumer();
        assert.equal(v.raw.native.result, v.result.native);
        assert.equal(v.raw.assumptionsAdded, 0);
        assert.equal(v.raw.replays, 0);
        assert.equal(v.raw.source.entries.length, v.result.source.entries.length);
        assert.equal(v.raw.entries.length, v.bundle.equations.entries.length);
        assert.equal(v.raw.unique.reduce((sum, group) => sum + group.labels.length, 0), v.raw.entries.length);
        for (const prefix of ['sequence/row/', 'snake/', 'snake-exact/', 'connecting/', 'long-exact/']) {
            assert.ok(v.raw.entries.some(entry => entry.id.startsWith(prefix)), prefix);
        }
        const checker = createCoreProofChecker(v.result.source.environment);
        v.raw.unique.forEach(entry => checker.check(checker.rootContext, entry.term, entry.type));
        assert.throws(() => constructAlgebraFormalFreydRawWitnesses({ prepared: { ...v.rawPreparation, shapeData: 'stale' },
            adopted: v.adopted, source: v.result.source }), /changed/u);
    });

    it('rejects forged preparations, missing whole adoption and a foreign profile before trust', async () => {
        const v = await consumer();
        const before = v.decisions.length;
        await assert.rejects(() => trustAlgebraFormalFreydLongExactHomology({ ...v.input, prepared: { ...v.prepared } }), /issued/u);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactHomology({ ...v.input, adopted: { ...v.adopted, source: v.initial } }), /original whole adoption/u);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactHomology({ ...v.input,
            adopted: { ...v.adopted, profileRevision: 'foreign' as typeof v.adopted.profileRevision } }), /profile/u);
        assert.equal(v.decisions.length, before);
    });

    it('rejects changed interior labels, pairs and choices before preparing a proof', async () => {
        const v = await consumer();
        const selected = v.bundle.selected;
        const point = selected.result.interior[0];
        for (const changed of [
            { ...point, term: { ...point.term, position: 7 } },
            { ...point, pair: selected.result.interior[1].pair },
            { ...point, exactness: selected.result.interior[1].exactness }
        ]) {
            const bundle = { ...v.bundle, selected: { ...selected, result: { ...selected.result,
                interior: [changed, ...selected.result.interior.slice(1)] } } };
            assert.throws(() => prepareAlgebraFormalFreydLongExactHomology(bundle), /actual|retain/iu);
        }
    });

    it('rejects changed adopted inventories and foreign replay identities before trust', async () => {
        const v = await consumer();
        const before = v.decisions.length;
        await assert.rejects(() => trustAlgebraFormalFreydLongExactHomology({ ...v.input, adopted: { ...v.adopted,
            equations: { ...v.adopted.equations, entries: v.adopted.equations.entries.slice(1) } } }), /inventory/u);
        const adoption = v.adopted.adoption;
        await assert.rejects(() => trustAlgebraFormalFreydLongExactHomology({ ...v.input, adopted: { ...v.adopted,
            adoption: { ...adoption, result: { ...adoption.result, request: { ...adoption.result.request,
                adapter: { ...adoption.result.request.adapter } } } } } }), /another whole replay/u);
        assert.equal(v.decisions.length, before);
    });

    it('checks the formal spine, twelve homology/exactness terms and all distinct raw witnesses together', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_LONG_EXACT_HOMOLOGY !== '1'
    }, async () => {
        const { result, raw } = await consumer();
        let environment = result.source.environment;
        const terms: [string, KernelExpression, KernelExpression][] = [['whole_actual_spine', result.spine.spine.term, result.spine.spine.type]];
        result.interiors.forEach(entry => {
            terms.push(['whole_actual_homology_' + entry.position, entry.constructed.term, entry.constructed.type]);
            terms.push(['whole_actual_exactness_' + entry.position, entry.constructed.exactness, entry.constructed.exactnessType]);
        });
        raw.unique.forEach((entry, index) => terms.push(['whole_raw_witness_' + index, entry.term, entry.type]));
        const assertions = terms.map(([name, term, type], index) => {
            environment = environment.extend({ name, type, body: term, transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
            return { label: name, term: kernelFree(name, p), type, span: sourceSpan('generated/whole-actual-homology.ts', index + 1, 1) };
        });
        const serialized = serializeCoreLfKernelProbe({ environment, externalFreeReferences: bindings, assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            imports) },
        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});
