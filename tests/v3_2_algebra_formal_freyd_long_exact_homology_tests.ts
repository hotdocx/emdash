/** Every retained interior becomes a formal selected homology/exactness pair. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it, mock } from 'node:test';
import { AFFINE_FORMAL_FINITE_MODULE_BINDINGS } from '../src/v3_2/algebra_formal_finite_module';
import { AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS } from '../src/v3_2/algebra_formal_localization_signatures';
import { AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS } from '../src/v3_2/algebra_formal_presentation_morphism';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';
import { INTEGER_DOMAIN, RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialConstant } from '../src/v3_2/algebra_polynomial';
import { affineFormalRingElementType } from '../src/v3_2/algebra_formal_conformance';
import { binderMode, kernelExpressionEquals, kernelFree, provenance, sourceSpan } from '../src/v3_2/kernel';
import { checkLambdapiProbe } from '../src/v3_2/probe';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { defineAffineFormalPolynomialReifier } from '../src/v3_2/algebra_formal_reifier';
import { runAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';
import { KernelExpression } from '../src/v3_2/kernel';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeConnecting from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import * as nativeWindow from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { isPolynomialFreydMorphismZero, polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { algebraFormalFreydLongExactDelegationBundle, trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_actual_homology_signatures';
import { prepareAlgebraFormalFreydRawWitnesses,
    constructAlgebraFormalFreydRawWitnesses, FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_raw_witnesses';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_kernel_choice_provider_signatures';
import {
    ALGEBRA_FORMAL_FREYD_LONG_EXACT_HOMOLOGY_PROFILE,
    prepareAlgebraFormalFreydLongExactHomology, trustAlgebraFormalFreydLongExactHomology
} from '../src/v3_2/algebra_formal_freyd_long_exact_homology';
import { algebraFormalFreydLongExactModelInventory, prepareAlgebraFormalFreydLongExactModel } from '../src/v3_2/algebra_formal_freyd_long_exact_model_preparation';
import { trustAlgebraFormalFreydLongExactModel } from '../src/v3_2/algebra_formal_freyd_long_exact_model';
import { algebraFormalFreydModelType, FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_model_signatures';
import { FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_model_map_signatures';
import { algebraFormalFreydModelNormalityType, FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_model_connecting_signatures';
import * as nativeFunctorialHomology from '../src/v3_2/algebra_polynomial_freyd_functorial_homology';
import { defineAlgebraFormalFreydRationalBackend, prepareAlgebraFormalFreydRationalModelContext } from '../src/v3_2/algebra_formal_freyd_rational_model_context';

const p = provenance('surface', 'whole actual formal homology', sourceSpan('tests/whole-actual-homology.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});

const backend = defineAlgebraFormalFreydRationalBackend({
    id: 'tests.retained-polynomial-freyd', revision: 'v1',
    coefficientContract: 'Interpret the formal ring and coefficient names in the retained rational polynomial ring.',
    modelContract: 'Supply the coherent Freyd model matching the retained choices; no closed model is derived here.',
    normalityContract: 'Supply the normality enhancement of that same retained model.'
});
let retainedSelection: ReturnType<typeof selectResult> | undefined;
const selectResult = () => {
    const sequence = polynomialFreydHomologyFixture('two');
    return algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(sequence));
};
const selectedResult = () => retainedSelection ??= selectResult();
let preparedContext: ReturnType<typeof prepareAlgebraFormalFreydRationalModelContext> | undefined;
const modelContext = () => preparedContext ??= prepareAlgebraFormalFreydRationalModelContext({
    backend, selected: selectedResult(), namePrefix: 'whole_actual',
    moduleId: 'proof.cas.whole-actual-homology', sourceId: 'tests/whole-actual-homology.assumptions'
});

const construct = async () => {
    const setup = modelContext();
    const { bundle, preparedHomology: prepared, preparedRaw: rawPreparation,
        preparedModel: modelPreparation, formalModel: model, normality, environment, initialSource: initial } = setup;
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
        return { bundle, prepared, rawPreparation, raw, initial, adopted, input, result, decisions, model, normality, modelPreparation };
    } finally { spies.forEach(spy => spy.mock.restore()); }
};
let resultPromise: ReturnType<typeof construct> | undefined;
const consumer = () => resultPromise ??= construct();

const observeModels = async () => {
    const v = await consumer();
    const decisions: string[] = [];
    const input = { artifactId: 'bounded-model', modelId: 'bounded-model', formalModel: v.model,
        prepared: v.modelPreparation, adopted: v.adopted, source: v.result.source, fingerprint,
        decisionEvidence: (id: string) => { decisions.push(id); return 'Explicit retained bounded-model interpretation/equation ' + id; } };
    const result = await trustAlgebraFormalFreydLongExactModel(input);
    return { v, input, result, decisions };
};
let modelPromise: ReturnType<typeof observeModels> | undefined;
const modelConsumer = () => modelPromise ??= observeModels();

const observeConnectings = async () => {
    const prefix = await modelConsumer(), decisions: string[] = [];
    const input = { ...prefix.input, artifactId: 'bounded-model-complete', normality: prefix.v.normality,
        source: prefix.result.source, decisionEvidence: (id: string) => {
            decisions.push(id); return 'Explicit retained connecting interpretation/equation ' + id;
        } };
    const result = await trustAlgebraFormalFreydLongExactModel(input);
    return { prefix, input, result, decisions };
};
let connectingPromise: ReturnType<typeof observeConnectings> | undefined;
const connectingConsumer = () => connectingPromise ??= observeConnectings();

const bindings = {
    ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
    ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
    ...FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS,
    ...FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS
};
const imports = 'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;\n' +
    'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;\n' +
    'require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_connecting;';

describe('v3.2 whole long-exact actual formal homologies', () => {
    it('prepares a registered rational model context without reselection or adoption', () => {
        const selected = selectedResult();
        const forbid = () => { throw new Error('Context preparation must retain the original computations'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeWindow, 'algebraPolynomialFreydHomologyWindow', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            // The prepared engine retains its implementation function values. Keep
            // this no-execution probe separate from the later replay fixture.
            const setup = prepareAlgebraFormalFreydRationalModelContext({ backend, selected, namePrefix: 'guarded_setup' });
            assert.equal(setup.selected, selected);
            assert.equal(setup.bundle.selected, selected);
            assert.equal(setup.preparedHomology.bundle, setup.bundle);
            assert.equal(setup.preparedRaw.bundle, setup.bundle);
            assert.equal(setup.preparedModel.bundle, setup.bundle);
            assert.equal(setup.initialSource.entries.length, 0);
            assert.equal(setup.initialSource.environment, setup.environment);
            assert.equal(setup.profile.constructsModel, false);
            assert.equal(setup.profile.nativeWholeConnectingObservation, false);
            assert.deepEqual(setup.suppliedInputs.map(value => value.role),
                ['coefficient-interpretation', 'coherent-model', 'normality']);
            assert.ok(setup.suppliedInputs.every(value => value.classification === 'supplied-input'));
            const checker = createCoreProofChecker(setup.environment);
            checker.check(checker.rootContext, setup.formalModel, algebraFormalFreydModelType(setup.formalRing));
            checker.check(checker.rootContext, setup.normality, algebraFormalFreydModelNormalityType(setup.formalRing, setup.formalModel));
            for (const term of [...setup.generatorTerms, ...setup.coefficients.map(value => value.term)]) {
                checker.check(checker.rootContext, term, affineFormalRingElementType(setup.formalRing));
            }
            const names = [setup.formalRing, setup.formalModel, setup.normality,
                ...setup.generatorTerms, ...setup.coefficients.map(value => value.term)].map(term => term.name);
            assert.equal(new Set(names).size, names.length);
            assert.ok(Object.isFrozen(setup) && Object.isFrozen(setup.coefficients) && Object.isFrozen(setup.backend));
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });
    it('prepares registered rational model inventories identically to the retained manual interfaces', () => {
        const setup = modelContext();
        const coefficients = new Map(setup.coefficients.map(entry => [entry.value, entry.term]));
        const manualReifier = defineAffineFormalPolynomialReifier({ algebra: setup.reifier.algebra,
            formalRing: setup.formalRing, generatorTerms: setup.generatorTerms,
            coefficientReifier: value => {
                const term = coefficients.get(RATIONAL_DOMAIN.text(value));
                assert.ok(term, 'The automatic context must include every manually requested coefficient');
                return term;
            }, status: 'trusted-computation' });
        const manual = algebraFormalFreydLongExactDelegationBundle({ selected: setup.selected, reifier: manualReifier });
        assert.equal(manual.equationsData, setup.bundle.equationsData);
        assert.equal(prepareAlgebraFormalFreydLongExactHomology(manual).entriesData, setup.preparedHomology.entriesData);
        assert.equal(prepareAlgebraFormalFreydLongExactModel(manual).inventory.data, setup.preparedModel.inventory.data);
        const again = prepareAlgebraFormalFreydRationalModelContext({ backend, selected: setup.selected, namePrefix: 'whole_actual' });
        assert.equal(again.bundle.equationsData, setup.bundle.equationsData);
        assert.deepEqual(again.coefficients.map(c => [c.value, c.term.name]), setup.coefficients.map(c => [c.value, c.term.name]));
        const another = prepareAlgebraFormalFreydRationalModelContext({ backend, selected: setup.selected, namePrefix: 'another_scope' });
        assert.notEqual(another.formalRing.name, setup.formalRing.name);
        assert.notEqual(another.formalModel.name, setup.formalModel.name);
    });
    it('rejects invalid registered rational model contexts and coefficients after sealing', () => {
        const setup = modelContext(), base = { backend, selected: setup.selected, namePrefix: 'valid_scope' };
        assert.throws(() => prepareAlgebraFormalFreydRationalModelContext({ ...base, backend: { ...backend } }), /issued/iu);
        for (const namePrefix of ['', 'a/b', 'a-b', '1bad', 'a'.repeat(129)]) {
            assert.throws(() => prepareAlgebraFormalFreydRationalModelContext({ ...base, namePrefix }), /identifier/iu);
        }
        assert.throws(() => defineAlgebraFormalFreydRationalBackend({ ...backend, modelContract: ' ' }), /contract/iu);
        const selected = { ...setup.selected, result: { ...setup.selected.result,
            sequence: { ...setup.selected.result.sequence, ring: { ...setup.selected.result.sequence.ring,
                coefficientDomain: INTEGER_DOMAIN } } } };
        assert.throws(() => prepareAlgebraFormalFreydRationalModelContext({ ...base, selected: selected as unknown as typeof setup.selected }), /rational polynomial/iu);
        const before = setup.coefficients.map(c => c.term.name);
        const unknown = algebraPolynomialConstant(setup.selected.result.sequence.ring, '987654321');
        assert.throws(() => setup.reifier.reifyPolynomial(unknown), /not included/iu);
        assert.deepEqual(setup.coefficients.map(c => c.term.name), before);
        assert.equal(setup.initialSource.entries.length, 0);
        const known = RATIONAL_DOMAIN.normalize(setup.coefficients[0].value);
        const a = algebraPolynomialConstant(setup.selected.result.sequence.ring, known);
        const b = algebraPolynomialConstant(setup.selected.result.sequence.ring,
            { numerator: known.numerator * 2n, denominator: known.denominator * 2n });
        assert.ok(kernelExpressionEquals(setup.reifier.reifyPolynomial(a), setup.reifier.reifyPolynomial(b)));
    });
    it('replays the retained nonsplit result from a registered rational model context without adopting claims', async () => {
        const setup = modelContext(), goalId = 'registered-rational-model-replay';
        const target = setup.bundle.realization.claimType;
        const run = await runAlgebraFormalWorkflow({
            document: { moduleId: setup.initialSource.moduleId, declarationId: goalId,
                environment: setup.environment, type: target,
                plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
                provenance: p, fingerprint: fingerprint(goalId) },
            goalId, adapter: setup.bundle.adapter, realization: setup.bundle.realization, engine: setup.bundle.engine
        });
        assert.equal(run.result.interpretation.kind, 'claim');
        assert.equal(algebraFormalFreydLongExactModelInventory(setup.bundle, run.result.computed.value).data,
            setup.preparedModel.inventory.data);
        assert.equal(setup.initialSource.entries.length, 0);
    });
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

    it('observes every retained H point and induced map under one model without recomputation', async () => {
        await consumer();
        const forbid = () => { throw new Error('Bounded model observations must not recompute homology or its universals'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeFunctorialHomology, 'algebraPolynomialFreydInducedHomologyMap', forbid),
            mock.method(nativeWindow, 'algebraPolynomialFreydHomologyWindow', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid), mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { v, result } = await modelConsumer();
            assert.equal(result.native, v.result.native);
            assert.equal(result.points.length, 18);
            assert.equal(result.maps.length, 8);
            assert.equal(result.connectingCoverage, 'not-requested');
            assert.equal(result.connectings.length, 0);
            assert.equal(result.spineArrows.length, 0);
            assert.equal(result.counts.wholeHomologyReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            assert.ok(result.counts.reusedClaims > 0);
            assert.deepEqual(result.source.entries.slice(0, v.result.source.entries.length), v.result.source.entries);
            const checker = createCoreProofChecker(result.source.environment);
            result.points.forEach(({ entry, observation, proof }) => {
                const expected = entry.kind === 'degree' ? result.native.degrees[entry.degree + 1][entry.role].homology :
                    result.native.interior[entry.position! - 1].exactness.homology;
                assert.equal(observation.realization.actual.selected, expected);
                checker.check(checker.rootContext, proof, observation.realization.claimType);
            });
            result.maps.forEach(({ entry, observation, proof }) => {
                assert.equal(observation.realization.prepared.selected, result.native.degrees[entry.degree + 1][entry.role]);
                assert.equal(observation.profile.endpointTransport, false);
                checker.check(checker.rootContext, observation.realization.chain.term, observation.realization.chain.type);
                checker.check(checker.rootContext, proof, observation.realization.claimType);
            });
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('rejects invalid bounded model inventories and replay contexts before further adoption', async () => {
        const { v, input, decisions } = await modelConsumer();
        const before = decisions.length;
        await assert.rejects(() => trustAlgebraFormalFreydLongExactModel({ ...input, prepared: { ...input.prepared } }), /issued/iu);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactModel({ ...input, source: v.initial }), /original whole adoption/iu);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactModel({ ...input, formalModel: v.bundle.reifier.formalRing }), /type|convert|unif/iu);
        assert.equal(decisions.length, before);
        const selected = v.bundle.selected, degree = selected.result.degrees[1];
        for (const changed of [
            { ...degree, degree: 999 },
            { ...degree, inclusion: selected.result.degrees[0].inclusion },
            { ...degree, A: { ...degree.A, complex: degree.B.complex } }
        ]) assert.throws(() => prepareAlgebraFormalFreydLongExactModel({ ...v.bundle, selected: { ...selected,
            result: { ...selected.result, degrees: [selected.result.degrees[0], changed, ...selected.result.degrees.slice(2)] } } }), /degree|view|selection/iu);
    });

    it('upgrades the adopted prefix with every retained connecting arrow, including both endpoints', async () => {
        await modelConsumer();
        const forbid = () => { throw new Error('The connecting inventory must reuse every retained algorithm result'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeFunctorialHomology, 'algebraPolynomialFreydInducedHomologyMap', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(nativeWindow, 'algebraPolynomialFreydHomologyWindow', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const { prefix, result } = await connectingConsumer();
            assert.equal(result.native, prefix.result.native);
            assert.equal(result.connectingCoverage, 'all-retained-windows');
            assert.equal(result.connectings.length, 3);
            assert.equal(result.counts.connectings, result.native.windows.length);
            assert.equal(result.counts.connectingReplays, 0);
            assert.equal(result.counts.wholeHomologyReplays, 0);
            assert.equal(result.counts.universalReselections, 0);
            assert.deepEqual(result.source.entries.slice(0, prefix.result.source.entries.length), prefix.result.source.entries);
            for (const role of ['points', 'maps'] as const) {
                result[role].forEach((point, i) => assert.equal(point.proof, prefix.result[role][i].proof));
            }
            assert.deepEqual(result.connectings.map(({ entry }) => [entry.degree, entry.position]), [[0, 6], [1, 3], [2, 0]]);
            assert.deepEqual(result.spineArrows.map(arrow => arrow.kind),
                ['connecting', 'inclusion', 'projection', 'connecting', 'inclusion', 'projection', 'connecting']);
            result.spineArrows.forEach((value, position) => {
                assert.equal(value.position, position);
                assert.equal(value.entry.prepared.selected.homologyMap, result.native.arrows[position]);
                const owner = value.kind === 'connecting' ? result.connectings : result.maps;
                assert.ok(owner.some(entry => entry.observation === value.observation && entry.proof === value.proof));
            });
            assert.deepEqual(result.connectings.map(({ entry }) => isPolynomialFreydMorphismZero(entry.prepared.selected.homologyMap)),
                [true, false, true]);
            const checker = createCoreProofChecker(result.source.environment);
            for (const { entry, observation, proof } of result.connectings) {
                const value = observation.realization;
                assert.equal(entry.prepared.selected, result.native.windows[entry.degree].connecting);
                assert.equal(entry.prepared.selected.homologyMap, result.native.arrows[entry.position]);
                assert.equal(value.source.actual.selected, result.native.degrees[entry.degree + 1].C.homology);
                assert.equal(value.target.actual.selected, result.native.degrees[entry.degree].A.homology);
                checker.check(checker.rootContext, proof, value.claimType);
                for (const row of value.rowMaps) checker.check(checker.rootContext, row.term, row.type);
                const recorded = result.source.entries.find(e => kernelExpressionEquals(e.reference, proof));
                assert.equal(recorded?.classification, 'trusted-presentation-semantics');
            }
            // Consecutive windows share the very same model-side row proofs.
            for (let i = 0; i < result.connectings.length - 1; i++) {
                for (let row = 0; row < 3; row++) {
                    assert.equal(result.connectings[i].rows[row].exact, result.connectings[i + 1].rows[row + 1].exact);
                }
            }
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('reuses all connecting claims and rejects incomplete or mismatched windows before trust', async () => {
        const { prefix, input, result, decisions } = await connectingConsumer(), before = decisions.length;
        const replay = await trustAlgebraFormalFreydLongExactModel({ ...input, source: result.source });
        assert.equal(replay.counts.newAssumptions, 0);
        assert.equal(decisions.length, before);
        replay.connectings.forEach((entry, i) => assert.equal(entry.proof, result.connectings[i].proof));
        await assert.rejects(() => trustAlgebraFormalFreydLongExactModel({ ...input, normality: prefix.v.model }), /type|convert|unif/iu);
        assert.equal(decisions.length, before);
        const bundle = prefix.v.bundle, selected = bundle.selected, original = selected.result;
        for (const windows of [
            original.windows.slice(1),
            [...original.windows].reverse(),
            [{ ...original.windows[0], connecting: original.windows[1].connecting }, ...original.windows.slice(1)],
            [{ ...original.windows[0], connecting: { ...original.windows[0].connecting,
                source: original.windows[1].connecting.source } }, ...original.windows.slice(1)]
        ]) assert.throws(() => prepareAlgebraFormalFreydLongExactModel({ ...bundle,
            selected: { ...selected, result: { ...original, windows } } }), /retain|window|degree/iu);
    });

    it('checks the complete bounded connecting inventory against Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_LONG_EXACT_CONNECTING !== '1'
    }, async () => {
        const { result } = await connectingConsumer();
        // Separate independently bounded targets for the two zero endpoints and nonzero middle.
        for (const { entry, observation, proof } of result.connectings) {
            const value = observation.realization;
            const triples: [string, KernelExpression, KernelExpression][] = [
                ['model_delta', value.formalArrow, value.observationType],
                ['native_delta', value.nativeArrow, value.observationType],
                ['delta_interpretation', proof, value.claimType],
                ...value.rowMaps.map((row, i): [string, KernelExpression, KernelExpression] => ['row_map_' + i, row.term, row.type])
            ];
            const assertions = triples.map(([name, term, type]) => ({ label: name + '_' + entry.degree,
                term, type, span: sourceSpan('generated/bounded-connecting.ts', 1, 1) }));
            const serialized = serializeCoreLfKernelProbe({ environment: result.source.environment, externalFreeReferences: bindings, assertions });
            const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;', imports) },
                { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
            assert.equal(checked.timedOut, false, 'degree ' + entry.degree + '\n' + checked.diagnostics.slice(-5000));
            assert.equal(checked.accepted, true, 'degree ' + entry.degree + '\n' + checked.diagnostics.slice(-10000));
        }
    });

    it('checks every bounded model point, raw map input and complete H arrow in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_LONG_EXACT_MODEL !== '1'
    }, async () => {
        const { result } = await modelConsumer();
        let environment = result.source.environment;
        const terms: [string, KernelExpression, KernelExpression][] = [];
        result.points.forEach(({ observation }, i) => {
            const value = observation.realization;
            terms.push(['model_point_' + i, value.formalPoint, value.pointType], ['native_point_' + i, value.nativePoint, value.pointType]);
        });
        result.maps.forEach(({ observation }, i) => {
            const value = observation.realization;
            terms.push(['model_chain_' + i, value.chain.term, value.chain.type],
                ['model_arrow_' + i, value.formalArrow, value.observationType], ['native_arrow_' + i, value.nativeArrow, value.observationType]);
        });
        const assertions = terms.map(([name, term, type]) => {
            environment = environment.extend({ name, type, body: term, transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
            return { label: name, term: kernelFree(name, p), type, span: sourceSpan('generated/whole-model.ts', 1, 1) };
        });
        const serialized = serializeCoreLfKernelProbe({ environment, externalFreeReferences: bindings, assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;', imports) },
            { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics.slice(-5000));
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
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
