/** Direct whole P/Q contracts share CAS preparations, not legacy model inputs. */
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { describe, it, mock } from 'node:test';
import { INTEGER_DOMAIN, RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialConstant } from '../src/v3_2/algebra_polynomial';
import { affineFormalCommRingType, affineFormalRingElementType } from '../src/v3_2/algebra_formal_conformance';
import { kernelFree, kernelExpressionEquals, binderMode, provenance, sourceSpan } from '../src/v3_2/kernel';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { runAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';
import { trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { constructAlgebraFormalFreydRawWitnesses, FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_raw_witnesses';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { defineAlgebraFormalFreydNativeRationalBackend, prepareAlgebraFormalFreydNativeRationalModelContext } from '../src/v3_2/algebra_formal_freyd_native_rational_model_context';
import { algebraFormalFreydNativeModelType, algebraFormalFreydNativeModelNormalityType,
    FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_model_signatures';
import { defineAlgebraFormalFreydRationalBackend, prepareAlgebraFormalFreydRationalModelContext } from '../src/v3_2/algebra_formal_freyd_rational_model_context';
import { algebraFormalFreydModelType } from '../src/v3_2/algebra_formal_freyd_model_signatures';
import { algebraFormalFreydModelNormalityType } from '../src/v3_2/algebra_formal_freyd_model_connecting_signatures';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';
import { AFFINE_FORMAL_FINITE_MODULE_BINDINGS } from '../src/v3_2/algebra_formal_finite_module';
import { AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS } from '../src/v3_2/algebra_formal_localization_signatures';
import { AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS } from '../src/v3_2/algebra_formal_presentation_morphism';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_kernel_choice_provider_signatures';
import { FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_actual_homology_signatures';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeConnecting from '../src/v3_2/algebra_polynomial_freyd_homology_connecting';
import * as nativeWindow from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';

const p = provenance('surface', 'native rational model context', sourceSpan('tests/native-model-context.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '1'.repeat(64) }, profileSha256: 'sha256:' + '2'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({
    id: 'tests.native-rational-freyd', revision: 'v1',
    coefficientContract: 'Interpret the formal ring and coefficients in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native whole P/Q over that Freyd category; no closed model is derived here.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality for that same native model.'
});
const legacyBackend = defineAlgebraFormalFreydRationalBackend({ ...backend,
    modelContract: 'Supply the separate legacy selected-dictionary model.' });
const select = () => algebraPolynomialFreydLongExactSnakeReferences(
    nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(polynomialFreydHomologyFixture('two')));
let selected: ReturnType<typeof select>;
const selection = () => selected ??= select();
let prepared: ReturnType<typeof prepareAlgebraFormalFreydNativeRationalModelContext>;
const context = () => prepared ??= prepareAlgebraFormalFreydNativeRationalModelContext({
    backend, selected: selection(), namePrefix: 'native_context'
});

describe('v3.2 direct native Freyd model context', () => {
    it('prepares native inputs without model adaptation, CAS recomputation or adoption', () => {
        const selected = selection();
        const forbid = () => { throw new Error('Preparation must retain the original CAS selections'); };
        const spies = [mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbid),
            mock.method(nativeConnecting, 'algebraPolynomialFreydHomologyConnecting', forbid),
            mock.method(nativeWindow, 'algebraPolynomialFreydHomologyWindow', forbid),
            mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            // This prepared engine captures the mock implementations: discard it.
            const v = prepareAlgebraFormalFreydNativeRationalModelContext({ backend, selected, namePrefix: 'native_guarded' });
            assert.equal(v.selected, selected);
            assert.equal(v.bundle.selected, selected);
            assert.ok([v.preparedHomology, v.preparedRaw, v.preparedModel].every(x => x.bundle === v.bundle));
            assert.equal(v.preparedModel.inventory.points.length, 18);
            assert.equal(v.preparedModel.inventory.maps.length, 8);
            assert.equal(v.preparedModel.inventory.connectings.length, 3);
            assert.equal(v.initialSource.entries.length, 0);
            assert.equal(v.initialSource.environment, v.environment);
            assert.deepEqual(v.suppliedInputs.map(x => x.role),
                ['coefficient-interpretation', 'whole-adjunction-model', 'native-whole-normality']);
            assert.ok(v.suppliedInputs.every(x => x.classification === 'supplied-input'));
            assert.ok(Object.isFrozen(v) && Object.isFrozen(v.coefficients) && Object.isFrozen(v.backend));
            assert.equal(v.environment.lookup('bridge_FreydHomologyModel'), undefined);
            assert.equal(v.environment.lookup('bridge_freyd_homology_model_object'), undefined);
            assert.equal(v.environment.lookup('bridge_FreydHomologyModelNativeNormality'), undefined);
            const checker = createCoreProofChecker(v.environment);
            checker.validateEnvironment();
            checker.check(checker.rootContext, v.formalModel, algebraFormalFreydNativeModelType(v.formalRing));
            checker.check(checker.rootContext, v.normality, algebraFormalFreydNativeModelNormalityType(v.formalRing, v.formalModel));
            for (const term of [...v.generatorTerms, ...v.coefficients.map(c => c.term)]) {
                checker.check(checker.rootContext, term, affineFormalRingElementType(v.formalRing));
            }
            spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        } finally { spies.forEach(spy => spy.mock.restore()); }
    });

    it('preserves CAS inventories while separating native and legacy model types', () => {
        const v = context();
        const old = prepareAlgebraFormalFreydRationalModelContext({ backend: legacyBackend,
            selected: v.selected, namePrefix: 'native_context' });
        assert.equal(v.bundle.equationsData, old.bundle.equationsData);
        assert.equal(v.preparedHomology.entriesData, old.preparedHomology.entriesData);
        assert.equal(v.preparedModel.inventory.data, old.preparedModel.inventory.data);
        assert.deepEqual(v.coefficients.map(c => [c.value, c.term.name]), old.coefficients.map(c => [c.value, c.term.name]));
        let environment = v.environment;
        for (const name of ['bridge_FreydHomologyModel', 'bridge_FreydHomologyModelNativeNormality']) {
            environment = environment.extend(old.environment.lookup(name)!);
        }
        const oldM = kernelFree('legacy_model', p), oldN = kernelFree('legacy_normality', p);
        const otherM = kernelFree('other_native_model', p), otherR = kernelFree('other_ring', p);
        for (const [term, type] of [
            [oldM, algebraFormalFreydModelType(v.formalRing)],
            [oldN, algebraFormalFreydModelNormalityType(v.formalRing, oldM)],
            [otherM, algebraFormalFreydNativeModelType(v.formalRing)], [otherR, affineFormalCommRingType()]
        ] as const) environment = environment.extend({ name: term.name, type, mode: binderMode('explicit', 'functorial'), provenance: p });
        const checker = createCoreProofChecker(environment);
        checker.validateEnvironment();
        assert.throws(() => checker.check(checker.rootContext, oldM, algebraFormalFreydNativeModelType(v.formalRing)));
        assert.throws(() => checker.check(checker.rootContext, oldN, algebraFormalFreydNativeModelNormalityType(v.formalRing, v.formalModel)));
        assert.throws(() => checker.check(checker.rootContext, v.normality, algebraFormalFreydNativeModelNormalityType(v.formalRing, otherM)));
        assert.throws(() => checker.check(checker.rootContext, v.formalModel, algebraFormalFreydNativeModelType(otherR)));
    });

    it('rejects legacy registrations, missing native contracts and unprepared coefficients', () => {
        const v = context(), input = { backend, selected: v.selected, namePrefix: 'native_valid' };
        assert.throws(() => prepareAlgebraFormalFreydNativeRationalModelContext({ ...input, backend: { ...backend } }), /issued/iu);
        assert.throws(() => prepareAlgebraFormalFreydNativeRationalModelContext({ ...input,
            backend: legacyBackend as unknown as typeof backend }), /issued/iu);
        assert.throws(() => prepareAlgebraFormalFreydRationalModelContext({ ...input,
            backend: backend as unknown as typeof legacyBackend }), /issued/iu);
        assert.throws(() => defineAlgebraFormalFreydNativeRationalBackend(legacyBackend as unknown as typeof backend), /adjunction model contract/iu);
        for (const key of ['coefficientContract', 'adjunctionModelContract', 'nativeNormalityContract'] as const) {
            assert.throws(() => defineAlgebraFormalFreydNativeRationalBackend({ ...backend, [key]: '' }), /contract/iu);
        }
        for (const namePrefix of ['', 'a/b', 'a-b', '1bad', 'a'.repeat(129)]) {
            assert.throws(() => prepareAlgebraFormalFreydNativeRationalModelContext({ ...input, namePrefix }), /identifier/iu);
        }
        const wrong = { ...v.selected, result: { ...v.selected.result, sequence: { ...v.selected.result.sequence,
            ring: { ...v.selected.result.sequence.ring, coefficientDomain: INTEGER_DOMAIN } } } };
        assert.throws(() => prepareAlgebraFormalFreydNativeRationalModelContext({ ...input,
            selected: wrong as unknown as typeof v.selected }), /rational polynomial/iu);
        assert.throws(() => v.reifier.reifyPolynomial(algebraPolynomialConstant(v.selected.result.sequence.ring, '987654321')), /not included/iu);
        const known = RATIONAL_DOMAIN.normalize(v.coefficients[0].value);
        assert.ok(kernelExpressionEquals(v.reifier.reifyPolynomial(algebraPolynomialConstant(v.selected.result.sequence.ring, known)),
            v.reifier.reifyPolynomial(algebraPolynomialConstant(v.selected.result.sequence.ring,
                { numerator: known.numerator * 2n, denominator: known.denominator * 2n }))));
        assert.equal(v.initialSource.entries.length, 0);
    });

    it('emits the actual native model input owners for Lambdapi conformance', () => {
        const v = context();
        const terms = [v.formalRing, ...v.generatorTerms, ...v.coefficients.map(c => c.term), v.formalModel, v.normality];
        const probe = serializeCoreLfKernelProbe({ environment: v.environment,
            externalFreeReferences: { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
                ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS },
            assertions: terms.map(term => ({ label: term.name, term, type: v.environment.lookup(term.name)!.type, span: p.span! }))
        });
        const source = probe.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;\n' +
            'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;\n' +
            'require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;');
        assert.match(source, /FreydAdjunctionModel/u);
        assert.match(source, /FreydAdjunctionModelNormality/u);
        assert.doesNotMatch(source, /FreydHomologyModel|freyd_homology_model/u);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_CONTEXT_PROBE_OUTPUT) {
            writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_CONTEXT_PROBE_OUTPUT, source);
        }
    });

    it('replays and adopts the selected CAS equations directly in the native context', async t => {
        const v = context(), goalId = 'native-context-replay', target = v.bundle.realization.claimType;
        const run = await runAlgebraFormalWorkflow({ document: {
            moduleId: v.initialSource.moduleId, declarationId: goalId, environment: v.environment, type: target,
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
            provenance: p, fingerprint: fingerprint(goalId)
        }, goalId, adapter: v.bundle.adapter, realization: v.bundle.realization, engine: v.bundle.engine });
        const adopted = await trustAlgebraFormalFreydLongExact({ artifactId: 'native-context-equations', bundle: v.bundle,
            run, source: v.initialSource, fingerprint, decisionEvidence: id => 'Explicitly adopt original CAS equation ' + id });
        assert.equal(adopted.adoption.execution.state.status, 'complete');
        assert.equal(adopted.source.entries.length, v.bundle.equations.claims.length);
        assert.equal(adopted.bindings.flatMap(x => x.labels).length, v.bundle.equations.entries.length);
        assert.ok(adopted.source.entries.every(x => x.classification === 'computed-equation'));
        assert.equal(adopted.source.environment.lookup('bridge_FreydHomologyModel'), undefined);
        const raw = constructAlgebraFormalFreydRawWitnesses({ prepared: v.preparedRaw, adopted, source: adopted.source });
        assert.equal(raw.native, adopted.adoption.result.computed.value);
        assert.equal(raw.entries.length, v.bundle.equations.entries.length);
        assert.equal(raw.assumptionsAdded, 0);
        assert.equal(v.initialSource.entries.length, 0);
        t.diagnostic(adopted.source.entries.length + ' computed equations; ' + adopted.bindings.flatMap(x => x.labels).length +
            ' original labels; no model realization or output exactness assumed');
    });
});
