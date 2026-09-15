/** Direct native snake realization of 0 → R ─x→ R → R/(x) → 0. */
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { describe, it, mock } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialRing, algebraPolynomialVariable, algebraPolynomialText } from '../src/v3_2/algebra_polynomial';
import { algebraPolynomialFreeModule, algebraPolynomialSubmodule, algebraPolynomialModuleVector } from '../src/v3_2/algebra_polynomial_module';
import { algebraPresentedPolynomialModule, algebraPolynomialModuleMap } from '../src/v3_2/algebra_polynomial_presentation';
import { algebraPolynomialPresentationMorphism } from '../src/v3_2/algebra_polynomial_presentation_morphism';
import { algebraPolynomialPresentationMorphismIdentity, algebraPolynomialPresentationMorphismZero } from '../src/v3_2/algebra_polynomial_freyd_category';
import * as snake from '../src/v3_2/algebra_polynomial_freyd_snake';
import * as snakeExact from '../src/v3_2/algebra_polynomial_freyd_snake_exact';
import * as weakKernel from '../src/v3_2/algebra_polynomial_weak_kernel';
import * as weakPullback from '../src/v3_2/algebra_polynomial_weak_pullback';
import { defineAlgebraFormalFreydNativeRationalBackend } from '../src/v3_2/algebra_formal_freyd_native_rational_model_context';
import { prepareAlgebraFormalFreydNativeRationalSnakeContext } from '../src/v3_2/algebra_formal_freyd_native_snake_context';
import { prepareAlgebraFormalFreydNativeSnake } from '../src/v3_2/algebra_formal_freyd_native_snake_preparation';
import { algebraFormalFreydNativeSnakeObservationBundle } from '../src/v3_2/algebra_formal_freyd_native_snake_observation';
import { createFormalFreydNativeSnakeProofEnvironment, FORMAL_FREYD_NATIVE_SNAKE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_snake_signatures';
import { trustAlgebraFormalFreydNativeSnake } from '../src/v3_2/algebra_formal_freyd_native_snake_workflow';
import { constructAlgebraFormalFreydNativeSnakeExactness } from '../src/v3_2/algebra_formal_freyd_native_snake_exactness';
import { createFormalFreydNativeSnakeExactnessProofEnvironment, FORMAL_FREYD_NATIVE_SNAKE_EXACTNESS_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_snake_exactness_signatures';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { createCoreProofChecker } from '../src/v3_2/proof_checker';
import { kernelFree, kernelExpressionEquals, provenance, sourceSpan } from '../src/v3_2/kernel';
import { serializeCoreExpression } from '../src/v3_2/core_serialization';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';
import { FREYD_NATIVE_MODEL_PROBE_BINDINGS } from './v3_2_algebra_formal_freyd_native_model_fixtures';

const p = provenance('surface', 'native nonsplit snake', sourceSpan('tests/native-nonsplit-snake.ts', 1, 1));
const fingerprint = (id: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + id + '.ts', sha256: 'sha256:' + '3'.repeat(64) }, profileSha256: 'sha256:' + '4'.repeat(64)
});
const backend = defineAlgebraFormalFreydNativeRationalBackend({ id: 'tests.native-nonsplit-snake', revision: 'v1',
    coefficientContract: 'Interpret R and x in the original rational polynomial ring.',
    adjunctionModelContract: 'Supply coherent native P/Q; selected-arrow interpretation is separately explicit.',
    nativeNormalityContract: 'Supply whole Coim⇒Im normality of that native model.' });
const makeSelected = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex'), x = algebraPolynomialVariable(ring, 0);
    const ambient = algebraPolynomialFreeModule(ring, 1);
    const object = algebraPresentedPolynomialModule(algebraPolynomialSubmodule(ambient, []));
    const a = algebraPolynomialPresentationMorphism({ source: object, target: object,
        map: algebraPolynomialModuleMap(ambient, ambient, [algebraPolynomialModuleVector(ambient, [x])]) });
    return snakeExact.algebraPolynomialFreydSnakeExactSequence(snake.algebraPolynomialFreydSnakeTriple(a,
        algebraPolynomialPresentationMorphismIdentity(object), algebraPolynomialPresentationMorphismZero(object, object)));
};
let setup: ReturnType<typeof prepareAlgebraFormalFreydNativeRationalSnakeContext>;
const context = () => setup ??= prepareAlgebraFormalFreydNativeRationalSnakeContext({ backend, namePrefix: 'native_snake', selected: makeSelected() });
const input = () => { const v = context(); return { artifactId: 'native-snake-adoption', modelId: 'native-snake-model',
    observationId: 'nonsplit-x', formalModel: v.formalModel, normality: v.normality, prepared: v.prepared,
    source: v.initialSource, fingerprint, decisionEvidence: (id: string) => 'Explicit matrix equation or native complete-arrow interpretation: ' + id }; };
let pending: ReturnType<typeof trustAlgebraFormalFreydNativeSnake>;
const result = () => pending ??= trustAlgebraFormalFreydNativeSnake(input());
const probe = (environment: Parameters<typeof serializeCoreLfKernelProbe>[0]['environment'],
    assertions: Parameters<typeof serializeCoreLfKernelProbe>[0]['assertions'], exactness = false) => serializeCoreLfKernelProbe({ environment,
    externalFreeReferences: Object.fromEntries(Object.entries({ ...FREYD_NATIVE_MODEL_PROBE_BINDINGS,
        ...FORMAL_FREYD_NATIVE_SNAKE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_SNAKE_EXACTNESS_SIGNATURE_BINDINGS })
        .filter(([name]) => environment.lookup(name) !== undefined)), assertions
}).source.replace('require open emdash.emdash3_2;', [
    ...(exactness ? ['require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_point_exactness;'] : []),
    'require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_observations;',
    'require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_matrices;'
].join('\n')).replace(/^assert ⊢ ([A-Za-z_][A-Za-z0-9_]*) :/gmu, 'assert ⊢ @$1 :');

describe('v3.2 direct native nonsplit snake proof–CAS realization', () => {
    it('prepares the original six terms and nonzero connecting matrix without a LES input', () => {
        const v = context(), selected = v.selected;
        assert.equal(v.prepared.selected, selected);
        assert.equal(v.initialSource.entries.length, 0);
        assert.equal(v.suppliedInputs.length, 3);
        assert.equal(v.profile.requiresLongExactInput, false);
        assert.equal(v.profile.constructsModel, false);
        assert.equal(v.environment.lookup('bridge_FreydHomologyModel'), undefined);
        assert.equal(selected.objects.length, 6);
        assert.deepEqual(selected.arrows.map(a => a.map.columns.map(c => c.components.map(algebraPolynomialText))),
            [[], [], [['1']], [['1']], [['0']]]);
        assert.deepEqual(selected.objects.slice(2, 4).map(o => o.relations.generators.map(g => g.components.map(algebraPolynomialText))),
            [[['1*x']], [['1*x']]]);
        assert.ok(selected.pairs.every(p => p.chainAgreement.agrees));
        assert.equal(selected.assumesSplitEpimorphisms, false);
        assert.throws(() => prepareAlgebraFormalFreydNativeRationalSnakeContext({ backend: { ...backend }, namePrefix: 'forged', selected }), /issued/iu);
    });

    it('mirrors the seven active signatures for Lambdapi conformance', () => {
        const environment = createFormalFreydNativeSnakeProofEnvironment([]);
        const assertions = Object.keys(FORMAL_FREYD_NATIVE_SNAKE_SIGNATURE_BINDINGS).map(name => ({
            label: name, term: kernelFree(name, p), type: environment.lookup(name)!.type, span: p.span!
        }));
        const source = probe(environment, assertions);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_SIGNATURE_OUTPUT) writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_SIGNATURE_OUTPUT, source);
        assert.equal(assertions.length, 7);
    });

    it('realizes all five native arrows with automatic matrix prerequisites and no universal reselection', async t => {
        const v = context();
        const forbid = () => { throw new Error('Realization must retain the original snake and universal selections'); };
        const spies = [mock.method(snake, 'algebraPolynomialFreydSnakeConnecting', forbid),
            mock.method(snakeExact, 'algebraPolynomialFreydSnakeExactSequenceFromConnecting', forbid),
            mock.method(weakKernel, 'algebraPolynomialModuleMapWeakKernel', forbid),
            mock.method(weakPullback, 'algebraPolynomialModuleMapWeakPullback', forbid)];
        try {
            const r = await result();
            assert.equal(r.observations.length, 5);
            assert.equal(r.prepared.selected, v.selected);
            assert.equal(r.counts.snakeReplays, 0);
            assert.equal(r.counts.universalReselections, 0);
            assert.equal(r.counts.interpretationClaims, 5);
            assert.equal(r.provesDisplayedCasExactness, false);
            const checker = createCoreProofChecker(r.source.environment);
            r.observations.forEach((o, i) => {
                const value = o.observation.realization;
                assert.equal(value.prepared.selected.arrows[i], v.selected.arrows[i]);
                checker.check(checker.rootContext, value.formalArrow, value.observationType);
                checker.check(checker.rootContext, value.nativeArrow, value.observationType);
                checker.check(checker.rootContext, o.proof, value.claimType);
                assert.match(serializeCoreExpression(value.formalArrow), /bridge_freyd_raw_native_snake_/u);
            });
            assert.ok(r.source.entries.filter(e => e.classification === 'trusted-presentation-semantics')
                .every(e => serializeCoreExpression(e.declaration.type).includes('bridge_FreydArrowObservation')));
            spies.forEach(s => assert.equal(s.mock.callCount(), 0));
            t.diagnostic(JSON.stringify(r.counts));
        } finally { spies.forEach(s => s.mock.restore()); }
    });

    it('reuses all fourteen requests and rejects changed models, zero data and preparations', async () => {
        const r = await result(), v = context();
        const again = await trustAlgebraFormalFreydNativeSnake({ ...input(), source: r.source, artifactId: 'native-snake-reuse',
            decisionEvidence: () => { assert.fail('Every request must reuse its existing evidence'); } });
        assert.equal(again.source, r.source);
        assert.equal(again.counts.reused, 14);
        assert.equal(again.counts.newAssumptions, 0);
        again.observations.forEach((o, i) => assert.ok(kernelExpressionEquals(o.proof, r.observations[i].proof)));
        await assert.rejects(trustAlgebraFormalFreydNativeSnake({ ...input(), prepared: { ...v.prepared } }), /issued/iu);
        await assert.rejects(trustAlgebraFormalFreydNativeSnake({ ...input(), normality: v.formalModel,
            decisionEvidence: () => { assert.fail('Reject invalid normality before adopting anything'); } }));
        assert.throws(() => prepareAlgebraFormalFreydNativeSnake({ reifier: v.reifier,
            selected: { ...v.selected, arrows: [v.selected.arrows[1], v.selected.arrows[0],
                v.selected.arrows[2], v.selected.arrows[3], v.selected.arrows[4]] } }), /owners/iu);
        const first = r.observations[0];
        assert.throws(() => algebraFormalFreydNativeSnakeObservationBundle({ ...first.observationInput, zeroLaw: r.inputLaws[0] }));
        assert.throws(() => first.observation.adapter.normalizeRealization({ ...first.observation.realization }, 'test'), /Foreign/iu);
    });

    it('emits the five native arrows, original CAS arrows and explicit interpretations', async () => {
        const r = await result();
        const assertions = r.observations.flatMap(o => {
            const v = o.observation.realization;
            return [{ label: o.role + ' native', term: v.formalArrow, type: v.observationType, span: p.span! },
                { label: o.role + ' CAS', term: v.nativeArrow, type: v.observationType, span: p.span! },
                { label: o.role + ' interpretation', term: o.proof, type: v.claimType, span: p.span! }];
        });
        const source = probe(r.source.environment, assertions);
        assert.doesNotMatch(source, /FreydHomologyModel|freyd_homology_model|abelian_snake/u);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_OUTPUT) writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_OUTPUT, source);
        assert.equal(assertions.length, 15);
    });

    it('constructs all four original whole exactness proofs and point witnesses without new assumptions', async () => {
        const r = await result(), before = r.source.entries.length;
        const exact = constructAlgebraFormalFreydNativeSnakeExactness(r);
        assert.equal(exact.source, r.source);
        assert.equal(exact.prepared, r.prepared);
        assert.equal(exact.source.entries.length, before);
        assert.equal(exact.assumptionsAdded, 0);
        assert.equal(exact.trustDecisions, 0);
        assert.equal(exact.wholeCategoricalEvidence, true);
        assert.equal(exact.provesDisplayedCasExactness, false);
        assert.deepEqual(exact.evidence.map(e => e.position), ['first', 'second', 'third', 'fourth']);
        for (const item of exact.evidence) {
            assert.match(serializeCoreExpression(item.term), new RegExp('bridge_freyd_native_snake_' + item.position + '_exact_evidence', 'u'));
            assert.match(serializeCoreExpression(item.data), new RegExp('bridge_freyd_native_snake_' + item.position + '_point_exact_data', 'u'));
        }
        assert.throws(() => constructAlgebraFormalFreydNativeSnakeExactness({ ...r, observations: r.observations.slice(0, 4) }), /complete/iu);
        const observations = r.observations.map((o, i) => i === 0 ? { ...o,
            observationInput: { ...o.observationInput, normality: context().formalModel } } : o);
        assert.throws(() => constructAlgebraFormalFreydNativeSnakeExactness({ ...r, observations }), /one original/iu);
    });

    it('emits the actual native exactness constructors, point comparisons and evidence for Lambdapi', async () => {
        const exact = constructAlgebraFormalFreydNativeSnakeExactness(await result());
        const environment = createFormalFreydNativeSnakeExactnessProofEnvironment([]);
        const signatures = Object.keys(FORMAL_FREYD_NATIVE_SNAKE_EXACTNESS_SIGNATURE_BINDINGS).map(name => ({
            label: name, term: kernelFree(name, p), type: environment.lookup(name)!.type, span: p.span!
        }));
        const assertions = exact.evidence.flatMap(e => [
            { label: e.position + ' whole proof', term: e.term, type: e.type, span: p.span! },
            { label: e.position + ' point data', term: e.data, type: e.dataType, span: p.span! },
            { label: e.position + ' comparison', term: e.arrow, type: e.arrowType, span: p.span! },
            { label: e.position + ' fixed-arrow evidence', term: e.evidence, type: e.evidenceType, span: p.span! }
        ]);
        const source = probe(exact.source.environment, assertions, true);
        assert.doesNotMatch(source, /symbol bridge_freyd_native_snake|symbol bridge_FreydNativeSnake/u);
        if (process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_EXACT_SIGNATURE_OUTPUT) writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_EXACT_SIGNATURE_OUTPUT, probe(environment, signatures, true));
        if (process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_EXACT_OUTPUT) writeFileSync(process.env.EMDASH_PROOF_CAS_NATIVE_SNAKE_EXACT_OUTPUT, source);
        assert.equal(signatures.length, 16);
        assert.equal(assertions.length, 16);
    });
});
