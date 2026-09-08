/** Constructive formal Freyd objects from explicitly adopted matrix computations. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS, AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN, affineFormalCommRingType, affineFormalRingElementType,
    algebraPolynomialIdeal, algebraPolynomialQuotientRing, algebraPresentedAlgebra,
    appendAlgebraFormalAssumption, binderMode, checkLambdapiProbe, coreProofPlanHole,
    createAlgebraFormalAssumptionSource, createAlgebraPolynomialFreydHomologyEngine,
    createCoreProofArtifactFingerprint, createCoreProofChecker, defineAffineFormalPolynomialReifier,
    delegateAlgebraFormalPresentationMorphismEquations, kernelFree, kernelUniverse, provenance,
    runAlgebraFormalWorkflow, serializeCoreLfKernelProbe, sourceSpan, trustAlgebraFormalWorkflow
} from '../src/v3_2';
import {
    FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, createFormalFreydSpineProofEnvironment, formalFreydSpineLanguage
} from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import {
    algebraFormalFreydChainPairDelegationBundle, algebraFormalFreydChainPairTerm
} from '../src/v3_2/algebra_formal_freyd_chain_pair';
import { algebraFormalFreydBoundedSpineTerm } from '../src/v3_2/algebra_formal_freyd_bounded_spine';
import { CoreLfScopedBuilder } from '../src/v3_2/lf_builder';
import { algebraFormalFreydLongExactDelegationBundle, trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { trustAlgebraFormalFreydLongExactSpine } from '../src/v3_2/algebra_formal_freyd_long_exact_spine';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';

const p = provenance('surface', 'formal Freyd spine consumer', sourceSpan('tests/formal-freyd-spine.ts', 1, 1, 1, 2));
const fingerprint = (goalId: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + goalId + '.ts', sha256: 'sha256:' + 'c'.repeat(64) },
    profileSha256: 'sha256:' + 'd'.repeat(64)
});

const fixture = (whole = false) => {
    const sequence = polynomialFreydHomologyFixture(whole ? 'two' : 'one');
    const selected = sequence.rows[0].triple.pair;
    const algebra = algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(sequence.ring, [])));
    const R = kernelFree('formal_spine_R', p);
    const x = kernelFree('formal_spine_x', p);
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra, formalRing: R, generatorTerms: [x],
        coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(key);
            if (!term) {
                term = kernelFree('formal_spine_c_' + [...key].map(c => c.codePointAt(0)!.toString(16)).join('_'), p);
                coefficients.set(key, term);
            }
            return term;
        }, status: 'trusted-computation'
    });
    const bundle = algebraFormalFreydChainPairDelegationBundle({ reifier, selected });
    const longBundle = whole ? algebraFormalFreydLongExactDelegationBundle({ reifier,
        selected: algebraPolynomialFreydLongExactSnakeReferences(algebraPolynomialFreydBoundedLongExactHomology(sequence)) }) : undefined;
    const elementType = affineFormalRingElementType(R);
    const environment = createFormalFreydSpineProofEnvironment([
        { name: R.name, type: affineFormalCommRingType() }, { name: x.name, type: elementType },
        ...[...coefficients.values()].map(term => ({ name: term.name, type: elementType }))
    ]);
    return { R, selected, reifier, bundle, longBundle, environment };
};

const construct = async () => {
    const value = fixture();
    let source = createAlgebraFormalAssumptionSource({
        moduleId: 'proof.cas.freyd-spine', sourceId: 'tests/freyd-spine.assumptions', baseEnvironment: value.environment
    });
    const batch = await delegateAlgebraFormalPresentationMorphismEquations({
        artifactId: 'freyd-spine-maps', reifier: value.reifier,
        morphisms: [value.selected.dNext, value.selected.d], agreements: [], chainSquares: [], source,
        fingerprint, decisionEvidence: id => 'Explicitly adopt map relation equation ' + id
    });
    source = batch.source;
    const target = value.bundle.realization.claimType;
    const goalId = 'freyd-spine-chain';
    const run = await runAlgebraFormalWorkflow({
        document: { moduleId: source.moduleId, declarationId: goalId, environment: source.environment,
            type: target, plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
            provenance: p, fingerprint: fingerprint(goalId) },
        goalId, adapter: value.bundle.adapter, realization: value.bundle.realization,
        engine: createAlgebraPolynomialFreydHomologyEngine(value.bundle.model)
    });
    const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: 'formal_spine_chain_law',
        decision: { kind: 'trust-exact-algebra-computation', evidence: 'Explicitly adopt the formal composite zero equation' } });
    source = appendAlgebraFormalAssumption({ source, adoption, classification: 'computed-equation' });
    const pair = algebraFormalFreydChainPairTerm(value.bundle.realization,
        source.entries[0].reference, source.entries[1].reference, source.entries[2].reference);
    const spine = algebraFormalFreydBoundedSpineTerm({ formalRing: value.R,
        presentations: value.bundle.realization.presentations, arrows: [pair.above, pair.below], laws: [pair.term] });
    return { ...value, source, run, pair, spine };
};

const constructLongExact = async () => {
    const value = fixture(true);
    const bundle = value.longBundle!;
    const source = createAlgebraFormalAssumptionSource({
        moduleId: 'proof.cas.freyd-long-exact-spine', sourceId: 'tests/freyd-long-exact-spine.assumptions', baseEnvironment: value.environment
    });
    const goalId = 'freyd-long-exact-spine';
    const target = bundle.realization.claimType;
    const run = await runAlgebraFormalWorkflow({ document: { moduleId: source.moduleId, declarationId: goalId,
        environment: source.environment, type: target, plan: coreProofPlanHole(goalId,
            { provenance: p, expectation: { contextDepth: 0, target } }), provenance: p, fingerprint: fingerprint(goalId) },
        goalId, adapter: bundle.adapter, realization: bundle.realization, engine: bundle.engine });
    const adopted = await trustAlgebraFormalFreydLongExact({ artifactId: 'freyd-long-exact-equations', bundle, run, source,
        fingerprint, decisionEvidence: id => 'Explicit whole-output equation adoption ' + id });
    const result = await trustAlgebraFormalFreydLongExactSpine({ artifactId: goalId, bundle, adopted,
        fingerprint, decisionEvidence: id => 'Explicit semantic-composition equation adoption ' + id });
    return { ...value, bundle, adopted, result };
};
let wholePromise: ReturnType<typeof constructLongExact> | undefined;
const wholeConsumer = () => wholePromise ??= constructLongExact();

describe('v3.2 formal Freyd-spine constructors', () => {
    it('checks all signature mirrors and constructs a nonsplit formal chain from semantic equations', async () => {
        const value = await construct();
        const checker = createCoreProofChecker(value.source.environment);
        checker.validateEnvironment();
        checker.check(checker.rootContext, value.bundle.realization.claimType, kernelUniverse(p));
        checker.check(checker.rootContext, value.pair.term, value.pair.type);
        checker.check(checker.rootContext, value.spine.term, value.spine.type);
        assert.deepEqual(value.spine.displayedToFormalDegree, [2, 1, 0]);
        assert.equal(value.run.result.interpretation.kind, 'claim');
        assert.equal(value.source.entries.length, 3);
        const wrong = algebraFormalFreydChainPairTerm(value.bundle.realization,
            value.source.entries[0].reference, value.source.entries[1].reference, value.source.entries[0].reference);
        assert.throws(() => checker.check(checker.rootContext, wrong.term, wrong.type));
        assert.throws(() => algebraFormalFreydBoundedSpineTerm({ formalRing: value.R,
            presentations: value.bundle.realization.presentations, arrows: [value.pair.above, value.pair.below], laws: [] }), /one law/u);
        const reversed = algebraFormalFreydBoundedSpineTerm({ formalRing: value.R,
            presentations: value.bundle.realization.presentations, arrows: [value.pair.below, value.pair.above], laws: [value.pair.term] });
        assert.throws(() => checker.check(checker.rootContext, reversed.term, reversed.type));
    });

    it('constructs the zero- and one-arrow recursion endpoints without inventing a chain law', async () => {
        const value = await construct();
        const checker = createCoreProofChecker(value.source.environment);
        const singleton = algebraFormalFreydBoundedSpineTerm({ formalRing: value.R,
            presentations: value.bundle.realization.presentations.slice(0, 1), arrows: [], laws: [] });
        const segment = algebraFormalFreydBoundedSpineTerm({ formalRing: value.R,
            presentations: value.bundle.realization.presentations.slice(0, 2), arrows: [value.pair.above], laws: [] });
        checker.check(checker.rootContext, singleton.term, singleton.type);
        checker.check(checker.rootContext, segment.term, segment.type);
        assert.equal(singleton.length, 0);
        assert.equal(segment.length, 1);
    });

    it('checks actual Lambdapi constructors and their ordinary projection computations', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_SPINE !== '1'
    }, async () => {
        const value = await construct();
        const b = new CoreLfScopedBuilder(p);
        const L = formalFreydSpineLanguage(b);
        let environment = value.source.environment;
        const add = (name: string, type: typeof value.spine.type, body: typeof value.spine.term) => {
            environment = environment.extend({ name, type, body, transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
        };
        const presentationType = b.lower(L.presentationType(b.embed(value.R)));
        value.bundle.realization.presentations.forEach((body, index) => add('formal_spine_P' + (2 - index), presentationType, body));
        const [P2, P1, P0] = value.bundle.realization.presentations.map(term => b.embed(term));
        add('formal_spine_above', b.lower(L.morphismType(b.embed(value.R), P2, P1)), value.pair.above);
        add('formal_spine_below', b.lower(L.morphismType(b.embed(value.R), P1, P0)), value.pair.below);
        add('formal_spine_pair', value.pair.type, value.pair.term);
        add('formal_spine_result', value.spine.type, value.spine.term);
        const serialized = serializeCoreLfKernelProbe({ environment,
            externalFreeReferences: { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS },
            assertions: [{ label: 'actual constructed bounded Freyd spine', term: kernelFree('formal_spine_result', p),
                type: value.spine.type, span: sourceSpan('generated/formal-freyd-spine.ts', 1, 1, 1, 2) }]
        });
        const source = serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;') +
            '\nassert ⊢ @comm_ring_freyd_bounded_complex_P0 formal_spine_R (succ zero) formal_spine_result ≡ formal_spine_P0;\n' +
            'assert ⊢ @comm_ring_freyd_bounded_complex_P1 formal_spine_R (succ zero) formal_spine_result ≡ formal_spine_P1;\n' +
            'assert ⊢ @comm_ring_freyd_bounded_complex_d1 formal_spine_R (succ zero) formal_spine_result ≡ formal_spine_below;\n' +
            'assert ⊢ @comm_ring_freyd_chain_tail_differential formal_spine_R zero formal_spine_P0 formal_spine_P1 formal_spine_below ' +
                '(@comm_ring_freyd_bounded_complex_tail formal_spine_R (succ zero) formal_spine_result) ≡ formal_spine_above;\n' +
            'assert ⊢ @comm_ring_freyd_chain_tail_law formal_spine_R zero formal_spine_P0 formal_spine_P1 formal_spine_below ' +
                '(@comm_ring_freyd_bounded_complex_tail formal_spine_R (succ zero) formal_spine_result) ≡ formal_spine_pair;\n';
        const checked = checkLambdapiProbe({ ...serialized, source }, { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });

    it('constructs the complete formal long-exact spine after one whole replay and explicit equation adoption', async () => {
        const { result, adopted } = await wholeConsumer();
        assert.equal(result.spine.length, 7);
        assert.equal(result.presentations.length, 8);
        assert.equal(result.pairTerms.length, 6);
        assert.equal(result.semanticBindings.length, 6);
        assert.deepEqual(result.spine.displayedToFormalDegree, [7, 6, 5, 4, 3, 2, 1, 0]);
        assert.equal(result.source.entries.length, adopted.source.entries.length + 6);
        const checker = createCoreProofChecker(result.source.environment);
        checker.validateEnvironment();
        checker.check(checker.rootContext, result.spine.term, result.spine.type);
        assert.equal(result.native.windows[1].connecting.homologyMap,
            adopted.adoption.result.computed.value.result.windows[1].connecting.homologyMap);
    });

    it('rejects foreign upstream bundles and missing adopted-map bindings without changing the source', async () => {
        const value = await wholeConsumer();
        const input = { artifactId: 'negative-formal-spine', bundle: value.bundle, adopted: value.adopted,
            fingerprint, decisionEvidence: () => 'Explicit test adoption' };
        await assert.rejects(() => trustAlgebraFormalFreydLongExactSpine({ ...input,
            bundle: { ...value.bundle, adapter: { ...value.bundle.adapter } } }), /another prepared whole bundle/u);
        const count = value.adopted.source.entries.length;
        await assert.rejects(() => trustAlgebraFormalFreydLongExactSpine({ ...input,
            adopted: { ...value.adopted, bindings: [] } }), /Missing adopted morphism equation/u);
        assert.equal(value.adopted.source.entries.length, count);
    });

    it('checks the complete constructed long-exact spine in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_SPINE !== '1'
    }, async () => {
        const value = await wholeConsumer();
        const environment = value.result.source.environment.extend({ name: 'formal_long_exact_spine',
            type: value.result.spine.type, body: value.result.spine.term, transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
        const serialized = serializeCoreLfKernelProbe({ environment,
            externalFreeReferences: { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS },
            assertions: [{ label: 'constructed complete nonsplit long-exact spine', term: kernelFree('formal_long_exact_spine', p),
                type: value.result.spine.type, span: sourceSpan('generated/formal-freyd-long-exact-spine.ts', 1, 1, 1, 2) }]
        });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;') }, { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});
