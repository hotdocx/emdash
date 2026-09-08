/** Existing formal boundary-epicity witnesses from explicitly adopted native blocks. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS, AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN, affineFormalCommRingType, affineFormalRingElementType, algebraPolynomialAdd,
    algebraPolynomialFreeModule, algebraPolynomialFreydChainPair, algebraPolynomialFreydCokernel,
    algebraPolynomialFreydExactnessAt, algebraPolynomialFreydHomologyAt, algebraPolynomialIdeal,
    algebraPolynomialModuleMap, algebraPolynomialModuleMapIsZero, algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector, algebraPolynomialOne, algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismZero, algebraPolynomialQuotientRing, algebraPolynomialRing,
    algebraPolynomialSubmodule, algebraPolynomialVariable, algebraPresentedAlgebra, algebraPresentedPolynomialModule,
    appendAlgebraFormalAssumption, binderMode, checkLambdapiProbe, coreProofPlanHole,
    createAlgebraFormalAssumptionSource, createAlgebraPolynomialFreydAbelianEngine,
    createCoreProofArtifactFingerprint, createCoreProofChecker, defineAffineFormalPolynomialReifier,
    delegateAlgebraFormalPresentationMorphismEquations, kernelExpressionEquals, kernelFree, kernelUniverse,
    provenance, runAlgebraFormalWorkflow, serializeCoreLfKernelProbe, sourceSpan, trustAlgebraFormalWorkflow
} from '../src/v3_2';
import { CoreLfScopedBuilder } from '../src/v3_2/lf_builder';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, formalFreydSpineLanguage } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { algebraFormalFreydMorphismTerm } from '../src/v3_2/algebra_formal_freyd_chain_pair';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS, createFormalFreydEpimorphismProofEnvironment } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import {
    ALGEBRA_FORMAL_FREYD_EPIMORPHISM_PROFILE, algebraFormalFreydEpimorphismBlockDelegationBundle,
    algebraFormalFreydEpimorphismTerm, defineAlgebraFormalFreydEpimorphismBlockRealization
} from '../src/v3_2/algebra_formal_freyd_epimorphism';

const p = provenance('surface', 'formal Freyd boundary-epicity consumer', sourceSpan('tests/formal-freyd-epimorphism.ts', 1, 1, 1, 2));
const fingerprint = (goalId: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + goalId + '.ts', sha256: 'sha256:' + 'e'.repeat(64) },
    profileSha256: 'sha256:' + 'f'.repeat(64)
});

const fixture = (nontrivialBlocks = false) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const free = algebraPolynomialFreeModule(ring, 1);
    const object = algebraPresentedPolynomialModule(algebraPolynomialSubmodule(free, []));
    const multiply = algebraPolynomialPresentationMorphism({ source: object, target: object,
        map: algebraPolynomialModuleMap(free, free, [algebraPolynomialModuleVector(free, [x])]) });
    const quotient = algebraPolynomialFreydCokernel(multiply);
    const zeroObject = algebraPresentedPolynomialModule(algebraPolynomialSubmodule(algebraPolynomialFreeModule(ring, 0), []));
    const incoming = nontrivialBlocks ? algebraPolynomialPresentationMorphism({ source: object, target: quotient.object,
        map: algebraPolynomialModuleMap(free, free, [algebraPolynomialModuleVector(free, [algebraPolynomialAdd(x, algebraPolynomialOne(ring))])]) }) : multiply;
    const outgoing = nontrivialBlocks ? algebraPolynomialPresentationMorphismZero(quotient.object, zeroObject) : quotient.projection;
    const homology = algebraPolynomialFreydHomologyAt(algebraPolynomialFreydChainPair(incoming, outgoing));
    const exactness = algebraPolynomialFreydExactnessAt(homology);
    assert.equal(exactness.exact, true);
    assert.ok(exactness.epimorphism);
    const selected = exactness.epimorphism;
    assert.equal(selected.morphism, homology.boundaryMorphism);
    const algebra = algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, [])));
    const R = kernelFree('formal_epi_R', p);
    const formalX = kernelFree('formal_epi_x', p);
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({ algebra, formalRing: R, generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(key);
            if (!term) {
                term = kernelFree('formal_epi_c_' + [...key].map(c => c.codePointAt(0)!.toString(16)).join('_'), p);
                coefficients.set(key, term);
            }
            return term;
        }, status: 'trusted-computation' });
    const bundle = algebraFormalFreydEpimorphismBlockDelegationBundle({ reifier, selected });
    const elementType = affineFormalRingElementType(R);
    const environment = createFormalFreydEpimorphismProofEnvironment([
        { name: R.name, type: affineFormalCommRingType() }, { name: formalX.name, type: elementType },
        ...[...coefficients.values()].map(term => ({ name: term.name, type: elementType }))
    ]);
    return { R, ring, reifier, homology, exactness, selected, bundle, environment };
};

const construct = async (nontrivialBlocks = false) => {
    const value = fixture(nontrivialBlocks);
    const original = createAlgebraFormalAssumptionSource({ moduleId: 'proof.cas.freyd-epimorphism',
        sourceId: 'tests/freyd-epimorphism.assumptions', baseEnvironment: value.environment });
    const batch = await delegateAlgebraFormalPresentationMorphismEquations({ artifactId: 'freyd-epimorphism-map',
        reifier: value.reifier, morphisms: [value.selected.morphism], agreements: [], chainSquares: [], source: original,
        fingerprint, decisionEvidence: id => 'Explicitly adopt the boundary relation equation ' + id });
    const target = value.bundle.realization.claimType;
    const goalId = 'freyd-epimorphism-block';
    const input = { document: { moduleId: batch.source.moduleId, declarationId: goalId, environment: batch.source.environment,
        type: target, plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
        provenance: p, fingerprint: fingerprint(goalId) }, goalId,
        adapter: value.bundle.adapter, realization: value.bundle.realization,
        engine: createAlgebraPolynomialFreydAbelianEngine(value.bundle.model) };
    const run = await runAlgebraFormalWorkflow(input);
    assert.equal(original.entries.length, 0);
    assert.equal(batch.source.entries.length, 1);
    const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: 'formal_epi_block_law',
        decision: { kind: 'trust-exact-algebra-computation', evidence: 'Explicitly adopt this selected boundary block identity' } });
    const source = appendAlgebraFormalAssumption({ source: batch.source, adoption, classification: 'computed-equation' });
    const result = algebraFormalFreydEpimorphismTerm(value.bundle.realization, source.entries[0].reference, source.entries[1].reference);
    return { ...value, original, source, run, input, result };
};

describe('v3.2 formal Freyd boundary epicity', () => {
    it('constructs the existing witness for an actual nonzero native homology boundary', async () => {
        const value = await construct();
        const checker = createCoreProofChecker(value.source.environment);
        checker.validateEnvironment();
        checker.check(checker.rootContext, value.bundle.realization.claimType, kernelUniverse(p));
        checker.check(checker.rootContext, value.result.term, value.result.type);
        assert.equal(value.run.result.interpretation.kind, 'claim');
        assert.equal(value.source.entries.length, 2);
        assert.equal(value.result.selected.morphism, value.homology.boundaryMorphism);
        assert.equal(algebraPolynomialModuleMapIsZero(value.homology.boundaryMorphism.map), false);
        assert.ok(kernelExpressionEquals(value.result.morphism,
            algebraFormalFreydMorphismTerm(value.bundle.realization.morphism, value.source.entries[0].reference)));
        assert.deepEqual(value.result.presentations, value.bundle.realization.presentations);
        assert.equal(ALGEBRA_FORMAL_FREYD_EPIMORPHISM_PROFILE.claimsChainExactness, false);
        assert.equal(ALGEBRA_FORMAL_FREYD_EPIMORPHISM_PROFILE.suppliesWeakKernelCapability, false);
    });

    it('retains both nonzero Bezout blocks for the x+1 boundary over R/(x)', async () => {
        const value = await construct(true);
        assert.equal(algebraPolynomialModuleMapIsZero(value.selected.targetRelationComponent), false);
        assert.equal(algebraPolynomialModuleMapIsZero(value.selected.sourceGeneratorComponent), false);
        const checker = createCoreProofChecker(value.source.environment);
        checker.check(checker.rootContext, value.result.term, value.result.type);
        assert.equal(value.result.selected.morphism, value.homology.boundaryMorphism);
        assert.equal(defineAlgebraFormalFreydEpimorphismBlockRealization(value.bundle.realization).formalData, value.bundle.realization.formalData);
    });

    it('rejects changed blocks, stale reification, foreign reifiers, and broken selected sharing', () => {
        const value = fixture(true);
        const { selected, bundle } = value;
        const badU = algebraPolynomialModuleMapZero(selected.targetRelationComponent.source, selected.targetRelationComponent.target);
        assert.throws(() => defineAlgebraFormalFreydEpimorphismBlockRealization({ reifier: value.reifier,
            selected: { ...selected, targetRelationComponent: badU } }), /blocks differ/u);
        assert.throws(() => defineAlgebraFormalFreydEpimorphismBlockRealization({ reifier: value.reifier,
            selected: { ...selected, cokernel: { ...selected.cokernel, morphism: { ...selected.morphism } } } }), /original morphism/u);
        assert.throws(() => bundle.adapter.normalizeRealization({ ...bundle.realization, formalData: 'stale' }, 'test'), /drifted/u);
        assert.throws(() => bundle.adapter.normalizeRealization({ ...bundle.realization, claimType: bundle.realization.morphism.claimType }, 'test'), /drifted/u);
        assert.throws(() => bundle.adapter.normalizeRealization({ ...bundle.realization, reifier: { ...value.reifier } }, 'test'), /prepared/u);
        assert.throws(() => algebraFormalFreydEpimorphismTerm({ ...bundle.realization, formalData: 'stale' }, kernelFree('lawF', p), kernelFree('lawE', p)), /drifted/u);
    });

    it('rejects a wrong adopted law, altered endpoints, and a different proof goal', async () => {
        const value = await construct(true);
        const checker = createCoreProofChecker(value.source.environment);
        const wrong = algebraFormalFreydEpimorphismTerm(value.bundle.realization, value.source.entries[0].reference, value.source.entries[0].reference);
        assert.throws(() => checker.check(checker.rootContext, wrong.term, wrong.type));
        const b = new CoreLfScopedBuilder(p);
        const L = formalFreydSpineLanguage(b);
        const [P, Q] = value.result.presentations.map(term => b.embed(term));
        const wrongType = b.lower(L.tau(L.call('bridge_CommRingFreydEpimorphismWitness', [b.embed(value.R), Q, P, b.embed(value.result.morphism)], 3)));
        assert.throws(() => checker.check(checker.rootContext, value.result.term, wrongType));
        const target = value.bundle.realization.morphism.claimType;
        await assert.rejects(() => runAlgebraFormalWorkflow({ ...value.input, document: { ...value.input.document, type: target,
            plan: coreProofPlanHole(value.input.goalId, { provenance: p, expectation: { contextDepth: 0, target } }) } }), /Adapter could not acquire/u);
        assert.equal(value.original.entries.length, 0);
    });

    it('checks both constructed native boundary witnesses and retained blocks in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_EPIMORPHISM !== '1'
    }, async () => {
        for (const nontrivial of [false, true]) {
            const value = await construct(nontrivial);
            const b = new CoreLfScopedBuilder(p);
            const L = formalFreydSpineLanguage(b);
            const R = b.embed(value.R);
            let environment = value.source.environment;
            const add = (name: string, type: typeof value.result.type, body: typeof value.result.term) => {
                environment = environment.extend({ name, type, body, transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
            };
            value.result.presentations.forEach((body, index) => add('formal_epi_P' + index, b.lower(L.presentationType(R)), body));
            const [P, Q] = value.result.presentations.map(term => b.embed(term));
            const [pg, , qg, qr] = value.bundle.realization.ranks.map(L.nat);
            add('formal_epi_boundary', b.lower(L.morphismType(R, P, Q)), value.result.morphism);
            add('formal_epi_U', b.lower(L.tau(L.matrix(R, qr, qg))), value.bundle.realization.U);
            add('formal_epi_V', b.lower(L.tau(L.matrix(R, pg, qg))), value.bundle.realization.V);
            add('formal_epi_witness', value.result.type, value.result.term);
            const serialized = serializeCoreLfKernelProbe({ environment,
                externalFreeReferences: { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                    ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
                    ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS },
                assertions: [{ label: 'constructed actual native boundary epicity', term: kernelFree('formal_epi_witness', p),
                    type: value.result.type, span: sourceSpan('generated/formal-freyd-epimorphism.ts', 1, 1, 1, 2) }]
            });
            const nat = (n: number) => '(succ '.repeat(n) + 'zero' + ')'.repeat(n);
            const [pn, , qn, qrn] = value.bundle.realization.ranks;
            const source = serialized.source.replace('require open emdash.emdash3_2;',
                'require open emdash.emdash3_2_commutative_algebra_freyd_explicit_epimorphisms;') +
                '\nassert ⊢ @comm_ring_freyd_epimorphism_witness formal_epi_R formal_epi_P0 formal_epi_P1 formal_epi_boundary formal_epi_witness' +
                ' ≡ @comm_ring_matrix_vertical formal_epi_R ' + [qrn, pn, qn].map(nat).join(' ') + ' formal_epi_U formal_epi_V;\n';
            const checked = checkLambdapiProbe({ ...serialized, source }, { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
            assert.equal(checked.timedOut, false, checked.diagnostics);
            assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
        }
    });
});
