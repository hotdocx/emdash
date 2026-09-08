/** Whole nonsplit native boundaries become existing formal epimorphism witnesses. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it, mock } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS, AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    RATIONAL_DOMAIN, affineFormalCommRingType, affineFormalRingElementType,
    algebraPolynomialIdeal, algebraPolynomialQuotientRing, algebraPresentedAlgebra, binderMode,
    checkLambdapiProbe, coreProofPlanHole, createAlgebraFormalAssumptionSource,
    createCoreProofArtifactFingerprint, createCoreProofChecker, defineAffineFormalPolynomialReifier,
    kernelExpressionEquals, kernelFree, provenance, runAlgebraFormalWorkflow, serializeCoreLfKernelProbe, sourceSpan
} from '../src/v3_2';
import * as nativeHomology from '../src/v3_2/algebra_polynomial_freyd_homology';
import * as nativeWindow from '../src/v3_2/algebra_polynomial_freyd_homology_window';
import * as nativeLongExact from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import { polynomialFreydHomologyFixture } from './v3_2_algebra_polynomial_freyd_homology_fixtures';
import { algebraPolynomialFreydLongExactSnakeReferences } from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import { algebraFormalFreydLongExactDelegationBundle, trustAlgebraFormalFreydLongExact } from '../src/v3_2/algebra_formal_freyd_long_exact';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS, createFormalFreydEpimorphismProofEnvironment } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import {
    ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE, prepareAlgebraFormalFreydLongExactEpimorphisms,
    trustAlgebraFormalFreydLongExactEpimorphisms
} from '../src/v3_2/algebra_formal_freyd_long_exact_epimorphisms';
import { algebraFormalFreydMorphismTerm } from '../src/v3_2/algebra_formal_freyd_chain_pair';

const p = provenance('surface', 'whole formal boundary epicity', sourceSpan('tests/whole-formal-boundary-epicity.ts', 1, 1, 1, 2));
const fingerprint = (goalId: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + goalId + '.ts', sha256: 'sha256:' + '1'.repeat(64) },
    profileSha256: 'sha256:' + '2'.repeat(64)
});

const construct = async () => {
    const sequence = polynomialFreydHomologyFixture('two');
    const selected = algebraPolynomialFreydLongExactSnakeReferences(nativeLongExact.algebraPolynomialFreydBoundedLongExactHomology(sequence));
    const algebra = algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(sequence.ring, [])));
    const R = kernelFree('whole_epi_R', p);
    const x = kernelFree('whole_epi_x', p);
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({ algebra, formalRing: R, generatorTerms: [x],
        coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(key);
            if (!term) {
                term = kernelFree('whole_epi_c_' + [...key].map(c => c.codePointAt(0)!.toString(16)).join('_'), p);
                coefficients.set(key, term);
            }
            return term;
        }, status: 'trusted-computation' });
    const bundle = algebraFormalFreydLongExactDelegationBundle({ reifier, selected });
    const prepared = prepareAlgebraFormalFreydLongExactEpimorphisms(bundle);
    const elementType = affineFormalRingElementType(R);
    const environment = createFormalFreydEpimorphismProofEnvironment([
        { name: R.name, type: affineFormalCommRingType() }, { name: x.name, type: elementType },
        ...[...coefficients.values()].map(term => ({ name: term.name, type: elementType }))
    ]);
    const source = createAlgebraFormalAssumptionSource({ moduleId: 'proof.cas.whole-boundary-epicity',
        sourceId: 'tests/whole-boundary-epicity.assumptions', baseEnvironment: environment });
    const target = bundle.realization.claimType;
    const goalId = 'whole-boundary-epicity-replay';
    const run = await runAlgebraFormalWorkflow({ document: { moduleId: source.moduleId, declarationId: goalId,
        environment, type: target, plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
        provenance: p, fingerprint: fingerprint(goalId) }, goalId, adapter: bundle.adapter,
        realization: bundle.realization, engine: bundle.engine });
    const adopted = await trustAlgebraFormalFreydLongExact({ artifactId: 'whole-boundary-epicity-upstream', bundle, run, source,
        fingerprint, decisionEvidence: id => 'Explicitly adopt original whole-output equation ' + id });
    const decisions: string[] = [];
    const input = { artifactId: 'whole-boundary-epicity', prepared, adopted, fingerprint,
        decisionEvidence: (id: string) => { decisions.push(id); return 'Explicitly adopt the selected boundary equation ' + id; } };
    const forbidRecomputation = () => { throw new Error('Downstream boundary epicity must not recompute homology or windows'); };
    const spies = [
        mock.method(nativeHomology, 'algebraPolynomialFreydHomologyAt', forbidRecomputation),
        mock.method(nativeWindow, 'algebraPolynomialFreydHomologyWindow', forbidRecomputation),
        mock.method(nativeLongExact, 'algebraPolynomialFreydBoundedLongExactHomology', forbidRecomputation)
    ];
    try {
        const result = await trustAlgebraFormalFreydLongExactEpimorphisms(input);
        spies.forEach(spy => assert.equal(spy.mock.callCount(), 0));
        return { bundle, prepared, source, adopted, result, input, decisions };
    } finally {
        spies.forEach(spy => spy.mock.restore());
    }
};

let consumerPromise: ReturnType<typeof construct> | undefined;
const consumer = () => consumerPromise ??= construct();

describe('v3.2 whole long-exact formal boundary epimorphisms', () => {
    it('constructs every retained boundary witness after one nonsplit whole replay', async () => {
        const value = await consumer();
        const { result, adopted } = value;
        assert.equal(result.witnesses.length, 6);
        assert.equal(result.native, adopted.adoption.result.computed.value.result);
        assert.equal(result.upstreamAdoption, adopted);
        assert.equal(result.counts.boundaries, 6);
        assert.equal(result.counts.reusedBoundaryLaws, 3);
        assert.equal(result.counts.newBoundaryLaws, 3);
        assert.equal(result.counts.newBlockLaws, 6);
        assert.equal(result.counts.wholeHomologyReplays, 0);
        assert.equal(result.source.entries.length, adopted.source.entries.length + result.counts.newBoundaryLaws + result.counts.newBlockLaws);
        assert.equal(value.source.entries.length, 0);
        assert.deepEqual(result.witnesses.map(w => [w.position, w.degree, w.role]),
            [[1, 1, 'A'], [2, 1, 'B'], [3, 1, 'C'], [4, 0, 'A'], [5, 0, 'B'], [6, 0, 'C']]);
        const checker = createCoreProofChecker(result.source.environment);
        checker.validateEnvironment();
        result.witnesses.forEach((witness, index) => {
            const point = result.native.interior[index];
            assert.equal(witness.point, point);
            assert.equal(witness.homology, point.exactness.homology);
            assert.equal(witness.boundary, point.exactness.homology.boundaryMorphism);
            assert.equal(witness.epimorphism, point.exactness.epimorphism);
            assert.equal(witness.constructed.selected, witness.epimorphism);
            assert.equal(witness.constructed.selected.morphism, witness.boundary);
            assert.equal(witness.blockBinding.label, 'long-exact/boundary-epic/' + witness.position + '/block');
            assert.equal(witness.morphismBinding.label, 'long-exact/boundary-epic/' + witness.position + '/relation');
            assert.ok(value.decisions.includes(witness.blockBinding.label));
            assert.equal(result.source.entries[witness.blockBinding.sourceIndex].reference, witness.blockBinding.reference);
            assert.equal(result.source.entries[witness.morphismBinding.sourceIndex].reference, witness.morphismBinding.reference);
            const realization = value.prepared.entries[index].block.realization;
            assert.ok(kernelExpressionEquals(witness.constructed.morphism, algebraFormalFreydMorphismTerm(realization.morphism, witness.morphismBinding.reference)));
            checker.check(checker.rootContext, witness.constructed.term, witness.constructed.type);
        });
        assert.equal(ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE.claimsFormalChainExactness, false);
        assert.equal(ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE.suppliesWeakKernelCapability, false);
    });

    it('rejects foreign profiles, a different upstream bundle, and a source missing the whole adoption', async () => {
        const value = await consumer();
        await assert.rejects(() => trustAlgebraFormalFreydLongExactEpimorphisms({ ...value.input,
            prepared: { ...value.prepared, profileRevision: 'foreign' as typeof value.prepared.profileRevision } }), /profile/u);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactEpimorphisms({ ...value.input,
            adopted: { ...value.adopted, profileRevision: 'foreign' as typeof value.adopted.profileRevision } }), /profile/u);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactEpimorphisms({ ...value.input,
            prepared: { ...value.prepared, upstreamBundle: { ...value.bundle, adapter: { ...value.bundle.adapter } } } }), /another prepared bundle/u);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactEpimorphisms({ ...value.input,
            adopted: { ...value.adopted, source: value.source } }), /original whole-replay adoption/u);
        assert.equal(value.source.entries.length, 0);
    });

    it('rejects stale whole inventories and changed prepared boundary labels before adoption', async () => {
        const value = await consumer();
        const before = value.decisions.length;
        const sourceCount = value.adopted.source.entries.length;
        await assert.rejects(() => trustAlgebraFormalFreydLongExactEpimorphisms({ ...value.input,
            prepared: { ...value.prepared, upstreamEquationsData: 'stale' } }), /drifted/u);
        await assert.rejects(() => trustAlgebraFormalFreydLongExactEpimorphisms({ ...value.input,
            prepared: { ...value.prepared, entries: value.prepared.entries.map((entry, index) => index === 0 ? { ...entry, label: 'wrong-label' } : entry) } }), /drifted/u);
        assert.equal(value.decisions.length, before);
        assert.equal(value.adopted.source.entries.length, sourceCount);
    });

    it('checks all six constructed native boundary witnesses together in Lambdapi', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_LONG_EXACT_EPIMORPHISMS !== '1'
    }, async () => {
        const { result } = await consumer();
        let environment = result.source.environment;
        const assertions = result.witnesses.map(witness => {
            const name = 'whole_epi_boundary_' + witness.position;
            environment = environment.extend({ name, type: witness.constructed.type, body: witness.constructed.term,
                transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p });
            return { label: witness.label, term: kernelFree(name, p), type: witness.constructed.type,
                span: sourceSpan('generated/whole-boundary-epicity.ts', witness.position, 1, witness.position, 2) };
        });
        const serialized = serializeCoreLfKernelProbe({ environment,
            externalFreeReferences: { ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
                ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS }, assertions });
        const checked = checkLambdapiProbe({ ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
            'require open emdash.emdash3_2_commutative_algebra_freyd_explicit_epimorphisms;') },
        { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics.slice(-10000));
    });
});
