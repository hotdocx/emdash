/** Selected whole long-exact replay and explicit proof–CAS adoption. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS, AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS, AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    AlgebraFormalDelegationError, AlgebraProgressEvent, KernelExpression, RATIONAL_DOMAIN,
    affineFormalCommRingType, affineFormalRingElementType,
    algebraPolynomialIdeal, algebraPolynomialModuleMapZero, algebraPolynomialQuotientRing,
    algebraPolynomialText, algebraPresentedAlgebra,
    algebraAlgorithmIdentity, coreProofPlanHole, createAlgebraFormalAssumptionSource,
    checkLambdapiProbe, createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation,
    createCoreProofArtifactFingerprint, createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment, defineAffineFormalPolynomialReifier,
    kernelExpressionEquals, kernelFree, kernelUniverse, provenance,
    runAlgebraFormalWorkflow, serializeCoreExpression, serializeCoreLfKernelProbe, sourceSpan,
    validateAlgebraFormalAssumptionSource
} from '../src/v3_2';
import {
    ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE,
    algebraFormalFreydLongExactDelegationBundle,
    serializeAlgebraFormalFreydLongExactAdoption, trustAlgebraFormalFreydLongExact
} from '../src/v3_2/algebra_formal_freyd_long_exact';
import { algebraPolynomialFreydBoundedLongExactHomology } from '../src/v3_2/algebra_polynomial_freyd_long_exact';
import {
    algebraPolynomialFreydLongExactSnakeReferences, serializeAlgebraPolynomialFreydLongExactSnakeReferences
} from '../src/v3_2/algebra_polynomial_freyd_long_exact_reference_operations';
import {
    decodeAlgebraFormalFreydLongExactData, encodeAlgebraFormalFreydLongExactData
} from '../src/v3_2/algebra_formal_freyd_long_exact_encoding';
import {
    isPolynomialFreydMorphismZero, polynomialFreydHomologyFixture
} from './v3_2_algebra_polynomial_freyd_homology_fixtures';

const because = (detail: string) => provenance('surface', 'long-exact bridge: ' + detail);
const fingerprint = (goalId: string) => createCoreProofArtifactFingerprint({
    source: { id: 'tests/' + goalId + '.ts', sha256: 'sha256:' + 'a'.repeat(64) },
    profileSha256: 'sha256:' + 'b'.repeat(64)
});
const delegationError = (code: AlgebraFormalDelegationError['code']) => (error: unknown) => {
    assert.ok(error instanceof AlgebraFormalDelegationError);
    assert.equal(error.code, code);
    return true;
};

const fixture = (shape: 'one' | 'two' | 'boundary' = 'two') => {
    const sequence = polynomialFreydHomologyFixture(shape);
    const selected = algebraPolynomialFreydLongExactSnakeReferences(
        algebraPolynomialFreydBoundedLongExactHomology(sequence));
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(algebraPolynomialIdeal(sequence.ring, [])));
    const formalRing = kernelFree('formal_long_exact_R', because('ring'));
    const formalX = kernelFree('formal_long_exact_x', because('generator'));
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra, formalRing, generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(text);
            if (!term) {
                const suffix = [...text].map(c => c.codePointAt(0)!.toString(16)).join('_');
                term = kernelFree('formal_long_exact_coefficient_' + suffix, because('coefficient'));
                coefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    // Preparing first must enumerate all coefficients needed by every equation.
    const bundle = algebraFormalFreydLongExactDelegationBundle({ reifier, selected });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createFormalPresentationMorphismProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: elementType },
        ...[...coefficients.values()].map(term => ({ name: term.name, type: elementType }))
    ]);
    const source = createAlgebraFormalAssumptionSource({
        moduleId: 'proof.cas.long-exact', sourceId: 'tests/long-exact.assumptions', baseEnvironment: environment
    });
    return { sequence, selected, reifier, bundle, environment, source, coefficients };
};

const document = (value: ReturnType<typeof fixture>, goalId: string, target: KernelExpression = value.bundle.realization.claimType) => ({
    moduleId: value.source.moduleId, declarationId: goalId,
    environment: value.source.environment, type: target,
    plan: coreProofPlanHole(goalId, {
        provenance: because('hole'), expectation: { contextDepth: 0, target }
    }),
    provenance: because('root'), fingerprint: fingerprint(goalId)
});

describe('v3.2 bounded long exact proof–CAS bridge', () => {
    it('losslessly encodes nested JSON text without conflating strings, objects, keys or whitespace', () => {
        const child = JSON.stringify({ arrow: 'α → β', text: '{not json}', scalar: [null, true, -2] });
        for (const text of ['', child, child + '\n', '  ' + child, JSON.stringify({
            text: child, value: JSON.parse(child), repeated: [child, child],
            dangerousKeys: JSON.parse('{"__proto__":{},"constructor":"unchanged"}')
        }) + '\n']) {
            const encoded = encodeAlgebraFormalFreydLongExactData(text);
            assert.equal(decodeAlgebraFormalFreydLongExactData(encoded), text);
            assert.equal(encoded, encodeAlgebraFormalFreydLongExactData(text));
        }
        const valid = JSON.parse(encodeAlgebraFormalFreydLongExactData('x'));
        assert.throws(() => decodeAlgebraFormalFreydLongExactData(JSON.stringify({
            ...valid, nodes: [['array', [0]]]
        })), /Invalid long-exact data table/u);
        assert.throws(() => decodeAlgebraFormalFreydLongExactData(JSON.stringify({ ...valid, root: -1 })), /Invalid/u);
        assert.throws(() => decodeAlgebraFormalFreydLongExactData(JSON.stringify({ ...valid, revision: 'foreign' })), /Invalid/u);
    });

    it('reifies the full three-degree equation inventory, including nonzero connecting and boundary maps', context => {
        const value = fixture('boundary');
        const { entries, claims } = value.bundle.equations;
        const ids = new Set(entries.map(entry => entry.id));
        const whole = value.selected.result;
        const checker = createCoreProofChecker(value.environment);
        checker.validateEnvironment();
        claims.forEach(claim => checker.check(checker.rootContext,
            claim.representative.realization.claimType, kernelUniverse(because('equation type'))));
        assert.equal(ids.size, entries.length);
        const allLabels = claims.flatMap(claim => claim.labels);
        assert.deepEqual([...allLabels].sort(), [...ids].sort());
        const byId = new Map(entries.map(entry => [entry.id, entry]));
        claims.forEach(claim => claim.labels.forEach(label => assert.ok(kernelExpressionEquals(
            byId.get(label)!.realization.claimType, claim.representative.realization.claimType))));
        assert.ok(claims.length < entries.length);
        whole.arrows.forEach((_, index) => assert.ok(ids.has('long-exact/map/' + index)));
        whole.interior.forEach((point, index) => {
            assert.ok(ids.has('long-exact/zero/' + index));
            assert.ok(ids.has('long-exact/exact/' + point.term.position + '/boundary-epic-cokernel-zero'));
        });
        for (let degree = 0; degree <= whole.topDegree; degree++) {
            assert.ok(ids.has('sequence/row/' + degree + '/zero'));
            if (degree > 0) for (const map of ['inclusion', 'projection']) {
                assert.ok(ids.has('sequence/' + map + '/chain/' + degree));
            }
        }
        whole.windows.forEach(window => {
            for (let index = 0; index < 5; index++) assert.ok(ids.has('snake-exact/' + window.degree + '/map/' + index));
            for (let index = 0; index < 4; index++) assert.ok(ids.has('snake-exact/' + window.degree + '/zero/' + index));
            for (const suffix of ['reconstruction', 'descent/zero', 'descent/reconstruction',
                'targetFactor/test', 'targetFactor/reconstruction', 'target-factor']) {
                assert.ok(ids.has('connecting/' + window.degree + '/' + suffix));
            }
        });
        assert.equal(isPolynomialFreydMorphismZero(whole.windows[1].connecting.homologyMap), false);
        assert.equal(ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.claimsGenericFormalExactness, false);
        assert.equal(ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.claimsQuotientPathDecoding, false);
        assert.equal(decodeAlgebraFormalFreydLongExactData(value.bundle.equations.selectedOutputData),
            serializeAlgebraPolynomialFreydLongExactSnakeReferences(value.selected));
        assert.ok(Buffer.byteLength(value.bundle.equationsData) < 16 * 1024 * 1024);
        context.diagnostic(entries.length + ' labels, ' + claims.length + ' distinct claims, ' +
            Buffer.byteLength(value.bundle.equationsData) + ' inventory bytes');
    });

    for (const shape of ['two', 'boundary'] as const) it('replays and explicitly adopts the nonsplit ' + shape + ' example', async context => {
        const value = fixture(shape);
        const goalId = 'long-exact-reconstruction';
        const inputDocument = document(value, goalId);
        const originalPlan = inputDocument.plan;
        const events: AlgebraProgressEvent[] = [];
        const coefficientCount = value.coefficients.size;
        const run = await runAlgebraFormalWorkflow({
            document: inputDocument, goalId,
            adapter: value.bundle.adapter, realization: value.bundle.realization,
            engine: value.bundle.engine, execution: { onProgress: event => events.push(event) }
        });
        assert.equal(run.result.interpretation.kind, 'claim');
        assert.equal(value.source.entries.length, 0);
        assert.equal(inputDocument.plan, originalPlan);
        assert.equal(value.source.environment, value.environment);
        const starts = events.filter(event => event.completed === 0);
        for (const operation of [value.bundle.operation, value.bundle.model.native.boundedShortExact,
            value.bundle.model.native.boundedLongExact, value.bundle.model.native.snakeReferences]) {
            assert.equal(starts.filter(event => event.phase === operation.identity.id).length, 1);
        }
        const adopted = await trustAlgebraFormalFreydLongExact({
            artifactId: 'long-exact-fixture', bundle: value.bundle, run, source: value.source,
            fingerprint, decisionEvidence: id => 'Explicitly adopt selected long-exact equation ' + id
        });
        assert.equal(adopted.adoption.execution.state.status, 'complete');
        assert.equal(adopted.source.entries.length, value.bundle.equations.claims.length);
        assert.equal(adopted.bindings.flatMap(binding => binding.labels).length, value.bundle.equations.entries.length);
        assert.equal(validateAlgebraFormalAssumptionSource(adopted.source), adopted.source);
        const checker = createCoreProofChecker(adopted.source.environment);
        checker.validateEnvironment();
        adopted.bindings.forEach(binding => {
            const entry = adopted.source.entries[binding.sourceIndex];
            assert.equal(entry.classification, 'computed-equation');
            checker.check(checker.rootContext, binding.reference, entry.declaration.type);
        });
        assert.equal(value.source.entries.length, 0, 'original immutable source is preserved');
        assert.equal(value.coefficients.size, coefficientCount, 'preparation retained every coefficient binding');
        assert.equal(events.length, starts.length * 2, 'adoption did not replay the whole operation');
        const serialized = serializeAlgebraFormalFreydLongExactAdoption(adopted);
        assert.equal(serialized, serializeAlgebraFormalFreydLongExactAdoption(adopted));
        const portable = JSON.parse(decodeAlgebraFormalFreydLongExactData(serialized));
        assert.ok(Buffer.byteLength(serialized) < 16 * 1024 * 1024);
        assert.deepEqual(portable.bindings.map((binding: { reference: string }) => binding.reference),
            adopted.bindings.map(binding => serializeCoreExpression(binding.reference)));
        context.diagnostic(value.bundle.equations.entries.length + ' labelled equations adopted through ' +
            adopted.source.entries.length + ' assumptions; ' + Buffer.byteLength(serialized) + ' artifact bytes');
    });

    it('rejects unknown anchors, altered inventories and a different typed goal before computing', async () => {
        const value = fixture('one');
        assert.throws(() => algebraFormalFreydLongExactDelegationBundle({
            reifier: value.reifier, selected: value.selected, anchorId: 'absent'
        }), /Unknown long-exact equation anchor/u);
        const goalId = 'wrong-long-exact-goal';
        const other = value.bundle.equations.claims.find(claim => !kernelExpressionEquals(
            claim.representative.realization.claimType, value.bundle.realization.claimType))!;
        const events: AlgebraProgressEvent[] = [];
        await assert.rejects(() => runAlgebraFormalWorkflow({
            document: document(value, goalId, other.representative.realization.claimType), goalId,
            adapter: value.bundle.adapter, realization: value.bundle.realization,
            engine: value.bundle.engine, execution: { onProgress: event => events.push(event) }
        }), delegationError('INVALID_REALIZATION'));
        await assert.rejects(() => runAlgebraFormalWorkflow({
            document: document(value, goalId), goalId, adapter: value.bundle.adapter,
            realization: { ...value.bundle.realization, equations: {
                ...value.bundle.equations, entries: value.bundle.equations.entries.slice(1)
            } },
            engine: value.bundle.engine, execution: { onProgress: event => events.push(event) }
        }), delegationError('INVALID_REALIZATION'));
        assert.equal(events.length, 0);
        assert.equal(value.source.entries.length, 0);
    });

    it('preserves whole-output, prepared-bundle, coefficient and source-environment stale guards', async () => {
        const value = fixture('one');
        const goalId = 'long-exact-stale';
        const run = await runAlgebraFormalWorkflow({
            document: document(value, goalId), goalId, adapter: value.bundle.adapter,
            realization: value.bundle.realization, engine: value.bundle.engine
        });
        const input = {
            artifactId: 'long-exact-stale', bundle: value.bundle, run, source: value.source,
            fingerprint, decisionEvidence: (id: string) => 'Explicit selected adoption ' + id
        };
        // The full serialization, not just the selected anchor, is significant.
        const changed = { ...run.result.computed.value, result: {
            ...run.result.computed.value.result, endpoints: {
                ...run.result.computed.value.result.endpoints,
                initialZero: { ...run.result.computed.value.result.endpoints.initialZero, reductionSteps: 17 }
            }
        } };
        assert.notEqual(value.bundle.adapter.serializeOutput(changed), run.result.outputData);
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({
            ...input, run: { ...run, result: { ...run.result, computed: { ...run.result.computed, value: changed } } }
        }), delegationError('STALE_RESULT'));
        const computedSequence = run.result.computed.value.result.sequence;
        const row = computedSequence.rows[0];
        const originalWitness = row.triple.pair.chainAgreement.agreementWitness;
        assert.notEqual(algebraPolynomialText(originalWitness.columns[0].components[0]), '0');
        const alteredPair = { ...row.triple.pair, chainAgreement: { ...row.triple.pair.chainAgreement,
            agreementWitness: algebraPolynomialModuleMapZero(originalWitness.source, originalWitness.target)
        } };
        const brokenSharing = { ...run.result.computed.value, result: { ...run.result.computed.value.result,
            sequence: { ...computedSequence, rows: [{ ...row, triple: { ...row.triple,
                pair: alteredPair
            } }] }
        } };
        assert.throws(() => value.bundle.adapter.serializeOutput(brokenSharing), /actual retained pair and homology/u);
        const alteredHomology = { ...row.triple.homology, pair: alteredPair };
        const wrongWitness = { ...run.result.computed.value, result: { ...run.result.computed.value.result,
            sequence: { ...computedSequence, rows: [{ ...row, triple: { ...row.triple,
                pair: alteredPair, homology: alteredHomology,
                exactness: { ...row.triple.exactness, homology: alteredHomology }
            } }] }
        } };
        assert.ok(value.bundle.adapter.serializeOutput(wrongWitness) !== run.result.outputData,
            'The actual selected coefficient witness is part of the whole serialized result');
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({
            ...input, run: { ...run, result: { ...run.result, computed: { ...run.result.computed, value: wrongWitness } } }
        }), delegationError('STALE_RESULT'));
        const otherBundle = algebraFormalFreydLongExactDelegationBundle({ reifier: value.reifier, selected: value.selected });
        assert.equal(otherBundle.equationsData, value.bundle.equationsData);
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({ ...input, bundle: otherBundle }), delegationError('STALE_RESULT'));
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({
            ...input, bundle: { ...value.bundle, equationsData: value.bundle.equationsData + ' ' }
        }), delegationError('STALE_RESULT'));
        const driftedReifier = defineAffineFormalPolynomialReifier({
            algebra: value.reifier.algebra, formalRing: value.reifier.formalRing,
            generatorTerms: value.reifier.generatorTerms,
            coefficientReifier: () => value.reifier.generatorTerms[0], status: 'trusted-computation'
        });
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({
            ...input, bundle: { ...value.bundle, reifier: driftedReifier }
        }), delegationError('STALE_RESULT'));
        const foreign = createAlgebraFormalAssumptionSource({
            moduleId: value.source.moduleId, sourceId: value.source.sourceId,
            baseEnvironment: fixture('one').environment
        });
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({ ...input, source: foreign }), /current source environment/u);
        assert.equal(value.source.entries.length, 0);
        assert.equal(foreign.entries.length, 0);
    });

    it('reports a changed whole result as an observation and propagates cancellation into the graph', async () => {
        const value = fixture('one');
        const goalId = 'long-exact-observation';
        const changed = { ...value.selected, result: {
            ...value.selected.result, endpoints: {
                ...value.selected.result.endpoints,
                initialZero: { ...value.selected.result.endpoints.initialZero, reductionSteps: 23 }
            }
        } };
        const implementation = defineAlgebraReferenceImplementation({
            operation: value.bundle.operation,
            algorithm: algebraAlgorithmIdentity('test.long-exact-changed', 'v1'),
            execute: () => changed
        });
        const engine = createAlgebraTypeScriptReferenceEngine({
            id: 'test.long-exact-changed', revision: 'v1', implementations: [implementation]
        });
        const run = await runAlgebraFormalWorkflow({
            document: document(value, goalId), goalId, adapter: value.bundle.adapter,
            realization: value.bundle.realization, engine
        });
        assert.equal(run.result.interpretation.kind, 'observation');
        await assert.rejects(() => trustAlgebraFormalFreydLongExact({
            artifactId: goalId, bundle: value.bundle, run, source: value.source,
            fingerprint, decisionEvidence: () => 'Explicit attempt must not adopt a changed whole result'
        }), delegationError('STALE_RESULT'));
        let cancelled = false;
        const events: AlgebraProgressEvent[] = [];
        await assert.rejects(() => runAlgebraFormalWorkflow({
            document: document(value, goalId), goalId, adapter: value.bundle.adapter,
            realization: value.bundle.realization, engine: value.bundle.engine,
            execution: {
                onProgress: event => {
                    events.push(event);
                    if (event.phase === value.bundle.operation.identity.id && event.completed === 0) cancelled = true;
                },
                cancellation: { requested: () => cancelled, reason: () => 'cancel inside whole replay' }
            }
        }), delegationError('EXECUTION_FAILED'));
        assert.deepEqual(events.map(event => event.phase), [value.bundle.operation.identity.id]);
        assert.equal(value.source.entries.length, 0);
    });

    it('checks all distinct three-degree claim types with bounded Lambdapi conformance', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_LONG_EXACT !== '1'
    }, () => {
        const value = fixture('boundary');
        const serialized = serializeCoreLfKernelProbe({
            environment: value.environment,
            externalFreeReferences: {
                ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS
            },
            assertions: value.bundle.equations.claims.map((claim, index) => ({
                label: claim.labels.join(', '), term: claim.representative.realization.claimType,
                type: kernelUniverse(because('Lambdapi equation type')),
                span: sourceSpan('generated/proof-cas-long-exact.ts', index + 1, 1, index + 1, 2)
            }))
        });
        const checked = checkLambdapiProbe({
            ...serialized, source: serialized.source.replace('require open emdash.emdash3_2;',
                'require open emdash.emdash3_2_commutative_algebra_freyd_functorial_homology;')
        }, { packageRoot: resolve(__dirname, '..', 'emdash2'), timeoutMs: 60_000 });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics);
    });
});
