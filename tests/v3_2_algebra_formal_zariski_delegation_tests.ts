/** Focused PCD-ZARISKI-5A proof–CAS vertical-slice tests. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_ZARISKI_SIGNATURE_PROFILE,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE,
    AlgebraFormalDelegationError,
    RATIONAL_DOMAIN,
    adoptAlgebraFormalTrustedComputation,
    affineFormalCommRingType,
    affineFormalCoverLawType,
    affineFormalRingElementType,
    algebraAffineCover,
    algebraAffineScheme,
    algebraFormalZariskiDelegationBundle,
    algebraPolynomialIdeal,
    algebraPolynomialOne,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    algebraQuotientElement,
    applyCoreProofPlanPatch,
    buildAffineFormalCoverTerms,
    binderMode,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAffineFormalZariskiProofEnvironment,
    createAlgebraComputationGraphBuilder,
    createAlgebraFormalComputationRequest,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    defineAffineFormalCoverRealization,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalComputationGoal,
    defineAlgebraFormalZariskiDelegationRealization,
    executeAlgebraComputationGraph,
    executeAlgebraFormalComputationRequest,
    isCoreKind,
    kernelExpressionEquals,
    kernelFree,
    kernelUniverse,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraFormalComputationResult,
    serializeAlgebraUnimodularCombination,
    serializeCoreExpression,
    serializeCoreLfKernelProbe,
    sourceSpan,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

const hex = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0'))
    .join('');

const delegationError = (
    code: AlgebraFormalDelegationError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraFormalDelegationError);
    assert.equal(error.code, code);
    return true;
};

const fingerprint = () => createCoreProofArtifactFingerprint({
    source: {
        id: 'tests/fixtures/formal-zariski-delegation.surface.ts',
        sha256: `sha256:${'c'.repeat(64)}`
    },
    profileSha256: `sha256:${'d'.repeat(64)}`
});

const positiveFixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const oneMinusX = algebraPolynomialSubtract(algebraPolynomialOne(ring), x);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const cover = algebraAffineCover(algebraAffineScheme(algebra), [
        algebraQuotientElement(quotient, x),
        algebraQuotientElement(quotient, oneMinusX)
    ], 0);
    const formalRing = kernelFree('formal_zariski_R', because('formal ring'));
    const formalX = kernelFree('formal_zariski_x', because('formal x'));
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            const existing = coefficients.get(text);
            if (existing !== undefined) return existing;
            const term = kernelFree(
                `formal_zariski_coefficient_${hex(text)}`,
                because(`formal coefficient ${text}`)
            );
            coefficients.set(text, term);
            return term;
        },
        status: 'trusted-computation'
    });
    const trustedCover = defineAffineFormalCoverRealization({
        cover,
        algebra: reifier.realization,
        status: 'trusted-computation'
    });
    const realization = defineAlgebraFormalZariskiDelegationRealization({
        ideal: cover.unimodular.ideal,
        reifier,
        candidateCoefficients: cover.unimodular.coefficients,
        formalCover: trustedCover
    });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createAffineFormalZariskiProofEnvironment([
        {
            name: formalRing.name,
            type: affineFormalCommRingType()
        },
        { name: formalX.name, type: elementType },
        ...[...coefficients.values()].map(term => ({
            name: term.name,
            type: elementType
        }))
    ]);
    const document = Object.freeze({
        moduleId: 'proof.cas.zariski',
        declarationId: 'binary_cover_law',
        environment,
        type: realization.claimType,
        plan: coreProofPlanHole('binary-cover-law', {
            provenance: because('binary cover root hole'),
            expectation: {
                contextDepth: 0,
                target: realization.claimType
            }
        }),
        provenance: because('binary cover proof root'),
        fingerprint: fingerprint()
    });
    const goal = defineAlgebraFormalComputationGoal({
        document,
        goalId: 'binary-cover-law'
    });
    const bundle = algebraFormalZariskiDelegationBundle(ring);
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: 'proof-cas.zariski-reference',
        revision: 'v1',
        implementations: bundle.operations.implementations
    });
    return {
        ring,
        x,
        quotient,
        algebra,
        cover,
        formalRing,
        reifier,
        trustedCover,
        realization,
        environment,
        document,
        goal,
        bundle,
        engine
    };
};

const negativeFixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const formalRing = kernelFree(
        'formal_noncover_R',
        because('formal noncover ring')
    );
    const formalX = kernelFree('formal_noncover_x', because('formal x'));
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            const existing = coefficients.get(text);
            if (existing !== undefined) return existing;
            const term = kernelFree(
                `formal_noncover_coefficient_${hex(text)}`,
                because(`formal coefficient ${text}`)
            );
            coefficients.set(text, term);
            return term;
        },
        status: 'trusted-computation'
    });
    const ideal = algebraPolynomialIdeal(ring, [x]);
    const realization = defineAlgebraFormalZariskiDelegationRealization({
        ideal,
        reifier,
        candidateCoefficients: [algebraPolynomialZero(ring)]
    });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createAffineFormalZariskiProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: elementType },
        ...[...coefficients.values()].map(term => ({
            name: term.name,
            type: elementType
        }))
    ]);
    const document = Object.freeze({
        moduleId: 'proof.cas.zariski',
        declarationId: 'singleton_noncover_law',
        environment,
        type: realization.claimType,
        plan: coreProofPlanHole('singleton-noncover-law', {
            provenance: because('noncover root hole'),
            expectation: {
                contextDepth: 0,
                target: realization.claimType
            }
        }),
        provenance: because('noncover proof root'),
        fingerprint: fingerprint()
    });
    const goal = defineAlgebraFormalComputationGoal({
        document,
        goalId: 'singleton-noncover-law'
    });
    const bundle = algebraFormalZariskiDelegationBundle(ring);
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: 'proof-cas.zariski-negative-reference',
        revision: 'v1',
        implementations: bundle.operations.implementations
    });
    return { ring, ideal, realization, document, goal, bundle, engine };
};

describe('PCD-ZARISKI-5A exact proof–CAS vertical slice', () => {
    it('checks the exact opaque signature mirror and law target without a law',
        () => {
            const fixture = positiveFixture();
            const checker = createCoreProofChecker(fixture.environment);
            checker.validateEnvironment();

            assert.equal(fixture.trustedCover.formalCoverAvailable, false);
            assert.ok(kernelExpressionEquals(
                affineFormalCoverLawType(fixture.trustedCover),
                fixture.realization.claimType
            ));
            assert.doesNotThrow(() => checker.check(
                checker.rootContext,
                fixture.realization.claimType,
                kernelUniverse(because('law type universe'))
            ));
            assert.equal(
                AFFINE_FORMAL_ZARISKI_SIGNATURE_PROFILE.signatureNames.length,
                20
            );
        }
    );

    it('delegates the binary cover law and adopts it explicitly', async () => {
        const fixture = positiveFixture();
        const run = await runAlgebraFormalWorkflow({
            document: fixture.document,
            goalId: fixture.goal.goalId,
            adapter: fixture.bundle.adapter,
            realization: fixture.realization,
            engine: fixture.engine
        });
        const result = run.result;
        const adopted = trustAlgebraFormalWorkflow({
            run,
            assumptionName: 'trusted_binary_cover_law',
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: 'author adopts exact binary unimodular computation'
            }
        });
        const lawBearing = defineAffineFormalCoverRealization({
            cover: fixture.cover,
            algebra: fixture.reifier.realization,
            status: 'explicit-data',
            lawTerm: adopted.reference
        });
        const terms = buildAffineFormalCoverTerms(lawBearing);
        const checker = createCoreProofChecker(adopted.environment);
        checker.validateEnvironment();

        assert.equal(result.computed.value.unimodular, true);
        assert.equal(result.interpretation.kind, 'claim');
        assert.equal(result.interpretation.data.length, 2);
        assert.equal(adopted.execution.state.status, 'complete');
        assert.equal(lawBearing.formalCoverAvailable, true);
        assert.doesNotThrow(() => checker.infer(
            checker.rootContext,
            terms.cover
        ));
        assert.match(serializeCoreExpression(terms.cover),
            /bridge_comm_ring_zariski_cover_intro/u);
        assert.match(serializeAlgebraFormalComputationResult(result),
            /exact selected coefficients have dot product one/u);
        assert.equal(fixture.document.plan.tag, 'hole');
        assert.equal(
            applyCoreProofPlanPatch(fixture.document.plan, adopted.patch).tag,
            'exact'
        );
    });

    it('agrees with ordinary graph execution on the whole output', async () => {
        const fixture = positiveFixture();
        const request = createAlgebraFormalComputationRequest({
            adapter: fixture.bundle.adapter,
            goal: fixture.goal,
            realization: fixture.realization,
            engine: fixture.engine
        });
        const direct = await executeAlgebraFormalComputationRequest(request);
        const builder = createAlgebraComputationGraphBuilder(
            'proof-cas.zariski.graph',
            'v1'
        );
        const input = builder.input('ideal', fixture.bundle.operations.idealSchema);
        const output = builder.operation(
            'unimodular',
            fixture.bundle.operations.unimodular,
            input
        );
        const graph = builder.build([{ id: 'result', value: output }]);
        const executed = await executeAlgebraComputationGraph({
            graph,
            engine: fixture.engine,
            inputs: [{ id: 'ideal', value: fixture.cover.unimodular.ideal }]
        });

        assert.equal(
            serializeAlgebraUnimodularCombination(direct.computed.value),
            serializeAlgebraUnimodularCombination(
                executed.outputs[0].value as typeof direct.computed.value
            )
        );
    });

    it('retains a noncover remainder and leaves the proof goal open',
        async () => {
            const fixture = negativeFixture();
            const request = createAlgebraFormalComputationRequest({
                adapter: fixture.bundle.adapter,
                goal: fixture.goal,
                realization: fixture.realization,
                engine: fixture.engine
            });
            const result = await executeAlgebraFormalComputationRequest(request);

            assert.equal(result.computed.value.unimodular, false);
            assert.equal(result.interpretation.kind, 'observation');
            assert.match(result.interpretation.summary, /remainder/u);
            assert.equal(fixture.document.plan.tag, 'hole');
            assert.throws(
                () => adoptAlgebraFormalTrustedComputation({
                    result,
                    assumptionName: 'invalid_noncover_law',
                    decision: {
                        kind: 'trust-exact-algebra-computation',
                        evidence: 'negative result must not be adoptable'
                    }
                }),
                delegationError('NO_ADOPTABLE_CLAIM')
            );
        }
    );

    it('rejects a named goal for a different selected coefficient law', () => {
        const fixture = positiveFixture();
        const wrong = defineAlgebraFormalZariskiDelegationRealization({
            ideal: fixture.realization.ideal,
            reifier: fixture.reifier,
            candidateCoefficients: [
                algebraPolynomialZero(fixture.ring),
                algebraPolynomialZero(fixture.ring)
            ]
        });
        assert.throws(
            () => createAlgebraFormalComputationRequest({
                adapter: fixture.bundle.adapter,
                goal: fixture.goal,
                realization: wrong,
                engine: fixture.engine
            }),
            delegationError('INVALID_REALIZATION')
        );
    });

    it('publishes only an adapter and exact signature mirror', () => {
        assert.equal(
            ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.addsCoreOwner,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_ZARISKI_DELEGATION_PROFILE.relationfulCoverBridge,
            false
        );
        assert.equal(
            AFFINE_FORMAL_ZARISKI_SIGNATURE_PROFILE.addsRuntimeRule,
            false
        );
    });

    it(
        'passes bounded Lambdapi checking for the adopted cover term',
        {
            skip: process.env.EMDASH_RUN_PROOF_CAS_ZARISKI !== '1'
        },
        async () => {
            const fixture = positiveFixture();
            const lawName = 'trusted_binary_cover_law_probe';
            const lawProvenance = provenance(
                'surface',
                'trusted binary cover probe law',
                sourceSpan('generated/proof-cas-zariski.ts', 1, 1, 1, 2)
            );
            const environment = fixture.environment.extend({
                name: lawName,
                type: fixture.realization.claimType,
                mode: binderMode('explicit', 'functorial'),
                provenance: lawProvenance
            });
            const lawBearing = defineAffineFormalCoverRealization({
                cover: fixture.cover,
                algebra: fixture.reifier.realization,
                status: 'explicit-data',
                lawTerm: kernelFree(lawName, lawProvenance)
            });
            const terms = buildAffineFormalCoverTerms(lawBearing);
            const checker = createCoreProofChecker(environment);
            const inferred = checker.infer(checker.rootContext, terms.cover);
            if (isCoreKind(inferred.type)) {
                throw new Error('Formal cover term unexpectedly inferred KIND');
            }
            const serialized = serializeCoreLfKernelProbe({
                environment,
                externalFreeReferences:
                    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                assertions: [{
                    label: 'adopted binary Zariski cover',
                    term: terms.cover,
                    type: inferred.type,
                    span: sourceSpan(
                        'generated/proof-cas-zariski.ts',
                        2,
                        1,
                        2,
                        2
                    )
                }]
            });
            const probe = {
                ...serialized,
                source: serialized.source.replace(
                    'require open emdash.emdash3_2;',
                    'require open ' +
                        'emdash.emdash3_2_commutative_algebra_finite;'
                )
            };
            const checked = checkLambdapiProbe(probe, {
                packageRoot: resolve(__dirname, '..', 'emdash2'),
                timeoutMs: 60_000
            });

            assert.equal(checked.timedOut, false, checked.diagnostics);
            assert.equal(checked.accepted, true, checked.diagnostics);
        }
    );
});
