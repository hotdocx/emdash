/** Focused proof–CAS replay of selected polynomial Freyd snake equations. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    ALGEBRA_FORMAL_FREYD_SNAKE_PROFILE,
    AlgebraFormalComputationAdapter,
    AlgebraFormalDelegationError,
    KernelExpression,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalFreydSnakeDelegationBundle,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapZero,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydSnakeTriple,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAlgebraPolynomialFreydSnakeEngine,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    kernelFree,
    kernelUniverse,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraPolynomialFreydSnakeConnecting,
    serializeCoreExpression,
    serializeCoreLfKernelProbe,
    sourceSpan,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

const delegationError = (code: AlgebraFormalDelegationError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraFormalDelegationError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const free = algebraPolynomialFreeModule(ring, 1);
    const object = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const delta = algebraPolynomialPresentationMorphism({
        source: object,
        target: object,
        map: algebraPolynomialModuleMap(free, free, [
            algebraPolynomialModuleVector(free, [x])
        ])
    });
    const beta = algebraPolynomialPresentationMorphismIdentity(object);
    const lambda = algebraPolynomialPresentationMorphism({
        source: object,
        target: object,
        map: algebraPolynomialModuleMapZero(free, free)
    });
    const selected = algebraPolynomialFreydSnakeConnecting(
        algebraPolynomialFreydSnakeTriple(delta, beta, lambda)
    );
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
    );
    const formalRing = kernelFree('formal_freyd_snake_R', because('ring'));
    const formalX = kernelFree('formal_freyd_snake_x', because('x'));
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(text);
            if (term === undefined) {
                const suffix = [...text].map(character =>
                    character.codePointAt(0)!.toString(16)
                ).join('_');
                term = kernelFree(
                    `formal_freyd_snake_coefficient_${suffix}`,
                    because('coefficient')
                );
                coefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const bundle = algebraFormalFreydSnakeDelegationBundle({
        reifier,
        selected
    });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createFormalPresentationMorphismProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: elementType },
        ...[...coefficients.values()].map(term => ({
            name: term.name,
            type: elementType
        }))
    ]);
    const entries = [
        ['triple-zero', bundle.tripleZero],
        ['delta-cokernel-annihilation', bundle.deltaCokernelAnnihilation],
        ['gamma-test-zero', bundle.gammaTestZero],
        ['gamma-reconstruction', bundle.gammaReconstruction],
        ['gamma-kernel-annihilation', bundle.gammaKernelAnnihilation],
        ['lambda-kernel-annihilation', bundle.lambdaKernelAnnihilation],
        ['alpha-test-zero', bundle.alphaTestZero],
        ['alpha-reconstruction', bundle.alphaReconstruction],
        ['alpha-cokernel-annihilation', bundle.alphaCokernelAnnihilation],
        ['fiber-compatibility', bundle.fiberCompatibility],
        ['fiber-projection-left-reconstruction',
            bundle.fiberProjectionLeftReconstruction],
        ['fiber-projection-right-reconstruction',
            bundle.fiberProjectionRightReconstruction],
        ['epsilon-epicity', bundle.epsilonEpicity],
        ['p1-epicity', bundle.p1Epicity],
        ['mu-monicity', bundle.muMonicity],
        ['pushout-compatibility', bundle.pushoutCompatibility],
        ['pushout-injection-left-reconstruction',
            bundle.pushoutInjectionLeftReconstruction],
        ['pushout-injection-right-reconstruction',
            bundle.pushoutInjectionRightReconstruction],
        ['q2-monicity', bundle.q2Monicity],
        ['normal-epi-test', bundle.normalEpiTest],
        ['u', bundle.u],
        ['u-reconstruction', bundle.uReconstruction],
        ['normal-mono-test', bundle.normalMonoTest],
        ['connecting', bundle.connecting],
        ['connecting-reconstruction', bundle.connectingReconstruction]
    ] as const;
    return { selected, bundle, entries, environment };
};

const document = (
    goalId: string,
    target: KernelExpression,
    environment: ReturnType<typeof createFormalPresentationMorphismProofEnvironment>
) => Object.freeze({
    moduleId: `proof.cas.${goalId}`,
    declarationId: goalId,
    environment,
    type: target,
    plan: coreProofPlanHole(goalId, {
        provenance: because(`${goalId} hole`),
        expectation: { contextDepth: 0, target }
    }),
    provenance: because(`${goalId} root`),
    fingerprint: createCoreProofArtifactFingerprint({
        source: {
            id: `tests/${goalId}.ts`,
            sha256: `sha256:${'a'.repeat(64)}`
        },
        profileSha256: `sha256:${'b'.repeat(64)}`
    })
});

describe('v3.2 selected Freyd snake formal bridge', () => {
    it('reifies every selected snake equation', () => {
        const value = fixture();
        const checker = createCoreProofChecker(value.environment);
        checker.validateEnvironment();
        const universe = kernelUniverse(because('equation universe'));
        const claims = value.entries.map(([, entry]) =>
            entry.realization.claimType
        );
        claims.forEach(claim => checker.check(
            checker.rootContext,
            claim,
            universe
        ));
        assert.equal(
            claims.length,
            ALGEBRA_FORMAL_FREYD_SNAKE_PROFILE.exactEquationCount
        );
        assert.ok(claims.every(claim =>
            /bridge_eq/u.test(serializeCoreExpression(claim))
        ));
    });

    it('replays the native whole operation and adopts all equations', async () => {
        const value = fixture();
        const engine = createAlgebraPolynomialFreydSnakeEngine(
            value.bundle.model
        );
        for (const [goalId, entry] of value.entries) {
            const run = await runAlgebraFormalWorkflow({
                document: document(
                    goalId,
                    entry.realization.claimType,
                    value.environment
                ),
                goalId,
                adapter: entry.adapter as AlgebraFormalComputationAdapter<
                    typeof entry.realization,
                    unknown,
                    unknown
                >,
                realization: entry.realization,
                engine
            });
            assert.equal(run.result.interpretation.kind, 'claim');
            const adoption = trustAlgebraFormalWorkflow({
                run,
                assumptionName: `trusted_${goalId.replace(/-/gu, '_')}`,
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: `adopt selected ${goalId} equation`
                }
            });
            assert.equal(adoption.execution.state.status, 'complete');
        }
    });

    it('is deterministic and preserves the explicit capability boundary', () => {
        const first = fixture();
        const second = fixture();
        assert.equal(
            serializeAlgebraPolynomialFreydSnakeConnecting(first.selected),
            serializeAlgebraPolynomialFreydSnakeConnecting(second.selected)
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_SNAKE_PROFILE.claimsRingWideFormalCapability,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_SNAKE_PROFILE.claimsQuotientPathDecoding,
            false
        );
    });

    it('rejects a goal for a different selected equation', async () => {
        const value = fixture();
        const engine = createAlgebraPolynomialFreydSnakeEngine(
            value.bundle.model
        );
        const selected = value.entries[0][1];
        await assert.rejects(
            () => runAlgebraFormalWorkflow({
                document: document(
                    'wrong-snake-goal',
                    value.entries[1][1].realization.claimType,
                    value.environment
                ),
                goalId: 'wrong-snake-goal',
                adapter: selected.adapter as AlgebraFormalComputationAdapter<
                    typeof selected.realization,
                    unknown,
                    unknown
                >,
                realization: selected.realization,
                engine
            }),
            delegationError('INVALID_REALIZATION')
        );
    });

    it('passes one bounded live Lambdapi check for all equations', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_SNAKE !== '1'
    }, () => {
        const value = fixture();
        const universe = kernelUniverse(because('live equation universe'));
        const serialized = serializeCoreLfKernelProbe({
            environment: value.environment,
            externalFreeReferences: {
                ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
                ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS
            },
            assertions: value.entries.map(([, entry], index) => ({
                label: `Freyd snake selected equation ${index + 1}`,
                term: entry.realization.claimType,
                type: universe,
                span: sourceSpan(
                    'generated/proof-cas-freyd-snake.ts',
                    index + 1,
                    1,
                    index + 1,
                    2
                )
            }))
        });
        const probe = {
            ...serialized,
            source: serialized.source.replace(
                'require open emdash.emdash3_2;',
                'require open emdash.' +
                    'emdash3_2_commutative_algebra_' +
                    'freyd_snake_connecting;'
            )
        };
        const checked = checkLambdapiProbe(probe, {
            packageRoot: resolve(__dirname, '..', 'emdash2'),
            timeoutMs: 60_000
        });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics);
    });
});
