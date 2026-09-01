/** Focused selected proof–CAS bridge for constructive Freyd universals. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    ALGEBRA_FORMAL_FREYD_PREABELIAN_PROFILE,
    AlgebraFormalComputationAdapter,
    KernelExpression,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalFreydCokernelColiftDelegationBundle,
    algebraFormalFreydCokernelDelegationBundle,
    algebraFormalFreydKernelDelegationBundle,
    algebraFormalFreydKernelLiftDelegationBundle,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernelColift,
    algebraPolynomialFreydKernel,
    algebraPolynomialFreydKernelLift,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAlgebraPolynomialFreydPreAbelianEngine,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    kernelFree,
    kernelUniverse,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraPolynomialFreydCokernel,
    serializeAlgebraPolynomialFreydKernel,
    serializeCoreExpression,
    serializeCoreLfKernelProbe,
    sourceSpan,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const zero = algebraPolynomialZero(ring);
    const sourceAmbient = algebraPolynomialFreeModule(ring, 2);
    const targetAmbient = algebraPolynomialFreeModule(ring, 1);
    const source = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(sourceAmbient, [])
    );
    const target = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(targetAmbient, [])
    );
    const morphism = algebraPolynomialModuleMap(sourceAmbient, targetAmbient, [
        algebraPolynomialModuleVector(targetAmbient, [x]),
        algebraPolynomialModuleVector(targetAmbient, [y])
    ]);
    const selectedMorphism = algebraPolynomialPresentationMorphism({
        source,
        target,
        map: morphism
    });
    const testAmbient = algebraPolynomialFreeModule(ring, 1);
    const testSource = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(testAmbient, [])
    );
    const test = algebraPolynomialPresentationMorphism({
        source: testSource,
        target: source,
        map: algebraPolynomialModuleMap(testAmbient, sourceAmbient, [
            algebraPolynomialModuleVector(sourceAmbient, [
                algebraPolynomialSubtract(zero, y),
                x
            ])
        ])
    });
    const kernel = algebraPolynomialFreydKernel(selectedMorphism);
    const kernelLift = algebraPolynomialFreydKernelLift(kernel, test);
    const cokernel = algebraPolynomialFreydCokernel(selectedMorphism);
    const cokernelColift = algebraPolynomialFreydCokernelColift(
        cokernel,
        cokernel.projection
    );
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
    );
    const formalRing = kernelFree('formal_freyd_preabelian_R', because('ring'));
    const formalX = kernelFree('formal_freyd_preabelian_x', because('x'));
    const formalY = kernelFree('formal_freyd_preabelian_y', because('y'));
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX, formalY],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(text);
            if (term === undefined) {
                const suffix = [...text].map(character =>
                    character.codePointAt(0)!.toString(16)
                ).join('_');
                term = kernelFree(
                    `formal_freyd_preabelian_coefficient_${suffix}`,
                    because('coefficient')
                );
                coefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const kernelBundle = algebraFormalFreydKernelDelegationBundle({
        reifier,
        selected: kernel
    });
    const kernelLiftBundle = algebraFormalFreydKernelLiftDelegationBundle({
        reifier,
        selected: kernelLift
    });
    const cokernelBundle = algebraFormalFreydCokernelDelegationBundle({
        reifier,
        selected: cokernel
    });
    const cokernelColiftBundle =
        algebraFormalFreydCokernelColiftDelegationBundle({
            reifier,
            selected: cokernelColift
        });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createFormalPresentationMorphismProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: elementType },
        { name: formalY.name, type: elementType },
        ...[...coefficients.values()].map(term => ({
            name: term.name,
            type: elementType
        }))
    ]);
    return {
        kernel,
        cokernel,
        kernelBundle,
        kernelLiftBundle,
        cokernelBundle,
        cokernelColiftBundle,
        environment
    };
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

describe('v3.2 selected Freyd pre-Abelian formal bridge', () => {
    it('reifies structural, annihilation, and reconstruction equations', () => {
        const value = fixture();
        const claims = [
            value.kernelBundle.structural.realization.claimType,
            value.kernelBundle.annihilation.realization.claimType,
            value.kernelLiftBundle.structural.realization.claimType,
            value.kernelLiftBundle.reconstruction.realization.claimType,
            value.cokernelBundle.structural.realization.claimType,
            value.cokernelBundle.annihilation.realization.claimType,
            value.cokernelColiftBundle.structural.realization.claimType,
            value.cokernelColiftBundle.reconstruction.realization.claimType
        ];
        const checker = createCoreProofChecker(value.environment);
        checker.validateEnvironment();
        const universe = kernelUniverse(because('equation universe'));
        claims.forEach(claim => checker.check(
            checker.rootContext,
            claim,
            universe
        ));
        assert.equal(claims.length, 8);
        assert.ok(claims.every(claim =>
            /bridge_eq/u.test(serializeCoreExpression(claim))
        ));
    });

    it('replays all four actual pre-Abelian operations and adopts eight claims',
        async () => {
            const value = fixture();
            const engine = createAlgebraPolynomialFreydPreAbelianEngine(
                value.kernelBundle.model
            );
            const entries = [
                ['kernel-embedding', value.kernelBundle.structural],
                ['kernel-annihilation', value.kernelBundle.annihilation],
                ['kernel-lift', value.kernelLiftBundle.structural],
                ['kernel-reconstruction', value.kernelLiftBundle.reconstruction],
                ['cokernel-projection', value.cokernelBundle.structural],
                ['cokernel-annihilation', value.cokernelBundle.annihilation],
                ['cokernel-colift', value.cokernelColiftBundle.structural],
                ['cokernel-reconstruction',
                    value.cokernelColiftBundle.reconstruction]
            ] as const;
            for (const [goalId, entry] of entries) {
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

    it('is deterministic and does not claim a closed ring-wide capability', () => {
        const first = fixture();
        const second = fixture();
        assert.equal(
            serializeAlgebraPolynomialFreydKernel(first.kernel),
            serializeAlgebraPolynomialFreydKernel(second.kernel)
        );
        assert.equal(
            serializeAlgebraPolynomialFreydCokernel(first.cokernel),
            serializeAlgebraPolynomialFreydCokernel(second.cokernel)
        );
        assert.equal(
            serializeCoreExpression(
                first.kernelBundle.annihilation.realization.claimType
            ),
            serializeCoreExpression(
                second.kernelBundle.annihilation.realization.claimType
            )
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_PREABELIAN_PROFILE
                .claimsRingWideFormalCapability,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_PREABELIAN_PROFILE
                .claimsQuotientPathDecoding,
            false
        );
    });

    it('passes one bounded live Lambdapi check for all eight equations', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_PREABELIAN !== '1'
    }, () => {
        const value = fixture();
        const claims = [
            value.kernelBundle.structural.realization.claimType,
            value.kernelBundle.annihilation.realization.claimType,
            value.kernelLiftBundle.structural.realization.claimType,
            value.kernelLiftBundle.reconstruction.realization.claimType,
            value.cokernelBundle.structural.realization.claimType,
            value.cokernelBundle.annihilation.realization.claimType,
            value.cokernelColiftBundle.structural.realization.claimType,
            value.cokernelColiftBundle.reconstruction.realization.claimType
        ];
        const universe = kernelUniverse(because('live equation universe'));
        const serialized = serializeCoreLfKernelProbe({
            environment: value.environment,
            externalFreeReferences: {
                ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
                ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS
            },
            assertions: claims.map((term, index) => ({
                label: `Freyd pre-Abelian selected equation ${index + 1}`,
                term,
                type: universe,
                span: sourceSpan(
                    'generated/proof-cas-freyd-preabelian.ts',
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
                    'freyd_witnessed_preabelian;'
            )
        };
        const checked = checkLambdapiProbe(probe, {
            packageRoot: resolve(__dirname, '..', 'emdash2'),
            // The TypeScript probe API currently caps one child at 60 seconds;
            // the surrounding repository command remains bounded at 90.
            timeoutMs: 60_000
        });
        assert.equal(checked.timedOut, false, checked.diagnostics);
        assert.equal(checked.accepted, true, checked.diagnostics);
    });
});
