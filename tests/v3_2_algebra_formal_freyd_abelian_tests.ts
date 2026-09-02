/** Focused proof–CAS replay of constructive polynomial Freyd normality. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    ALGEBRA_FORMAL_FREYD_ABELIAN_PROFILE,
    AlgebraFormalComputationAdapter,
    AlgebraFormalDelegationError,
    KernelExpression,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalFreydEpimorphismDelegationBundle,
    algebraFormalFreydImageDelegationBundle,
    algebraFormalFreydMonomorphismDelegationBundle,
    algebraFormalFreydNormalEpiDelegationBundle,
    algebraFormalFreydNormalMonoDelegationBundle,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydColiftAlongEpimorphism,
    algebraPolynomialFreydEpimorphismWitness,
    algebraPolynomialFreydImages,
    algebraPolynomialFreydLiftAlongMonomorphism,
    algebraPolynomialFreydMonomorphismWitness,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialMultiply,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAlgebraPolynomialFreydAbelianEngine,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    kernelFree,
    kernelUniverse,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraPolynomialFreydImageIsomorphism,
    serializeAlgebraPolynomialFreydNormalMonoLift,
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
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const free = algebraPolynomialFreeModule(ring, 1);
    const presentation = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const map = (value: typeof x) => algebraPolynomialModuleMap(
        free,
        free,
        [algebraPolynomialModuleVector(free, [value])]
    );
    const morphism = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: map(x)
    });
    const monoTest = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: map(algebraPolynomialMultiply(x, y))
    });
    const monomorphism = algebraPolynomialFreydMonomorphismWitness(morphism);
    const monoLift = algebraPolynomialFreydLiftAlongMonomorphism(
        monomorphism,
        monoTest
    );
    const quotient = algebraPolynomialFreydCokernel(morphism);
    const epimorphism = algebraPolynomialFreydEpimorphismWitness(
        quotient.projection
    );
    const epiColift = algebraPolynomialFreydColiftAlongEpimorphism(
        epimorphism,
        quotient.projection
    );
    const images = algebraPolynomialFreydImages(morphism);
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
    );
    const formalRing = kernelFree('formal_freyd_abelian_R', because('ring'));
    const formalX = kernelFree('formal_freyd_abelian_x', because('x'));
    const formalY = kernelFree('formal_freyd_abelian_y', because('y'));
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
                    `formal_freyd_abelian_coefficient_${suffix}`,
                    because('coefficient')
                );
                coefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const monomorphismBundle = algebraFormalFreydMonomorphismDelegationBundle({
        reifier,
        selected: monomorphism
    });
    const monoLiftBundle = algebraFormalFreydNormalMonoDelegationBundle({
        reifier,
        selected: monoLift
    });
    const epimorphismBundle = algebraFormalFreydEpimorphismDelegationBundle({
        reifier,
        selected: epimorphism
    });
    const epiColiftBundle = algebraFormalFreydNormalEpiDelegationBundle({
        reifier,
        selected: epiColift
    });
    const imageBundle = algebraFormalFreydImageDelegationBundle({
        reifier,
        selected: images
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
    const entries = [
        ['monomorphism-kernel-zero', monomorphismBundle.kernelZero],
        ['normal-mono-lift', monoLiftBundle.structural],
        ['normal-mono-reconstruction', monoLiftBundle.reconstruction],
        ['epimorphism-cokernel-zero', epimorphismBundle.cokernelZero],
        ['normal-epi-colift', epiColiftBundle.structural],
        ['normal-epi-reconstruction', epiColiftBundle.reconstruction],
        ['image-comparison', imageBundle.comparison],
        ['image-factorization', imageBundle.factorization],
        ['comparison-monic', imageBundle.comparisonMonic],
        ['comparison-epic', imageBundle.comparisonEpic],
        ['inverse-candidates', imageBundle.inverseCandidates],
        ['comparison-left-inverse', imageBundle.leftInverse],
        ['comparison-right-inverse', imageBundle.rightInverse]
    ] as const;
    return {
        monomorphism,
        monoLift,
        images,
        imageBundle,
        entries,
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
            sha256: `sha256:${'c'.repeat(64)}`
        },
        profileSha256: `sha256:${'d'.repeat(64)}`
    })
});

describe('v3.2 selected Freyd Abelian formal bridge', () => {
    it('reifies all thirteen normality and comparison equations', () => {
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
        assert.equal(claims.length, 13);
        assert.ok(claims.every(claim =>
            /bridge_eq/u.test(serializeCoreExpression(claim))
        ));
    });

    it('replays actual Abelian operations and adopts every exact claim',
        async () => {
            const value = fixture();
            const engine = createAlgebraPolynomialFreydAbelianEngine(
                value.imageBundle.model
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

    it('is deterministic and states the formal capability boundary', () => {
        const first = fixture();
        const second = fixture();
        assert.equal(
            serializeAlgebraPolynomialFreydNormalMonoLift(first.monoLift),
            serializeAlgebraPolynomialFreydNormalMonoLift(second.monoLift)
        );
        assert.equal(
            serializeAlgebraPolynomialFreydImageIsomorphism(first.images),
            serializeAlgebraPolynomialFreydImageIsomorphism(second.images)
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_ABELIAN_PROFILE.claimsRingWideFormalCapability,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_ABELIAN_PROFILE.claimsQuotientPathDecoding,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_ABELIAN_PROFILE.claimsPrimitiveIsomorphism,
            false
        );
    });

    it('rejects a goal for a different selected Abelian equation', async () => {
        const value = fixture();
        const engine = createAlgebraPolynomialFreydAbelianEngine(
            value.imageBundle.model
        );
        const selected = value.entries[0][1];
        const wrongTarget = value.entries[1][1].realization.claimType;
        await assert.rejects(
            () => runAlgebraFormalWorkflow({
                document: document('wrong-abelian-goal', wrongTarget,
                    value.environment),
                goalId: 'wrong-abelian-goal',
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

    it('passes one bounded live Lambdapi check for all thirteen equations', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_ABELIAN !== '1'
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
                label: `Freyd Abelian selected equation ${index + 1}`,
                term: entry.realization.claimType,
                type: universe,
                span: sourceSpan(
                    'generated/proof-cas-freyd-abelian.ts',
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
                    'emdash3_2_commutative_algebra_freyd_images;'
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
