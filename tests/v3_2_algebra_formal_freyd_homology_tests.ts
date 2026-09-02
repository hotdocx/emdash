/** Focused proof–CAS replay of Freyd homology and induced-map equations. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    ALGEBRA_FORMAL_FREYD_HOMOLOGY_PROFILE,
    AlgebraFormalComputationAdapter,
    AlgebraFormalDelegationError,
    KernelExpression,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalFreydExactnessDelegationBundle,
    algebraFormalFreydHomologyDelegationBundle,
    algebraFormalFreydInducedHomologyDelegationBundle,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydChainPair,
    algebraPolynomialFreydCokernel,
    algebraPolynomialFreydExactnessAt,
    algebraPolynomialFreydHomologyAt,
    algebraPolynomialFreydHomologyChainMap,
    algebraPolynomialFreydInducedHomologyMap,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAlgebraPolynomialFreydHomologyEngine,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    kernelFree,
    kernelUniverse,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraPolynomialFreydHomologyAt,
    serializeAlgebraPolynomialFreydInducedHomologyMap,
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
    const one = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const morphism = (value: typeof x) =>
        algebraPolynomialPresentationMorphism({
            source: one,
            target: one,
            map: algebraPolynomialModuleMap(free, free, [
                algebraPolynomialModuleVector(free, [value])
            ])
        });
    const multiplicationX = morphism(x);
    const multiplicationY = morphism(y);
    const quotient = algebraPolynomialFreydCokernel(multiplicationX);
    const exactHomology = algebraPolynomialFreydHomologyAt(
        algebraPolynomialFreydChainPair(
            multiplicationX,
            quotient.projection
        )
    );
    const exactness = algebraPolynomialFreydExactnessAt(exactHomology);
    const zero = algebraPolynomialPresentationMorphismZero(one, one);
    const scalarHomology = algebraPolynomialFreydHomologyAt(
        algebraPolynomialFreydChainPair(zero, zero)
    );
    const chainMap = algebraPolynomialFreydHomologyChainMap({
        source: scalarHomology,
        target: scalarHomology,
        fNext: multiplicationY,
        f: multiplicationY,
        fPrev: multiplicationY
    });
    const induced = algebraPolynomialFreydInducedHomologyMap(chainMap);
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
    );
    const formalRing = kernelFree('formal_freyd_homology_R', because('ring'));
    const formalX = kernelFree('formal_freyd_homology_x', because('x'));
    const formalY = kernelFree('formal_freyd_homology_y', because('y'));
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
                    `formal_freyd_homology_coefficient_${suffix}`,
                    because('coefficient')
                );
                coefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const homologyBundle = algebraFormalFreydHomologyDelegationBundle({
        reifier,
        selected: exactHomology
    });
    const exactnessBundle = algebraFormalFreydExactnessDelegationBundle({
        reifier,
        selected: exactness
    });
    const inducedBundle = algebraFormalFreydInducedHomologyDelegationBundle({
        reifier,
        selected: induced
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
        ['chain', homologyBundle.chain],
        ['boundary', homologyBundle.boundary],
        ['boundary-reconstruction', homologyBundle.boundaryReconstruction],
        ['homology-projection', homologyBundle.projection],
        ['homology-annihilation', homologyBundle.annihilation],
        ['exactness', exactnessBundle.projectionZero],
        ['upper-square', inducedBundle.upperSquare],
        ['lower-square', inducedBundle.lowerSquare],
        ['cycles-map', inducedBundle.cyclesMap],
        ['cycles-reconstruction', inducedBundle.cyclesReconstruction],
        ['boundary-compatibility', inducedBundle.boundaryCompatibility],
        ['source-boundary-zero', inducedBundle.sourceBoundaryZero],
        ['induced-map', inducedBundle.homologyMap],
        ['induced-reconstruction', inducedBundle.homologyReconstruction]
    ] as const;
    return {
        exactHomology,
        scalarHomology,
        induced,
        homologyBundle,
        entries,
        reifier,
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
            sha256: `sha256:${'e'.repeat(64)}`
        },
        profileSha256: `sha256:${'f'.repeat(64)}`
    })
});

describe('v3.2 selected Freyd homology formal bridge', () => {
    it('reifies all fourteen homology and induced-map equations', () => {
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
        assert.equal(claims.length,
            ALGEBRA_FORMAL_FREYD_HOMOLOGY_PROFILE.exactEquationCount);
        assert.ok(claims.every(claim =>
            /bridge_eq/u.test(serializeCoreExpression(claim))
        ));
    });

    it('replays five actual operations and adopts every exact equation',
        async () => {
            const value = fixture();
            const engine = createAlgebraPolynomialFreydHomologyEngine(
                value.homologyBundle.model
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

    it('is deterministic and preserves the capability boundary', () => {
        const first = fixture();
        const second = fixture();
        assert.equal(
            serializeAlgebraPolynomialFreydHomologyAt(first.exactHomology),
            serializeAlgebraPolynomialFreydHomologyAt(second.exactHomology)
        );
        assert.equal(
            serializeAlgebraPolynomialFreydInducedHomologyMap(first.induced),
            serializeAlgebraPolynomialFreydInducedHomologyMap(second.induced)
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_HOMOLOGY_PROFILE
                .claimsRingWideFormalCapability,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_FREYD_HOMOLOGY_PROFILE.claimsQuotientPathDecoding,
            false
        );
        assert.throws(
            () => algebraFormalFreydExactnessDelegationBundle({
                reifier: first.reifier,
                selected: algebraPolynomialFreydExactnessAt(
                    first.scalarHomology
                )
            }),
            /positive witness/u
        );
    });

    it('rejects a goal for a different selected equation', async () => {
        const value = fixture();
        const engine = createAlgebraPolynomialFreydHomologyEngine(
            value.homologyBundle.model
        );
        const selected = value.entries[0][1];
        await assert.rejects(
            () => runAlgebraFormalWorkflow({
                document: document(
                    'wrong-homology-goal',
                    value.entries[1][1].realization.claimType,
                    value.environment
                ),
                goalId: 'wrong-homology-goal',
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

    it('passes one bounded live Lambdapi check for all fourteen equations', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_FREYD_HOMOLOGY !== '1'
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
                label: `Freyd homology selected equation ${index + 1}`,
                term: entry.realization.claimType,
                type: universe,
                span: sourceSpan(
                    'generated/proof-cas-freyd-homology.ts',
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
                    'freyd_functorial_homology;'
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
