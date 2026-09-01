/** Focused explicit-Core and proof-CAS weak-kernel equation bridge tests. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    KernelExpression,
    AFFINE_FORMAL_FINITE_MODULE_BINDINGS,
    AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
    AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraPolynomialAdd,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapWeakKernel,
    algebraPolynomialModuleVector,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialWeakKernelFactor,
    algebraPresentedAlgebra,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAlgebraPolynomialWeakKernelEngine,
    createCoreProofArtifactFingerprint,
    createCoreProofChecker,
    createFormalFiniteModuleProofEnvironment,
    defineAffineFormalPolynomialReifier,
    kernelFree,
    kernelUniverse,
    provenance,
    runAlgebraFormalWorkflow,
    serializeCoreLfKernelProbe,
    serializeCoreExpression,
    sourceSpan,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';
import {
    algebraFormalWeakKernelDelegationBundle,
    algebraFormalWeakKernelFactorizationDelegationBundle,
    defineAlgebraFormalWeakKernelFactorizationRealization,
    defineAlgebraFormalWeakKernelRealization
} from '../src/v3_2/algebra_formal_weak_kernel';

const because = (detail: string) => provenance('surface', detail);

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const source = algebraPolynomialFreeModule(ring, 3);
    const target = algebraPolynomialFreeModule(ring, 1);
    const map = algebraPolynomialModuleMap(source, target, [
        algebraPolynomialModuleVector(target, [x]),
        algebraPolynomialModuleVector(target, [y]),
        algebraPolynomialModuleVector(target, [algebraPolynomialAdd(x, y)])
    ]);
    const weakKernel = algebraPolynomialModuleMapWeakKernel(map);
    const factorization = algebraPolynomialWeakKernelFactor(
        weakKernel,
        weakKernel.morphism
    );
    const algebra = algebraPresentedAlgebra(
        algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
    );
    const formalRing = kernelFree('formal_weak_kernel_R', because('ring'));
    const formalX = kernelFree('formal_weak_kernel_x', because('x'));
    const formalY = kernelFree('formal_weak_kernel_y', because('y'));
    const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const reifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing,
        generatorTerms: [formalX, formalY],
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = coefficients.get(text);
            if (term === undefined) {
                term = kernelFree(
                    `formal_weak_kernel_coefficient_${text.replace('-', 'neg')}`,
                    because('coefficient')
                );
                coefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const annihilationRealization = defineAlgebraFormalWeakKernelRealization({
        reifier,
        selected: weakKernel
    });
    const factorizationRealization =
        defineAlgebraFormalWeakKernelFactorizationRealization({
            reifier,
            selected: factorization
        });
    const elementType = affineFormalRingElementType(formalRing);
    const environment = createFormalFiniteModuleProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        { name: formalX.name, type: elementType },
        { name: formalY.name, type: elementType },
        ...[...coefficients.values()].map(term => ({
            name: term.name,
            type: elementType
        }))
    ]);
    return {
        ring,
        map,
        weakKernel,
        factorization,
        reifier,
        environment,
        annihilationRealization,
        factorizationRealization
    };
};

const document = (
    goalId: string,
    target: KernelExpression,
    environment: ReturnType<typeof createFormalFiniteModuleProofEnvironment>
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
            sha256: `sha256:${'d'.repeat(64)}`
        },
        profileSha256: `sha256:${'e'.repeat(64)}`
    })
});

describe('v3.2 computational weak-kernel formal bridge', () => {
    it('reifies annihilation and selected lift reconstruction equations', () => {
        const value = fixture();
        const annihilation = value.annihilationRealization;
        const factorization = value.factorizationRealization;
        assert.match(
            serializeCoreExpression(annihilation.claimType),
            /bridge_CommRingMatrixCompositeZero/u
        );
        assert.match(
            serializeCoreExpression(factorization.claimType),
            /bridge_comm_ring_matrix_comp/u
        );
        assert.match(
            serializeCoreExpression(factorization.claimType),
            /bridge_eq/u
        );
        const checker = createCoreProofChecker(value.environment);
        checker.validateEnvironment();
        const universe = kernelUniverse(because('claim universe'));
        checker.check(checker.rootContext, annihilation.claimType, universe);
        checker.check(checker.rootContext, factorization.claimType, universe);
    });

    it('delegates and explicitly adopts both exact equations', async () => {
        const value = fixture();
        const annihilation = algebraFormalWeakKernelDelegationBundle({
            reifier: value.reifier,
            selected: value.weakKernel
        });
        const annihilationGoal = 'formal-weak-kernel-annihilation';
        const annihilationRun = await runAlgebraFormalWorkflow({
            document: document(
                annihilationGoal,
                annihilation.realization.claimType,
                value.environment
            ),
            goalId: annihilationGoal,
            adapter: annihilation.adapter,
            realization: annihilation.realization,
            engine: createAlgebraPolynomialWeakKernelEngine(annihilation.model)
        });
        assert.equal(annihilationRun.result.interpretation.kind, 'claim');
        const adoptedAnnihilation = trustAlgebraFormalWorkflow({
            run: annihilationRun,
            assumptionName: 'trusted_formal_weak_kernel_annihilation',
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: 'adopt selected weak-kernel annihilation equation'
            }
        });
        assert.equal(adoptedAnnihilation.execution.state.status, 'complete');

        const factor = algebraFormalWeakKernelFactorizationDelegationBundle({
            reifier: value.reifier,
            selected: value.factorization
        });
        const factorGoal = 'formal-weak-kernel-factor';
        const factorRun = await runAlgebraFormalWorkflow({
            document: document(
                factorGoal,
                factor.realization.claimType,
                value.environment
            ),
            goalId: factorGoal,
            adapter: factor.adapter,
            realization: factor.realization,
            engine: createAlgebraPolynomialWeakKernelEngine(factor.model)
        });
        assert.equal(factorRun.result.interpretation.kind, 'claim');
        const adoptedFactor = trustAlgebraFormalWorkflow({
            run: factorRun,
            assumptionName: 'trusted_formal_weak_kernel_factor',
            decision: {
                kind: 'trust-exact-algebra-computation',
                evidence: 'adopt selected weak-kernel reconstruction equation'
            }
        });
        assert.equal(adoptedFactor.execution.state.status, 'complete');
    });

    it('is deterministic and does not claim a ring-wide factor operation', () => {
        const value = fixture();
        const first = defineAlgebraFormalWeakKernelRealization({
            reifier: value.reifier,
            selected: value.weakKernel
        });
        const second = defineAlgebraFormalWeakKernelRealization({
            reifier: value.reifier,
            selected: value.weakKernel
        });
        assert.equal(
            serializeCoreExpression(first.claimType),
            serializeCoreExpression(second.claimType)
        );
        assert.match(
            serializeCoreExpression(first.formalObjectRank),
            /bridge_nat_/u
        );
        assert.equal(first.selected.claimsUniqueLifts, false);
    });

    it('passes bounded Lambdapi checking for both selected equations', {
        skip: process.env.EMDASH_RUN_PROOF_CAS_WEAK_KERNEL !== '1'
    }, () => {
        const value = fixture();
        const universe = kernelUniverse(because('claim universe'));
        const claims = [
            ['weak-kernel annihilation',
                value.annihilationRealization.claimType],
            ['weak-kernel selected lift',
                value.factorizationRealization.claimType]
        ] as const;
        const serialized = serializeCoreLfKernelProbe({
            environment: value.environment,
            externalFreeReferences: {
                ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS,
                ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS
            },
            assertions: claims.map(([label, term], index) => ({
                label,
                term,
                type: universe,
                span: sourceSpan(
                    'generated/proof-cas-weak-kernel.ts',
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
                'require open ' +
                    'emdash.emdash3_2_commutative_algebra_finite_modules;'
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
