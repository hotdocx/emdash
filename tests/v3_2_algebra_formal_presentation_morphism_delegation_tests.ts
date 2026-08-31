/** Focused proof–CAS delegation for presentation-map equations. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraFormalComputationAdapter,
    AlgebraFormalDelegationError,
    KernelExpression,
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalChainMapSquareDelegationBundle,
    algebraFormalPresentationAgreementDelegationBundle,
    algebraFormalPresentationMorphismDelegationBundle,
    algebraPolynomialChainMapSquare,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    algebraPresentedPolynomialModule,
    appendAlgebraFormalAssumption,
    coreProofPlanHole,
    createAlgebraFormalAssumptionSource,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    delegateAlgebraFormalPresentationMorphismEquations,
    kernelFree,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraFormalPresentationMorphismBatchResult,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPMAP proof–CAS equation delegation', () => {
    it('adopts map, agreement, and chain laws but not a failed map', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const source = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        );
        const target = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        );
        const stricterTarget = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [
                    algebraPolynomialMultiply(x, x)
                ])
            ])
        );
        const map = (polynomial: typeof x) => algebraPolynomialModuleMap(
            ambient,
            ambient,
            [algebraPolynomialModuleVector(ambient, [polynomial])]
        );
        const selectedMorphism = algebraPolynomialPresentationMorphism({
            source,
            target,
            map: map(y)
        });
        const selectedNegative = algebraPolynomialPresentationMorphism({
            source,
            target: stricterTarget,
            map: map(one)
        });
        const selectedAgreement =
            algebraPolynomialPresentationMorphismAgreement({
                source,
                target,
                left: map(x),
                right: map(zero)
            });
        const selectedChain = algebraPolynomialChainMapSquare({
            differentialSource: map(x),
            differentialTarget: map(x),
            componentPrevious: map(y),
            componentNow: map(y)
        });
        const algebra = algebraPresentedAlgebra(
            algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
        );
        const formalRing = kernelFree('formal_delegate_R', because('ring'));
        const formalX = kernelFree('formal_delegate_x', because('x'));
        const formalY = kernelFree('formal_delegate_y', because('y'));
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
                        `formal_delegate_coefficient_${suffix}`,
                        because('coefficient')
                    );
                    coefficients.set(text, term);
                }
                return term;
            },
            status: 'trusted-computation'
        });
        const morphism = algebraFormalPresentationMorphismDelegationBundle({
            reifier,
            selected: selectedMorphism
        });
        const negative = algebraFormalPresentationMorphismDelegationBundle({
            reifier,
            selected: selectedNegative
        });
        const agreement = algebraFormalPresentationAgreementDelegationBundle({
            reifier,
            selected: selectedAgreement
        });
        const chain = algebraFormalChainMapSquareDelegationBundle({
            reifier,
            selected: selectedChain
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
        let sourceEvidence = createAlgebraFormalAssumptionSource({
            moduleId: 'proof.cas.presentation-morphism.assumptions',
            sourceId: 'generated/presentation-morphism-assumptions.ts',
            baseEnvironment: environment
        });
        const document = (
            goalId: string,
            targetType: typeof morphism.realization.claimType
        ) => Object.freeze({
            moduleId: 'proof.cas.presentation-morphism',
            declarationId: goalId,
            environment: sourceEvidence.environment,
            type: targetType,
            plan: coreProofPlanHole(goalId, {
                provenance: because(`${goalId} hole`),
                expectation: { contextDepth: 0, target: targetType }
            }),
            provenance: because(`${goalId} root`),
            fingerprint: createCoreProofArtifactFingerprint({
                source: {
                    id: `tests/${goalId}.ts`,
                    sha256: `sha256:${goalId.includes('chain')
                        ? 'c'.repeat(64)
                        : goalId.includes('agreement')
                            ? 'b'.repeat(64)
                            : 'a'.repeat(64)}`
                },
                profileSha256: `sha256:${'d'.repeat(64)}`
            })
        });
        const engine = createAlgebraTypeScriptReferenceEngine({
            id: 'presentation-morphism-delegation-reference',
            revision: 'v1',
            implementations: morphism.operations.implementations
        });
        const adopt = async <R, I, O>(
            goalId: string,
            targetType: KernelExpression,
            adapter: AlgebraFormalComputationAdapter<R, I, O>,
            realization: R,
            assumptionName: string
        ) => {
            const run = await runAlgebraFormalWorkflow({
                document: document(goalId, targetType),
                goalId,
                adapter,
                realization,
                engine
            });
            const adoption = trustAlgebraFormalWorkflow({
                run,
                assumptionName,
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: `adopt exact equation ${goalId}`
                }
            });
            sourceEvidence = appendAlgebraFormalAssumption({
                source: sourceEvidence,
                adoption,
                classification: 'computed-equation'
            });
            return run;
        };
        const morphismRun = await adopt(
            'presentation-morphism-law',
            morphism.realization.claimType,
            morphism.adapter,
            morphism.realization,
            'presentation_morphism_law'
        );
        const agreementRun = await adopt(
            'presentation-agreement-law',
            agreement.realization.claimType,
            agreement.adapter,
            agreement.realization,
            'presentation_agreement_law'
        );
        const chainRun = await adopt(
            'presentation-chain-law',
            chain.realization.claimType,
            chain.adapter,
            chain.realization,
            'presentation_chain_law'
        );
        const negativeGoalId = 'presentation-morphism-negative';
        const negativeRun = await runAlgebraFormalWorkflow({
            document: document(negativeGoalId, negative.realization.claimType),
            goalId: negativeGoalId,
            adapter: negative.adapter,
            realization: negative.realization,
            engine
        });

        assert.equal(morphismRun.result.interpretation.kind, 'claim');
        assert.equal(agreementRun.result.interpretation.kind, 'claim');
        assert.equal(chainRun.result.interpretation.kind, 'claim');
        assert.equal(negativeRun.result.interpretation.kind, 'observation');
        assert.deepEqual(
            sourceEvidence.entries.map(entry => entry.declaration.name),
            [
                'presentation_morphism_law',
                'presentation_agreement_law',
                'presentation_chain_law'
            ]
        );
        assert.throws(
            () => trustAlgebraFormalWorkflow({
                run: negativeRun,
                assumptionName: 'invalid_negative_map_law',
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: 'negative observations are not adoptable'
                }
            }),
            error => {
                assert.ok(error instanceof AlgebraFormalDelegationError);
                assert.equal(error.code, 'NO_ADOPTABLE_CLAIM');
                return true;
            }
        );

        const batchSource = createAlgebraFormalAssumptionSource({
            moduleId: 'proof.cas.presentation-morphism.batch',
            sourceId: 'generated/presentation-morphism-batch.ts',
            baseEnvironment: environment
        });
        const batch = await delegateAlgebraFormalPresentationMorphismEquations({
            artifactId: 'presentation-batch',
            reifier,
            morphisms: [selectedMorphism],
            agreements: [selectedAgreement],
            chainSquares: [selectedChain],
            source: batchSource,
            fingerprint: goalId => createCoreProofArtifactFingerprint({
                source: {
                    id: `tests/${goalId}.ts`,
                    sha256: `sha256:${'e'.repeat(64)}`
                },
                profileSha256: `sha256:${'f'.repeat(64)}`
            }),
            decisionEvidence: goalId => `adopt batch equation ${goalId}`
        });
        assert.deepEqual(
            batch.source.entries.map(entry => entry.declaration.name),
            [
                'presentation_batch_morphism_0',
                'presentation_batch_agreement_0',
                'presentation_batch_chain_0'
            ]
        );
        const serialized =
            serializeAlgebraFormalPresentationMorphismBatchResult(batch);
        assert.equal(
            serialized,
            serializeAlgebraFormalPresentationMorphismBatchResult(batch)
        );
        assert.match(serialized, /bridge_comm_ring_matrix_sub/u);
    });
});
