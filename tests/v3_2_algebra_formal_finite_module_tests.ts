/** Focused formal finite-module reification tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalModuleMembershipBundle,
    algebraFormalCompositeZeroClaimType,
    algebraFormalSyzygyClaimType,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleGroebnerBasis,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleSchreyerSyzygies,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialSubmodule,
    algebraPolynomialZero,
    algebraPresentedPolynomialModule,
    algebraPolynomialSchreyerResolution,
    algebraPresentedAlgebra,
    createAlgebraTypeScriptReferenceEngine,
    createAlgebraFormalAssumptionSource,
    createCoreProofArtifactFingerprint,
    createFormalFiniteModuleProofEnvironment,
    coreProofPlanHole,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalModuleMembershipRealization,
    delegateAlgebraFormalFiniteModuleEquations,
    computeAlgebraOperation,
    kernelFree,
    provenance,
    runAlgebraFormalWorkflow,
    serializeCoreExpression,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPM-REIFY membership representation', () => {
    it('reifies a selected one-generator module membership equation',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const module = algebraPolynomialFreeModule(ring, 1);
            const generator = algebraPolynomialModuleVector(module, [x]);
            const basis = algebraPolynomialModuleGroebnerBasis(
                algebraPolynomialSubmodule(module, [generator])
            );
            const selected = algebraPolynomialModuleMembership(generator, basis);
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const formalRing = kernelFree('formal_module_R', because('ring'));
            const formalX = kernelFree('formal_module_x', because('x'));
            const coefficientTerms = new Map<string, ReturnType<typeof kernelFree>>();
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [formalX],
                coefficientReifier: coefficient => {
                    const text = RATIONAL_DOMAIN.text(coefficient);
                    let term = coefficientTerms.get(text);
                    if (term === undefined) {
                        term = kernelFree(
                            `formal_module_coefficient_${text.replace('-', 'neg')}`,
                            because('coefficient')
                        );
                        coefficientTerms.set(text, term);
                    }
                    return term;
                },
                status: 'trusted-computation'
            });
            const realization = defineAlgebraFormalModuleMembershipRealization({
                reifier,
                vector: generator,
                basis,
                selected
            });
            const negative = algebraPolynomialModuleVector(module, [
                algebraPolynomialOne(ring)
            ]);
            const negativeSelected = algebraPolynomialModuleMembership(
                negative,
                basis
            );
            const negativeRealization =
                defineAlgebraFormalModuleMembershipRealization({
                    reifier,
                    vector: negative,
                    basis,
                    selected: negativeSelected
                });
            const core = serializeCoreExpression(realization.claimType);
            assert.match(core, /bridge_comm_ring_matrix_apply/u);
            assert.match(core, /bridge_FiniteFamily/u);
            assert.equal(selected.member, true);

            const bundle = algebraFormalModuleMembershipBundle(generator);
            const engine = createAlgebraTypeScriptReferenceEngine({
                implementations: bundle.implementations
            });
            const computed = await computeAlgebraOperation({
                engine,
                operation: bundle.operation,
                input: realization.input
            });
            assert.equal(computed.value.member, true);

            const elementType = affineFormalRingElementType(formalRing);
            const environment = createFormalFiniteModuleProofEnvironment([
                { name: formalRing.name, type: affineFormalCommRingType() },
                { name: formalX.name, type: elementType },
                ...[...coefficientTerms.values()].map(term => ({
                    name: term.name,
                    type: elementType
                }))
            ]);
            const goalId = 'formal-module-membership';
            const document = Object.freeze({
                moduleId: 'proof.cas.formal-module',
                declarationId: goalId,
                environment,
                type: realization.claimType,
                plan: coreProofPlanHole(goalId, {
                    provenance: because('membership hole'),
                    expectation: {
                        contextDepth: 0,
                        target: realization.claimType
                    }
                }),
                provenance: because('membership root'),
                fingerprint: createCoreProofArtifactFingerprint({
                    source: {
                        id: 'tests/formal-module-membership.ts',
                        sha256: `sha256:${'8'.repeat(64)}`
                    },
                    profileSha256: `sha256:${'9'.repeat(64)}`
                })
            });
            const run = await runAlgebraFormalWorkflow({
                document,
                goalId,
                adapter: bundle.adapter,
                realization,
                engine
            });
            const adopted = trustAlgebraFormalWorkflow({
                run,
                assumptionName: 'trusted_formal_module_membership',
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: 'adopt selected module membership equation'
                }
            });
            assert.equal(run.result.interpretation.kind, 'claim');
            assert.equal(adopted.execution.state.status, 'complete');

            const negativeGoalId = 'formal-module-nonmembership';
            const negativeDocument = Object.freeze({
                ...document,
                declarationId: negativeGoalId,
                type: negativeRealization.claimType,
                plan: coreProofPlanHole(negativeGoalId, {
                    provenance: because('nonmembership hole'),
                    expectation: {
                        contextDepth: 0,
                        target: negativeRealization.claimType
                    }
                })
            });
            const negativeRun = await runAlgebraFormalWorkflow({
                document: negativeDocument,
                goalId: negativeGoalId,
                adapter: bundle.adapter,
                realization: negativeRealization,
                engine
            });
            assert.equal(negativeSelected.member, false);
            assert.equal(negativeRun.result.interpretation.kind, 'observation');
            assert.equal(
                negativeSelected.remainder.components[0].terms.length > 0,
                true
            );
        }
    );

    it('delegates and adopts Schreyer syzygy and resolution equations',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const zero = algebraPolynomialZero(ring);
            const ambient = algebraPolynomialFreeModule(
                ring,
                2,
                'position-over-term'
            );
            const relations = algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x, y]),
                algebraPolynomialModuleVector(ambient, [y, zero])
            ]);
            const basis = algebraPolynomialModuleGroebnerBasis(relations);
            const syzygies = algebraPolynomialModuleSchreyerSyzygies(basis);
            const algebra = algebraPresentedAlgebra(
                algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
            );
            const formalRing = kernelFree('formal_resolution_R', because('ring'));
            const formalX = kernelFree('formal_resolution_x', because('x'));
            const formalY = kernelFree('formal_resolution_y', because('y'));
            const coefficientTerms = new Map<string, ReturnType<typeof kernelFree>>();
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [formalX, formalY],
                coefficientReifier: coefficient => {
                    const text = RATIONAL_DOMAIN.text(coefficient);
                    let term = coefficientTerms.get(text);
                    if (term === undefined) {
                        const suffix = [...text].map(character =>
                            character.codePointAt(0)!.toString(16)
                        ).join('_');
                        term = kernelFree(
                            `formal_resolution_coefficient_${suffix}`,
                            because('coefficient')
                        );
                        coefficientTerms.set(text, term);
                    }
                    return term;
                },
                status: 'trusted-computation'
            });
            const syzygyClaim = algebraFormalSyzygyClaimType({
                reifier,
                generators: basis.basis,
                syzygy: syzygies.generators[0]
            });
            assert.match(
                serializeCoreExpression(syzygyClaim),
                /bridge_CommRingMatrixSyzygy/u
            );

            const resolution = algebraPolynomialSchreyerResolution(
                algebraPresentedPolynomialModule(relations),
                4
            );
            const compositeClaim = algebraFormalCompositeZeroClaimType({
                reifier,
                left: resolution.differentials[0],
                right: resolution.differentials[1]
            });
            assert.match(
                serializeCoreExpression(compositeClaim),
                /bridge_CommRingMatrixCompositeZero/u
            );
            assert.equal(resolution.complete, true);
            assert.equal(resolution.length, 2);

            const elementType = affineFormalRingElementType(formalRing);
            const environment = createFormalFiniteModuleProofEnvironment([
                { name: formalRing.name, type: affineFormalCommRingType() },
                { name: formalX.name, type: elementType },
                { name: formalY.name, type: elementType },
                ...[...coefficientTerms.values()].map(term => ({
                    name: term.name,
                    type: elementType
                }))
            ]);
            const source = createAlgebraFormalAssumptionSource({
                moduleId: 'proof.cas.formal-resolution.assumptions',
                sourceId: 'generated/formal-resolution-assumptions.ts',
                baseEnvironment: environment
            });
            const delegated = await delegateAlgebraFormalFiniteModuleEquations({
                artifactId: 'formal-resolution',
                reifier,
                basis,
                selectedSyzygies: syzygies,
                relations,
                maximumLength: 4,
                selectedResolution: resolution,
                source,
                fingerprint: goalId => createCoreProofArtifactFingerprint({
                    source: {
                        id: `tests/${goalId}.ts`,
                        sha256: `sha256:${goalId.includes('syzygy')
                            ? 'a'.repeat(64)
                            : 'b'.repeat(64)}`
                    },
                    profileSha256: `sha256:${'c'.repeat(64)}`
                }),
                decisionEvidence: goalId => `adopt exact equation ${goalId}`
            });
            assert.equal(delegated.syzygies.length, 1);
            assert.equal(delegated.composites.length, 1);
            assert.deepEqual(
                delegated.source.entries.map(entry => entry.declaration.name),
                [
                    'formal_resolution_syzygy_0',
                    'formal_resolution_composite_0'
                ]
            );
        }
    );
});
