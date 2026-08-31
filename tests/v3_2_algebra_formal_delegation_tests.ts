/** Focused proof–CAS delegation contract and execution tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_FORMAL_DELEGATION_PROFILE,
    ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE,
    ALGEBRA_FORMAL_ADOPTION_PROFILE,
    ALGEBRA_FORMAL_WORKFLOW_PROFILE,
    AlgebraComputed,
    AlgebraFormalComputationGoal,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    AlgebraFormalTrustedAdoptionDecision,
    CoreLfDeclarationEnvironment,
    algebraAlgorithmIdentity,
    algebraReferenceExecutionResult,
    adoptAlgebraFormalCheckedPlan,
    adoptAlgebraFormalTrustedComputation,
    binderMode,
    coreProofPlanHole,
    coreProofPlanExact,
    createAlgebraFormalComputationRequest,
    createAlgebraFormalWorkflowReceipt,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    checkAlgebraFormalComputationData,
    checkAlgebraFormalWorkflow,
    defineAlgebraFormalComputationAdapter,
    defineAlgebraFormalComputationGoal,
    defineAlgebraOperation,
    defineAlgebraReferenceImplementation,
    defineAlgebraRuntimeSchema,
    executeAlgebraFormalComputationRequest,
    kernelBound,
    kernelFree,
    kernelUniverse,
    normalizeAlgebraFormalComputationInterpretation,
    provenance,
    serializeAlgebraFormalComputationRequest,
    serializeAlgebraFormalComputationResult,
    serializeAlgebraFormalTrustedAdoptionArtifact,
    reuseAlgebraFormalWorkflowResult,
    runAlgebraFormalWorkflow,
    serializeAlgebraFormalWorkflowReceipt,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);
const mode = binderMode('explicit', 'functorial');

const delegationError = (
    code: AlgebraFormalDelegationError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraFormalDelegationError);
    assert.equal(error.code, code);
    assert.ok(error.path.length > 0);
    return true;
};

const proofGoal = (withCheckedWitness = false) => {
    const declaration = because('formal computation proposition');
    const environment = CoreLfDeclarationEnvironment.empty().extend({
        name: 'ComputationClaim',
        type: kernelUniverse(declaration),
        mode,
        provenance: declaration
    });
    const target = kernelFree('ComputationClaim', because('goal target'));
    const checkedEnvironment = withCheckedWitness
        ? environment.extend({
            name: 'checked_computation_witness',
            type: target,
            mode,
            provenance: because('checked computation witness')
        })
        : environment;
    const fingerprint = createCoreProofArtifactFingerprint({
        source: {
            id: 'tests/fixtures/formal-computation.surface.ts',
            sha256: `sha256:${'a'.repeat(64)}`
        },
        profileSha256: `sha256:${'b'.repeat(64)}`
    });
    const document = Object.freeze({
        moduleId: 'proof.cas.fixture',
        declarationId: 'delegated_claim',
        environment: checkedEnvironment,
        type: target,
        plan: coreProofPlanHole('delegated-goal', {
            provenance: because('delegated root hole'),
            expectation: {
                contextDepth: 0,
                target
            }
        }),
        provenance: because('delegated proof root'),
        fingerprint
    });
    return {
        environment: checkedEnvironment,
        target,
        document,
        goal: defineAlgebraFormalComputationGoal({
            document,
            goalId: 'delegated-goal'
        })
    };
};

const operationFixture = (
    quality: 'exact' | 'heuristic' = 'exact',
    withAssumption = false
) => {
    const numberSchema = defineAlgebraRuntimeSchema<number>({
        id: 'proof-cas.number',
        revision: 'v1',
        normalize(value, path) {
            if (typeof value !== 'number' || !Number.isSafeInteger(value)) {
                throw new Error(`safe integer expected at ${path}`);
            }
            return value;
        }
    });
    const operation = defineAlgebraOperation({
        id: 'proof-cas.successor',
        revision: 'v1',
        input: numberSchema,
        output: numberSchema
    });
    const algorithm = algebraAlgorithmIdentity(
        'proof-cas.successor.reference',
        'v1'
    );
    const implementation = defineAlgebraReferenceImplementation({
        operation,
        algorithm,
        execute: (value, context) => {
            if (context.cancellation?.requested()) {
                throw new Error(
                    context.cancellation.reason?.() ?? 'cancelled'
                );
            }
            context.onProgress?.({
                phase: 'successor',
                completed: 1,
                total: 1
            });
            return algebraReferenceExecutionResult({
                value: value + 1,
                quality,
                ...(withAssumption
                    ? {
                        assumptions: [{
                            id: 'fixture.assumption',
                            detail: 'focused assumption-bearing result'
                        }]
                    }
                    : {})
            });
        }
    });
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: 'proof-cas.reference',
        revision: 'v1',
        implementations: [implementation]
    });
    return { numberSchema, operation, algorithm, engine };
};

interface NumberRealization {
    readonly id: string;
    readonly value: number;
}

const adapterFixture = (
    changed: Partial<{
        normalizeRealization: (value: unknown, path: string) => NumberRealization;
        serializeRealization: (value: NumberRealization) => string;
        acquire: (goal: ReturnType<typeof proofGoal>['goal'], value: NumberRealization) => unknown;
        serializeInput: (value: number) => string;
        serializeOutput: (value: number) => string;
        interpret: (input: {
            readonly goal: AlgebraFormalComputationGoal;
            readonly realization: NumberRealization;
            readonly operationInput: number;
            readonly computed: AlgebraComputed<number>;
        }) => AlgebraFormalComputationInterpretationInput;
    }> = {},
    quality: 'exact' | 'heuristic' = 'exact',
    withAssumption = false
) => {
    const { operation, algorithm, engine } = operationFixture(
        quality,
        withAssumption
    );
    const normalizeRealization = changed.normalizeRealization ??
        ((value: unknown, path: string): NumberRealization => {
            if (
                value === null ||
                typeof value !== 'object' ||
                (value as NumberRealization).id !== 'fixture-realization' ||
                !Number.isSafeInteger((value as NumberRealization).value)
            ) {
                throw new Error(`number realization expected at ${path}`);
            }
            return Object.freeze({
                id: (value as NumberRealization).id,
                value: (value as NumberRealization).value
            });
        });
    const adapter = defineAlgebraFormalComputationAdapter({
        id: 'proof-cas.successor-adapter',
        revision: 'v1',
        operation,
        normalizeRealization,
        serializeRealization: changed.serializeRealization ??
            (value => `${JSON.stringify(value)}\n`),
        acquire: changed.acquire ?? ((_goal, value) => value.value),
        serializeInput: changed.serializeInput ?? (value => `${value}\n`),
        serializeOutput: changed.serializeOutput ?? (value => `${value}\n`),
        interpret: changed.interpret ?? (({ goal, computed }) =>
            computed.value > 0
            ? {
                kind: 'claim',
                summary: 'successor computation is positive',
                claimType: goal.target
            }
            : {
                kind: 'observation',
                summary: 'successor computation is not positive'
            })
    });
    return { adapter, algorithm, engine };
};

const realization = (): NumberRealization => Object.freeze({
    id: 'fixture-realization',
    value: 4
});

const exactResult = async (
    fixture = proofGoal(),
    changed: Parameters<typeof adapterFixture>[0] = {},
    withAssumption = false
) => {
    const { adapter, engine } = adapterFixture(
        changed,
        'exact',
        withAssumption
    );
    const request = createAlgebraFormalComputationRequest({
        adapter,
        goal: fixture.goal,
        realization: realization(),
        engine
    });
    return executeAlgebraFormalComputationRequest(request);
};

describe('PCD-CONTRACT-2A proof–CAS delegation contracts', () => {
    it('selects one exact closed root goal and serializes payload-bound input',
        () => {
            const { goal, target } = proofGoal();
            const { adapter, algorithm, engine } = adapterFixture();
            const request = createAlgebraFormalComputationRequest({
                adapter,
                goal,
                realization: realization(),
                engine,
                algorithm,
                limits: { fuel: 12, maximumOutputItems: 3 }
            });
            const serialized = serializeAlgebraFormalComputationRequest(request);

            assert.equal(goal.contextDepth, 0);
            assert.equal(goal.goalId, 'delegated-goal');
            assert.equal(goal.target, target);
            assert.equal(goal.sourceArtifact.state.status, 'incomplete');
            assert.equal(request.operationInput, 4);
            assert.equal(request.operationInputData, '4\n');
            assert.equal(request.realizationData,
                '{"id":"fixture-realization","value":4}\n');
            assert.match(serialized, /proof-cas\.successor-adapter/u);
            assert.match(serialized, /operationInputData/u);
            assert.match(serialized, /fixture-realization/u);
            assert.match(serialized, /delegated-goal/u);
            assert.equal(
                serialized,
                serializeAlgebraFormalComputationRequest(request)
            );
            assert.equal(Object.isFrozen(goal), true);
            assert.equal(Object.isFrozen(request), true);
        }
    );

    it('rejects nested, unannotated, and target-drifting source goals', () => {
        const fixture = proofGoal();
        const nested = {
            ...fixture.document,
            plan: {
                tag: 'intro' as const,
                provenance: because('unsupported nested plan'),
                body: fixture.document.plan
            }
        };
        assert.throws(
            () => defineAlgebraFormalComputationGoal({
                document: nested,
                goalId: 'delegated-goal'
            }),
            delegationError('UNSUPPORTED_GOAL')
        );
        assert.throws(
            () => defineAlgebraFormalComputationGoal({
                document: {
                    ...fixture.document,
                    plan: coreProofPlanHole('delegated-goal', {
                        provenance: because('unannotated hole')
                    })
                },
                goalId: 'delegated-goal'
            }),
            delegationError('UNSUPPORTED_GOAL')
        );
        assert.throws(
            () => defineAlgebraFormalComputationGoal({
                document: {
                    ...fixture.document,
                    plan: coreProofPlanHole('delegated-goal', {
                        provenance: because('drifting hole'),
                        expectation: {
                            contextDepth: 0,
                            target: kernelUniverse(because('wrong target'))
                        }
                    })
                },
                goalId: 'delegated-goal'
            }),
            delegationError('UNSUPPORTED_GOAL')
        );
    });

    it('rejects nondeterministic realization, acquisition, and serialization',
        () => {
            const { goal } = proofGoal();
            let normalization = 0;
            const normalized = adapterFixture({
                normalizeRealization: () => Object.freeze({
                    id: 'fixture-realization',
                    value: ++normalization
                })
            });
            assert.throws(
                () => createAlgebraFormalComputationRequest({
                    adapter: normalized.adapter,
                    goal,
                    realization: realization(),
                    engine: normalized.engine
                }),
                delegationError('NONDETERMINISTIC_REALIZATION')
            );

            let acquisition = 0;
            const acquired = adapterFixture({
                acquire: () => ++acquisition
            });
            assert.throws(
                () => createAlgebraFormalComputationRequest({
                    adapter: acquired.adapter,
                    goal,
                    realization: realization(),
                    engine: acquired.engine
                }),
                delegationError('NONDETERMINISTIC_ACQUISITION')
            );

            let serialization = 0;
            const serialized = adapterFixture({
                serializeInput: value => `${value}:${++serialization}\n`
            });
            assert.throws(
                () => createAlgebraFormalComputationRequest({
                    adapter: serialized.adapter,
                    goal,
                    realization: realization(),
                    engine: serialized.engine
                }),
                delegationError('NONDETERMINISTIC_ENCODING')
            );
        }
    );

    it('normalizes exact claims and non-adoptable observations separately',
        () => {
            const { goal, target } = proofGoal();
            const datumType = kernelUniverse(because('datum type'));
            const datumTerm = kernelFree('ComputationClaim',
                because('datum term'));
            const claim = normalizeAlgebraFormalComputationInterpretation(
                goal,
                {
                    kind: 'claim',
                    summary: ' exact computed claim ',
                    claimType: target,
                    data: [{
                        id: 'computed-value',
                        type: datumType,
                        term: datumTerm
                    }]
                }
            );
            const observation =
                normalizeAlgebraFormalComputationInterpretation(goal, {
                    kind: 'observation',
                    summary: 'negative result retained'
                });

            assert.equal(claim.kind, 'claim');
            assert.equal(claim.claimType, target);
            assert.equal(claim.data.length, 1);
            assert.equal(observation.kind, 'observation');
            assert.equal(observation.data.length, 0);
            assert.equal(Object.isFrozen(claim.data), true);
            assert.equal(
                claim.profileRevision,
                ALGEBRA_FORMAL_DELEGATION_PROFILE.interpretationRevision
            );
        }
    );

    it('rejects claim drift, duplicate data, and open Core data', () => {
        const { goal } = proofGoal();
        assert.throws(
            () => normalizeAlgebraFormalComputationInterpretation(goal, {
                kind: 'claim',
                summary: 'wrong claim',
                claimType: kernelUniverse(because('wrong claim type'))
            }),
            delegationError('CLAIM_TARGET_MISMATCH')
        );
        const datum = {
            id: 'duplicate',
            type: kernelUniverse(because('datum type')),
            term: kernelFree('ComputationClaim', because('datum'))
        };
        assert.throws(
            () => normalizeAlgebraFormalComputationInterpretation(goal, {
                kind: 'observation',
                summary: 'duplicate data',
                data: [datum, datum]
            }),
            delegationError('INVALID_INTERPRETATION')
        );
        assert.throws(
            () => normalizeAlgebraFormalComputationInterpretation(goal, {
                kind: 'observation',
                summary: 'open data',
                data: [{
                    id: 'open',
                    type: kernelUniverse(because('open type')),
                    term: kernelBound(0, because('open term'))
                }]
            }),
            delegationError('INVALID_CORE_DATA')
        );
    });

    it('publishes an inert non-kernel non-execution profile', () => {
        assert.equal(ALGEBRA_FORMAL_DELEGATION_PROFILE.addsCoreOwner, false);
        assert.equal(ALGEBRA_FORMAL_DELEGATION_PROFILE.addsProofPlanTag, false);
        assert.equal(
            ALGEBRA_FORMAL_DELEGATION_PROFILE.performsComputation,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_DELEGATION_PROFILE.goalBoundary,
            'closed-depth-zero-root-hole'
        );
        assert.equal(Object.isFrozen(ALGEBRA_FORMAL_DELEGATION_PROFILE), true);
    });
});

describe('PCD-DELEGATE-3A exact execution and observation', () => {
    it('executes once, retains progress and whole exact interpretation',
        async () => {
            const { goal } = proofGoal();
            const { adapter, algorithm, engine } = adapterFixture();
            const request = createAlgebraFormalComputationRequest({
                adapter,
                goal,
                realization: realization(),
                engine,
                algorithm,
                limits: { fuel: 4 }
            });
            const progress: string[] = [];
            const result = await executeAlgebraFormalComputationRequest(
                request,
                {
                    onProgress: event => progress.push(event.phase)
                }
            );
            const serialized = serializeAlgebraFormalComputationResult(result);

            assert.equal(result.computed.value, 5);
            assert.equal(result.computed.quality, 'exact');
            assert.equal(result.outputData, '5\n');
            assert.equal(result.interpretation.kind, 'claim');
            assert.deepEqual(progress, [
                'proof-cas.successor',
                'successor',
                'proof-cas.successor'
            ]);
            assert.match(serialized, /successor computation is positive/u);
            assert.match(serialized, /operationInputData/u);
            assert.equal(
                serialized,
                serializeAlgebraFormalComputationResult(result)
            );
            assert.equal(Object.isFrozen(result), true);
        }
    );

    it('retains an exact negative observation without an adoptable claim',
        async () => {
            const { goal } = proofGoal();
            const { adapter, engine } = adapterFixture();
            const request = createAlgebraFormalComputationRequest({
                adapter,
                goal,
                realization: Object.freeze({
                    id: 'fixture-realization',
                    value: -3
                }),
                engine
            });
            const result = await executeAlgebraFormalComputationRequest(request);

            assert.equal(result.computed.value, -2);
            assert.equal(result.interpretation.kind, 'observation');
            assert.equal('claimType' in result.interpretation, false);
        }
    );

    it('propagates runtime cancellation without changing proof source',
        async () => {
            const fixture = proofGoal();
            const { adapter, engine } = adapterFixture();
            const request = createAlgebraFormalComputationRequest({
                adapter,
                goal: fixture.goal,
                realization: realization(),
                engine
            });

            await assert.rejects(
                executeAlgebraFormalComputationRequest(request, {
                    cancellation: {
                        requested: () => true,
                        reason: () => 'focused cancellation'
                    }
                }),
                delegationError('EXECUTION_FAILED')
            );
            assert.equal(fixture.document.plan.tag, 'hole');
        }
    );

    it('rejects heuristic output and nondeterministic result surfaces',
        async () => {
            const { goal } = proofGoal();
            const heuristic = adapterFixture({}, 'heuristic');
            await assert.rejects(
                executeAlgebraFormalComputationRequest(
                    createAlgebraFormalComputationRequest({
                        adapter: heuristic.adapter,
                        goal,
                        realization: realization(),
                        engine: heuristic.engine
                    })
                ),
                delegationError('UNSUPPORTED_RESULT_QUALITY')
            );

            let outputSerial = 0;
            const output = adapterFixture({
                serializeOutput: value => `${value}:${++outputSerial}\n`
            });
            await assert.rejects(
                executeAlgebraFormalComputationRequest(
                    createAlgebraFormalComputationRequest({
                        adapter: output.adapter,
                        goal,
                        realization: realization(),
                        engine: output.engine
                    })
                ),
                delegationError('NONDETERMINISTIC_ENCODING')
            );

            let interpreted = 0;
            const interpretation = adapterFixture({
                interpret: ({ goal: selectedGoal }) => ({
                    kind: 'claim',
                    summary: `interpretation ${++interpreted}`,
                    claimType: selectedGoal.target
                })
            });
            await assert.rejects(
                executeAlgebraFormalComputationRequest(
                    createAlgebraFormalComputationRequest({
                        adapter: interpretation.adapter,
                        goal,
                        realization: realization(),
                        engine: interpretation.engine
                    })
                ),
                delegationError('NONDETERMINISTIC_INTERPRETATION')
            );
        }
    );

    it('keeps execution outside proof plans, workspaces, and Core', () => {
        assert.equal(
            ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.mutatesProofPlan,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.mutatesWorkspace,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE.acceptedQuality,
            'exact'
        );
        assert.equal(
            Object.isFrozen(ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE),
            true
        );
    });
});

describe('PCD-ADOPT-4A explicit checked and trusted adoption', () => {
    it('checks reified data in the original declaration environment',
        async () => {
            const fixture = proofGoal(true);
            const result = await exactResult(fixture, {
                interpret: ({ goal }) => ({
                    kind: 'claim',
                    summary: 'claim with checked explicit data',
                    claimType: goal.target,
                    data: [{
                        id: 'claim-classifier',
                        type: goal.target,
                        term: kernelFree(
                            'checked_computation_witness',
                            because('checked datum')
                        )
                    }]
                })
            });
            const checked = checkAlgebraFormalComputationData(result);

            assert.equal(checked.data.length, 1);
            assert.equal(checked.data[0].id, 'claim-classifier');
            assert.equal(Object.isFrozen(checked.data), true);
        }
    );

    it('replays a genuine checked replacement in the original environment',
        async () => {
            const fixture = proofGoal(true);
            const result = await exactResult(fixture);
            const adopted = adoptAlgebraFormalCheckedPlan({
                result,
                replacement: coreProofPlanExact(kernelFree(
                    'checked_computation_witness',
                    because('checked replacement')
                ))
            });

            assert.equal(adopted.kind, 'checked-plan');
            assert.equal(adopted.authority, 'checked-proof-plan');
            assert.equal(adopted.environment, fixture.environment);
            assert.equal(adopted.execution.state.status, 'complete');
            assert.equal(adopted.checkedTerm.tag, 'reference');
            assert.equal(fixture.document.plan.tag, 'hole');
        }
    );

    it('adopts one explicit trusted assumption and records its authority',
        async () => {
            const fixture = proofGoal();
            const result = await exactResult(fixture);
            const adopted = adoptAlgebraFormalTrustedComputation({
                result,
                assumptionName: 'trusted_computed_claim',
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: 'author selected the exact native computation'
                }
            });
            const serialized =
                serializeAlgebraFormalTrustedAdoptionArtifact(adopted.artifact);

            assert.equal(adopted.kind, 'trusted-assumption');
            assert.equal(
                adopted.authority,
                'checked-relative-to-explicit-assumption'
            );
            assert.equal(fixture.environment.lookup('trusted_computed_claim'),
                undefined);
            assert.equal(adopted.assumption.name, 'trusted_computed_claim');
            assert.equal(adopted.assumption.body, undefined);
            assert.equal(adopted.assumption.transparency, 'opaque');
            assert.equal(adopted.execution.state.status, 'complete');
            assert.equal(adopted.checkedTerm.tag, 'reference');
            assert.match(serialized, /trusted-assumption/u);
            assert.match(serialized,
                /checked-relative-to-explicit-assumption/u);
            assert.match(serialized, /trusted_computed_claim/u);
            assert.equal(
                serialized,
                serializeAlgebraFormalTrustedAdoptionArtifact(adopted.artifact)
            );
            assert.equal(fixture.document.plan.tag, 'hole');
        }
    );

    it('rejects observations, stale results, implicit trust, and assumptions',
        async () => {
            const fixture = proofGoal();
            const negativeAdapter = adapterFixture();
            const negativeRequest = createAlgebraFormalComputationRequest({
                adapter: negativeAdapter.adapter,
                goal: fixture.goal,
                realization: Object.freeze({
                    id: 'fixture-realization',
                    value: -3
                }),
                engine: negativeAdapter.engine
            });
            const negative = await executeAlgebraFormalComputationRequest(
                negativeRequest
            );
            assert.throws(
                () => adoptAlgebraFormalTrustedComputation({
                    result: negative,
                    assumptionName: 'negative_claim',
                    decision: {
                        kind: 'trust-exact-algebra-computation',
                        evidence: 'must remain unavailable'
                    }
                }),
                delegationError('NO_ADOPTABLE_CLAIM')
            );

            const exact = await exactResult(fixture);
            assert.throws(
                () => adoptAlgebraFormalTrustedComputation({
                    result: { ...exact, outputData: 'tampered\n' },
                    assumptionName: 'stale_claim',
                    decision: {
                        kind: 'trust-exact-algebra-computation',
                        evidence: 'must reject stale output'
                    }
                }),
                delegationError('STALE_RESULT')
            );
            assert.throws(
                () => adoptAlgebraFormalTrustedComputation({
                    result: exact,
                    assumptionName: 'implicit_claim',
                    decision: {
                        kind: 'wrong-kind'
                    } as unknown as AlgebraFormalTrustedAdoptionDecision
                }),
                delegationError('INVALID_APPROVAL')
            );

            const assumed = await exactResult(fixture, {}, true);
            assert.throws(
                () => adoptAlgebraFormalTrustedComputation({
                    result: assumed,
                    assumptionName: 'assumption_laden_claim',
                    decision: {
                        kind: 'trust-exact-algebra-computation',
                        evidence: 'must acknowledge assumptions later'
                    }
                }),
                delegationError('UNACKNOWLEDGED_ASSUMPTIONS')
            );
        }
    );

    it('rejects ill-typed reified data before either adoption route',
        async () => {
            const fixture = proofGoal();
            const result = await exactResult(fixture, {
                interpret: ({ goal }) => ({
                    kind: 'claim',
                    summary: 'claim with invalid data',
                    claimType: goal.target,
                    data: [{
                        id: 'bad-datum',
                        type: goal.target,
                        term: kernelUniverse(because('ill-typed datum'))
                    }]
                })
            });
            assert.throws(
                () => checkAlgebraFormalComputationData(result),
                delegationError('ADOPTION_FAILED')
            );
        }
    );

    it('keeps trusted completion explicitly assumption-relative', () => {
        assert.equal(
            ALGEBRA_FORMAL_ADOPTION_PROFILE.completionAuthority.trusted,
            'checked-relative-to-explicit-assumption'
        );
        assert.equal(
            ALGEBRA_FORMAL_ADOPTION_PROFILE.trustedDeclaration,
            'checked-type-body-free-opaque'
        );
        assert.equal(ALGEBRA_FORMAL_ADOPTION_PROFILE.addsCoreOwner, false);
        assert.equal(ALGEBRA_FORMAL_ADOPTION_PROFILE.addsProofPlanTag, false);
        assert.equal(Object.isFrozen(ALGEBRA_FORMAL_ADOPTION_PROFILE), true);
    });
});

describe('PCD-REPLAY-6A direct workflow and exact reuse', () => {
    it('runs without adoption, emits a receipt, then trusts separately',
        async () => {
            const fixture = proofGoal();
            const { adapter, engine } = adapterFixture();
            const run = await runAlgebraFormalWorkflow({
                document: fixture.document,
                goalId: fixture.goal.goalId,
                adapter,
                realization: realization(),
                engine,
                limits: { fuel: 4 }
            });
            const receipt = createAlgebraFormalWorkflowReceipt(run);
            const serialized = serializeAlgebraFormalWorkflowReceipt(receipt);

            assert.equal(run.result.interpretation.kind, 'claim');
            assert.equal(fixture.document.plan.tag, 'hole');
            assert.equal(receipt.outcome, 'claim');
            assert.match(serialized, /delegated-goal/u);
            assert.equal(
                serialized,
                serializeAlgebraFormalWorkflowReceipt(receipt)
            );

            const adopted = trustAlgebraFormalWorkflow({
                run,
                assumptionName: 'workflow_trusted_claim',
                decision: {
                    kind: 'trust-exact-algebra-computation',
                    evidence: 'separate explicit workflow adoption'
                }
            });
            assert.equal(adopted.execution.state.status, 'complete');
            assert.equal(fixture.document.plan.tag, 'hole');
        }
    );

    it('reuses only an exact current in-memory result', async () => {
        const fixture = proofGoal();
        const { adapter, engine } = adapterFixture();
        const run = await runAlgebraFormalWorkflow({
            document: fixture.document,
            goalId: fixture.goal.goalId,
            adapter,
            realization: realization(),
            engine
        });
        assert.equal(
            reuseAlgebraFormalWorkflowResult({
                stored: run.result,
                currentRequest: run.request
            }),
            run.result
        );

        const changed = createAlgebraFormalComputationRequest({
            adapter,
            goal: fixture.goal,
            realization: realization(),
            engine,
            limits: { fuel: 9 }
        });
        assert.throws(
            () => reuseAlgebraFormalWorkflowResult({
                stored: run.result,
                currentRequest: changed
            }),
            delegationError('STALE_RESULT')
        );
    });

    it('retains the ordinary checked-plan route in the concise surface',
        async () => {
            const fixture = proofGoal(true);
            const { adapter, engine } = adapterFixture();
            const run = await runAlgebraFormalWorkflow({
                document: fixture.document,
                goalId: fixture.goal.goalId,
                adapter,
                realization: realization(),
                engine
            });
            const checked = checkAlgebraFormalWorkflow({
                run,
                replacement: coreProofPlanExact(kernelFree(
                    'checked_computation_witness',
                    because('workflow checked witness')
                ))
            });
            assert.equal(checked.authority, 'checked-proof-plan');
            assert.equal(checked.execution.state.status, 'complete');
        }
    );

    it('publishes no combined run-and-trust operation', () => {
        assert.equal(ALGEBRA_FORMAL_WORKFLOW_PROFILE.runAndTrustSeparated, true);
        assert.equal(
            ALGEBRA_FORMAL_WORKFLOW_PROFILE.reusePolicy,
            'exact-current-in-memory-result-only'
        );
        assert.equal(ALGEBRA_FORMAL_WORKFLOW_PROFILE.parsesStrings, false);
        assert.equal(Object.isFrozen(ALGEBRA_FORMAL_WORKFLOW_PROFILE), true);
    });
});
