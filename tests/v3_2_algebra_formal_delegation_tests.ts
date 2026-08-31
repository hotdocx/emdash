/** Focused proof–CAS delegation contract and execution tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_FORMAL_DELEGATION_PROFILE,
    ALGEBRA_FORMAL_DELEGATION_EXECUTION_PROFILE,
    AlgebraComputed,
    AlgebraFormalComputationGoal,
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    CoreLfDeclarationEnvironment,
    algebraAlgorithmIdentity,
    algebraReferenceExecutionResult,
    binderMode,
    coreProofPlanHole,
    createAlgebraFormalComputationRequest,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
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
    serializeAlgebraFormalComputationResult
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

const proofGoal = () => {
    const declaration = because('formal computation proposition');
    const environment = CoreLfDeclarationEnvironment.empty().extend({
        name: 'ComputationClaim',
        type: kernelUniverse(declaration),
        mode,
        provenance: declaration
    });
    const target = kernelFree('ComputationClaim', because('goal target'));
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
        environment,
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
        environment,
        target,
        document,
        goal: defineAlgebraFormalComputationGoal({
            document,
            goalId: 'delegated-goal'
        })
    };
};

const operationFixture = (
    quality: 'exact' | 'heuristic' = 'exact'
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
                quality
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
    quality: 'exact' | 'heuristic' = 'exact'
) => {
    const { operation, algorithm, engine } = operationFixture(quality);
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
