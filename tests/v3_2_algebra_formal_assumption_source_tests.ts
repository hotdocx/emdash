/** Focused ALC-SOURCE-2A computed-assumption source tests. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import { ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE, AlgebraFormalAssumptionSourceError,
    AlgebraFormalAssumptionClassification, appendAlgebraFormalAssumption, createAlgebraFormalAssumptionSource,
    serializeAlgebraFormalAssumptionKernelProbe, serializeAlgebraFormalAssumptionSource,
    validateAlgebraFormalAssumptionSource } from '../src/v3_2/algebra_formal_assumption_source';
import { CoreLfDeclarationEnvironment } from '../src/v3_2/lf_declarations';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from '../src/v3_2/algebra_engine';
import { algebraReferenceExecutionResult, createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation } from '../src/v3_2/algebra_reference_engine';
import { defineAlgebraFormalComputationAdapter } from '../src/v3_2/algebra_formal_delegation';
import { binderMode, kernelFree, kernelUniverse, provenance, sourceSpan } from '../src/v3_2/kernel';
import { checkLambdapiProbe } from '../src/v3_2/probe';
import { coreProofPlanHole } from '../src/v3_2/proof_plan';
import { createCoreProofArtifactFingerprint } from '../src/v3_2/proof_document';
import { runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from '../src/v3_2/algebra_formal_workflow';

const mode = binderMode('explicit', 'functorial');
const because = (detail: string) => provenance('surface', detail);

const sourceError = (
    code: AlgebraFormalAssumptionSourceError['code']
): ((error: unknown) => boolean) => error => {
    assert.ok(error instanceof AlgebraFormalAssumptionSourceError);
    assert.equal(error.code, code);
    return true;
};

const baseEnvironment = () => {
    let environment = CoreLfDeclarationEnvironment.empty();
    ['ComputedClaimA', 'ComputedClaimB'].forEach((name, index) => {
        const node = provenance(
            'surface',
            `computed claim ${name}`,
            sourceSpan('tests/computed-assumption-base.ts', index + 1, 1)
        );
        environment = environment.extend({
            name,
            type: kernelUniverse(node),
            mode,
            provenance: node
        });
    });
    return environment;
};

const operationFixture = (beforeSerializeOutput?: () => void) => {
    const schema = defineAlgebraRuntimeSchema<number>({
        id: 'assumption-source.number',
        revision: 'v1',
        normalize(value, path) {
            if (typeof value !== 'number' || !Number.isSafeInteger(value)) {
                throw new Error(`safe integer expected at ${path}`);
            }
            return value;
        }
    });
    const operation = defineAlgebraOperation({
        id: 'assumption-source.positive',
        revision: 'v1',
        input: schema,
        output: schema
    });
    const implementation = defineAlgebraReferenceImplementation({
        operation,
        algorithm: algebraAlgorithmIdentity(
            'assumption-source.positive.reference',
            'v1'
        ),
        execute: value => algebraReferenceExecutionResult({ value })
    });
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: 'assumption-source.reference',
        revision: 'v1',
        implementations: [implementation]
    });
    const adapter = defineAlgebraFormalComputationAdapter({
        id: 'assumption-source.adapter',
        revision: 'v1',
        operation,
        normalizeRealization(value, path) {
            if (
                value === null ||
                typeof value !== 'object' ||
                typeof (value as { claim?: unknown }).claim !== 'string'
            ) throw new Error(`claim realization expected at ${path}`);
            return Object.freeze({
                claim: (value as { claim: string }).claim,
                value: (value as { value: number }).value
            });
        },
        serializeRealization: value => `${JSON.stringify(value)}\n`,
        acquire: (_goal, value) => value.value,
        serializeInput: value => `${value}\n`,
        serializeOutput: value => {
            beforeSerializeOutput?.();
            return `${value}\n`;
        },
        interpret: ({ goal, computed }) => computed.value > 0
            ? {
                kind: 'claim',
                summary: 'positive source fixture',
                claimType: goal.target
            }
            : {
                kind: 'observation',
                summary: 'nonpositive source fixture'
            }
    });
    return { adapter, engine };
};

const document = (
    environment: CoreLfDeclarationEnvironment,
    claimName: string,
    goalId: string
) => {
    const target = kernelFree(claimName, because(`target ${claimName}`));
    return Object.freeze({
        moduleId: 'proof.cas.assumption-source',
        declarationId: goalId,
        environment,
        type: target,
        plan: coreProofPlanHole(goalId, {
            provenance: because(`hole ${goalId}`),
            expectation: { contextDepth: 0, target }
        }),
        provenance: because(`root ${goalId}`),
        fingerprint: createCoreProofArtifactFingerprint({
            source: {
                id: `tests/${goalId}.surface.ts`,
                sha256: `sha256:${claimName.endsWith('A')
                    ? 'a'.repeat(64)
                    : 'b'.repeat(64)}`
            },
            profileSha256: `sha256:${'c'.repeat(64)}`
        })
    });
};

const adopt = async (
    environment: CoreLfDeclarationEnvironment,
    claimName: string,
    goalId: string,
    assumptionName: string,
    fixture = operationFixture()
) => {
    const { adapter, engine } = fixture;
    const run = await runAlgebraFormalWorkflow({
        document: document(environment, claimName, goalId),
        goalId,
        adapter,
        realization: Object.freeze({ claim: claimName, value: 1 }),
        engine
    });
    return trustAlgebraFormalWorkflow({
        run,
        assumptionName,
        decision: {
            kind: 'trust-exact-algebra-computation',
            evidence: `explicit decision for ${assumptionName}`
        }
    });
};

describe('ALC-SOURCE-2A computed-assumption source', () => {
    it('rechecks every adoption on repeated source validation and rejects later drift', async () => {
        const visits = [0, 0];
        let stale = false;
        let source = createAlgebraFormalAssumptionSource({
            moduleId: 'proof.cas.fresh-batch',
            sourceId: 'generated/fresh-batch.ts',
            baseEnvironment: baseEnvironment()
        });
        for (const [index, name] of ['ComputedClaimA', 'ComputedClaimB'].entries()) {
            const fixture = operationFixture(() => {
                visits[index]++;
                if (stale && index === 1) throw new Error('retained computation drifted');
            });
            source = appendAlgebraFormalAssumption({
                source,
                adoption: await adopt(source.environment, name, 'fresh-' + index, 'fresh_' + index, fixture),
                classification: 'computed-equation'
            });
        }
        for (let i = 0; i < 2; i++) {
            const before = [...visits];
            assert.equal(validateAlgebraFormalAssumptionSource(source), source);
            assert.ok(visits.every((count, index) => count > before[index]));
        }
        stale = true;
        assert.throws(() => validateAlgebraFormalAssumptionSource(source), sourceError('SOURCE_DRIFT'));
    });

    it('accumulates classified adoptions in exact dependency order',
        async () => {
            const base = baseEnvironment();
            const empty = createAlgebraFormalAssumptionSource({
                moduleId: 'proof.cas.computed-assumptions',
                sourceId: 'generated/computed-assumptions.ts',
                baseEnvironment: base
            });
            const firstAdoption = await adopt(
                empty.environment,
                'ComputedClaimA',
                'claim-a',
                'computed_assumption_a'
            );
            const first = appendAlgebraFormalAssumption({
                source: empty,
                adoption: firstAdoption,
                classification: 'computed-equation'
            });
            const secondAdoption = await adopt(
                first.environment,
                'ComputedClaimB',
                'claim-b',
                'computed_assumption_b'
            );
            const second = appendAlgebraFormalAssumption({
                source: first,
                adoption: secondAdoption,
                classification: 'trusted-presentation-semantics'
            });
            const serialized = serializeAlgebraFormalAssumptionSource(second);

            assert.deepEqual(
                second.entries.map(entry => entry.classification),
                ['computed-equation', 'trusted-presentation-semantics']
            );
            assert.deepEqual(
                second.entries.map(entry => entry.declaration.name),
                ['computed_assumption_a', 'computed_assumption_b']
            );
            assert.equal(second.environment.declarations.length,
                base.declarations.length + 2);
            assert.equal(validateAlgebraFormalAssumptionSource(second), second);
            assert.equal(
                serialized,
                serializeAlgebraFormalAssumptionSource(second)
            );
            assert.match(serialized, /explicit decision for/u);
            assert.equal(Object.isFrozen(second.entries), true);
        }
    );

    it('emits source-spanned assumptions through the existing probe owner',
        async () => {
            const source0 = createAlgebraFormalAssumptionSource({
                moduleId: 'proof.cas.emitted-assumptions',
                sourceId: 'generated/emitted-assumptions.ts',
                baseEnvironment: baseEnvironment()
            });
            const adoption = await adopt(
                source0.environment,
                'ComputedClaimA',
                'emitted-claim',
                'emitted_computed_assumption'
            );
            const source = appendAlgebraFormalAssumption({
                source: source0,
                adoption,
                classification: 'computed-equation'
            });
            const entry = source.entries[0];
            const serialized = serializeAlgebraFormalAssumptionKernelProbe({
                source,
                assertions: [{
                    label: 'source-spanned computed assumption',
                    term: entry.reference,
                    type: entry.declaration.type,
                    span: sourceSpan('generated/emitted-assumptions.ts', 2, 1)
                }]
            });

            assert.match(serialized.source,
                /symbol emitted_computed_assumption/u);
            assert.match(serialized.source,
                /assert ⊢ emitted_computed_assumption/u);
            assert.equal(serialized.sourceMap.length,
                source.environment.declarations.length + 1);

            if (process.env.EMDASH_RUN_ASSUMPTION_SOURCE === '1') {
                const checked = checkLambdapiProbe(serialized, {
                    packageRoot: resolve(__dirname, '..', 'emdash2'),
                    timeoutMs: 60_000
                });
                assert.equal(checked.timedOut, false, checked.diagnostics);
                assert.equal(checked.accepted, true, checked.diagnostics);
            }
        }
    );

    it('rejects foreign order, stale results, and invalid classifications',
        async () => {
            const base = baseEnvironment();
            const source0 = createAlgebraFormalAssumptionSource({
                moduleId: 'proof.cas.negative-assumptions',
                sourceId: 'generated/negative-assumptions.ts',
                baseEnvironment: base
            });
            const firstAdoption = await adopt(
                base,
                'ComputedClaimA',
                'negative-a',
                'negative_assumption_a'
            );
            const first = appendAlgebraFormalAssumption({
                source: source0,
                adoption: firstAdoption,
                classification: 'computed-equation'
            });
            const foreign = await adopt(
                base,
                'ComputedClaimB',
                'negative-b',
                'negative_assumption_b'
            );
            assert.throws(
                () => appendAlgebraFormalAssumption({
                    source: first,
                    adoption: foreign,
                    classification: 'computed-equation'
                }),
                sourceError('FOREIGN_ENVIRONMENT')
            );
            assert.throws(
                () => appendAlgebraFormalAssumption({
                    source: source0,
                    adoption: firstAdoption,
                    classification: 'invalid' as
                        AlgebraFormalAssumptionClassification
                }),
                sourceError('INVALID_CLASSIFICATION')
            );
            const drifted = {
                ...first,
                entries: Object.freeze([{ ...first.entries[0], index: 4 }])
            };
            assert.throws(
                () => validateAlgebraFormalAssumptionSource(drifted),
                sourceError('SOURCE_DRIFT')
            );
        }
    );

    it('publishes a narrow nonsemantic source profile', () => {
        assert.deepEqual(
            ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.classifications,
            ['computed-equation', 'trusted-presentation-semantics']
        );
        assert.equal(
            ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.addsCoreOwner,
            false
        );
        assert.equal(
            ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.addsProofPlanTag,
            false
        );
    });
});
