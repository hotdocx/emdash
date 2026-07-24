/**
 * Focused TSK-3A owner-level differential matrix and oracle tests.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_MVP_DIFFERENTIAL_SCOPE,
    CORE_MVP_MANIFEST,
    CoreChecker,
    CoreCheckerError,
    CoreElaborationSession,
    CoreMvpDifferentialError,
    CoreMvpDifferentialScopeInput,
    buildCoreMvpOwnerDifferentialCorpus,
    checkLambdapiProbe,
    kernelExpressionEquals,
    serializeKernelProbe,
    validateCoreMvpDifferentialScope
} from '../src/v3_2';

const cloneScope = (): CoreMvpDifferentialScopeInput =>
    JSON.parse(JSON.stringify(CORE_MVP_DIFFERENTIAL_SCOPE));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

describe('TypeScript v3.2 TSK-3A owner differential corpus', () => {
    it('pins the exact owner, rule, and higher-cell exit matrix', () => {
        assert.equal(
            CORE_MVP_DIFFERENTIAL_SCOPE.manifestRevision,
            CORE_MVP_MANIFEST.revision
        );
        assert.equal(
            CORE_MVP_DIFFERENTIAL_SCOPE.manifestContentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            CORE_MVP_DIFFERENTIAL_SCOPE.ownerCases.map(entry => entry.owner),
            CORE_MVP_MANIFEST.owners.map(entry => entry.owner)
        );
        assert.equal(CORE_MVP_DIFFERENTIAL_SCOPE.ownerCases.length, 16);
        assert.deepEqual(
            CORE_MVP_DIFFERENTIAL_SCOPE.ruleCases.map(entry => entry.ruleId),
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );
        assert.equal(CORE_MVP_DIFFERENTIAL_SCOPE.ruleCases.length, 3);
        assert.deepEqual(
            [
                ...new Set(
                    CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.flatMap(
                        entry => entry.ruleIds
                    )
                )
            ],
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );
        assertDeepFrozen(CORE_MVP_DIFFERENTIAL_SCOPE);
    });

    it('checks every shared positive owner judgment in TypeScript', () => {
        const corpus = buildCoreMvpOwnerDifferentialCorpus();
        const checker = new CoreChecker(
            new CoreElaborationSession(corpus.environment)
        );
        checker.validateEnvironment();

        for (const testCase of corpus.cases) {
            const inferred = checker.infer(
                checker.rootContext,
                testCase.term
            );
            assert.equal(
                kernelExpressionEquals(
                    inferred.type as typeof testCase.expectedType,
                    testCase.expectedType
                ),
                true,
                `Expected exact TypeScript type for ${testCase.owner}`
            );
        }
        assert.deepEqual(
            corpus.ownerIds,
            CORE_MVP_MANIFEST.owners.map(entry => entry.owner)
        );
    });

    it('rejects every shared negative owner judgment in TypeScript', () => {
        const corpus = buildCoreMvpOwnerDifferentialCorpus();

        for (const testCase of corpus.cases) {
            const checker = new CoreChecker(
                new CoreElaborationSession(corpus.environment)
            );
            assert.throws(
                () => checker.check(
                    checker.rootContext,
                    testCase.term,
                    testCase.rejectedType
                ),
                (error: unknown) => {
                    assert.ok(error instanceof CoreCheckerError);
                    assert.equal(error.code, 'TYPE_MISMATCH');
                    return true;
                },
                `Expected TypeScript rejection for ${testCase.owner}`
            );
        }
    });

    it('serializes the same 16 positive and 16 negative judgments', () => {
        const corpus = buildCoreMvpOwnerDifferentialCorpus();
        const serialized = serializeKernelProbe(corpus.probe);
        const positive = serialized.sourceMap.filter(
            entry => entry.kind === 'assertion'
        );
        const negative = serialized.sourceMap.filter(
            entry => entry.kind === 'negative-assertion'
        );

        assert.equal(positive.length, 16);
        assert.equal(negative.length, 16);
        assert.deepEqual(
            positive.map(entry => entry.label),
            corpus.cases.map(
                testCase => `TSK-3 owner positive ${testCase.owner}`
            )
        );
        assert.deepEqual(
            negative.map(entry => entry.label),
            corpus.cases.map(
                testCase => `TSK-3 owner negative ${testCase.owner}`
            )
        );
        assert.equal(
            serialized.source.match(/^assert ⊢/gm)?.length,
            16
        );
        assert.equal(
            serialized.source.match(/^assertnot ⊢/gm)?.length,
            16
        );
    });

    it(
        'has all shared owner judgments accepted by the Lambdapi oracle',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const corpus = buildCoreMvpOwnerDifferentialCorpus();
            const serialized = serializeKernelProbe(corpus.probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected TSK-3A owner differential acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );

    it('rejects any drift from the frozen differential scope', () => {
        const ownerDrift = cloneScope() as any;
        ownerDrift.ownerCases.pop();
        assert.throws(
            () => validateCoreMvpDifferentialScope(ownerDrift),
            (error: unknown) => {
                assert.ok(error instanceof CoreMvpDifferentialError);
                assert.equal(error.code, 'DIFFERENTIAL_SCOPE_MISMATCH');
                return true;
            }
        );

        const ruleDrift = cloneScope() as any;
        ruleDrift.ruleCases[0].required.pop();
        assert.throws(
            () => validateCoreMvpDifferentialScope(ruleDrift),
            (error: unknown) => {
                assert.ok(error instanceof CoreMvpDifferentialError);
                assert.equal(error.code, 'DIFFERENTIAL_SCOPE_MISMATCH');
                return true;
            }
        );
    });
});
