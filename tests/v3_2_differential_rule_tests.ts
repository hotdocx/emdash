/**
 * Focused TSK-3B runtime-rule differential matrix and oracle tests.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_MVP_DIFFERENTIAL_SCOPE
} from '../src/v3_2/differential';
import {
    CORE_MVP_MANIFEST
} from '../src/v3_2/manifest';
import {
    CORE_MVP_RUNTIME_PROGRAM,
    CoreRuntimeCompilationError,
    compileCoreRuntimeRuleCandidate
} from '../src/v3_2/runtime';
import {
    CoreChecker
} from '../src/v3_2/checker';
import {
    CoreElaborationSession
} from '../src/v3_2/session';
import {
    buildCoreMvpRuleDifferentialCorpus
} from '../src/v3_2/differential_rule';
import {
    checkLambdapiProbe,
    serializeKernelProbe
} from '../src/v3_2/probe';
import {
    coreRuntimeDefinitionalCompare
} from '../src/v3_2/conversion';
import {
    coreRuntimeRewriteHead
} from '../src/v3_2/evaluator';
import {
    kernelExpressionEquals
} from '../src/v3_2/kernel';

describe('TypeScript v3.2 TSK-3B rule differential corpus', () => {
    it('pins exactly one shared row to each reviewed runtime rule', () => {
        const corpus = buildCoreMvpRuleDifferentialCorpus();
        const expectedIds = CORE_MVP_MANIFEST.rules.map(rule => rule.id);

        assert.deepEqual(corpus.ruleIds, expectedIds);
        assert.deepEqual(
            corpus.ruleIds,
            CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id)
        );
        assert.deepEqual(
            corpus.ruleIds,
            CORE_MVP_DIFFERENTIAL_SCOPE.ruleCases.map(row => row.ruleId)
        );
        assert.equal(corpus.cases.length, 3);

        corpus.cases.forEach((testCase, order) => {
            assert.equal(testCase.order, order);
            assert.deepEqual(
                CORE_MVP_DIFFERENTIAL_SCOPE.ruleCases[order].required,
                [
                    'positive-conversion',
                    'well-typed-near-miss-non-conversion',
                    'malformed-rule-rejection'
                ]
            );
            assert.equal(
                testCase.malformed.candidate.id,
                testCase.ruleId
            );
            assert.equal(
                testCase.malformed.oracleAbsenceWitness.malformedRuleId,
                testCase.ruleId
            );
            assert.equal(
                testCase.malformed.oracleAbsenceWitness.interpretation,
                'oracle-rejects-erased-full-projection-conversion'
            );
        });
    });

    it('runs the same three positive conversions in TypeScript', () => {
        const corpus = buildCoreMvpRuleDifferentialCorpus();

        for (const testCase of corpus.cases) {
            assert.equal(
                kernelExpressionEquals(
                    testCase.redexType,
                    testCase.reductType
                ),
                true
            );
            const rewrite = coreRuntimeRewriteHead(testCase.redex);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                throw new Error('Expected a reviewed runtime rewrite');
            }
            assert.equal(rewrite.ruleId, testCase.ruleId);
            assert.equal(
                kernelExpressionEquals(rewrite.after, testCase.reduct),
                true
            );

            const comparison = coreRuntimeDefinitionalCompare(
                testCase.redex,
                testCase.reduct,
                1
            );
            assert.equal(comparison.status, 'equal');
            assert.equal(comparison.steps, 1);
            assert.equal(comparison.trace[0].ruleId, testCase.ruleId);
        }
    });

    it('records every near miss as well typed and non-convertible', () => {
        const corpus = buildCoreMvpRuleDifferentialCorpus();
        const checker = new CoreChecker(
            new CoreElaborationSession(corpus.environment)
        );
        checker.validateEnvironment();

        for (const testCase of corpus.cases) {
            const inferredReduct = checker.infer(
                checker.rootContext,
                testCase.reduct
            );
            const typing = testCase.nearMissTyping;
            const declaration = corpus.environment.lookup(
                testCase.nearMissFunctorName
            );
            assert.ok(declaration);
            assert.equal(
                typing.replacementFunctor,
                declaration.reference
            );
            assert.equal(
                kernelExpressionEquals(
                    typing.originalFunctorType,
                    typing.replacementFunctorType
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    typing.originalFunctor,
                    typing.replacementFunctor
                ),
                false
            );
            assert.equal(
                kernelExpressionEquals(
                    inferredReduct.type as typeof testCase.reductType,
                    testCase.reductType
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    typing.resultType,
                    testCase.nearMissType
                ),
                true
            );
            assert.equal(
                typing.method,
                'same-classifier-substitution-into-surface-elaborated-redex'
            );
            assert.equal(
                typing.standaloneCheckerBoundary,
                'withheld-active-classifier-computation'
            );

            assert.equal(testCase.redex.tag, 'application');
            assert.equal(testCase.nearMiss.tag, 'application');
            if (
                testCase.redex.tag !== 'application' ||
                testCase.nearMiss.tag !== 'application'
            ) {
                throw new Error('Expected evaluator applications');
            }
            assert.equal(
                kernelExpressionEquals(
                    testCase.redex.arguments[2].value,
                    typing.originalFunctor
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    testCase.nearMiss.arguments[2].value,
                    typing.replacementFunctor
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    {
                        ...testCase.nearMiss,
                        arguments: testCase.nearMiss.arguments.map(
                            (argument, index) => index === 2
                                ? {
                                    ...argument,
                                    value: typing.originalFunctor
                                }
                                : argument
                        )
                    },
                    testCase.redex
                ),
                true
            );

            assert.equal(
                coreRuntimeRewriteHead(testCase.nearMiss).status,
                'irreducible'
            );
            const comparison = coreRuntimeDefinitionalCompare(
                testCase.nearMiss,
                testCase.reduct,
                1
            );
            assert.equal(comparison.status, 'not-equal');
            assert.equal(comparison.steps, 0);
        }
    });

    it('rejects every paired malformed rule candidate in TypeScript', () => {
        const corpus = buildCoreMvpRuleDifferentialCorpus();

        for (const testCase of corpus.cases) {
            const variables = testCase.malformed.candidate.variables;
            assert.equal(
                new Set(variables).size,
                variables.length
            );
            assert.equal(variables[variables.length - 1], 'H');
            assert.equal(
                testCase.malformed.mutation,
                'erase-required-full-projection'
            );
            assert.equal(
                testCase.malformed.candidate.left.tag,
                'owner-application'
            );
            if (
                testCase.malformed.candidate.left.tag !==
                'owner-application'
            ) {
                throw new Error('Expected a broadened owner pattern');
            }
            assert.deepEqual(
                testCase.malformed.candidate.left.arguments[2],
                { tag: 'variable', name: 'H' }
            );
            assert.throws(
                () => compileCoreRuntimeRuleCandidate(
                    testCase.malformed.candidate,
                    CORE_MVP_RUNTIME_PROGRAM.ownerIds
                ),
                (error: unknown) => {
                    assert.ok(error instanceof CoreRuntimeCompilationError);
                    assert.equal(
                        error.code,
                        testCase.malformed.expectedError
                    );
                    if (
                        testCase.malformed.expectedError ===
                        'INVALID_PROJECTION_DECREASE'
                    ) {
                        assert.match(
                            error.message,
                            /eliminate exactly one reviewed full projection/
                        );
                    } else {
                        assert.match(
                            error.message,
                            /does not bind declared variable 'eta'/
                        );
                    }
                    return true;
                },
                `Expected malformed rejection for ${testCase.ruleId}`
            );
        }
    });

    it('serializes the same conversions and paired absence witnesses', () => {
        const corpus = buildCoreMvpRuleDifferentialCorpus();
        const serialized = serializeKernelProbe(corpus.probe);
        const conversions = serialized.sourceMap.filter(
            entry => entry.kind === 'conversion'
        );
        const nonConversions = serialized.sourceMap.filter(
            entry => entry.kind === 'non-conversion'
        );

        assert.equal(conversions.length, 3);
        assert.equal(nonConversions.length, 3);
        assert.deepEqual(
            conversions.map(entry => entry.label),
            corpus.cases.map(
                testCase =>
                    `TSK-3 rule conversion ${testCase.ruleId}`
            )
        );
        assert.deepEqual(
            nonConversions.map(entry => entry.label),
            corpus.cases.map(
                testCase =>
                    `TSK-3 rule near-miss absence ${testCase.ruleId}`
            )
        );
        assert.equal(
            serialized.source.match(/^assert ⊢ .* ≡ .*;$/gm)?.length,
            3
        );
        assert.equal(
            serialized.source.match(/^assertnot ⊢ .* ≡ .*;$/gm)?.length,
            3
        );

        corpus.cases.forEach((testCase, order) => {
            assert.equal(
                corpus.probe.conversions?.[order].left,
                testCase.redex
            );
            assert.equal(
                corpus.probe.conversions?.[order].right,
                testCase.reduct
            );
            assert.equal(
                corpus.probe.nonConversions?.[order].left,
                testCase.malformed.oracleAbsenceWitness.left
            );
            assert.equal(
                corpus.probe.nonConversions?.[order].right,
                testCase.malformed.oracleAbsenceWitness.right
            );
        });
    });

    it(
        'has all shared rule judgments accepted by the Lambdapi oracle',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const corpus = buildCoreMvpRuleDifferentialCorpus();
            const serialized = serializeKernelProbe(corpus.probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected TSK-3B rule differential acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
