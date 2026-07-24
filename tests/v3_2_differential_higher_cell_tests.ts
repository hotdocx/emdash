/**
 * Focused TSK-3C higher-cell differential matrix and oracle tests.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_MVP_DIFFERENTIAL_COMPLETION,
    CORE_MVP_DIFFERENTIAL_SCOPE,
    CoreMvpDifferentialCompletionInput,
    CoreMvpDifferentialError,
    KernelExpression,
    V32ElaborationError,
    buildCoreMvpHigherCellDifferentialCorpus,
    checkLambdapiProbe,
    coreRuntimeDefinitionalCompare,
    coreRuntimeRewriteHead,
    coreTypeToKernelType,
    elaborateSurfaceTerm,
    kernelExpressionEquals,
    serializeKernelExpression,
    serializeKernelProbe,
    validateCoreMvpDifferentialCompletion
} from '../src/v3_2';

const cloneCompletion = (): CoreMvpDifferentialCompletionInput =>
    JSON.parse(JSON.stringify(CORE_MVP_DIFFERENTIAL_COMPLETION));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

const collectOwners = (
    expression: KernelExpression,
    owners = new Set<string>()
): ReadonlySet<string> => {
    switch (expression.tag) {
        case 'application':
            owners.add(expression.owner);
            expression.arguments.forEach(argument =>
                collectOwners(argument.value, owners)
            );
            return owners;
        case 'call':
            collectOwners(expression.callee, owners);
            expression.arguments.forEach(argument =>
                collectOwners(argument.value, owners)
            );
            return owners;
        case 'pi':
        case 'lambda':
            collectOwners(expression.binder.type, owners);
            collectOwners(expression.body, owners);
            return owners;
        case 'meta':
            expression.spine.forEach(item => collectOwners(item, owners));
            return owners;
        case 'universe':
        case 'reference':
        case 'bound':
            return owners;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

describe('TypeScript v3.2 TSK-3C higher-cell differential corpus', () => {
    it('pins the two exact higher-cell packages and completed exit matrix', () => {
        const corpus = buildCoreMvpHigherCellDifferentialCorpus();

        assert.deepEqual(
            corpus.packages.map(package_ => package_.id),
            CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.map(row => row.id)
        );
        assert.deepEqual(
            corpus.packages.map(package_ => package_.ownerIds),
            CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.map(
                row => row.ownerIds
            )
        );
        assert.deepEqual(
            corpus.packages.map(package_ => package_.ruleIds),
            CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.map(
                row => row.ruleIds
            )
        );
        assert.deepEqual(
            corpus.packages.map(package_ => package_.required),
            CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.map(
                row => row.required
            )
        );
        assert.equal(
            CORE_MVP_DIFFERENTIAL_COMPLETION.status,
            'frozen-fragment-parity-complete'
        );
        assert.equal(
            CORE_MVP_DIFFERENTIAL_COMPLETION.oraclePolicy,
            'required-until-graduation'
        );
        assert.deepEqual(
            CORE_MVP_DIFFERENTIAL_COMPLETION.higherCellCases.map(
                row => row.completed
            ),
            CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.map(
                row => row.required
            )
        );
        assert.deepEqual(
            CORE_MVP_DIFFERENTIAL_COMPLETION.unclosedRows,
            []
        );
        assertDeepFrozen(CORE_MVP_DIFFERENTIAL_COMPLETION);
    });

    it('re-elaborates all nine shared positive typings in TypeScript', () => {
        const corpus = buildCoreMvpHigherCellDifferentialCorpus();
        const positives = corpus.packages.flatMap(
            package_ => package_.positives
        );

        assert.equal(positives.length, 9);
        for (const testCase of positives) {
            const repeated = elaborateSurfaceTerm(
                corpus.context,
                testCase.surfaceTerm
            );
            assert.equal(
                kernelExpressionEquals(repeated.term, testCase.term),
                true,
                `Expected stable Core term for ${testCase.id}`
            );
            assert.equal(
                kernelExpressionEquals(
                    coreTypeToKernelType(
                        repeated.type,
                        repeated.sourceSpan,
                        `TSK-3C repeated type for ${testCase.id}`
                    ),
                    testCase.type
                ),
                true,
                `Expected stable Core type for ${testCase.id}`
            );
        }
        for (const package_ of corpus.packages) {
            const observed = new Set<string>();
            package_.positives.forEach(testCase => {
                collectOwners(testCase.term, observed);
                collectOwners(testCase.type, observed);
            });
            for (const owner of package_.ownerIds) {
                assert.equal(
                    observed.has(owner),
                    true,
                    `Expected ${package_.id} to exercise ${owner}`
                );
            }
        }

        const recursive = positives.find(
            testCase => testCase.id === 'recursive-evaluator-redex'
        );
        assert.ok(recursive);
        const serialized = serializeKernelExpression(recursive.term);
        assert.doesNotMatch(serialized, /fapp2/);
        assert.match(serialized, /Hom_cat \(Hom_cat/);
    });

    it('rejects the same three wrong endpoints in TypeScript', () => {
        const corpus = buildCoreMvpHigherCellDifferentialCorpus();
        const wrongEndpoints = corpus.packages.flatMap(
            package_ => package_.wrongEndpoints
        );

        assert.equal(wrongEndpoints.length, 3);
        for (const testCase of wrongEndpoints) {
            assert.throws(
                () => elaborateSurfaceTerm(
                    corpus.context,
                    testCase.surfaceTerm
                ),
                (error: unknown) => {
                    assert.ok(error instanceof V32ElaborationError);
                    assert.equal(error.code, testCase.expectedError);
                    assert.deepEqual(
                        error.span,
                        testCase.expectedErrorSpan
                    );
                    return true;
                },
                `Expected TypeScript endpoint rejection for ${testCase.id}`
            );

            const validTerm = testCase.validTerm;
            const corruptedTerm = testCase.corruptedTerm;
            assert.equal(validTerm.tag, 'application');
            assert.equal(corruptedTerm.tag, 'application');
            if (
                validTerm.tag !== 'application' ||
                corruptedTerm.tag !== 'application'
            ) {
                throw new Error('Expected full projection applications');
            }
            assert.equal(
                corruptedTerm.owner,
                testCase.corruptedOwner
            );
            const supplied = corpus.context.lookup(
                testCase.suppliedBindingName
            );
            assert.ok(supplied);
            assert.equal(
                kernelExpressionEquals(
                    corruptedTerm.arguments[
                        testCase.corruptedSlot
                    ].value,
                    supplied.reference
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    {
                        ...corruptedTerm,
                        arguments: corruptedTerm.arguments.map(
                            (argument, index) => index ===
                                testCase.corruptedSlot
                                ? {
                                    ...argument,
                                    value: validTerm.arguments[
                                        testCase.corruptedSlot
                                    ].value
                                }
                                : argument
                        )
                    },
                    validTerm
                ),
                true
            );
        }
    });

    it('runs all three higher-cell conversions in TypeScript', () => {
        const corpus = buildCoreMvpHigherCellDifferentialCorpus();
        const conversions = corpus.packages.flatMap(
            package_ => package_.conversions
        );

        assert.deepEqual(
            conversions.map(testCase => testCase.ruleId),
            CORE_MVP_DIFFERENTIAL_SCOPE.higherCellCases.flatMap(
                row => row.ruleIds
            )
        );
        for (const testCase of conversions) {
            assert.equal(
                kernelExpressionEquals(
                    testCase.leftType,
                    testCase.rightType
                ),
                true
            );
            const rewrite = coreRuntimeRewriteHead(testCase.left);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                throw new Error('Expected a higher-cell runtime rewrite');
            }
            assert.equal(rewrite.ruleId, testCase.ruleId);
            assert.equal(
                kernelExpressionEquals(rewrite.after, testCase.right),
                true
            );

            const comparison = coreRuntimeDefinitionalCompare(
                testCase.left,
                testCase.right,
                1
            );
            assert.equal(comparison.status, 'equal');
            assert.equal(comparison.steps, 1);
            assert.equal(comparison.trace[0].ruleId, testCase.ruleId);
        }
    });

    it('serializes the exact shared positive, negative, and conversion rows', () => {
        const corpus = buildCoreMvpHigherCellDifferentialCorpus();
        const serialized = serializeKernelProbe(corpus.probe);
        const positives = serialized.sourceMap.filter(
            entry => entry.kind === 'assertion'
        );
        const negatives = serialized.sourceMap.filter(
            entry => entry.kind === 'negative-assertion'
        );
        const conversions = serialized.sourceMap.filter(
            entry => entry.kind === 'conversion'
        );

        assert.equal(positives.length, 9);
        assert.equal(negatives.length, 3);
        assert.equal(conversions.length, 3);
        assert.equal(
            serialized.source.match(/^assert ⊢ .* : .*;$/gm)?.length,
            9
        );
        assert.equal(
            serialized.source.match(/^assertnot ⊢ .* : .*;$/gm)?.length,
            3
        );
        assert.equal(
            serialized.source.match(/^assert ⊢ .* ≡ .*;$/gm)?.length,
            3
        );
        assert.deepEqual(
            conversions.map(entry => entry.label),
            corpus.packages.flatMap(package_ =>
                package_.conversions.map(testCase =>
                    `TSK-3 higher conversion ${package_.id} ` +
                    testCase.ruleId
                )
            )
        );
    });

    it(
        'has all shared higher-cell judgments accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const corpus = buildCoreMvpHigherCellDifferentialCorpus();
            const serialized = serializeKernelProbe(corpus.probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected TSK-3C higher-cell differential acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );

    it('rejects any drift from the completed exit matrix', () => {
        const missingHigher = cloneCompletion() as any;
        missingHigher.higherCellCases.pop();
        assert.throws(
            () => validateCoreMvpDifferentialCompletion(missingHigher),
            (error: unknown) => {
                assert.ok(error instanceof CoreMvpDifferentialError);
                assert.equal(error.code, 'DIFFERENTIAL_SCOPE_MISMATCH');
                return true;
            }
        );

        const reopened = cloneCompletion() as any;
        reopened.unclosedRows.push('recursive-functor-hom-2-cell');
        assert.throws(
            () => validateCoreMvpDifferentialCompletion(reopened),
            (error: unknown) => {
                assert.ok(error instanceof CoreMvpDifferentialError);
                assert.equal(error.code, 'DIFFERENTIAL_SCOPE_MISMATCH');
                return true;
            }
        );
    });
});
