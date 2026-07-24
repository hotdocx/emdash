/**
 * Focused TSK-2B tests for matching and bounded weak-head rewriting.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_MVP_RUNTIME_PROGRAM,
    CoreRuntimeEvaluationError,
    KernelApplication,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    SurfaceContext,
    SurfaceTerm,
    binderMode,
    categoryType,
    checkLambdapiProbe,
    coreTypeToKernelType,
    coreRuntimeMatchRule,
    coreRuntimeRewriteHead,
    coreRuntimeWeakHead,
    declarationsFromSurfaceContext,
    elaborateSurfaceTerm,
    functorType,
    homType,
    kernelApplication,
    kernelExpressionEquals,
    objectType,
    provenance,
    serializeKernelProbe,
    sourceSpan,
    surfaceBinding,
    surfaceFapp0,
    surfaceFapp1,
    surfaceFapp1Func,
    surfaceReference,
    surfaceTapp0,
    surfaceTapp0Func,
    surfaceTapp1,
    surfaceTapp1Func,
    transforType
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_runtime_rewrite.surface.ts';
const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(fixture, line, startColumn, line, endColumn);

const runtimeContext = (): SurfaceContext => new SurfaceContext([
    surfaceBinding('runtime_A', categoryType(), at(1)),
    surfaceBinding('runtime_B', categoryType(), at(2)),
    surfaceBinding('runtime_x', objectType('runtime_A'), at(3)),
    surfaceBinding('runtime_y', objectType('runtime_A'), at(4)),
    surfaceBinding(
        'runtime_F',
        functorType('runtime_A', 'runtime_B'),
        at(5)
    ),
    surfaceBinding(
        'runtime_G',
        functorType('runtime_A', 'runtime_B'),
        at(6)
    ),
    surfaceBinding(
        'runtime_f',
        homType('runtime_A', 'runtime_x', 'runtime_y'),
        at(7)
    ),
    surfaceBinding(
        'runtime_eta',
        transforType(
            'runtime_A',
            'runtime_B',
            'runtime_F',
            'runtime_G'
        ),
        at(8),
        binderMode('implicit', 'natural')
    )
]);

const ref = (name: string, line: number) =>
    surfaceReference(name, at(line));

interface RuntimeRewriteCase {
    readonly ruleId: string;
    readonly left: KernelExpression;
    readonly expected: KernelExpression;
    readonly leftType: KernelExpression;
    readonly expectedType: KernelExpression;
}

const runtimeCases = (
    context: SurfaceContext
): readonly RuntimeRewriteCase[] => {
    const compileCase = (
        ruleId: string,
        leftSurface: SurfaceTerm,
        expectedSurface: SurfaceTerm
    ): RuntimeRewriteCase => {
        const left = elaborateSurfaceTerm(context, leftSurface);
        const expected = elaborateSurfaceTerm(context, expectedSurface);
        return {
            ruleId,
            left: left.term,
            expected: expected.term,
            leftType: coreTypeToKernelType(
                left.type,
                left.sourceSpan,
                `TSK-2B left type for ${ruleId}`
            ),
            expectedType: coreTypeToKernelType(
                expected.type,
                expected.sourceSpan,
                `TSK-2B expected type for ${ruleId}`
            )
        };
    };
    const fullFunctorHom = surfaceFapp1Func(
        ref('runtime_F', 20),
        ref('runtime_x', 20),
        ref('runtime_y', 20),
        at(20, 1, 32)
    );
    const fullTransforComponent = surfaceTapp0Func(
        ref('runtime_F', 21),
        ref('runtime_G', 21),
        ref('runtime_x', 21),
        at(21, 1, 35)
    );
    const fullTransforHom = surfaceTapp1Func(
        ref('runtime_eta', 22),
        ref('runtime_x', 22),
        ref('runtime_y', 22),
        at(22, 1, 39)
    );

    return [
        compileCase(
            'projection.functor-hom.evaluate',
            surfaceFapp0(
                fullFunctorHom,
                ref('runtime_f', 23),
                at(23, 1, 44)
            ),
            surfaceFapp1(
                ref('runtime_F', 24),
                ref('runtime_f', 24),
                at(24, 1, 28)
            )
        ),
        compileCase(
            'projection.transfor-component.evaluate',
            surfaceFapp0(
                fullTransforComponent,
                ref('runtime_eta', 25),
                at(25, 1, 48)
            ),
            surfaceTapp0(
                ref('runtime_eta', 26),
                ref('runtime_x', 26),
                at(26, 1, 30)
            )
        ),
        compileCase(
            'projection.transfor-hom.evaluate',
            surfaceFapp0(
                fullTransforHom,
                ref('runtime_f', 27),
                at(27, 1, 50)
            ),
            surfaceTapp1(
                ref('runtime_eta', 28),
                ref('runtime_f', 28),
                at(28, 1, 32)
            )
        )
    ];
};

const replaceApplicationArgument = (
    expression: KernelExpression,
    index: number,
    value: KernelExpression
): KernelApplication => {
    assert.equal(expression.tag, 'application');
    if (expression.tag !== 'application') {
        throw new Error('Expected a Core owner application');
    }
    return {
        ...expression,
        arguments: expression.arguments.map((argument, argumentIndex) =>
            argumentIndex === index
                ? { ...argument, value }
                : argument
        )
    };
};

const mismatchedRepeatedFunctor = (
    context: SurfaceContext,
    expression: KernelExpression
): KernelExpression => {
    assert.equal(expression.tag, 'application');
    if (expression.tag !== 'application') {
        throw new Error('Expected the evaluator application');
    }
    const full = expression.arguments[2].value;
    assert.equal(full.tag, 'application');
    if (full.tag !== 'application') {
        throw new Error('Expected the full projection application');
    }
    const replacement = context.lookup('runtime_G');
    assert.ok(replacement);
    const inconsistentFull = replaceApplicationArgument(
        full,
        2,
        replacement.reference
    );
    return replaceApplicationArgument(expression, 2, inconsistentFull);
};

describe('TypeScript v3.2 TSK-2B runtime rewriting', () => {
    it('matches all three rules with deterministic repeated-variable slots', () => {
        const context = runtimeContext();
        const cases = runtimeCases(context);

        cases.forEach((testCase, index) => {
            const rule = CORE_MVP_RUNTIME_PROGRAM.rules[index];
            const first = coreRuntimeMatchRule(testCase.left, rule);
            const second = coreRuntimeMatchRule(testCase.left, rule);
            assert.ok(first);
            assert.ok(second);
            assert.equal(first.ruleId, testCase.ruleId);
            assert.deepEqual(first, second);
            assert.equal(Object.isFrozen(first), true);
            assert.equal(Object.isFrozen(first.bindings), true);
            assert.equal(first.bindings.length, rule.variables.length);
        });
    });

    it('rejects repeated-variable and plicity near misses', () => {
        const context = runtimeContext();
        const testCase = runtimeCases(context)[0];
        const rule = CORE_MVP_RUNTIME_PROGRAM.rules[0];
        const inconsistent = mismatchedRepeatedFunctor(
            context,
            testCase.left
        );
        assert.equal(
            coreRuntimeMatchRule(inconsistent, rule),
            undefined
        );

        assert.equal(testCase.left.tag, 'application');
        if (testCase.left.tag !== 'application') {
            throw new Error('Expected an evaluator application');
        }
        const wrongPlicity: KernelApplication = {
            ...testCase.left,
            arguments: testCase.left.arguments.map((argument, index) =>
                index === 0
                    ? { ...argument, plicity: 'explicit' }
                    : argument
            )
        };
        assert.equal(coreRuntimeMatchRule(wrongPlicity, rule), undefined);
    });

    it('rewrites each reviewed head to its exact capped projection', () => {
        const context = runtimeContext();
        for (const testCase of runtimeCases(context)) {
            const first = coreRuntimeRewriteHead(testCase.left);
            const second = coreRuntimeRewriteHead(testCase.left);
            assert.equal(first.status, 'rewritten');
            assert.equal(second.status, 'rewritten');
            if (
                first.status !== 'rewritten' ||
                second.status !== 'rewritten'
            ) {
                throw new Error('Expected both heads to rewrite');
            }

            assert.equal(first.ruleId, testCase.ruleId);
            assert.equal(first.before, testCase.left);
            assert.equal(
                kernelExpressionEquals(first.after, testCase.expected),
                true
            );
            assert.equal(
                kernelExpressionEquals(first.after, second.after),
                true
            );
            assert.equal(first.after.provenance.origin, 'derived');
            assert.deepEqual(
                first.after.provenance.span,
                testCase.left.provenance.span
            );
            assert.equal(first.after.tag, 'application');
            if (first.after.tag !== 'application') {
                throw new Error('Expected a capped owner application');
            }
            first.after.arguments.forEach((argument, slot) => {
                assert.equal(argument.value, first.match.bindings[slot]);
            });
            assert.match(
                first.after.provenance.detail,
                new RegExp(testCase.ruleId.replace(/\./g, '\\.'))
            );
        }
    });

    it('preserves each exact elaborated result classifier', () => {
        const context = runtimeContext();

        for (const testCase of runtimeCases(context)) {
            const rewrite = coreRuntimeRewriteHead(testCase.left);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                throw new Error('Expected a reviewed runtime rewrite');
            }
            assert.equal(
                kernelExpressionEquals(
                    testCase.leftType,
                    testCase.expectedType
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(rewrite.after, testCase.expected),
                true
            );
        }
    });

    it('leaves wrong roots, capped forms, and near misses unchanged', () => {
        const context = runtimeContext();
        const testCase = runtimeCases(context)[0];
        const capped = coreRuntimeRewriteHead(testCase.expected);
        assert.deepEqual(capped, {
            status: 'irreducible',
            expression: testCase.expected
        });

        const inconsistent = mismatchedRepeatedFunctor(
            context,
            testCase.left
        );
        const nearMiss = coreRuntimeRewriteHead(inconsistent);
        assert.equal(nearMiss.status, 'irreducible');
        if (nearMiss.status === 'irreducible') {
            assert.equal(nearMiss.expression, inconsistent);
        }

        const reference = context.lookup('runtime_f');
        assert.ok(reference);
        const free = coreRuntimeRewriteHead(reference.reference);
        assert.equal(free.status, 'irreducible');
        if (free.status === 'irreducible') {
            assert.equal(free.expression, reference.reference);
        }
    });

    it('evaluates weak heads under an explicit deterministic step bound', () => {
        const context = runtimeContext();
        for (const testCase of runtimeCases(context)) {
            const result = coreRuntimeWeakHead(testCase.left, 1);
            assert.equal(result.status, 'weak-head-normal');
            assert.equal(result.steps, 1);
            assert.equal(result.trace.length, 1);
            assert.equal(result.trace[0].step, 0);
            assert.equal(result.trace[0].ruleId, testCase.ruleId);
            assert.equal(
                kernelExpressionEquals(result.expression, testCase.expected),
                true
            );
            assert.equal(Object.isFrozen(result), true);
            assert.equal(Object.isFrozen(result.trace), true);

            const exhausted = coreRuntimeWeakHead(testCase.left, 0);
            assert.equal(exhausted.status, 'step-limit-exceeded');
            assert.equal(exhausted.expression, testCase.left);
            assert.equal(exhausted.steps, 0);
            assert.deepEqual(exhausted.trace, []);
            if (exhausted.status === 'step-limit-exceeded') {
                assert.equal(exhausted.nextRuleId, testCase.ruleId);
            }
        }

        const alreadyNormal = runtimeCases(context)[0].expected;
        const zeroStepNormal = coreRuntimeWeakHead(alreadyNormal, 0);
        assert.equal(zeroStepNormal.status, 'weak-head-normal');
        assert.equal(zeroStepNormal.expression, alreadyNormal);
        assert.equal(zeroStepNormal.steps, 0);
    });

    it('does not recursively normalize a reducible argument', () => {
        const context = runtimeContext();
        const nestedRedex = runtimeCases(context)[0].left;
        const wrapper = kernelApplication('decode', [{
            value: nestedRedex
        }], provenance(
            'surface',
            'TSK-2B head-only wrapper',
            at(40, 1, 30)
        ));
        const result = coreRuntimeWeakHead(wrapper, 1);
        assert.equal(result.status, 'weak-head-normal');
        assert.equal(result.expression, wrapper);
        assert.equal(result.steps, 0);
    });

    it('rejects invalid weak-head bounds at the input provenance', () => {
        const expression = runtimeCases(runtimeContext())[0].left;
        for (const invalid of [-1, 0.5, Number.MAX_SAFE_INTEGER + 1]) {
            assert.throws(
                () => coreRuntimeWeakHead(expression, invalid),
                (error: unknown) => {
                    assert.ok(error instanceof CoreRuntimeEvaluationError);
                    assert.equal(error.code, 'INVALID_STEP_LIMIT');
                    assert.deepEqual(
                        error.provenance,
                        expression.provenance
                    );
                    return true;
                }
            );
        }
    });

    it(
        'agrees with Lambdapi on all three reviewed head conversions',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const context = runtimeContext();
            const cases = runtimeCases(context);
            const conversions = cases.map((testCase, index) => {
                const rewrite = coreRuntimeRewriteHead(testCase.left);
                assert.equal(rewrite.status, 'rewritten');
                if (rewrite.status !== 'rewritten') {
                    throw new Error('Expected runtime rewrite');
                }
                assert.equal(
                    kernelExpressionEquals(
                        rewrite.after,
                        testCase.expected
                    ),
                    true
                );
                return {
                    label: `TSK-2B differential ${testCase.ruleId}`,
                    left: rewrite.before,
                    right: rewrite.after,
                    span: at(50 + index, 1, 60)
                };
            });
            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: declarationsFromSurfaceContext(context),
                assertions: [],
                conversions
            };
            const serialized = serializeKernelProbe(probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected TSK-2B differential acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
