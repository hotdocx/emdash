/**
 * Focused DTTLF LF-1A tests for isolated, bounded outer-LF beta.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreLfEvaluationError,
    KernelCall,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    Plicity,
    binderMode,
    checkLambdapiProbe,
    coreLfBetaReduceHead,
    coreLfBetaWeakHead,
    coreRuntimeDefinitionalCompare,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_lf_beta.surface.ts';
const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const categoryUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'category-universe',
        [],
        because(line, 'LF-1A category universe')
    );

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `LF-1A free declaration ${name}`));

const lambda = (
    hint: string,
    plicity: Plicity,
    body: KernelExpression,
    line: number
) => kernelLambda(
    kernelBinder(
        hint,
        categoryUniverse(line),
        binderMode(plicity, 'functorial'),
        because(line, `LF-1A ${plicity} binder ${hint}`)
    ),
    body,
    because(line, `LF-1A lambda ${hint}`)
);

const identity = (
    plicity: Plicity,
    line: number
): KernelExpression => lambda(
    'value',
    plicity,
    kernelBound(0, because(line, 'LF-1A identity body')),
    line
);

describe('TypeScript v3.2 DTTLF LF-1A generic beta', () => {
    it('contracts a direct identity while preserving the frozen MVP boundary', () => {
        const argument = free('lf_beta_argument', 10);
        const redex = kernelCall(
            identity('explicit', 10),
            [{
                plicity: 'explicit',
                value: argument,
                provenance: because(10, 'LF-1A identity argument')
            }],
            because(10, 'LF-1A identity redex')
        );

        const head = coreLfBetaReduceHead(redex);
        assert.equal(head.status, 'reduced');
        if (head.status !== 'reduced') {
            throw new Error('Expected one LF beta reduction');
        }
        assert.equal(head.before, redex);
        assert.equal(kernelExpressionEquals(head.after, argument), true);
        assert.deepEqual(
            {
                binder: head.binderPlicity,
                argument: head.argumentPlicity,
                residual: head.residualArgumentCount
            },
            {
                binder: 'explicit',
                argument: 'explicit',
                residual: 0
            }
        );

        const result = coreLfBetaWeakHead(redex, 1);
        assert.equal(result.status, 'weak-head-normal');
        assert.equal(result.steps, 1);
        assert.equal(kernelExpressionEquals(result.expression, argument), true);
        assert.equal(result.trace.length, 1);
        assert.deepEqual(
            {
                step: result.trace[0].step,
                kind: result.trace[0].kind,
                binder: result.trace[0].binderPlicity,
                argument: result.trace[0].argumentPlicity,
                residual: result.trace[0].residualArgumentCount
            },
            {
                step: 0,
                kind: 'beta',
                binder: 'explicit',
                argument: 'explicit',
                residual: 0
            }
        );

        const frozenComparison = coreRuntimeDefinitionalCompare(
            redex,
            argument,
            4
        );
        assert.equal(frozenComparison.status, 'not-equal');
        assert.equal(frozenComparison.steps, 0);
    });

    it('consumes multiargument and nested call spines in binder order', () => {
        const first = free('lf_beta_first', 20);
        const second = free('lf_beta_second', 20);
        const secondArgumentProvenance = because(
            20,
            'LF-1A preserved second argument'
        );
        const curried = lambda(
            'first',
            'explicit',
            lambda(
                'second',
                'implicit',
                kernelBound(1, because(20, 'LF-1A curried first result')),
                20
            ),
            20
        );
        const multiargument = kernelCall(
            curried,
            [
                {
                    plicity: 'explicit',
                    value: first,
                    provenance: because(20, 'LF-1A first argument')
                },
                {
                    plicity: 'implicit',
                    value: second,
                    provenance: secondArgumentProvenance
                }
            ],
            because(20, 'LF-1A multiargument redex')
        );

        const oneStep = coreLfBetaWeakHead(multiargument, 1);
        assert.equal(oneStep.status, 'step-limit-exceeded');
        assert.equal(oneStep.steps, 1);
        assert.equal(oneStep.trace[0].residualArgumentCount, 1);
        assert.deepEqual(
            oneStep.status === 'step-limit-exceeded'
                ? oneStep.next
                : undefined,
            {
                binderPlicity: 'implicit',
                argumentPlicity: 'implicit',
                residualArgumentCount: 0
            }
        );
        assert.equal(oneStep.expression.tag, 'call');
        if (oneStep.expression.tag !== 'call') {
            throw new Error('Expected a residual call spine');
        }
        assert.equal(oneStep.expression.arguments.length, 1);
        assert.equal(oneStep.expression.arguments[0].plicity, 'implicit');
        assert.equal(oneStep.expression.arguments[0].value, second);
        assert.equal(
            oneStep.expression.arguments[0].provenance,
            secondArgumentProvenance
        );

        const completed = coreLfBetaWeakHead(multiargument, 2);
        assert.equal(completed.status, 'weak-head-normal');
        assert.equal(completed.steps, 2);
        assert.equal(kernelExpressionEquals(completed.expression, first), true);
        assert.deepEqual(
            completed.trace.map(entry => entry.residualArgumentCount),
            [1, 0]
        );

        const nested = kernelCall(
            kernelCall(
                curried,
                [{
                    plicity: 'explicit',
                    value: first
                }],
                because(21, 'LF-1A nested inner call')
            ),
            [{
                plicity: 'implicit',
                value: second
            }],
            because(21, 'LF-1A nested outer call')
        );
        const nestedResult = coreLfBetaWeakHead(nested, 2);
        assert.equal(nestedResult.status, 'weak-head-normal');
        assert.equal(nestedResult.steps, 2);
        assert.equal(
            kernelExpressionEquals(nestedResult.expression, first),
            true
        );
    });

    it('instantiates beneath a nested binder without capturing an ambient variable', () => {
        const openArgument = kernelBound(
            0,
            because(30, 'LF-1A ambient argument')
        );
        const returnOuter = lambda(
            'outer',
            'explicit',
            lambda(
                'inner',
                'explicit',
                kernelBound(1, because(30, 'LF-1A outer occurrence')),
                30
            ),
            30
        );
        const redex = kernelCall(
            returnOuter,
            [{
                plicity: 'explicit',
                value: openArgument
            }],
            because(30, 'LF-1A open capture test')
        );

        const result = coreLfBetaWeakHead(redex, 1);
        assert.equal(result.status, 'weak-head-normal');
        assert.equal(result.expression.tag, 'lambda');
        if (result.expression.tag !== 'lambda') {
            throw new Error('Expected the nested lambda result');
        }
        assert.equal(result.expression.body.tag, 'bound');
        assert.equal(
            result.expression.body.tag === 'bound'
                ? result.expression.body.index
                : undefined,
            1
        );

        const closed = lambda(
            'ambient',
            'explicit',
            result.expression,
            31
        );
        assert.doesNotThrow(() => kernelAssertScoped(closed));
        assert.equal(
            serializeKernelExpression(closed),
            'λ (v0 : Cat), λ (v1 : Cat), v0'
        );
    });

    it('reports plicity mismatch as stuck without consuming a beta step', () => {
        const mismatched = kernelCall(
            identity('implicit', 40),
            [{
                plicity: 'explicit',
                value: free('lf_beta_mismatch_argument', 40)
            }],
            because(40, 'LF-1A mismatched redex')
        );
        const head = coreLfBetaReduceHead(mismatched);
        assert.equal(head.status, 'stuck');
        assert.deepEqual(
            head.status === 'stuck'
                ? {
                    reason: head.reason,
                    expected: head.expectedPlicity,
                    actual: head.actualPlicity
                }
                : undefined,
            {
                reason: 'plicity-mismatch',
                expected: 'implicit',
                actual: 'explicit'
            }
        );

        const result = coreLfBetaWeakHead(mismatched, 4);
        assert.equal(result.status, 'stuck');
        assert.equal(result.expression, mismatched);
        assert.equal(result.steps, 0);
        assert.deepEqual(result.trace, []);

        const firstThenMismatch = kernelCall(
            lambda(
                'first',
                'explicit',
                identity('implicit', 41),
                41
            ),
            [
                {
                    plicity: 'explicit',
                    value: free('lf_beta_first_ok', 41)
                },
                {
                    plicity: 'explicit',
                    value: free('lf_beta_second_wrong_plicity', 41)
                }
            ],
            because(41, 'LF-1A later plicity mismatch')
        );
        const later = coreLfBetaWeakHead(firstThenMismatch, 4);
        assert.equal(later.status, 'stuck');
        assert.equal(later.steps, 1);
        assert.equal(later.trace.length, 1);
        assert.deepEqual(
            later.status === 'stuck'
                ? [later.expectedPlicity, later.actualPlicity]
                : undefined,
            ['implicit', 'explicit']
        );
    });

    it('distinguishes irreducible and structurally empty calls', () => {
        const nonLambda = kernelCall(
            free('lf_beta_function', 50),
            [{
                plicity: 'explicit',
                value: free('lf_beta_value', 50)
            }],
            because(50, 'LF-1A neutral call')
        );
        const neutral = coreLfBetaWeakHead(nonLambda, 0);
        assert.equal(neutral.status, 'weak-head-normal');
        assert.equal(
            neutral.status === 'weak-head-normal'
                ? neutral.reason
                : undefined,
            'head-not-lambda'
        );
        assert.equal(neutral.expression, nonLambda);

        const plain = free('lf_beta_plain', 51);
        const plainResult = coreLfBetaWeakHead(plain, 0);
        assert.equal(plainResult.status, 'weak-head-normal');
        assert.equal(
            plainResult.status === 'weak-head-normal'
                ? plainResult.reason
                : undefined,
            'not-a-call'
        );

        const empty: KernelCall = {
            tag: 'call',
            callee: identity('explicit', 52),
            arguments: Object.freeze([]),
            provenance: because(52, 'LF-1A structural empty call')
        };
        const emptyResult = coreLfBetaWeakHead(empty, 3);
        assert.equal(emptyResult.status, 'weak-head-normal');
        assert.equal(
            emptyResult.status === 'weak-head-normal'
                ? emptyResult.reason
                : undefined,
            'empty-call'
        );
        assert.equal(emptyResult.steps, 0);
    });

    it('returns structured budget exhaustion and rejects invalid limits', () => {
        const first = free('lf_beta_budget_first', 60);
        const second = free('lf_beta_budget_second', 60);
        const redex = kernelCall(
            lambda(
                'first',
                'explicit',
                lambda(
                    'second',
                    'explicit',
                    kernelBound(0, because(60, 'LF-1A budget result')),
                    60
                ),
                60
            ),
            [
                { plicity: 'explicit', value: first },
                { plicity: 'explicit', value: second }
            ],
            because(60, 'LF-1A two-step redex')
        );

        const zero = coreLfBetaWeakHead(redex, 0);
        assert.equal(zero.status, 'step-limit-exceeded');
        assert.equal(zero.steps, 0);
        assert.deepEqual(zero.trace, []);
        assert.deepEqual(
            zero.status === 'step-limit-exceeded' ? zero.next : undefined,
            {
                binderPlicity: 'explicit',
                argumentPlicity: 'explicit',
                residualArgumentCount: 1
            }
        );

        const one = coreLfBetaWeakHead(redex, 1);
        assert.equal(one.status, 'step-limit-exceeded');
        assert.equal(one.steps, 1);
        assert.equal(one.trace.length, 1);
        assert.equal(one.expression.tag, 'call');

        for (const invalid of [-1, 0.5, Number.NaN, Number.POSITIVE_INFINITY]) {
            assert.throws(
                () => coreLfBetaWeakHead(redex, invalid),
                (error: unknown) => {
                    assert.ok(error instanceof CoreLfEvaluationError);
                    assert.equal(error.code, 'INVALID_STEP_LIMIT');
                    assert.equal(error.provenance, redex.provenance);
                    return true;
                }
            );
        }
    });

    it(
        'agrees with bounded Lambdapi on a checked generic beta judgment',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const argument = free('lf_beta_A', 70);
            const redex = kernelCall(
                identity('explicit', 70),
                [{
                    plicity: 'explicit',
                    value: argument
                }],
                because(70, 'LF-1A Lambdapi beta redex')
            );
            const reduced = coreLfBetaWeakHead(redex, 1);
            assert.equal(reduced.status, 'weak-head-normal');
            assert.equal(
                kernelExpressionEquals(reduced.expression, argument),
                true
            );

            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: [{
                    name: 'lf_beta_A',
                    type: categoryUniverse(70),
                    span: at(70, 1, 20)
                }],
                assertions: [{
                    label: 'LF-1A well-typed direct beta redex',
                    term: redex,
                    type: categoryUniverse(70),
                    span: at(70, 21, 60)
                }],
                conversions: [{
                    label: 'LF-1A generic beta conversion',
                    left: redex,
                    right: argument,
                    span: at(71, 1, 60)
                }]
            };
            const serialized = serializeKernelProbe(probe);
            assert.match(
                serialized.source,
                /assert ⊢ \(λ \(v0 : Cat\), v0\) lf_beta_A : Cat;/
            );
            assert.match(
                serialized.source,
                /assert ⊢ \(λ \(v0 : Cat\), v0\) lf_beta_A ≡ lf_beta_A;/
            );

            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected LF-1A beta acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
