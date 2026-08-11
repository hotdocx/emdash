/**
 * Focused DTTLF LF-1C tests for combined conversion and candidate checking.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreChecker,
    CoreCheckerError,
    CoreElaborationSession,
    CoreLfChecker,
    CoreLfCatalogRuntime,
    CoreLfConversionError,
    CoreLfDeclarationEnvironment,
    CoreLfElaborationSession,
    KernelExpression,
    binderMode,
    checkLambdapiProbe,
    coreLfCombinedNormalize,
    coreLfCombinedWeakHead,
    coreLfDefinitionalCompare,
    createCoreLfChecker,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelMeta,
    kernelPi,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_lf_conversion.surface.ts';
const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const categoryUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'category-universe',
        [],
        because(line, 'LF-1C category universe')
    );

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `LF-1C free declaration ${name}`));

const objectTypeOf = (
    category: KernelExpression,
    line: number
): KernelExpression => {
    const nodeProvenance = because(line, 'LF-1C object type');
    return kernelApplication('decode', [{
        value: kernelApplication('object-classifier', [{
            value: category
        }], nodeProvenance)
    }], nodeProvenance);
};

const identity = (line: number): KernelExpression => kernelLambda(
    kernelBinder(
        'value',
        categoryUniverse(line),
        explicitFunctorial,
        because(line, 'LF-1C identity binder')
    ),
    kernelBound(0, because(line, 'LF-1C identity body')),
    because(line, 'LF-1C identity lambda')
);

const identityCall = (
    argument: KernelExpression,
    line: number
): KernelExpression => kernelCall(
    identity(line),
    [{
        plicity: 'explicit',
        value: argument
    }],
    because(line, 'LF-1C identity call')
);

interface CombinedFixture {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly call: KernelExpression;
    readonly runtimeRedex: KernelExpression;
    readonly expected: KernelExpression;
    readonly resultType: KernelExpression;
}

const combinedFixture = (): CombinedFixture => {
    let environment = CoreLfDeclarationEnvironment.empty();
    const assume = (
        name: string,
        type: KernelExpression,
        line: number
    ): void => {
        environment = environment.extend({
            name,
            type,
            mode: explicitFunctorial,
            provenance: because(line, `LF-1C runtime assumption ${name}`)
        });
    };
    assume('lf_combo_A', categoryUniverse(1), 1);
    assume('lf_combo_B', categoryUniverse(2), 2);
    const A = free('lf_combo_A', 3);
    const B = free('lf_combo_B', 3);
    assume('lf_combo_x', objectTypeOf(A, 3), 3);
    assume('lf_combo_y', objectTypeOf(A, 4), 4);
    const functorClassifier = kernelApplication(
        'functor-classifier',
        [{ value: A }, { value: B }],
        because(5, 'LF-1C runtime functor classifier')
    );
    assume(
        'lf_combo_F',
        kernelApplication('decode', [{
            value: functorClassifier
        }], because(5, 'LF-1C runtime functor type')),
        5
    );

    const x = free('lf_combo_x', 6);
    const y = free('lf_combo_y', 6);
    const F = free('lf_combo_F', 6);
    const sourceHom = kernelApplication('hom-category', [
        { value: A },
        { value: x },
        { value: y }
    ], because(6, 'LF-1C runtime source Hom category'));
    assume('lf_combo_f', objectTypeOf(sourceHom, 6), 6);
    const f = free('lf_combo_f', 7);
    const Fx = kernelApplication('functor-object', [
        { value: A },
        { value: B },
        { value: F },
        { value: x }
    ], because(7, 'LF-1C runtime F x'));
    const Fy = kernelApplication('functor-object', [
        { value: A },
        { value: B },
        { value: F },
        { value: y }
    ], because(7, 'LF-1C runtime F y'));
    const targetHom = kernelApplication('hom-category', [
        { value: B },
        { value: Fx },
        { value: Fy }
    ], because(7, 'LF-1C runtime target Hom category'));
    const full = kernelApplication('functor-hom-full', [
        { value: A },
        { value: B },
        { value: F },
        { value: x },
        { value: y }
    ], because(8, 'LF-1C full functor hom action'));
    const runtimeRedex = kernelApplication('functor-object', [
        { value: sourceHom },
        { value: targetHom },
        { value: full },
        { value: f }
    ], because(9, 'LF-1C reviewed runtime redex'));
    const expected = kernelApplication('functor-hom-capped', [
        { value: A },
        { value: B },
        { value: F },
        { value: x },
        { value: y },
        { value: f }
    ], because(10, 'LF-1C capped runtime result'));

    const resultType = objectTypeOf(
        targetHom,
        11
    );

    const functionType = kernelPi(
        kernelBinder(
            'value',
            resultType,
            explicitFunctorial,
            because(13, 'LF-1C combined function type binder')
        ),
        resultType,
        because(13, 'LF-1C combined function type')
    );
    const functionBody = kernelLambda(
        kernelBinder(
            'value',
            resultType,
            explicitFunctorial,
            because(14, 'LF-1C combined function body binder')
        ),
        kernelBound(0, because(14, 'LF-1C combined identity body')),
        because(14, 'LF-1C combined function body')
    );
    environment = environment.extend({
        name: 'lf_combo_function',
        type: functionType,
        mode: explicitFunctorial,
        provenance: because(15, 'LF-1C transparent combined definition'),
        body: functionBody,
        transparency: 'transparent'
    });
    const call = kernelCall(
        free('lf_combo_function', 16),
        [{
            plicity: 'explicit',
            value: runtimeRedex
        }],
        because(16, 'LF-1C delta-beta-runtime call')
    );
    return {
        environment,
        call,
        runtimeRedex,
        expected,
        resultType
    };
};

const simpleDefinitionEnvironment = (): CoreLfDeclarationEnvironment => {
    let environment = CoreLfDeclarationEnvironment.empty();
    environment = environment.extend({
        name: 'lf_check_A',
        type: categoryUniverse(30),
        mode: explicitFunctorial,
        provenance: because(30, 'LF-1C base category')
    });
    environment = environment.extend({
        name: 'lf_check_alias',
        type: categoryUniverse(31),
        mode: explicitFunctorial,
        provenance: because(31, 'LF-1C transparent category alias'),
        body: free('lf_check_A', 31),
        transparency: 'transparent'
    });
    environment = environment.extend({
        name: 'lf_check_x',
        type: objectTypeOf(free('lf_check_A', 32), 32),
        mode: explicitFunctorial,
        provenance: because(32, 'LF-1C object at base category')
    });
    return environment;
};

describe('TypeScript v3.2 DTTLF LF-1C combined conversion', () => {
    it('shares one ordered budget across delta, beta, and reviewed runtime', () => {
        const fixture_ = combinedFixture();
        const complete = coreLfCombinedWeakHead(
            fixture_.environment,
            fixture_.call,
            3
        );
        assert.equal(complete.status, 'weak-head-normal');
        assert.equal(complete.steps, 3);
        assert.deepEqual(
            complete.trace.map(entry => entry.kind),
            ['delta', 'beta', 'runtime']
        );
        assert.equal(
            kernelExpressionEquals(
                complete.expression,
                fixture_.expected
            ),
            true
        );
        assert.equal(
            complete.trace[2].kind === 'runtime'
                ? complete.trace[2].ruleId
                : undefined,
            'projection.functor-hom.evaluate'
        );

        const zero = coreLfCombinedWeakHead(
            fixture_.environment,
            fixture_.call,
            0
        );
        assert.equal(zero.status, 'step-limit-exceeded');
        assert.deepEqual(
            zero.status === 'step-limit-exceeded' ? zero.next : undefined,
            {
                kind: 'delta',
                declarationName: 'lf_combo_function',
                declarationOrdinal: 6
            }
        );

        const two = coreLfCombinedWeakHead(
            fixture_.environment,
            fixture_.call,
            2
        );
        assert.equal(two.status, 'step-limit-exceeded');
        assert.equal(two.steps, 2);
        assert.deepEqual(
            two.trace.map(entry => entry.kind),
            ['delta', 'beta']
        );
        assert.deepEqual(
            two.status === 'step-limit-exceeded' ? two.next : undefined,
            {
                kind: 'runtime',
                ruleId: 'projection.functor-hom.evaluate',
                ruleIndex: 0
            }
        );
    });

    it('closes conversion by congruence with one global path-aware trace', () => {
        const fixture_ = combinedFixture();
        const left = kernelApplication('decode', [{
            value: fixture_.call
        }], because(20, 'LF-1C left congruence wrapper'));
        const right = kernelApplication('decode', [{
            value: fixture_.expected
        }], because(20, 'LF-1C right congruence wrapper'));

        const equal = coreLfDefinitionalCompare(
            fixture_.environment,
            left,
            right,
            3
        );
        assert.equal(equal.status, 'equal');
        assert.equal(equal.steps, 3);
        assert.deepEqual(
            equal.trace.map(entry => entry.reduction.kind),
            ['delta', 'beta', 'runtime']
        );
        assert.deepEqual(
            equal.trace.map(entry => entry.path),
            [
                ['$', 'application:decode:argument:0'],
                ['$', 'application:decode:argument:0'],
                ['$', 'application:decode:argument:0']
            ]
        );

        const exhausted = coreLfDefinitionalCompare(
            fixture_.environment,
            left,
            right,
            2
        );
        assert.equal(exhausted.status, 'step-limit-exceeded');
        assert.equal(exhausted.steps, 2);
        assert.deepEqual(
            exhausted.status === 'step-limit-exceeded'
                ? exhausted.next
                : undefined,
            {
                kind: 'runtime',
                ruleId: 'projection.functor-hom.evaluate',
                ruleIndex: 0
            }
        );
        assert.deepEqual(
            exhausted.status === 'step-limit-exceeded'
                ? exhausted.path
                : undefined,
            ['$', 'application:decode:argument:0']
        );
    });

    it('retries a mismatched parent after nested normalization exposes a redex', () => {
        let environment = CoreLfDeclarationEnvironment.empty();
        environment = environment.extend({
            name: 'lf_parent_alias',
            type: categoryUniverse(25),
            mode: explicitFunctorial,
            provenance: because(25, 'LF-1C parent-redex alias'),
            body: kernelApplication(
                'category-of-categories',
                [],
                because(25, 'LF-1C parent-redex alias body')
            ),
            transparency: 'transparent'
        });
        const normalizedRedex = kernelApplication(
            'object-classifier',
            [{
                value: kernelApplication(
                    'category-of-categories',
                    [],
                    because(26, 'LF-1C normalized parent argument')
                )
            }],
            because(26, 'LF-1C normalized parent redex')
        );
        const left = categoryUniverse(27);
        const runtime: CoreLfCatalogRuntime = Object.freeze({
            revision: 'LF-1C-PARENT-AFTER-CHILD-1',
            ruleIds: Object.freeze(['fixture.parent-after-child']),
            rewriteHead(expression) {
                if (!kernelExpressionEquals(expression, normalizedRedex)) {
                    return Object.freeze({
                        status: 'irreducible',
                        expression
                    });
                }
                return Object.freeze({
                    status: 'rewritten',
                    ruleId: 'fixture.parent-after-child',
                    ruleIndex: 0,
                    before: expression,
                    after: left,
                    match: Object.freeze({
                        ruleId: 'fixture.parent-after-child',
                        bindings: Object.freeze([])
                    })
                });
            }
        });
        const right = kernelApplication(
            'object-classifier',
            [{ value: free('lf_parent_alias', 28) }],
            because(28, 'LF-1C parent-before-child wrapper')
        );

        const comparison = coreLfDefinitionalCompare(
            environment,
            left,
            right,
            2,
            undefined,
            runtime
        );
        assert.equal(comparison.status, 'equal');
        assert.deepEqual(
            comparison.trace.map(entry => ({
                kind: entry.reduction.kind,
                path: entry.path,
                ruleId: entry.reduction.kind === 'runtime'
                    ? entry.reduction.ruleId
                    : undefined
            })),
            [
                {
                    kind: 'delta',
                    path: [
                        '$',
                        'application:object-classifier:argument:0'
                    ],
                    ruleId: undefined
                },
                {
                    kind: 'runtime',
                    path: ['$'],
                    ruleId: 'fixture.parent-after-child'
                }
            ]
        );

        const exhausted = coreLfDefinitionalCompare(
            environment,
            left,
            right,
            1,
            undefined,
            runtime
        );
        assert.equal(exhausted.status, 'step-limit-exceeded');
        assert.deepEqual(
            exhausted.status === 'step-limit-exceeded'
                ? {
                    side: exhausted.side,
                    path: exhausted.path,
                    next: exhausted.next
                }
                : undefined,
            {
                side: 'right',
                path: ['$'],
                next: {
                    kind: 'runtime',
                    ruleId: 'fixture.parent-after-child',
                    ruleIndex: 0
                }
            }
        );
    });

    it('normalizes descendants and retries their parent under one budget',
        () => {
            let environment = CoreLfDeclarationEnvironment.empty();
            environment = environment.extend({
                name: 'lf_normalize_alias',
                type: categoryUniverse(29),
                mode: explicitFunctorial,
                provenance: because(29, 'LF normalizer nested alias'),
                body: kernelApplication(
                    'category-of-categories',
                    [],
                    because(29, 'LF normalizer alias body')
                ),
                transparency: 'transparent'
            });
            const parentRedex = kernelApplication(
                'object-classifier',
                [{
                    value: kernelApplication(
                        'category-of-categories',
                        [],
                        because(29, 'LF normalizer parent argument')
                    )
                }],
                because(29, 'LF normalizer parent redex')
            );
            const expected = categoryUniverse(29);
            const runtime: CoreLfCatalogRuntime = Object.freeze({
                revision: 'LF-NORMALIZE-PARENT-1',
                ruleIds: Object.freeze(['fixture.normalize-parent']),
                rewriteHead(expression) {
                    if (!kernelExpressionEquals(expression, parentRedex)) {
                        return Object.freeze({
                            status: 'irreducible',
                            expression
                        });
                    }
                    return Object.freeze({
                        status: 'rewritten',
                        ruleId: 'fixture.normalize-parent',
                        ruleIndex: 0,
                        before: expression,
                        after: expected,
                        match: Object.freeze({
                            ruleId: 'fixture.normalize-parent',
                            bindings: Object.freeze([])
                        })
                    });
                }
            });
            const input = kernelApplication(
                'object-classifier',
                [{ value: free('lf_normalize_alias', 29) }],
                because(29, 'LF normalizer input')
            );

            const normalized = coreLfCombinedNormalize(
                environment,
                input,
                2,
                undefined,
                runtime
            );
            assert.equal(normalized.status, 'normal');
            assert.equal(normalized.steps, 2);
            assert.equal(
                kernelExpressionEquals(
                    normalized.expression,
                    expected
                ),
                true
            );
            assert.deepEqual(
                normalized.trace.map(entry => ({
                    kind: entry.reduction.kind,
                    path: entry.path
                })),
                [
                    {
                        kind: 'delta',
                        path: [
                            '$',
                            'application:object-classifier:argument:0'
                        ]
                    },
                    { kind: 'runtime', path: ['$'] }
                ]
            );

            const exhausted = coreLfCombinedNormalize(
                environment,
                input,
                1,
                undefined,
                runtime
            );
            assert.equal(exhausted.status, 'step-limit-exceeded');
            assert.deepEqual(
                exhausted.status === 'step-limit-exceeded'
                    ? exhausted.next
                    : undefined,
                {
                    kind: 'runtime',
                    ruleId: 'fixture.normalize-parent',
                    ruleIndex: 0
                }
            );
        });

    it('closes a terminal paired miss through exact shared normal forms', () => {
        let environment = CoreLfDeclarationEnvironment.empty();
        environment = environment.extend({
            name: 'lf_terminal_closure_alias',
            type: categoryUniverse(35),
            mode: explicitFunctorial,
            provenance: because(35, 'LF terminal-closure alias'),
            body: kernelApplication(
                'category-of-categories',
                [],
                because(35, 'LF terminal-closure alias body')
            ),
            transparency: 'transparent'
        });
        const alias = free('lf_terminal_closure_alias', 36);
        const normalizedType = kernelApplication(
            'category-of-categories',
            [],
            because(36, 'LF terminal-closure normalized binder type')
        );
        const explicit = kernelLambda(
            kernelBinder(
                'explicitValue',
                alias,
                explicitFunctorial,
                because(36, 'LF terminal-closure explicit binder')
            ),
            kernelBound(0, because(36, 'LF terminal-closure explicit body')),
            because(36, 'LF terminal-closure explicit input')
        );
        const implicit = kernelLambda(
            kernelBinder(
                'implicitValue',
                alias,
                binderMode('implicit', 'functorial'),
                because(37, 'LF terminal-closure implicit binder')
            ),
            kernelBound(0, because(37, 'LF terminal-closure implicit body')),
            because(37, 'LF terminal-closure implicit input')
        );
        const normalizedExplicit = kernelLambda(
            kernelBinder(
                'explicitValue',
                normalizedType,
                explicitFunctorial,
                because(38, 'LF terminal-closure normalized explicit binder')
            ),
            kernelBound(0, because(38, 'LF terminal-closure normalized explicit body')),
            because(38, 'LF terminal-closure normalized explicit input')
        );
        const normalizedImplicit = kernelLambda(
            kernelBinder(
                'implicitValue',
                normalizedType,
                binderMode('implicit', 'functorial'),
                because(39, 'LF terminal-closure normalized implicit binder')
            ),
            kernelBound(0, because(39, 'LF terminal-closure normalized implicit body')),
            because(39, 'LF terminal-closure normalized implicit input')
        );
        const sharedNormalForm = kernelApplication(
            'category-of-categories',
            [],
            because(39, 'LF terminal-closure shared normal form')
        );
        const runtime: CoreLfCatalogRuntime = Object.freeze({
            revision: 'LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
            ruleIds: Object.freeze([
                'fixture.terminal-closure.explicit',
                'fixture.terminal-closure.implicit'
            ]),
            rewriteHead(expression) {
                const rule = kernelExpressionEquals(
                    expression,
                    normalizedExplicit
                )
                    ? {
                        ruleId: 'fixture.terminal-closure.explicit',
                        ruleIndex: 0
                    }
                    : kernelExpressionEquals(expression, normalizedImplicit)
                        ? {
                            ruleId: 'fixture.terminal-closure.implicit',
                            ruleIndex: 1
                        }
                        : undefined;
                if (rule === undefined) {
                    return Object.freeze({
                        status: 'irreducible',
                        expression
                    });
                }
                return Object.freeze({
                    status: 'rewritten',
                    ...rule,
                    before: expression,
                    after: sharedNormalForm,
                    match: Object.freeze({
                        ruleId: rule.ruleId,
                        bindings: Object.freeze([])
                    })
                });
            }
        });

        const assertClosed = (
            left: KernelExpression,
            right: KernelExpression,
            expectedRuleIds: readonly string[]
        ): void => {
            const comparison = coreLfDefinitionalCompare(
                environment,
                left,
                right,
                4,
                undefined,
                runtime
            );
            assert.equal(comparison.status, 'equal');
            assert.equal(comparison.steps, 4);
            assert.deepEqual(
                comparison.trace.map(entry => ({
                    side: entry.side,
                    path: entry.path,
                    kind: entry.reduction.kind,
                    ruleId: entry.reduction.kind === 'runtime'
                        ? entry.reduction.ruleId
                        : undefined
                })),
                [
                    {
                        side: 'left',
                        path: ['$', 'lambda:binder-type'],
                        kind: 'delta',
                        ruleId: undefined
                    },
                    {
                        side: 'left',
                        path: ['$'],
                        kind: 'runtime',
                        ruleId: expectedRuleIds[0]
                    },
                    {
                        side: 'right',
                        path: ['$', 'lambda:binder-type'],
                        kind: 'delta',
                        ruleId: undefined
                    },
                    {
                        side: 'right',
                        path: ['$'],
                        kind: 'runtime',
                        ruleId: expectedRuleIds[1]
                    }
                ]
            );
        };

        assertClosed(explicit, implicit, [
            'fixture.terminal-closure.explicit',
            'fixture.terminal-closure.implicit'
        ]);
        assertClosed(implicit, explicit, [
            'fixture.terminal-closure.implicit',
            'fixture.terminal-closure.explicit'
        ]);

        const exhausted = coreLfDefinitionalCompare(
            environment,
            explicit,
            implicit,
            3,
            undefined,
            runtime
        );
        assert.equal(exhausted.status, 'step-limit-exceeded');
        assert.equal(exhausted.steps, 3);
        assert.deepEqual(
            exhausted.status === 'step-limit-exceeded'
                ? {
                    side: exhausted.side,
                    path: exhausted.path,
                    next: exhausted.next
                }
                : undefined,
            {
                side: 'right',
                path: ['$'],
                next: {
                    kind: 'runtime',
                    ruleId: 'fixture.terminal-closure.implicit',
                    ruleIndex: 1
                }
            }
        );

        const distinct = coreLfDefinitionalCompare(
            environment,
            explicit,
            categoryUniverse(39),
            4,
            undefined,
            runtime
        );
        assert.equal(distinct.status, 'not-equal');
        assert.equal(
            distinct.status === 'not-equal'
                ? distinct.mismatch.code
                : undefined,
            'OWNER_MISMATCH'
        );
    });

    it('replays original roots after paired over-normalization', () => {
        let environment = CoreLfDeclarationEnvironment.empty();
        const assumeCategory = (name: string, line: number): void => {
            environment = environment.extend({
                name,
                type: categoryUniverse(line),
                mode: explicitFunctorial,
                provenance: because(line, `LF source-replay category ${name}`)
            });
        };
        assumeCategory('lf_replay_A', 45);
        assumeCategory('lf_replay_B', 46);
        const A = free('lf_replay_A', 47);
        const B = free('lf_replay_B', 47);
        const defineAlias = (
            name: string,
            body: KernelExpression,
            line: number
        ): void => {
            environment = environment.extend({
                name,
                type: categoryUniverse(line),
                mode: explicitFunctorial,
                provenance: because(line, `LF source-replay alias ${name}`),
                body,
                transparency: 'transparent'
            });
        };
        defineAlias('lf_replay_gate', A, 47);
        defineAlias('lf_replay_left_payload', A, 48);
        defineAlias('lf_replay_right_payload', B, 49);

        const parent = free('lf_replay_parent', 50);
        const gate = free('lf_replay_gate', 50);
        const leftPayload = free('lf_replay_left_payload', 50);
        const rightPayload = free('lf_replay_right_payload', 50);
        const parentCall = (
            first: KernelExpression,
            second: KernelExpression,
            line: number
        ): KernelExpression => kernelCall(parent, [
            { plicity: 'explicit', value: first },
            { plicity: 'explicit', value: second }
        ], because(line, 'LF source-replay parent call'));
        const left = parentCall(gate, leftPayload, 50);
        const right = parentCall(gate, rightPayload, 51);
        const leftIntermediate = parentCall(A, leftPayload, 52);
        const rightIntermediate = parentCall(A, rightPayload, 53);
        const sharedNormalForm = categoryUniverse(54);
        const runtime: CoreLfCatalogRuntime = Object.freeze({
            revision: 'LF-COMPARISON-SOURCE-REPLAY-1',
            ruleIds: Object.freeze([
                'fixture.source-replay.left-intermediate',
                'fixture.source-replay.right-intermediate'
            ]),
            rewriteHead(expression) {
                const rule = kernelExpressionEquals(
                    expression,
                    leftIntermediate
                )
                    ? {
                        ruleId: 'fixture.source-replay.left-intermediate',
                        ruleIndex: 0
                    }
                    : kernelExpressionEquals(expression, rightIntermediate)
                        ? {
                            ruleId:
                                'fixture.source-replay.right-intermediate',
                            ruleIndex: 1
                        }
                        : undefined;
                if (rule === undefined) {
                    return Object.freeze({
                        status: 'irreducible',
                        expression
                    });
                }
                return Object.freeze({
                    status: 'rewritten',
                    ...rule,
                    before: expression,
                    after: sharedNormalForm,
                    match: Object.freeze({
                        ruleId: rule.ruleId,
                        bindings: Object.freeze([])
                    })
                });
            }
        });

        const assertReplay = (
            first: KernelExpression,
            second: KernelExpression,
            expectedReplayRuleIds: readonly string[]
        ): void => {
            const comparison = coreLfDefinitionalCompare(
                environment,
                first,
                second,
                8,
                undefined,
                runtime
            );
            assert.equal(comparison.status, 'equal');
            assert.equal(comparison.steps, 8);
            assert.deepEqual(
                comparison.trace.slice(-4).map(entry => ({
                    side: entry.side,
                    path: entry.path,
                    kind: entry.reduction.kind,
                    ruleId: entry.reduction.kind === 'runtime'
                        ? entry.reduction.ruleId
                        : undefined
                })),
                [
                    {
                        side: 'left',
                        path: ['$','call:argument:0'],
                        kind: 'delta',
                        ruleId: undefined
                    },
                    {
                        side: 'left',
                        path: ['$'],
                        kind: 'runtime',
                        ruleId: expectedReplayRuleIds[0]
                    },
                    {
                        side: 'right',
                        path: ['$','call:argument:0'],
                        kind: 'delta',
                        ruleId: undefined
                    },
                    {
                        side: 'right',
                        path: ['$'],
                        kind: 'runtime',
                        ruleId: expectedReplayRuleIds[1]
                    }
                ]
            );
        };

        assertReplay(left, right, [
            'fixture.source-replay.left-intermediate',
            'fixture.source-replay.right-intermediate'
        ]);
        assertReplay(right, left, [
            'fixture.source-replay.right-intermediate',
            'fixture.source-replay.left-intermediate'
        ]);

        const exhausted = coreLfDefinitionalCompare(
            environment,
            left,
            right,
            7,
            undefined,
            runtime
        );
        assert.equal(exhausted.status, 'step-limit-exceeded');
        assert.equal(exhausted.steps, 7);
        assert.deepEqual(
            exhausted.status === 'step-limit-exceeded'
                ? {
                    side: exhausted.side,
                    path: exhausted.path,
                    next: exhausted.next
                }
                : undefined,
            {
                side: 'right',
                path: ['$'],
                next: {
                    kind: 'runtime',
                    ruleId: 'fixture.source-replay.right-intermediate',
                    ruleIndex: 1
                }
            }
        );
    });

    it('counts solved-meta zonking in the same budget as transparent delta', () => {
        let environment = CoreLfDeclarationEnvironment.empty();
        environment = environment.extend({
            name: 'lf_zonk_A',
            type: categoryUniverse(40),
            mode: explicitFunctorial,
            provenance: because(40, 'LF-1C zonk base')
        });
        environment = environment.extend({
            name: 'lf_zonk_alias',
            type: categoryUniverse(41),
            mode: explicitFunctorial,
            provenance: because(41, 'LF-1C zonk alias'),
            body: free('lf_zonk_A', 41),
            transparency: 'transparent'
        });
        const session = new CoreLfElaborationSession(environment);
        const meta = session.freshMeta(
            session.rootContext,
            categoryUniverse(42),
            because(42, 'LF-1C zonked meta')
        );
        session.solve(meta, free('lf_zonk_alias', 42));

        const comparison = coreLfDefinitionalCompare(
            environment,
            meta,
            free('lf_zonk_A', 43),
            2,
            session
        );
        assert.equal(comparison.status, 'equal');
        assert.deepEqual(
            comparison.trace.map(entry => entry.reduction.kind),
            ['zonk', 'delta']
        );

        const exhausted = coreLfDefinitionalCompare(
            environment,
            meta,
            free('lf_zonk_A', 44),
            1,
            session
        );
        assert.equal(exhausted.status, 'step-limit-exceeded');
        assert.deepEqual(
            exhausted.status === 'step-limit-exceeded'
                ? exhausted.next
                : undefined,
            {
                kind: 'delta',
                declarationName: 'lf_zonk_alias',
                declarationOrdinal: 1
            }
        );
    });

    it('checks transparent and beta-convertible types only on the candidate path', () => {
        const environment = simpleDefinitionEnvironment();
        const oldChecker = new CoreChecker(
            new CoreElaborationSession(environment.coreEnvironment)
        );
        const candidate = createCoreLfChecker(environment);
        const term = free('lf_check_x', 50);
        const aliasExpected = objectTypeOf(
            free('lf_check_alias', 50),
            50
        );

        assert.throws(
            () => oldChecker.check(
                oldChecker.rootContext,
                term,
                aliasExpected
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                return true;
            }
        );
        assert.doesNotThrow(() => candidate.check(
            candidate.rootContext,
            term,
            aliasExpected
        ));
        assert.ok(candidate.checkerComparisonRecords.some(result =>
            result.trace.some(entry => entry.reduction.kind === 'delta')
        ));

        const betaExpected = objectTypeOf(
            identityCall(free('lf_check_A', 51), 51),
            51
        );
        assert.doesNotThrow(() => candidate.check(
            candidate.rootContext,
            term,
            betaExpected
        ));
        assert.ok(candidate.checkerComparisonRecords.some(result =>
            result.trace.some(entry => entry.reduction.kind === 'beta')
        ));

        const directCall = identityCall(free('lf_check_A', 52), 52);
        assert.throws(
            () => oldChecker.infer(oldChecker.rootContext, directCall),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'CANNOT_INFER_LAMBDA');
                return true;
            }
        );
        const inferred = candidate.infer(
            candidate.rootContext,
            directCall
        );
        assert.equal(
            kernelExpressionEquals(
                inferred.type as KernelExpression,
                categoryUniverse(52)
            ),
            true
        );
    });

    it('revisits a Miller-pattern solution through candidate beta conversion', () => {
        let environment = CoreLfDeclarationEnvironment.empty();
        environment = environment.extend({
            name: 'lf_pattern_A',
            type: categoryUniverse(60),
            mode: explicitFunctorial,
            provenance: because(60, 'LF-1C pattern category')
        });
        const session = new CoreLfElaborationSession(environment);
        const xContext = session.rootContext.extend({
            name: 'x',
            type: categoryUniverse(61),
            mode: explicitFunctorial,
            provenance: because(61, 'LF-1C pattern x')
        });
        const meta = session.freshMeta(
            xContext,
            categoryUniverse(62),
            because(62, 'LF-1C pattern meta')
        );
        const xyContext = xContext.extend({
            name: 'y',
            type: categoryUniverse(63),
            mode: explicitFunctorial,
            provenance: because(63, 'LF-1C pattern y')
        });
        const occurrence = kernelMeta(
            meta.identity,
            [kernelBound(1, because(64, 'LF-1C weakened pattern x'))],
            because(64, 'LF-1C weakened pattern occurrence')
        );
        const rigid = identityCall(
            kernelBound(1, because(65, 'LF-1C rigid x')),
            65
        );
        session.addConstraint(
            xyContext,
            occurrence,
            rigid,
            because(66, 'LF-1C pattern assignment')
        );
        session.addConstraint(
            xyContext,
            occurrence,
            kernelBound(1, because(67, 'LF-1C revisited x')),
            because(67, 'LF-1C pattern conversion revisit')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'solved');
        assert.deepEqual(
            report.constraints.map(constraint => constraint.reason),
            [
                'ASSIGNED_LEFT_PATTERN_META',
                'DEFINITIONAL_EQUALITY'
            ]
        );
        assert.ok(session.constraintComparisonRecords.some(result =>
            result.status === 'equal' &&
            result.trace.some(entry => entry.reduction.kind === 'beta')
        ));

        const zonked = session.zonk(occurrence);
        const reduced = coreLfCombinedWeakHead(
            environment,
            zonked,
            1
        );
        assert.equal(reduced.status, 'weak-head-normal');
        assert.equal(
            kernelExpressionEquals(
                reduced.expression,
                kernelBound(1, because(68, 'LF-1C expected pattern x'))
            ),
            true
        );
    });

    it('keeps plicity mismatch stuck and eta outside candidate conversion', () => {
        const environment = simpleDefinitionEnvironment();
        const mismatch = kernelCall(
            kernelLambda(
                kernelBinder(
                    'implicitValue',
                    categoryUniverse(70),
                    binderMode('implicit', 'functorial'),
                    because(70, 'LF-1C implicit binder')
                ),
                kernelBound(0, because(70, 'LF-1C implicit body')),
                because(70, 'LF-1C implicit lambda')
            ),
            [{
                plicity: 'explicit',
                value: free('lf_check_A', 70)
            }],
            because(70, 'LF-1C plicity mismatch')
        );
        const stuck = coreLfCombinedWeakHead(
            environment,
            mismatch,
            4
        );
        assert.equal(stuck.status, 'stuck');
        assert.equal(stuck.steps, 0);

        const plicityComparison = coreLfDefinitionalCompare(
            environment,
            mismatch,
            free('lf_check_A', 70),
            4
        );
        assert.equal(plicityComparison.status, 'not-equal');
        assert.equal(
            plicityComparison.status === 'not-equal'
                ? plicityComparison.mismatch.code
                : undefined,
            'PLICITY_MISMATCH'
        );

        const structuralPlicityCallee = free(
            'lf_structural_plicity_function',
            70
        );
        const explicitApplication = kernelCall(structuralPlicityCallee, [{
            plicity: 'explicit',
            value: categoryUniverse(70)
        }], because(70, 'LF-1C explicit structural plicity'));
        const implicitApplication = kernelCall(structuralPlicityCallee, [{
            plicity: 'implicit',
            value: categoryUniverse(70)
        }], because(70, 'LF-1C implicit structural plicity'));
        const structuralPlicity = coreLfDefinitionalCompare(
            environment,
            explicitApplication,
            implicitApplication,
            4
        );
        assert.equal(structuralPlicity.status, 'not-equal');
        assert.equal(
            structuralPlicity.status === 'not-equal'
                ? structuralPlicity.mismatch.code
                : undefined,
            'PLICITY_MISMATCH'
        );
        assert.equal(
            structuralPlicity.status === 'not-equal'
                ? structuralPlicity.normalizedLeft.tag
                : undefined,
            'call'
        );
        assert.equal(
            structuralPlicity.status === 'not-equal'
                ? structuralPlicity.normalizedRight.tag
                : undefined,
            'call'
        );

        const function_ = free('lf_eta_function', 71);
        const etaExpansion = kernelLambda(
            kernelBinder(
                'value',
                categoryUniverse(71),
                explicitFunctorial,
                because(71, 'LF-1C eta binder')
            ),
            kernelCall(
                function_,
                [{
                    plicity: 'explicit',
                    value: kernelBound(0, because(71, 'LF-1C eta value'))
                }],
                because(71, 'LF-1C eta body')
            ),
            because(71, 'LF-1C eta expansion')
        );
        const eta = coreLfDefinitionalCompare(
            environment,
            etaExpansion,
            function_,
            8
        );
        assert.equal(eta.status, 'not-equal');
        assert.equal(
            eta.status === 'not-equal'
                ? eta.mismatch.code
                : undefined,
            'TAG_MISMATCH'
        );
    });

    it('rejects a conversion session from another declaration environment', () => {
        const left = simpleDefinitionEnvironment();
        let right = CoreLfDeclarationEnvironment.empty();
        right = right.extend({
            name: 'lf_foreign_A',
            type: categoryUniverse(80),
            mode: explicitFunctorial,
            provenance: because(80, 'LF-1C foreign category')
        });
        const foreign = new CoreLfElaborationSession(right);
        assert.throws(
            () => coreLfCombinedWeakHead(
                left,
                free('lf_check_alias', 81),
                2,
                foreign
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfConversionError);
                assert.equal(
                    error.code,
                    'FOREIGN_DECLARATION_ENVIRONMENT'
                );
                return true;
            }
        );
    });

    it(
        'agrees with bounded Lambdapi on delta-beta-runtime conversion',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture_ = combinedFixture();
            const serialized = serializeCoreLfKernelProbe({
                environment: fixture_.environment,
                assertions: [{
                    label: 'LF-1C combined call typing',
                    term: fixture_.call,
                    type: fixture_.resultType,
                    span: at(90, 1, 60)
                }],
                conversions: [{
                    label: 'LF-1C delta-beta-runtime conversion',
                    left: fixture_.call,
                    right: fixture_.expected,
                    span: at(91, 1, 80)
                }]
            });
            assert.match(
                serialized.source,
                /symbol lf_combo_function : .* ≔ λ /
            );
            assert.match(
                serialized.source,
                /assert ⊢ lf_combo_function .*fapp0.* ≡ /
            );

            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected LF-1C combined acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
