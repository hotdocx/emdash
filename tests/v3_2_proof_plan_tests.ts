/**
 * Focused AI-PROOF-1 tests for inert plans and stable named Core goals.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    BinderMode,
    CoreBindingInput,
    CoreChecker,
    CoreCheckerError,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreProofPlan,
    CoreProofPlanError,
    CoreProofRefiner,
    CORE_PROOF_PLAN_PROFILE,
    CORE_PROOF_PLAN_MACRO_PROFILE,
    KernelExpression,
    binderMode,
    coreProofPlanApply,
    coreProofPlanConstructor,
    coreProofPlanExact,
    coreProofPlanHave,
    coreProofPlanHole,
    coreProofPlanIntro,
    executeCoreProofPlan,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelPi,
    kernelUniverse,
    provenance,
    serializeCoreProofPlanState,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_proof_plan.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');
const explicitNatural = binderMode('explicit', 'natural');

const universe = (line: number, detail = 'AI-PROOF-1 universe') =>
    kernelUniverse(because(line, detail));

const free = (name: string, line: number, detail: string) =>
    kernelFree(name, because(line, detail));

const bound = (index: number, line: number, detail: string) =>
    kernelBound(index, because(line, detail));

const pi = (
    name: string,
    type: KernelExpression,
    mode: BinderMode,
    body: KernelExpression,
    line: number,
    detail: string
) => kernelPi(
    kernelBinder(
        name,
        type,
        mode,
        because(line, `${detail} binder`)
    ),
    body,
    because(line, detail)
);

const call = (
    callee: KernelExpression,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: KernelExpression;
    }[],
    line: number,
    detail: string
) => kernelCall(
    callee,
    arguments_,
    because(line, detail)
);

const declaration = (
    name: string,
    type: KernelExpression,
    line: number
): CoreBindingInput => ({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `AI-PROOF-1 declaration ${name}`)
});

const proofEnvironment = (): CoreDeclarationEnvironment => {
    let environment = CoreDeclarationEnvironment.empty();
    environment = environment.extend(declaration(
        'plan_A',
        universe(1),
        1
    ));
    environment = environment.extend(declaration(
        'plan_B',
        universe(2),
        2
    ));

    const typeA = free('plan_A', 3, 'AI-PROOF-1 type A');
    const typeB = free('plan_B', 4, 'AI-PROOF-1 type B');
    environment = environment.extend(declaration('plan_z', typeA, 3));
    environment = environment.extend(declaration('plan_b', typeB, 4));
    environment = environment.extend(declaration(
        'plan_s',
        pi(
            'predecessor',
            typeA,
            explicitFunctorial,
            typeA,
            5,
            'AI-PROOF-1 unary function'
        ),
        5
    ));
    environment = environment.extend(declaration(
        'plan_const',
        pi(
            'left',
            typeA,
            explicitFunctorial,
            pi(
                'right',
                typeB,
                explicitFunctorial,
                typeA,
                6,
                'AI-PROOF-1 constant right binder'
            ),
            6,
            'AI-PROOF-1 constant left binder'
        ),
        6
    ));
    environment = environment.extend(declaration(
        'plan_P',
        pi(
            'index',
            typeA,
            explicitFunctorial,
            universe(7),
            7,
            'AI-PROOF-1 family'
        ),
        7
    ));
    environment = environment.extend(declaration(
        'plan_k',
        pi(
            'index',
            typeA,
            explicitFunctorial,
            pi(
                'witness',
                call(
                    free('plan_P', 8, 'AI-PROOF-1 family use'),
                    [{
                        plicity: 'explicit',
                        value: bound(
                            0,
                            8,
                            'AI-PROOF-1 dependent index'
                        )
                    }],
                    8,
                    'AI-PROOF-1 dependent premise'
                ),
                explicitFunctorial,
                typeA,
                8,
                'AI-PROOF-1 witness binder'
            ),
            8,
            'AI-PROOF-1 indexed eliminator'
        ),
        8
    ));
    return environment;
};

interface ProofFixture {
    readonly session: CoreElaborationSession;
    readonly checker: CoreChecker;
}

const proofFixture = (): ProofFixture => {
    const session = new CoreElaborationSession(proofEnvironment());
    const checker = new CoreChecker(session);
    checker.validateEnvironment();
    return { session, checker };
};

const typeA = (line: number) =>
    free('plan_A', line, 'AI-PROOF-1 use of type A');

const typeB = (line: number) =>
    free('plan_B', line, 'AI-PROOF-1 use of type B');

const freshRoot = (
    session: CoreElaborationSession,
    type: KernelExpression,
    line: number
) => session.freshMeta(
    session.rootContext,
    type,
    because(line, 'AI-PROOF-1 root goal')
);

describe('TypeScript v3.2 AI-PROOF-1 proof plans', () => {
    it('replays a compact immutable intro/exact identity plan', () => {
        const { session, checker } = proofFixture();
        const identityType = pi(
            'value',
            typeA(20),
            explicitNatural,
            typeA(20),
            20,
            'AI-PROOF-1 identity type'
        );
        const root = freshRoot(session, identityType, 21);
        const plan = coreProofPlanIntro(
            coreProofPlanExact(bound(
                0,
                23,
                'AI-PROOF-1 introduced value'
            )),
            {
                name: 'renamed',
                provenance: because(22, 'AI-PROOF-1 intro')
            }
        );

        assert.equal(Object.isFrozen(plan), true);
        assert.equal(Object.isFrozen(plan.body), true);

        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );

        assert.equal(execution.state.status, 'complete');
        assert.deepEqual(
            execution.trace.map(step => step.operation),
            ['intro', 'exact']
        );
        assert.deepEqual(execution.snapshot.goals, []);
        assert.match(execution.snapshot.term, /^lambda renamed/);
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            execution.term,
            identityType
        ));
    });

    it('maps ordered apply premises to checked exact subplans', () => {
        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(30), 30);
        const plan = coreProofPlanApply(
            free('plan_const', 31, 'AI-PROOF-1 applied constant'),
            [
                coreProofPlanExact(free(
                    'plan_z',
                    32,
                    'AI-PROOF-1 left premise'
                )),
                coreProofPlanExact(free(
                    'plan_b',
                    33,
                    'AI-PROOF-1 right premise'
                ))
            ],
            { id: 'constant_application' }
        );

        assert.equal(Object.isFrozen(plan.premises), true);
        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );

        assert.equal(execution.state.status, 'complete');
        assert.deepEqual(
            execution.trace.map(step => step.operation),
            ['apply', 'exact', 'exact']
        );
        assert.equal(execution.trace[0].introducedGoalCount, 2);
        assert.equal(execution.term.tag, 'call');
        const expected = call(
            free('plan_const', 34, 'AI-PROOF-1 expected constant'),
            [
                {
                    plicity: 'explicit',
                    value: free(
                        'plan_z',
                        34,
                        'AI-PROOF-1 expected left'
                    )
                },
                {
                    plicity: 'explicit',
                    value: free(
                        'plan_b',
                        34,
                        'AI-PROOF-1 expected right'
                    )
                }
            ],
            34,
            'AI-PROOF-1 expected application'
        );
        assert.equal(kernelExpressionEquals(execution.term, expected), true);
    });

    it('lowers selected constructor syntax exactly to checked apply', () => {
        const callee = free(
            'plan_const',
            35,
            'PLAN-DECOMPOSE-3B selected constructor'
        );
        const premises = [
            coreProofPlanExact(free(
                'plan_z',
                36,
                'PLAN-DECOMPOSE-3B constructor left field'
            )),
            coreProofPlanExact(free(
                'plan_b',
                37,
                'PLAN-DECOMPOSE-3B constructor right field'
            ))
        ];
        const options = {
            id: 'selected_constructor',
            provenance: because(35, 'PLAN-DECOMPOSE-3B constructor macro')
        };
        const macro = coreProofPlanConstructor(
            callee,
            premises,
            options
        );
        const direct = coreProofPlanApply(callee, premises, options);
        assert.deepEqual(macro, direct);
        assert.equal(macro.tag, 'apply');
        assert.equal(
            CORE_PROOF_PLAN_MACRO_PROFILE.addsProofPlanTags,
            false
        );
        assert.equal(
            CORE_PROOF_PLAN_MACRO_PROFILE.constructorLowering,
            'apply'
        );
        assert.equal(
            Object.isFrozen(CORE_PROOF_PLAN_MACRO_PROFILE.basePlanTags),
            true
        );

        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(38), 38);
        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            macro
        );
        assert.equal(execution.state.status, 'complete');
        assert.deepEqual(
            execution.trace.map(step => step.operation),
            ['apply', 'exact', 'exact']
        );
    });

    it('keeps an unused contextual have fact as a named source goal', () => {
        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(39), 39);
        const plan = coreProofPlanHave(
            kernelBinder(
                'fact',
                typeB(40),
                explicitNatural,
                because(40, 'PLAN-DECOMPOSE-3B1B have binder')
            ),
            coreProofPlanHole('fact_proof', {
                provenance: because(
                    41,
                    'PLAN-DECOMPOSE-3B1B retained fact hole'
                ),
                expectation: {
                    contextDepth: 0,
                    target: typeB(41)
                }
            }),
            coreProofPlanExact(free(
                'plan_z',
                42,
                'PLAN-DECOMPOSE-3B1B body ignores fact'
            )),
            { id: 'contextual_have' }
        );

        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );

        assert.equal(CORE_PROOF_PLAN_PROFILE.revision, 'emdash-proof-plan-v2');
        assert.deepEqual(CORE_PROOF_PLAN_PROFILE.tags, [
            'exact',
            'intro',
            'apply',
            'have',
            'hole'
        ]);
        assert.equal(execution.snapshot.status, 'incomplete');
        assert.deepEqual(
            execution.trace.map(step => step.operation),
            ['have', 'hole', 'exact']
        );
        assert.equal(execution.trace[0].introducedGoalCount, 2);
        assert.deepEqual(
            execution.snapshot.goals.map(goal => goal.id),
            ['fact_proof']
        );
        assert.equal(
            execution.snapshot.goals[0].reachability,
            'retained-source-obligation'
        );
        assert.equal(execution.snapshot.goals[0].occurrenceCount, 0);
        assert.equal(execution.snapshot.term, 'plan_z');
    });

    it('substitutes a checked contextual have fact into its body', () => {
        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(43), 43);
        const plan = coreProofPlanHave(
            kernelBinder(
                'fact',
                typeA(44),
                explicitFunctorial,
                because(44, 'PLAN-DECOMPOSE-3B1B used have binder')
            ),
            coreProofPlanExact(free(
                'plan_z',
                45,
                'PLAN-DECOMPOSE-3B1B fact proof'
            )),
            coreProofPlanExact(bound(
                0,
                46,
                'PLAN-DECOMPOSE-3B1B contextual fact use'
            )),
            { id: 'used_contextual_have' }
        );

        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );

        assert.equal(execution.snapshot.status, 'complete');
        assert.deepEqual(execution.snapshot.goals, []);
        assert.deepEqual(
            execution.trace.map(step => step.operation),
            ['have', 'exact', 'exact']
        );
        assert.equal(
            kernelExpressionEquals(
                execution.term,
                free('plan_z', 47, 'PLAN-DECOMPOSE-3B1B expected term')
            ),
            true
        );
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            execution.term,
            typeA(47)
        ));
    });

    it('preserves a contextual have under dependent outer binders', () => {
        const familyAt = (index: number, line: number) => call(
            free('plan_P', line, 'PLAN-DECOMPOSE-3B1B family'),
            [{
                plicity: 'explicit',
                value: bound(
                    index,
                    line,
                    'PLAN-DECOMPOSE-3B1B family index'
                )
            }],
            line,
            'PLAN-DECOMPOSE-3B1B family application'
        );
        const dependentType = pi(
            'index',
            typeA(48),
            explicitFunctorial,
            pi(
                'witness',
                familyAt(0, 48),
                explicitNatural,
                familyAt(1, 48),
                48,
                'PLAN-DECOMPOSE-3B1B dependent witness'
            ),
            48,
            'PLAN-DECOMPOSE-3B1B dependent have target'
        );
        const { session, checker } = proofFixture();
        const root = freshRoot(session, dependentType, 48);
        const plan = coreProofPlanIntro(
            coreProofPlanIntro(
                coreProofPlanHave(
                    kernelBinder(
                        'fact',
                        familyAt(1, 51),
                        explicitNatural,
                        because(
                            51,
                            'PLAN-DECOMPOSE-3B1B dependent fact binder'
                        )
                    ),
                    coreProofPlanExact(bound(
                        0,
                        52,
                        'PLAN-DECOMPOSE-3B1B dependent witness proof'
                    )),
                    coreProofPlanExact(bound(
                        0,
                        53,
                        'PLAN-DECOMPOSE-3B1B dependent fact body'
                    ))
                ),
                {
                    name: 'witness',
                    provenance: because(
                        50,
                        'PLAN-DECOMPOSE-3B1B witness intro'
                    )
                }
            ),
            {
                name: 'index',
                provenance: because(
                    49,
                    'PLAN-DECOMPOSE-3B1B index intro'
                )
            }
        );

        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );
        assert.equal(execution.snapshot.status, 'complete');
        assert.deepEqual(
            execution.trace.map(step => step.operation),
            ['intro', 'intro', 'have', 'exact', 'exact']
        );
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            execution.term,
            dependentType
        ));
    });

    it('serializes dependent open goals with stable source names', () => {
        const makeExecution = () => {
            const { session, checker } = proofFixture();
            const root = freshRoot(session, typeA(40), 40);
            const plan = coreProofPlanConstructor(
                free('plan_k', 41, 'AI-PROOF-1 indexed application'),
                [
                    coreProofPlanHole('index', {
                        provenance: because(42, 'AI-PROOF-1 index hole'),
                        expectation: {
                            contextDepth: 0,
                            target: typeA(42)
                        }
                    }),
                    coreProofPlanHole('witness', {
                        provenance: because(43, 'AI-PROOF-1 witness hole'),
                        expectation: { contextDepth: 0 }
                    })
                ],
                { id: 'indexed_application' }
            );
            return executeCoreProofPlan(
                new CoreProofRefiner(checker, root),
                root.identity,
                plan
            );
        };

        const first = makeExecution();
        const second = makeExecution();
        assert.equal(first.state.status, 'incomplete');
        assert.deepEqual(
            first.snapshot.goals.map(goal => goal.id),
            ['index', 'witness']
        );
        assert.equal(first.snapshot.goals[0].target, 'plan_A');
        assert.equal(
            first.snapshot.goals[1].target,
            'plan_P(explicit:?index[])'
        );
        assert.equal(
            first.snapshot.term,
            'plan_k(explicit:?index[], explicit:?witness[])'
        );

        const firstJson = serializeCoreProofPlanState(first.snapshot);
        const secondJson = serializeCoreProofPlanState(second.snapshot);
        assert.equal(firstJson, secondJson);
        assert.doesNotMatch(firstJson, /\?m\d/);
        assert.doesNotMatch(firstJson, /session|Symbol/);
        assert.match(firstJson, /\?indexed_application/);
        assert.equal(firstJson.endsWith('\n'), true);
    });

    it('records an expected named goal under an introduced context', () => {
        const { session, checker } = proofFixture();
        const identityType = pi(
            'value',
            typeA(50),
            explicitNatural,
            typeA(50),
            50,
            'AI-PROOF-1 open identity type'
        );
        const root = freshRoot(session, identityType, 51);
        const plan = coreProofPlanIntro(
            coreProofPlanHole('body', {
                provenance: because(53, 'AI-PROOF-1 body hole'),
                expectation: {
                    contextDepth: 1,
                    target: typeA(53)
                }
            }),
            {
                name: 'value',
                provenance: because(52, 'AI-PROOF-1 open intro')
            }
        );

        const execution = executeCoreProofPlan(
            new CoreProofRefiner(checker, root),
            root.identity,
            plan
        );
        assert.equal(execution.snapshot.status, 'incomplete');
        assert.equal(execution.snapshot.goals.length, 1);
        assert.deepEqual(execution.snapshot.goals[0].context, [{
            index: 0,
            name: 'value',
            plicity: 'explicit',
            variation: 'natural',
            type: 'plan_A'
        }]);
        assert.equal(execution.snapshot.goals[0].target, 'plan_A');
        assert.match(execution.snapshot.term, /\?body\[#0\]/);
    });

    it('rejects a false expected target without changing the goal', () => {
        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(60), 60);
        const refiner = new CoreProofRefiner(checker, root);
        const plan = coreProofPlanHole('wrong_target', {
            provenance: because(61, 'AI-PROOF-1 false expectation'),
            expectation: {
                contextDepth: 0,
                target: typeB(61)
            }
        });

        assert.throws(
            () => executeCoreProofPlan(refiner, root.identity, plan),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofPlanError);
                assert.equal(error.code, 'GOAL_EXPECTATION_MISMATCH');
                assert.equal(error.nodeId, 'root');
                return true;
            }
        );
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.metavariable(root).solution, undefined);
        assert.deepEqual(
            refiner.inspect().goals.map(goal => goal.identity.index),
            [root.identity.index]
        );
    });

    it('rejects wrong selected constructors and arity atomically', () => {
        const wrongFixture = proofFixture();
        const wrongRoot = freshRoot(
            wrongFixture.session,
            typeB(69),
            69
        );
        const wrongRefiner = new CoreProofRefiner(
            wrongFixture.checker,
            wrongRoot
        );
        const wrongConstructor = coreProofPlanConstructor(
            free('plan_s', 69, 'PLAN-DECOMPOSE-3B wrong constructor'),
            [coreProofPlanExact(free(
                'plan_z',
                69,
                'PLAN-DECOMPOSE-3B wrong constructor premise'
            ))],
            { id: 'wrong_constructor' }
        );
        assert.throws(
            () => executeCoreProofPlan(
                wrongRefiner,
                wrongRoot.identity,
                wrongConstructor
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                return true;
            }
        );
        assert.equal(wrongFixture.session.metavariables.length, 1);
        assert.equal(
            wrongFixture.session.metavariable(wrongRoot).solution,
            undefined
        );

        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(70), 70);
        const refiner = new CoreProofRefiner(checker, root);
        const plan = coreProofPlanConstructor(
            free('plan_s', 71, 'AI-PROOF-1 arity mismatch'),
            [],
            { id: 'missing_premise' }
        );

        assert.throws(
            () => executeCoreProofPlan(refiner, root.identity, plan),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofPlanError);
                assert.equal(error.code, 'GOAL_ARITY_MISMATCH');
                assert.equal(error.nodeId, 'missing_premise');
                return true;
            }
        );
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.metavariable(root).solution, undefined);
        assert.deepEqual(
            refiner.inspect().goals.map(goal => goal.identity.index),
            [root.identity.index]
        );
    });

    it('preflights invalid and duplicate stable IDs before refinement', () => {
        const checkRejectedPlan = (
            plan: CoreProofPlan,
            code: CoreProofPlanError['code']
        ) => {
            const { session, checker } = proofFixture();
            const root = freshRoot(session, typeA(80), 80);
            const refiner = new CoreProofRefiner(checker, root);
            assert.throws(
                () => executeCoreProofPlan(refiner, root.identity, plan),
                (error: unknown) => {
                    assert.ok(error instanceof CoreProofPlanError);
                    assert.equal(error.code, code);
                    return true;
                }
            );
            assert.equal(session.metavariables.length, 1);
            assert.equal(session.metavariable(root).solution, undefined);
        };

        checkRejectedPlan(
            coreProofPlanHole('not portable', {
                provenance: because(81, 'AI-PROOF-1 invalid ID')
            }),
            'INVALID_ID'
        );
        checkRejectedPlan(
            coreProofPlanApply(
                free('plan_k', 82, 'AI-PROOF-1 duplicate holes'),
                [
                    coreProofPlanHole('duplicate', {
                        provenance: because(83, 'AI-PROOF-1 first duplicate')
                    }),
                    coreProofPlanHole('duplicate', {
                        provenance: because(84, 'AI-PROOF-1 second duplicate')
                    })
                ]
            ),
            'DUPLICATE_GOAL_ID'
        );
        checkRejectedPlan(
            coreProofPlanHave(
                kernelBinder(
                    'not portable',
                    typeA(85),
                    explicitFunctorial,
                    because(85, 'PLAN-DECOMPOSE-3B1B invalid have binder')
                ),
                coreProofPlanExact(free(
                    'plan_z',
                    86,
                    'PLAN-DECOMPOSE-3B1B invalid have proof'
                )),
                coreProofPlanExact(free(
                    'plan_z',
                    87,
                    'PLAN-DECOMPOSE-3B1B invalid have body'
                ))
            ),
            'INVALID_BINDER'
        );
    });

    it('rejects process-local metas in otherwise inert source plans', () => {
        const { session, checker } = proofFixture();
        const root = freshRoot(session, typeA(90), 90);
        const hidden = session.freshMeta(
            session.rootContext,
            typeA(91),
            because(91, 'AI-PROOF-1 hidden source meta')
        );
        const refiner = new CoreProofRefiner(checker, root);
        const plan = coreProofPlanExact(hidden);

        assert.throws(
            () => executeCoreProofPlan(refiner, root.identity, plan),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofPlanError);
                assert.equal(error.code, 'NON_SERIALIZABLE_EXPRESSION');
                return true;
            }
        );
        assert.equal(session.metavariables.length, 2);
        assert.equal(session.metavariable(root).solution, undefined);
        assert.equal(session.metavariable(hidden).solution, undefined);

        const hiddenBinderPlan = coreProofPlanHave(
            kernelBinder(
                'fact',
                hidden,
                explicitFunctorial,
                because(92, 'PLAN-DECOMPOSE-3B1B hidden binder type')
            ),
            coreProofPlanExact(free(
                'plan_z',
                93,
                'PLAN-DECOMPOSE-3B1B hidden binder proof'
            )),
            coreProofPlanExact(free(
                'plan_z',
                94,
                'PLAN-DECOMPOSE-3B1B hidden binder body'
            ))
        );
        assert.throws(
            () => executeCoreProofPlan(
                refiner,
                root.identity,
                hiddenBinderPlan
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofPlanError);
                assert.equal(error.code, 'NON_SERIALIZABLE_EXPRESSION');
                return true;
            }
        );
        assert.equal(session.metavariables.length, 2);
        assert.equal(session.metavariable(root).solution, undefined);
    });
});
