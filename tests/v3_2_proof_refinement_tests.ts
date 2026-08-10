/**
 * Focused MIGRATE-1C tests for checked Core proof refinement.
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
    CoreProofRefinementError,
    CoreProofRefiner,
    KernelExpression,
    binderMode,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelPi,
    kernelUniverse,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_proof_refinement.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');
const explicitNatural = binderMode('explicit', 'natural');
const explicitObjectOnly = binderMode('explicit', 'object-only');
const implicitNatural = binderMode('implicit', 'natural');

const universe = (line: number, detail = 'MIGRATE-1C universe') =>
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
        plicity: 'explicit' | 'implicit';
        value: KernelExpression;
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
    provenance: because(line, `MIGRATE-1C declaration ${name}`)
});

const proofEnvironment = (): CoreDeclarationEnvironment => {
    let environment = CoreDeclarationEnvironment.empty();
    environment = environment.extend(declaration(
        'proof_A',
        universe(1),
        1
    ));
    environment = environment.extend(declaration(
        'proof_B',
        universe(2),
        2
    ));

    const typeA = free('proof_A', 3, 'MIGRATE-1C type A');
    const typeB = free('proof_B', 4, 'MIGRATE-1C type B');
    environment = environment.extend(declaration('proof_z', typeA, 3));
    environment = environment.extend(declaration('proof_w', typeA, 4));
    environment = environment.extend(declaration('proof_b', typeB, 5));
    environment = environment.extend(declaration(
        'proof_s',
        pi(
            'n',
            typeA,
            explicitFunctorial,
            typeA,
            6,
            'MIGRATE-1C successor type'
        ),
        6
    ));
    environment = environment.extend(declaration(
        'proof_const',
        pi(
            'witness',
            typeA,
            implicitNatural,
            pi(
                'ignored',
                typeB,
                explicitFunctorial,
                typeA,
                7,
                'MIGRATE-1C const explicit binder'
            ),
            7,
            'MIGRATE-1C const implicit binder'
        ),
        7
    ));

    environment = environment.extend(declaration(
        'proof_P',
        pi(
            'x',
            typeA,
            explicitFunctorial,
            universe(8),
            8,
            'MIGRATE-1C unary family type'
        ),
        8
    ));
    environment = environment.extend(declaration(
        'proof_d',
        pi(
            'x',
            typeA,
            explicitFunctorial,
            call(
                free('proof_P', 9, 'MIGRATE-1C unary family'),
                [{
                    plicity: 'explicit',
                    value: bound(
                        0,
                        9,
                        'MIGRATE-1C dependent function argument'
                    )
                }],
                9,
                'MIGRATE-1C dependent function result'
            ),
            9,
            'MIGRATE-1C dependent function type'
        ),
        9
    ));

    environment = environment.extend(declaration(
        'proof_Q',
        pi(
            'left',
            typeA,
            explicitFunctorial,
            pi(
                'right',
                typeA,
                explicitFunctorial,
                universe(10),
                10,
                'MIGRATE-1C binary family right binder'
            ),
            10,
            'MIGRATE-1C binary family left binder'
        ),
        10
    ));
    environment = environment.extend(declaration(
        'proof_partial_bad',
        pi(
            'x',
            typeA,
            explicitFunctorial,
            call(
                free('proof_Q', 11, 'MIGRATE-1C binary family'),
                [
                    {
                        plicity: 'explicit',
                        value: bound(
                            0,
                            11,
                            'MIGRATE-1C partially solved argument'
                        )
                    },
                    {
                        plicity: 'explicit',
                        value: free(
                            'proof_z',
                            11,
                            'MIGRATE-1C rigid bad result argument'
                        )
                    }
                ],
                11,
                'MIGRATE-1C partially mismatching result'
            ),
            11,
            'MIGRATE-1C partially mismatching function'
        ),
        11
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
    free('proof_A', line, 'MIGRATE-1C use of type A');

const typeB = (line: number) =>
    free('proof_B', line, 'MIGRATE-1C use of type B');

describe('TypeScript v3.2 MIGRATE-1C proof refinement', () => {
    it('solves a reachable goal with a checker-validated exact term', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(20),
            because(20, 'MIGRATE-1C exact goal')
        );
        const proof = new CoreProofRefiner(checker, goal);
        const solution = free('proof_z', 21, 'MIGRATE-1C exact solution');

        const result = proof.exact(goal.identity, solution);
        assert.equal(result.tactic, 'exact');
        assert.equal(result.refinedGoal.identity, goal.identity);
        assert.deepEqual(result.introducedGoals, []);
        assert.equal(result.state.status, 'complete');
        assert.equal(
            kernelExpressionEquals(result.state.term, solution),
            true
        );
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            result.state.term,
            typeA(22)
        ));
    });

    it('proves an identity by intro followed by exact', () => {
        const { session, checker } = proofFixture();
        const identityType = pi(
            'original_name',
            typeA(30),
            explicitNatural,
            typeA(30),
            30,
            'MIGRATE-1C identity goal type'
        );
        const goal = session.freshMeta(
            session.rootContext,
            identityType,
            because(31, 'MIGRATE-1C identity goal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        const introduced = proof.intro(
            goal.identity,
            because(32, 'MIGRATE-1C intro invocation'),
            'renamed'
        );
        assert.equal(introduced.state.status, 'incomplete');
        assert.equal(introduced.introducedGoals.length, 1);
        const bodyGoal = introduced.introducedGoals[0];
        assert.equal(bodyGoal.contextDepth, 1);
        assert.equal(bodyGoal.context.depth, 1);
        assert.equal(bodyGoal.context.telescope[0].name, 'renamed');
        assert.deepEqual(
            bodyGoal.context.telescope[0].mode,
            explicitNatural
        );
        assert.equal(
            kernelExpressionEquals(bodyGoal.type, typeA(33)),
            true
        );
        assert.equal(introduced.state.term.tag, 'lambda');
        if (introduced.state.term.tag !== 'lambda') {
            throw new Error('Expected intro to construct a lambda');
        }
        assert.equal(introduced.state.term.binder.name, 'renamed');
        assert.deepEqual(
            introduced.state.term.binder.mode,
            explicitNatural
        );

        const complete = proof.exact(
            bodyGoal.identity,
            bound(0, 34, 'MIGRATE-1C introduced variable')
        );
        assert.equal(complete.state.status, 'complete');
        assert.deepEqual(complete.introducedGoals, []);
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            complete.state.term,
            identityType
        ));
    });

    it('retains an unused have fact until its source obligation is solved', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(35),
            because(35, 'PLAN-DECOMPOSE-3B1B have goal')
        );
        const proof = new CoreProofRefiner(checker, goal);
        const introduced = proof.have(
            goal.identity,
            kernelBinder(
                'fact',
                typeB(36),
                explicitNatural,
                because(36, 'PLAN-DECOMPOSE-3B1B have binder')
            )
        );

        assert.equal(introduced.tactic, 'have');
        assert.deepEqual(
            introduced.introducedGoals.map(item => item.contextDepth),
            [0, 1]
        );
        assert.equal(
            kernelExpressionEquals(
                introduced.introducedGoals[0].type,
                typeB(37)
            ),
            true
        );
        assert.deepEqual(
            introduced.introducedGoals[1].context.telescope[0].mode,
            explicitNatural
        );

        const ignored = proof.exact(
            introduced.introducedGoals[1].identity,
            free('proof_z', 38, 'PLAN-DECOMPOSE-3B1B ignored fact body')
        );
        assert.equal(ignored.state.status, 'incomplete');
        assert.equal(ignored.state.goals.length, 1);
        assert.equal(
            ignored.state.goals[0].identity.index,
            introduced.introducedGoals[0].identity.index
        );
        assert.equal(
            ignored.state.goals[0].reachability,
            'retained-source-obligation'
        );
        assert.equal(ignored.state.goals[0].occurrenceCount, 0);
        assert.equal(
            kernelExpressionEquals(
                ignored.state.term,
                free('proof_z', 39, 'PLAN-DECOMPOSE-3B1B ignored result')
            ),
            true
        );

        const complete = proof.exact(
            introduced.introducedGoals[0].identity,
            free('proof_b', 40, 'PLAN-DECOMPOSE-3B1B fact solution')
        );
        assert.equal(complete.state.status, 'complete');
        assert.doesNotThrow(() => checker.check(
            session.rootContext,
            complete.state.term,
            typeA(40)
        ));
    });

    it('substitutes a used have fact for every binder variation', () => {
        for (const mode of [
            explicitFunctorial,
            explicitNatural,
            explicitObjectOnly,
            implicitNatural
        ]) {
            const { session, checker } = proofFixture();
            const goal = session.freshMeta(
                session.rootContext,
                typeA(41),
                because(41, 'PLAN-DECOMPOSE-3B1B varied have goal')
            );
            const proof = new CoreProofRefiner(checker, goal);
            const introduced = proof.have(
                goal.identity,
                kernelBinder(
                    'fact',
                    typeA(42),
                    mode,
                    because(42, 'PLAN-DECOMPOSE-3B1B varied binder')
                )
            );
            assert.deepEqual(
                introduced.introducedGoals[1].context.telescope[0].mode,
                mode
            );
            proof.exact(
                introduced.introducedGoals[1].identity,
                bound(0, 43, 'PLAN-DECOMPOSE-3B1B used local fact')
            );
            const complete = proof.exact(
                introduced.introducedGoals[0].identity,
                free('proof_z', 44, 'PLAN-DECOMPOSE-3B1B varied fact')
            );
            assert.equal(complete.state.status, 'complete');
            assert.equal(
                kernelExpressionEquals(
                    complete.state.term,
                    free('proof_z', 44, 'PLAN-DECOMPOSE-3B1B expected fact')
                ),
                true
            );
        }
    });

    it('rolls back an ill-typed have binder and its retained metadata', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(45),
            because(45, 'PLAN-DECOMPOSE-3B1B rejected have goal')
        );
        const proof = new CoreProofRefiner(checker, goal);
        assert.throws(
            () => proof.have(
                goal.identity,
                kernelBinder(
                    'bad',
                    free('proof_z', 46, 'PLAN-DECOMPOSE-3B1B non-type'),
                    explicitFunctorial,
                    because(46, 'PLAN-DECOMPOSE-3B1B rejected binder')
                )
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                return true;
            }
        );
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.metavariable(goal).solution, undefined);
        assert.deepEqual(
            proof.inspect().goals.map(item => item.identity.index),
            [goal.identity.index]
        );
    });

    it('applies a unary function and exposes its explicit premise', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(40),
            because(40, 'MIGRATE-1C apply goal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        const applied = proof.apply(
            goal.identity,
            free('proof_s', 41, 'MIGRATE-1C applied function')
        );
        assert.equal(applied.state.status, 'incomplete');
        assert.equal(applied.introducedGoals.length, 1);
        assert.equal(
            kernelExpressionEquals(
                applied.introducedGoals[0].type,
                typeA(42)
            ),
            true
        );
        assert.equal(applied.state.term.tag, 'call');
        if (applied.state.term.tag !== 'call') {
            throw new Error('Expected apply to construct a generic call');
        }
        assert.deepEqual(
            applied.state.term.arguments.map(argument => argument.plicity),
            ['explicit']
        );

        const complete = proof.exact(
            applied.introducedGoals[0].identity,
            free('proof_z', 43, 'MIGRATE-1C premise solution')
        );
        assert.equal(complete.state.status, 'complete');
        const expected = call(
            free('proof_s', 44, 'MIGRATE-1C expected function'),
            [{
                plicity: 'explicit',
                value: free(
                    'proof_z',
                    44,
                    'MIGRATE-1C expected argument'
                )
            }],
            44,
            'MIGRATE-1C expected application'
        );
        assert.equal(
            kernelExpressionEquals(complete.state.term, expected),
            true
        );
    });

    it('preserves implicit and explicit plicity as ordered goals', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(50),
            because(50, 'MIGRATE-1C mixed apply goal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        const applied = proof.apply(
            goal.identity,
            free('proof_const', 51, 'MIGRATE-1C mixed function')
        );
        assert.equal(applied.introducedGoals.length, 2);
        assert.equal(
            kernelExpressionEquals(
                applied.introducedGoals[0].type,
                typeA(52)
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                applied.introducedGoals[1].type,
                typeB(53)
            ),
            true
        );
        assert.equal(applied.state.term.tag, 'call');
        if (applied.state.term.tag !== 'call') {
            throw new Error('Expected mixed apply to construct a call');
        }
        assert.deepEqual(
            applied.state.term.arguments.map(argument => argument.plicity),
            ['implicit', 'explicit']
        );

        proof.exact(
            applied.introducedGoals[0].identity,
            free('proof_z', 54, 'MIGRATE-1C implicit premise')
        );
        const complete = proof.exact(
            applied.introducedGoals[1].identity,
            free('proof_b', 55, 'MIGRATE-1C explicit premise')
        );
        assert.equal(complete.state.status, 'complete');
    });

    it('lets dependent result checking solve an apply argument', () => {
        const { session, checker } = proofFixture();
        const goalType = call(
            free('proof_P', 60, 'MIGRATE-1C dependent family'),
            [{
                plicity: 'explicit',
                value: free(
                    'proof_z',
                    60,
                    'MIGRATE-1C dependent target index'
                )
            }],
            60,
            'MIGRATE-1C dependent target'
        );
        const goal = session.freshMeta(
            session.rootContext,
            goalType,
            because(61, 'MIGRATE-1C dependent apply goal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        const applied = proof.apply(
            goal.identity,
            free('proof_d', 62, 'MIGRATE-1C dependent function')
        );
        assert.equal(applied.state.status, 'complete');
        assert.deepEqual(applied.introducedGoals, []);
        const expected = call(
            free('proof_d', 63, 'MIGRATE-1C expected dependent function'),
            [{
                plicity: 'explicit',
                value: free(
                    'proof_z',
                    63,
                    'MIGRATE-1C inferred dependent argument'
                )
            }],
            63,
            'MIGRATE-1C inferred dependent application'
        );
        assert.equal(
            kernelExpressionEquals(applied.state.term, expected),
            true
        );
    });

    it('rejects an ill-typed exact term without changing the proof', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(70),
            because(70, 'MIGRATE-1C rejected exact goal')
        );
        const proof = new CoreProofRefiner(checker, goal);
        const metaCount = session.metavariables.length;
        const constraintCount = session.constraints.length;

        assert.throws(
            () => proof.exact(
                goal.identity,
                free('proof_b', 71, 'MIGRATE-1C wrong exact term')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                assert.equal(error.provenance.span?.start.line, 71);
                return true;
            }
        );
        assert.equal(session.metavariables.length, metaCount);
        assert.equal(session.constraints.length, constraintCount);
        assert.equal(session.metavariable(goal).solution, undefined);
        assert.equal(proof.inspect().goals.length, 1);
    });

    it('does not let exact introduce an unresolved subgoal', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(80),
            because(80, 'MIGRATE-1C complete exact goal')
        );
        const unresolved = session.freshMeta(
            session.rootContext,
            typeA(81),
            because(81, 'MIGRATE-1C forbidden exact subgoal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        assert.throws(
            () => proof.exact(goal.identity, unresolved),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'UNRESOLVED_METAVARIABLE');
                assert.equal(error.provenance.span?.start.line, 81);
                return true;
            }
        );
        assert.equal(session.metavariable(goal).solution, undefined);
        assert.deepEqual(
            proof.inspect().goals.map(item => item.identity.index),
            [goal.identity.index]
        );
    });

    it('rejects intro on a non-Pi goal atomically', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(90),
            because(90, 'MIGRATE-1C non-Pi intro goal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        assert.throws(
            () => proof.intro(
                goal.identity,
                because(91, 'MIGRATE-1C invalid intro')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofRefinementError);
                assert.equal(error.code, 'INTRO_EXPECTED_PI');
                assert.equal(error.provenance.span?.start.line, 91);
                return true;
            }
        );
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.metavariable(goal).solution, undefined);
    });

    it('rejects apply on a non-function atomically', () => {
        const { session, checker } = proofFixture();
        const goal = session.freshMeta(
            session.rootContext,
            typeA(100),
            because(100, 'MIGRATE-1C non-function apply goal')
        );
        const proof = new CoreProofRefiner(checker, goal);

        assert.throws(
            () => proof.apply(
                goal.identity,
                free('proof_z', 101, 'MIGRATE-1C non-function')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofRefinementError);
                assert.equal(error.code, 'APPLY_EXPECTED_FUNCTION');
                assert.equal(error.provenance.span?.start.line, 101);
                return true;
            }
        );
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.metavariable(goal).solution, undefined);
    });

    it('rolls back a partially solved argument after apply mismatch', () => {
        const { session, checker } = proofFixture();
        const goalType = call(
            free('proof_Q', 110, 'MIGRATE-1C binary target family'),
            [
                {
                    plicity: 'explicit',
                    value: free(
                        'proof_z',
                        110,
                        'MIGRATE-1C binary target left'
                    )
                },
                {
                    plicity: 'explicit',
                    value: free(
                        'proof_w',
                        110,
                        'MIGRATE-1C binary target right'
                    )
                }
            ],
            110,
            'MIGRATE-1C binary target'
        );
        const goal = session.freshMeta(
            session.rootContext,
            goalType,
            because(111, 'MIGRATE-1C rollback goal')
        );
        const proof = new CoreProofRefiner(checker, goal);
        const constraintCount = session.constraints.length;

        assert.throws(
            () => proof.apply(
                goal.identity,
                free(
                    'proof_partial_bad',
                    112,
                    'MIGRATE-1C partially mismatching function'
                )
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                assert.equal(error.provenance.span?.start.line, 112);
                return true;
            }
        );
        assert.equal(session.metavariables.length, 1);
        assert.equal(session.constraints.length, constraintCount);
        assert.equal(session.metavariable(goal).solution, undefined);

        const next = session.freshMeta(
            session.rootContext,
            typeA(113),
            because(113, 'MIGRATE-1C ordinal after rollback')
        );
        assert.equal(next.identity.index, 1);
    });

    it('refuses to refine a session meta unreachable from the root', () => {
        const { session, checker } = proofFixture();
        const rootGoal = session.freshMeta(
            session.rootContext,
            typeA(120),
            because(120, 'MIGRATE-1C reachable goal')
        );
        const unrelated = session.freshMeta(
            session.rootContext,
            typeA(121),
            because(121, 'MIGRATE-1C unrelated goal')
        );
        const proof = new CoreProofRefiner(checker, rootGoal);

        assert.throws(
            () => proof.exact(
                unrelated.identity,
                free('proof_z', 122, 'MIGRATE-1C unreachable solution')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreProofRefinementError);
                assert.equal(error.code, 'GOAL_NOT_REACHABLE');
                assert.equal(error.provenance.span?.start.line, 122);
                return true;
            }
        );
        assert.equal(session.metavariable(rootGoal).solution, undefined);
        assert.equal(session.metavariable(unrelated).solution, undefined);
        assert.deepEqual(
            proof.inspect().goals.map(item => item.identity.index),
            [rootGoal.identity.index]
        );
    });
});
