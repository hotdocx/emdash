/**
 * Focused ELAB-2A2 tests for session-local metas and constraints.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreBindingInput,
    CoreContextError,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreSessionError,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    UnsolvedKernelMetaError,
    binderMode,
    checkLambdapiProbe,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelShift,
    kernelSubstitute,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_core_session.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const categoryUniverse = (line = 1) => kernelApplication(
    'category-universe',
    [],
    because(line, 'ELAB-2A2 category universe')
);

const categoryOfCategories = (line: number) => kernelApplication(
    'category-of-categories',
    [],
    because(line, 'ELAB-2A2 category of categories')
);

const oppositeCategory = (
    category: KernelExpression,
    line: number
) => kernelApplication('opposite-category', [{
    value: category
}], because(line, 'ELAB-2A2 opposite category'));

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => {
    const nodeProvenance = because(line, 'ELAB-2A2 object type');
    return kernelApplication('decode', [{
        value: kernelApplication('object-classifier', [{
            value: category
        }], nodeProvenance)
    }], nodeProvenance);
};

const free = (name: string, line: number) =>
    kernelFree(name, because(line, `ELAB-2A2 free occurrence ${name}`));

const bound = (index: number, line: number) =>
    kernelBound(index, because(line, `ELAB-2A2 bound occurrence ${index}`));

const binding = (
    name: string,
    type: KernelExpression,
    line: number
): CoreBindingInput => ({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `ELAB-2A2 binding ${name}`)
});

const categoryEnvironment = () =>
    CoreDeclarationEnvironment.empty()
        .extend(binding('session_A', categoryUniverse(1), 1))
        .extend(binding('session_B', categoryUniverse(2), 2));

const expectBoundIndex = (
    expression: KernelExpression,
    expected: number
) => {
    assert.equal(expression.tag, 'bound');
    assert.equal(
        expression.tag === 'bound' ? expression.index : undefined,
        expected
    );
};

describe('TypeScript v3.2 ELAB-2A2 Core sessions', () => {
    it('allocates deterministic local ordinals with isolated session identity', () => {
        const left = new CoreElaborationSession();
        const right = new CoreElaborationSession();
        const left0 = left.freshMeta(
            left.rootContext,
            categoryUniverse(10),
            because(10, 'left meta zero')
        );
        const left1 = left.freshMeta(
            left.rootContext,
            categoryUniverse(11),
            because(11, 'left meta one')
        );
        const right0 = right.freshMeta(
            right.rootContext,
            categoryUniverse(12),
            because(12, 'right meta zero')
        );

        assert.equal(left0.identity.index, 0);
        assert.equal(left1.identity.index, 1);
        assert.equal(right0.identity.index, 0);
        assert.notEqual(
            left0.identity.session,
            right0.identity.session
        );
        assert.equal(kernelExpressionEquals(left0, right0), false);
        assert.deepEqual(
            left.metavariables.map(entry => entry.identity.index),
            [0, 1]
        );
        assert.deepEqual(
            right.metavariables.map(entry => entry.identity.index),
            [0]
        );
    });

    it('rejects invalid meta types before consuming an ordinal', () => {
        const session = new CoreElaborationSession();
        assert.throws(
            () => session.freshMeta(
                session.rootContext,
                bound(0, 20),
                because(21, 'escaping meta declaration')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'INVALID_META_TYPE_SCOPE');
                assert.equal(error.provenance.span?.start.line, 20);
                assert.ok(error.contextError instanceof CoreContextError);
                return true;
            }
        );

        const first = session.freshMeta(
            session.rootContext,
            categoryUniverse(22),
            because(22, 'first valid meta')
        );
        assert.equal(first.identity.index, 0);
    });

    it('reindexes contextual occurrences through shift and substitution', () => {
        const environment = categoryEnvironment();
        const session = new CoreElaborationSession(environment);
        const context = session.rootContext.extend(binding(
            'local_A',
            categoryUniverse(30),
            30
        ));
        const meta = session.freshMeta(
            context,
            categoryUniverse(31),
            because(31, 'contextual meta')
        );

        assert.equal(meta.spine.length, 1);
        expectBoundIndex(meta.spine[0], 0);
        assert.equal(session.solve(meta, bound(0, 32)), 'solved');

        const weakened = kernelShift(meta, 1);
        assert.equal(weakened.tag, 'meta');
        if (weakened.tag !== 'meta') {
            throw new Error('Expected shifted contextual meta');
        }
        expectBoundIndex(weakened.spine[0], 1);
        expectBoundIndex(session.zonk(weakened), 1);
        assert.doesNotThrow(() => kernelAssertScoped(weakened, 2));

        const substituted = kernelSubstitute(
            meta,
            0,
            free('session_A', 33)
        );
        assert.equal(
            kernelExpressionEquals(
                session.zonk(substituted),
                free('session_A', 34)
            ),
            true
        );

        const binderProvenance = because(
            35,
            'nested contextual solution binder'
        );
        const nestedMeta = session.freshMeta(
            context,
            categoryUniverse(35),
            because(35, 'nested contextual meta')
        );
        const nestedSolution = kernelLambda(
            kernelBinder(
                'inner',
                categoryUniverse(36),
                explicitFunctorial,
                binderProvenance
            ),
            bound(1, 36),
            binderProvenance
        );
        assert.equal(
            session.solve(nestedMeta, nestedSolution),
            'solved'
        );
        const nestedZonked = session.zonk(kernelShift(nestedMeta, 1));
        assert.equal(nestedZonked.tag, 'lambda');
        if (nestedZonked.tag !== 'lambda') {
            throw new Error('Expected zonked nested lambda');
        }
        expectBoundIndex(nestedZonked.body, 2);
        assert.doesNotThrow(() => kernelAssertScoped(nestedZonked, 2));
    });

    it('keeps raw metas out of the backend and emits their zonked solution', () => {
        const session = new CoreElaborationSession();
        const meta = session.freshMeta(
            session.rootContext,
            categoryUniverse(40),
            because(40, 'backend meta')
        );

        assert.throws(
            () => serializeKernelExpression(meta),
            (error: unknown) => {
                assert.ok(error instanceof UnsolvedKernelMetaError);
                assert.equal(error.meta.identity.index, 0);
                return true;
            }
        );

        const solution = categoryOfCategories(41);
        assert.equal(session.solve(meta, solution), 'solved');
        assert.equal(
            serializeKernelExpression(session.zonk(meta)),
            'Cat_cat'
        );
        assert.equal(
            kernelExpressionEquals(
                session.metavariable(meta).solution!,
                solution
            ),
            true
        );
    });

    it('enforces idempotent single assignment', () => {
        const session = new CoreElaborationSession();
        const meta = session.freshMeta(
            session.rootContext,
            categoryUniverse(45),
            because(45, 'single-assignment meta')
        );
        const solution = categoryOfCategories(46);

        assert.equal(session.solve(meta, solution), 'solved');
        assert.equal(
            session.solve(meta, categoryOfCategories(47)),
            'already-solved'
        );
        assert.throws(
            () => session.solve(
                meta,
                oppositeCategory(categoryOfCategories(48), 48)
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'METAVARIABLE_ALREADY_SOLVED');
                return true;
            }
        );
    });

    it('rejects direct and transitive occurs cycles', () => {
        const direct = new CoreElaborationSession();
        const directMeta = direct.freshMeta(
            direct.rootContext,
            categoryUniverse(50),
            because(50, 'direct occurs meta')
        );
        assert.throws(
            () => direct.solve(directMeta, objectType(directMeta, 51)),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'META_OCCURS_CHECK');
                assert.equal(error.provenance.span?.start.line, 51);
                return true;
            }
        );
        assert.equal(direct.metavariable(directMeta).solution, undefined);

        const transitive = new CoreElaborationSession();
        const first = transitive.freshMeta(
            transitive.rootContext,
            categoryUniverse(52),
            because(52, 'transitive first meta')
        );
        const second = transitive.freshMeta(
            transitive.rootContext,
            categoryUniverse(53),
            because(53, 'transitive second meta')
        );
        assert.equal(transitive.solve(first, second), 'solved');
        assert.throws(
            () => transitive.solve(second, objectType(first, 54)),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'META_OCCURS_CHECK');
                return true;
            }
        );
        assert.equal(transitive.metavariable(second).solution, undefined);
    });

    it('rejects a solution that escapes the meta creation scope', () => {
        const session = new CoreElaborationSession();
        const meta = session.freshMeta(
            session.rootContext,
            categoryUniverse(60),
            because(60, 'closed-scope meta')
        );

        assert.throws(
            () => session.solve(meta, bound(0, 61)),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'INVALID_META_SOLUTION_SCOPE');
                assert.equal(error.provenance.span?.start.line, 61);
                return true;
            }
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('isolates equal local ordinals across sessions', () => {
        const environment = categoryEnvironment();
        const left = new CoreElaborationSession(environment);
        const right = new CoreElaborationSession(environment);
        const leftMeta = left.freshMeta(
            left.rootContext,
            categoryUniverse(70),
            because(70, 'left isolated meta')
        );
        const rightMeta = right.freshMeta(
            right.rootContext,
            categoryUniverse(71),
            because(71, 'right isolated meta')
        );

        left.solve(leftMeta, free('session_A', 72));
        right.solve(rightMeta, free('session_B', 73));
        assert.equal(
            kernelExpressionEquals(
                left.zonk(leftMeta),
                free('session_A', 74)
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                right.zonk(rightMeta),
                free('session_B', 75)
            ),
            true
        );
        assert.throws(
            () => left.zonk(rightMeta),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'FOREIGN_METAVARIABLE');
                assert.equal(error.provenance.span?.start.line, 71);
                return true;
            }
        );
    });

    it('leaves unconstrained flex-flex equations explicitly stuck', () => {
        const session = new CoreElaborationSession();
        const left = session.freshMeta(
            session.rootContext,
            categoryUniverse(80),
            because(80, 'ambiguous left meta')
        );
        const right = session.freshMeta(
            session.rootContext,
            categoryUniverse(81),
            because(81, 'ambiguous right meta')
        );
        session.addConstraint(
            session.rootContext,
            left,
            right,
            because(82, 'ambiguous constraint')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'stuck');
        assert.deepEqual(report.resolutionOrder, []);
        assert.equal(report.constraints[0].outcome, 'stuck');
        assert.equal(
            report.constraints[0].reason,
            'AMBIGUOUS_FLEX_FLEX'
        );
        assert.equal(session.metavariable(left).solution, undefined);
        assert.equal(session.metavariable(right).solution, undefined);
    });

    it('revisits constraints in deterministic insertion order after progress', () => {
        const run = () => {
            const environment = categoryEnvironment();
            const session = new CoreElaborationSession(environment);
            const first = session.freshMeta(
                session.rootContext,
                categoryUniverse(90),
                because(90, 'ordered first meta')
            );
            const second = session.freshMeta(
                session.rootContext,
                categoryUniverse(91),
                because(91, 'ordered second meta')
            );
            session.addConstraint(
                session.rootContext,
                first,
                second,
                because(92, 'ordered flex-flex')
            );
            session.addConstraint(
                session.rootContext,
                second,
                free('session_A', 93),
                because(93, 'ordered rigid solution')
            );
            const report = session.solveConstraints();
            return {
                outcome: report.outcome,
                resolutionOrder: [...report.resolutionOrder],
                constraintOutcomes: report.constraints.map(
                    constraint => constraint.outcome
                ),
                first: session.zonk(first),
                second: session.zonk(second)
            };
        };

        const firstRun = run();
        const secondRun = run();
        assert.equal(firstRun.outcome, 'solved');
        assert.deepEqual(firstRun.resolutionOrder, [1, 0]);
        assert.deepEqual(firstRun.constraintOutcomes, ['solved', 'solved']);
        assert.deepEqual(
            {
                outcome: secondRun.outcome,
                resolutionOrder: secondRun.resolutionOrder,
                constraintOutcomes: secondRun.constraintOutcomes
            },
            {
                outcome: firstRun.outcome,
                resolutionOrder: firstRun.resolutionOrder,
                constraintOutcomes: firstRun.constraintOutcomes
            }
        );
        assert.equal(
            kernelExpressionEquals(
                firstRun.first,
                free('session_A', 94)
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                firstRun.second,
                free('session_A', 95)
            ),
            true
        );
    });

    it('marks an occurs-check constraint rejected without solving the meta', () => {
        const session = new CoreElaborationSession();
        const meta = session.freshMeta(
            session.rootContext,
            categoryUniverse(100),
            because(100, 'constraint occurs meta')
        );
        session.addConstraint(
            session.rootContext,
            meta,
            objectType(meta, 101),
            because(102, 'occurs constraint')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'rejected');
        assert.equal(report.constraints[0].outcome, 'rejected');
        assert.equal(report.constraints[0].reason, 'META_OCCURS_CHECK');
        assert.equal(
            report.constraints[0].error?.provenance.span?.start.line,
            101
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('reports an unknown constraint through the session diagnostic type', () => {
        const session = new CoreElaborationSession();
        assert.throws(
            () => session.stepConstraint(0),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'UNKNOWN_CONSTRAINT');
                assert.equal(error.provenance.origin, 'derived');
                assert.equal(error.provenance.span, undefined);
                return true;
            }
        );
    });

    it('solves a weakened pattern while leaving rigid conversion stuck', () => {
        const environment = categoryEnvironment();
        const session = new CoreElaborationSession(environment);
        const creationContext = session.rootContext.extend(binding(
            'constraint_A',
            categoryUniverse(110),
            110
        ));
        const meta = session.freshMeta(
            creationContext,
            categoryUniverse(111),
            because(111, 'noncanonical meta')
        );
        const extendedContext = creationContext.extend(binding(
            'constraint_x',
            objectType(bound(0, 112), 112),
            112
        ));
        const weakened = kernelShift(meta, 1);
        session.addConstraint(
            extendedContext,
            weakened,
            bound(1, 113),
            because(113, 'noncanonical constraint')
        );
        session.addConstraint(
            session.rootContext,
            free('session_A', 114),
            free('session_B', 114),
            because(114, 'rigid deferred constraint')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'stuck');
        assert.deepEqual(
            report.constraints.map(constraint => constraint.reason),
            [
                'ASSIGNED_LEFT_PATTERN_META',
                'REQUIRES_DECOMPOSITION_OR_CONVERSION'
            ]
        );
        const solution = session.metavariable(meta).solution;
        assert.ok(solution);
        expectBoundIndex(solution, 0);
        assert.equal(
            kernelExpressionEquals(session.zonk(weakened), bound(1, 115)),
            true
        );
    });

    it(
        'emits a solved session meta accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const session = new CoreElaborationSession();
            const meta = session.freshMeta(
                session.rootContext,
                categoryUniverse(120),
                because(120, 'conformance meta')
            );
            session.solve(meta, categoryOfCategories(121));
            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: [],
                assertions: [{
                    label: 'ELAB-2A2 zonked meta',
                    term: session.zonk(meta),
                    type: categoryUniverse(121),
                    span: at(121, 1, 30)
                }]
            };
            const serialized = serializeKernelProbe(probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected zonked meta probe acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
