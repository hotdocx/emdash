/**
 * Focused MIGRATE-1B tests for contextual higher-order pattern solving.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreBindingInput,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreSessionError,
    KernelExpression,
    KernelMetaVariable,
    binderMode,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelMeta,
    kernelShift,
    kernelUniverse,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_pattern_unification.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const universe = (line: number, detail = 'MIGRATE-1B universe') =>
    kernelUniverse(because(line, detail));

const binding = (
    name: string,
    line: number
): CoreBindingInput => ({
    name,
    type: universe(line, `MIGRATE-1B type of ${name}`),
    mode: explicitFunctorial,
    provenance: because(line, `MIGRATE-1B binding ${name}`)
});

const bound = (index: number, line: number, detail: string) =>
    kernelBound(index, because(line, detail));

const free = (name: string, line: number, detail: string) =>
    kernelFree(name, because(line, detail));

const call = (
    callee: KernelExpression,
    arguments_: readonly KernelExpression[],
    line: number,
    detail: string
) => kernelCall(
    callee,
    arguments_.map(value => ({
        plicity: 'explicit',
        value
    })),
    because(line, detail)
);

const patternEnvironment = () => {
    let environment = CoreDeclarationEnvironment.empty();
    for (const [name, line] of [
        ['pattern_f', 1],
        ['pattern_pair', 2],
        ['pattern_c', 3]
    ] as const) {
        environment = environment.extend(binding(name, line));
    }
    return environment;
};

const occurrence = (
    meta: KernelMetaVariable,
    spine: readonly KernelExpression[],
    line: number,
    detail: string
) => kernelMeta(meta.identity, spine, because(line, detail));

const expectSolution = (
    session: CoreElaborationSession,
    meta: KernelMetaVariable,
    expected: KernelExpression
) => {
    const solution = session.metavariable(meta).solution;
    assert.ok(solution, `Expected ?m${meta.identity.index} to be solved`);
    assert.equal(kernelExpressionEquals(solution, expected), true);
};

describe('TypeScript v3.2 MIGRATE-1B pattern unification', () => {
    it('inverts a weakened distinct-variable occurrence', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_x',
            10
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(11),
            because(11, 'MIGRATE-1B weakened meta')
        );
        const occurrenceContext = creationContext.extend(binding(
            'pattern_unused',
            12
        ));
        const weakened = kernelShift(meta, 1);
        const rigid = call(
            free('pattern_f', 13, 'MIGRATE-1B weakened rigid head'),
            [bound(1, 13, 'MIGRATE-1B weakened selected local')],
            13,
            'MIGRATE-1B weakened rigid application'
        );
        const constraint = session.addConstraint(
            occurrenceContext,
            weakened,
            rigid,
            because(13, 'MIGRATE-1B weakened equation')
        );

        const step = session.stepConstraint(constraint.id);
        assert.equal(step.outcome, 'solved');
        assert.equal(step.reason, 'ASSIGNED_LEFT_PATTERN_META');
        expectSolution(
            session,
            meta,
            call(
                free('pattern_f', 14, 'MIGRATE-1B solution head'),
                [bound(0, 14, 'MIGRATE-1B creation local')],
                14,
                'MIGRATE-1B weakened solution'
            )
        );
        assert.equal(
            kernelExpressionEquals(session.zonk(weakened), rigid),
            true
        );
    });

    it('permits a rigid solution independent of its selected variable', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_constant_x',
            20
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(21),
            because(21, 'MIGRATE-1B constant meta')
        );
        const occurrenceContext = creationContext.extend(binding(
            'pattern_constant_unused',
            22
        ));
        const weakened = kernelShift(meta, 1);
        const rigid = free(
            'pattern_c',
            23,
            'MIGRATE-1B constant rigid term'
        );
        session.addConstraint(
            occurrenceContext,
            weakened,
            rigid,
            because(23, 'MIGRATE-1B constant equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'solved');
        assert.equal(
            report.constraints[0].reason,
            'ASSIGNED_LEFT_PATTERN_META'
        );
        expectSolution(session, meta, rigid);
    });

    it('inverts an exchanged two-variable spine deterministically', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const context = session.rootContext
            .extend(binding('pattern_exchange_x', 30))
            .extend(binding('pattern_exchange_y', 31));
        const meta = session.freshMeta(
            context,
            universe(32),
            because(32, 'MIGRATE-1B exchange meta')
        );
        const exchanged = occurrence(
            meta,
            [
                bound(1, 33, 'MIGRATE-1B exchange first image'),
                bound(0, 33, 'MIGRATE-1B exchange second image')
            ],
            33,
            'MIGRATE-1B exchanged occurrence'
        );
        const rigid = call(
            free('pattern_pair', 34, 'MIGRATE-1B pair head'),
            [
                bound(1, 34, 'MIGRATE-1B rigid outer local'),
                bound(0, 34, 'MIGRATE-1B rigid inner local')
            ],
            34,
            'MIGRATE-1B exchanged rigid application'
        );
        session.addConstraint(
            context,
            exchanged,
            rigid,
            because(34, 'MIGRATE-1B exchange equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'solved');
        expectSolution(
            session,
            meta,
            call(
                free('pattern_pair', 35, 'MIGRATE-1B solution pair head'),
                [
                    bound(0, 35, 'MIGRATE-1B inverse first local'),
                    bound(1, 35, 'MIGRATE-1B inverse second local')
                ],
                35,
                'MIGRATE-1B exchanged solution'
            )
        );
        assert.equal(
            kernelExpressionEquals(session.zonk(exchanged), rigid),
            true
        );
    });

    it('allows the rigid side to use only part of a distinct spine', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const context = session.rootContext
            .extend(binding('pattern_subset_x', 40))
            .extend(binding('pattern_subset_y', 41));
        const meta = session.freshMeta(
            context,
            universe(42),
            because(42, 'MIGRATE-1B subset meta')
        );
        const exchanged = occurrence(
            meta,
            [
                bound(1, 43, 'MIGRATE-1B subset first image'),
                bound(0, 43, 'MIGRATE-1B subset second image')
            ],
            43,
            'MIGRATE-1B subset occurrence'
        );
        const rigid = call(
            free('pattern_f', 44, 'MIGRATE-1B subset rigid head'),
            [bound(1, 44, 'MIGRATE-1B used outer local')],
            44,
            'MIGRATE-1B subset rigid application'
        );
        session.addConstraint(
            context,
            exchanged,
            rigid,
            because(44, 'MIGRATE-1B subset equation')
        );

        assert.equal(session.solveConstraints().outcome, 'solved');
        expectSolution(
            session,
            meta,
            call(
                free('pattern_f', 45, 'MIGRATE-1B subset solution head'),
                [bound(0, 45, 'MIGRATE-1B retained creation local')],
                45,
                'MIGRATE-1B subset solution'
            )
        );
    });

    it('remaps selected locals beneath an inner lambda without capture', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_lambda_x',
            50
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(51),
            because(51, 'MIGRATE-1B lambda meta')
        );
        const occurrenceContext = creationContext.extend(binding(
            'pattern_lambda_unused',
            52
        ));
        const weakened = kernelShift(meta, 1);
        const rigid = kernelLambda(
            kernelBinder(
                'pattern_inner',
                universe(53),
                explicitFunctorial,
                because(53, 'MIGRATE-1B inner lambda binder')
            ),
            call(
                free('pattern_pair', 54, 'MIGRATE-1B lambda rigid head'),
                [
                    bound(2, 54, 'MIGRATE-1B selected local under binder'),
                    bound(0, 54, 'MIGRATE-1B inner bound local')
                ],
                54,
                'MIGRATE-1B lambda rigid body'
            ),
            because(53, 'MIGRATE-1B rigid lambda')
        );
        session.addConstraint(
            occurrenceContext,
            weakened,
            rigid,
            because(55, 'MIGRATE-1B lambda equation')
        );

        assert.equal(session.solveConstraints().outcome, 'solved');
        expectSolution(
            session,
            meta,
            kernelLambda(
                kernelBinder(
                    'pattern_inner',
                    universe(56),
                    explicitFunctorial,
                    because(56, 'MIGRATE-1B solution lambda binder')
                ),
                call(
                    free(
                        'pattern_pair',
                        57,
                        'MIGRATE-1B lambda solution head'
                    ),
                    [
                        bound(
                            1,
                            57,
                            'MIGRATE-1B creation local under binder'
                        ),
                        bound(0, 57, 'MIGRATE-1B preserved inner local')
                    ],
                    57,
                    'MIGRATE-1B lambda solution body'
                ),
                because(56, 'MIGRATE-1B solution lambda')
            )
        );
    });

    it('solves a pattern occurrence on the right symmetrically', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_right_x',
            60
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(61),
            because(61, 'MIGRATE-1B right meta')
        );
        const occurrenceContext = creationContext.extend(binding(
            'pattern_right_unused',
            62
        ));
        const weakened = kernelShift(meta, 1);
        const rigid = call(
            free('pattern_f', 63, 'MIGRATE-1B right rigid head'),
            [bound(1, 63, 'MIGRATE-1B right selected local')],
            63,
            'MIGRATE-1B right rigid application'
        );
        session.addConstraint(
            occurrenceContext,
            rigid,
            weakened,
            because(63, 'MIGRATE-1B right equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'solved');
        assert.equal(
            report.constraints[0].reason,
            'ASSIGNED_RIGHT_PATTERN_META'
        );
        expectSolution(
            session,
            meta,
            call(
                free('pattern_f', 64, 'MIGRATE-1B right solution head'),
                [bound(0, 64, 'MIGRATE-1B right creation local')],
                64,
                'MIGRATE-1B right solution'
            )
        );
    });

    it('leaves a non-variable spine stuck without assigning the meta', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const context = session.rootContext.extend(binding(
            'pattern_nonvariable_x',
            70
        ));
        const meta = session.freshMeta(
            context,
            universe(71),
            because(71, 'MIGRATE-1B non-variable meta')
        );
        const nonVariable = occurrence(
            meta,
            [free('pattern_c', 72, 'MIGRATE-1B non-variable spine item')],
            72,
            'MIGRATE-1B non-variable occurrence'
        );
        session.addConstraint(
            context,
            nonVariable,
            free('pattern_c', 73, 'MIGRATE-1B non-variable rigid side'),
            because(73, 'MIGRATE-1B non-variable equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'stuck');
        assert.equal(
            report.constraints[0].reason,
            'NON_VARIABLE_PATTERN_SPINE'
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('leaves a repeated-variable spine stuck', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const context = session.rootContext
            .extend(binding('pattern_repeat_x', 80))
            .extend(binding('pattern_repeat_y', 81));
        const meta = session.freshMeta(
            context,
            universe(82),
            because(82, 'MIGRATE-1B repeated meta')
        );
        const repeated = occurrence(
            meta,
            [
                bound(0, 83, 'MIGRATE-1B repeated first item'),
                bound(0, 83, 'MIGRATE-1B repeated second item')
            ],
            83,
            'MIGRATE-1B repeated occurrence'
        );
        session.addConstraint(
            context,
            repeated,
            free('pattern_c', 84, 'MIGRATE-1B repeated rigid side'),
            because(84, 'MIGRATE-1B repeated equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'stuck');
        assert.equal(
            report.constraints[0].reason,
            'REPEATED_PATTERN_VARIABLE'
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('rejects a rigid dependency omitted from the pattern spine', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_escape_x',
            90
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(91),
            because(91, 'MIGRATE-1B escaping meta')
        );
        const occurrenceContext = creationContext.extend(binding(
            'pattern_escape_y',
            92
        ));
        const weakened = kernelShift(meta, 1);
        session.addConstraint(
            occurrenceContext,
            weakened,
            bound(0, 93, 'MIGRATE-1B omitted rigid dependency'),
            because(94, 'MIGRATE-1B escaping equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'rejected');
        assert.equal(report.constraints[0].reason, 'PATTERN_SCOPE_ESCAPE');
        assert.equal(
            report.constraints[0].error?.provenance.span?.start.line,
            93
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('applies the occurs check after capture-safe inversion', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_occurs_x',
            100
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(101),
            because(101, 'MIGRATE-1B occurs meta')
        );
        const occurrenceContext = creationContext.extend(binding(
            'pattern_occurs_unused',
            102
        ));
        const weakened = kernelShift(meta, 1);
        const rigid = call(
            free('pattern_f', 103, 'MIGRATE-1B occurs rigid head'),
            [weakened],
            103,
            'MIGRATE-1B recursive rigid side'
        );
        session.addConstraint(
            occurrenceContext,
            weakened,
            rigid,
            because(103, 'MIGRATE-1B occurs equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'rejected');
        assert.equal(report.constraints[0].reason, 'META_OCCURS_CHECK');
        assert.equal(
            report.constraints[0].error?.provenance.span?.start.line,
            103
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('keeps flex-flex constraints ambiguous', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const context = session.rootContext.extend(binding(
            'pattern_flex_x',
            110
        ));
        const left = session.freshMeta(
            context,
            universe(111),
            because(111, 'MIGRATE-1B left flex')
        );
        const right = session.freshMeta(
            context,
            universe(112),
            because(112, 'MIGRATE-1B right flex')
        );
        session.addConstraint(
            context,
            left,
            right,
            because(113, 'MIGRATE-1B flex-flex equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'stuck');
        assert.equal(
            report.constraints[0].reason,
            'AMBIGUOUS_FLEX_FLEX'
        );
        assert.equal(session.metavariable(left).solution, undefined);
        assert.equal(session.metavariable(right).solution, undefined);
    });

    it('rejects pattern solving across unrelated context lineages', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const creationContext = session.rootContext.extend(binding(
            'pattern_lineage_origin',
            120
        ));
        const unrelatedContext = session.rootContext.extend(binding(
            'pattern_lineage_other',
            121
        ));
        const meta = session.freshMeta(
            creationContext,
            universe(122),
            because(122, 'MIGRATE-1B lineage meta')
        );
        session.addConstraint(
            unrelatedContext,
            meta,
            free('pattern_c', 123, 'MIGRATE-1B lineage rigid side'),
            because(123, 'MIGRATE-1B unrelated-context equation')
        );

        const report = session.solveConstraints();
        assert.equal(report.outcome, 'stuck');
        assert.equal(
            report.constraints[0].reason,
            'NONCANONICAL_META_OCCURRENCE'
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });

    it('retains the canonical-only direct solve API boundary', () => {
        const session = new CoreElaborationSession(patternEnvironment());
        const context = session.rootContext
            .extend(binding('pattern_direct_x', 130))
            .extend(binding('pattern_direct_y', 131));
        const meta = session.freshMeta(
            context,
            universe(132),
            because(132, 'MIGRATE-1B direct meta')
        );
        const exchanged = occurrence(
            meta,
            [
                bound(1, 133, 'MIGRATE-1B direct first image'),
                bound(0, 133, 'MIGRATE-1B direct second image')
            ],
            133,
            'MIGRATE-1B direct exchanged occurrence'
        );

        assert.throws(
            () => session.solve(
                exchanged,
                free('pattern_c', 134, 'MIGRATE-1B direct solution')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(
                    error.code,
                    'NONCANONICAL_META_OCCURRENCE'
                );
                assert.equal(error.provenance.span?.start.line, 133);
                return true;
            }
        );
        assert.equal(session.metavariable(meta).solution, undefined);
    });
});
