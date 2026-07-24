/**
 * Focused MIGRATE-1A generic Core proof-state inspection tests.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreBindingInput,
    CoreElaborationSession,
    CoreSessionError,
    KernelExpression,
    binderMode,
    formatCoreProofExpression,
    formatCoreProofState,
    inspectCoreProofState,
    kernelApplication,
    kernelBinder,
    kernelCall,
    kernelLambda,
    kernelPi,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_proof_state.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const categoryUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'category-universe',
        [],
        because(line, 'MIGRATE-1A category universe')
    );

const categoryOfCategories = (line: number): KernelExpression =>
    kernelApplication(
        'category-of-categories',
        [],
        because(line, 'MIGRATE-1A category of categories')
    );

const binding = (
    name: string,
    type: KernelExpression,
    line: number
): CoreBindingInput => ({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `MIGRATE-1A binding ${name}`)
});

describe('TypeScript v3.2 MIGRATE-1A proof-state traversal', () => {
    it('finds only reachable goals through every generic Core container', () => {
        const session = new CoreElaborationSession();
        const unreachable = session.freshMeta(
            session.rootContext,
            categoryUniverse(10),
            because(10, 'unreachable goal')
        );
        const binderType = session.freshMeta(
            session.rootContext,
            categoryUniverse(11),
            because(11, 'Pi binder-type goal')
        );
        const callee = session.freshMeta(
            session.rootContext,
            categoryUniverse(12),
            because(12, 'generic callee goal')
        );
        const ownerArgument = session.freshMeta(
            session.rootContext,
            categoryUniverse(13),
            because(13, 'owner argument goal')
        );
        const callArgument = session.freshMeta(
            session.rootContext,
            categoryUniverse(14),
            because(14, 'generic call argument goal')
        );

        const owner = kernelApplication('object-classifier', [{
            value: ownerArgument
        }], because(15, 'owner application containing a goal'));
        const call = kernelCall(callee, [
            {
                plicity: 'explicit',
                value: owner
            },
            {
                plicity: 'implicit',
                value: callArgument
            }
        ], because(16, 'generic call containing goals'));
        const dependent = kernelPi(
            kernelBinder(
                'inner',
                binderType,
                explicitFunctorial,
                because(17, 'Pi binder')
            ),
            call,
            because(17, 'Pi containing goals')
        );
        const root = kernelLambda(
            kernelBinder(
                'outer',
                categoryUniverse(18),
                explicitFunctorial,
                because(18, 'lambda binder')
            ),
            dependent,
            because(18, 'lambda containing goals')
        );

        const state = inspectCoreProofState(session, root);
        assert.equal(state.status, 'incomplete');
        assert.deepEqual(
            state.goals.map(goal => goal.identity.index),
            [
                binderType.identity.index,
                callee.identity.index,
                ownerArgument.identity.index,
                callArgument.identity.index
            ]
        );
        assert.equal(
            state.goals.some(
                goal => goal.identity.index === unreachable.identity.index
            ),
            false
        );
        assert.equal(Object.isFrozen(state), true);
        assert.equal(Object.isFrozen(state.goals), true);
        assert.equal(
            state.goals.every(goal => Object.isFrozen(goal)),
            true
        );
    });

    it('follows solved metas and counts repeated reachable occurrences', () => {
        const session = new CoreElaborationSession();
        const solved = session.freshMeta(
            session.rootContext,
            categoryUniverse(20),
            because(20, 'solved wrapper')
        );
        const remaining = session.freshMeta(
            session.rootContext,
            categoryUniverse(21),
            because(21, 'remaining goal')
        );
        session.solve(
            solved,
            kernelApplication('object-classifier', [{
                value: remaining
            }], because(22, 'solution exposing the remaining goal'))
        );

        const root = kernelCall(solved, [
            {
                plicity: 'explicit',
                value: remaining
            },
            {
                plicity: 'explicit',
                value: remaining
            }
        ], because(23, 'repeated goal occurrences'));
        const state = inspectCoreProofState(session, root);

        assert.deepEqual(
            state.goals.map(goal => goal.identity.index),
            [remaining.identity.index]
        );
        assert.equal(state.goals[0].occurrenceCount, 3);
        assert.equal(
            state.goals.some(
                goal => goal.identity.index === solved.identity.index
            ),
            false
        );
    });

    it('records local depth, source, and goal-type dependencies', () => {
        const session = new CoreElaborationSession();
        const typeGoal = session.freshMeta(
            session.rootContext,
            categoryUniverse(30),
            because(30, 'goal type dependency')
        );
        const localContext = session.rootContext.extend(binding(
            'localCategory',
            categoryUniverse(31),
            31
        ));
        const localGoal = session.freshMeta(
            localContext,
            kernelApplication('object-classifier', [{
                value: typeGoal
            }], because(32, 'local goal classifier')),
            because(33, 'local proof goal')
        );
        const root = kernelLambda(
            kernelBinder(
                'localCategory',
                categoryUniverse(34),
                explicitFunctorial,
                because(34, 'local proof binder')
            ),
            localGoal,
            because(34, 'local proof')
        );

        const state = inspectCoreProofState(session, root);
        assert.deepEqual(
            state.goals.map(goal => goal.identity.index),
            [localGoal.identity.index, typeGoal.identity.index]
        );
        assert.equal(state.goals[0].contextDepth, 1);
        assert.equal(
            state.goals[0].firstOccurrenceProvenance.span?.start.line,
            33
        );
        assert.match(
            formatCoreProofExpression(state.goals[0].type),
            new RegExp(`\\?m${typeGoal.identity.index}\\[\\]`)
        );
    });

    it('formats stable incomplete and complete proof reports', () => {
        const session = new CoreElaborationSession();
        const goal = session.freshMeta(
            session.rootContext,
            categoryUniverse(40),
            because(40, 'reported proof goal')
        );

        const incomplete = formatCoreProofState(
            inspectCoreProofState(session, goal)
        );
        assert.match(incomplete, /^Goal \?m0/);
        assert.match(incomplete, /v3_2_proof_state\.surface\.ts:40:1/);
        assert.match(incomplete, /\[depth 0; 1 occurrence\]/);
        assert.match(incomplete, /\|- category-universe\(\)/);

        session.solve(goal, categoryOfCategories(41));
        const complete = inspectCoreProofState(session, goal);
        assert.equal(complete.status, 'complete');
        assert.deepEqual(complete.goals, []);
        assert.equal(formatCoreProofState(complete), 'Proof complete');
    });

    it('rejects a proof term containing a foreign session meta', () => {
        const owner = new CoreElaborationSession();
        const other = new CoreElaborationSession();
        const foreign = owner.freshMeta(
            owner.rootContext,
            categoryUniverse(50),
            because(50, 'foreign proof goal')
        );

        assert.throws(
            () => inspectCoreProofState(other, foreign),
            (error: unknown) => {
                assert.ok(error instanceof CoreSessionError);
                assert.equal(error.code, 'FOREIGN_METAVARIABLE');
                assert.equal(error.provenance.span?.start.line, 50);
                return true;
            }
        );
    });
});
