/**
 * Candidate definitional comparison for the reviewed runtime fragment.
 *
 * Comparison combines alpha-invariant structural Core equality with the exact
 * H-03 runtime program. It does not execute proof-time comparisons, excluded
 * owners, declaration unfolding, generic-call beta, or backend evidence.
 */

import {
    KernelExpression,
    kernelExpressionEquals
} from './kernel';
import {
    PROJECTION_PAIR_SCHEMAS,
    CoreOwnerId
} from './schema';
import {
    CoreRuntimeEvaluationError,
    CoreRuntimeWeakHeadTraceEntry,
    coreRuntimeWeakHead
} from './evaluator';

export type CoreRuntimeComparisonSide = 'left' | 'right';

export interface CoreRuntimeComparisonTraceEntry {
    readonly step: number;
    readonly side: CoreRuntimeComparisonSide;
    readonly path: readonly string[];
    readonly ruleId: string;
    readonly before: KernelExpression;
    readonly after: KernelExpression;
}

export type CoreRuntimeComparisonMismatchCode =
    | 'TAG_MISMATCH'
    | 'REFERENCE_MISMATCH'
    | 'BOUND_VARIABLE_MISMATCH'
    | 'METAVARIABLE_MISMATCH'
    | 'OWNER_MISMATCH'
    | 'ARITY_MISMATCH'
    | 'PLICITY_MISMATCH'
    | 'BINDER_MODE_MISMATCH';

export interface CoreRuntimeComparisonMismatch {
    readonly code: CoreRuntimeComparisonMismatchCode;
    readonly path: readonly string[];
    readonly left: KernelExpression;
    readonly right: KernelExpression;
}

interface CoreRuntimeComparisonBase {
    readonly steps: number;
    readonly trace: readonly CoreRuntimeComparisonTraceEntry[];
}

export interface CoreRuntimeComparisonEqual
    extends CoreRuntimeComparisonBase {
    readonly status: 'equal';
}

export interface CoreRuntimeComparisonNotEqual
    extends CoreRuntimeComparisonBase {
    readonly status: 'not-equal';
    readonly mismatch: CoreRuntimeComparisonMismatch;
}

export interface CoreRuntimeComparisonStepLimit
    extends CoreRuntimeComparisonBase {
    readonly status: 'step-limit-exceeded';
    readonly side: CoreRuntimeComparisonSide;
    readonly path: readonly string[];
    readonly expression: KernelExpression;
    readonly nextRuleId: string;
}

export type CoreRuntimeComparisonResult =
    | CoreRuntimeComparisonEqual
    | CoreRuntimeComparisonNotEqual
    | CoreRuntimeComparisonStepLimit;

interface MutableComparisonState {
    readonly stepLimit: number;
    readonly trace: CoreRuntimeComparisonTraceEntry[];
}

type InternalComparisonOutcome =
    | { readonly status: 'equal' }
    | {
        readonly status: 'not-equal';
        readonly mismatch: CoreRuntimeComparisonMismatch;
    }
    | {
        readonly status: 'step-limit-exceeded';
        readonly side: CoreRuntimeComparisonSide;
        readonly path: readonly string[];
        readonly expression: KernelExpression;
        readonly nextRuleId: string;
    };

type HeadResult =
    | {
        readonly status: 'weak-head-normal';
        readonly expression: KernelExpression;
    }
    | Extract<
        InternalComparisonOutcome,
        { readonly status: 'step-limit-exceeded' }
    >;

const freezePath = (path: readonly string[]): readonly string[] =>
    Object.freeze([...path]);

const appendTrace = (
    state: MutableComparisonState,
    side: CoreRuntimeComparisonSide,
    path: readonly string[],
    entries: readonly CoreRuntimeWeakHeadTraceEntry[]
): void => {
    for (const entry of entries) {
        state.trace.push({
            step: state.trace.length,
            side,
            path: freezePath(path),
            ruleId: entry.ruleId,
            before: entry.before,
            after: entry.after
        });
    }
};

const weakHeadAt = (
    expression: KernelExpression,
    side: CoreRuntimeComparisonSide,
    path: readonly string[],
    state: MutableComparisonState
): HeadResult => {
    const result = coreRuntimeWeakHead(
        expression,
        state.stepLimit - state.trace.length
    );
    appendTrace(state, side, path, result.trace);

    if (result.status === 'step-limit-exceeded') {
        return {
            status: 'step-limit-exceeded',
            side,
            path: freezePath(path),
            expression: result.expression,
            nextRuleId: result.nextRuleId
        };
    }
    return {
        status: 'weak-head-normal',
        expression: result.expression
    };
};

const mismatch = (
    code: CoreRuntimeComparisonMismatchCode,
    path: readonly string[],
    left: KernelExpression,
    right: KernelExpression
): InternalComparisonOutcome => ({
    status: 'not-equal',
    mismatch: Object.freeze({
        code,
        path: freezePath(path),
        left,
        right
    })
});

const childPath = (
    path: readonly string[],
    segment: string
): readonly string[] => [...path, segment];

const compareAt = (
    leftInput: KernelExpression,
    rightInput: KernelExpression,
    path: readonly string[],
    state: MutableComparisonState
): InternalComparisonOutcome => {
    if (kernelExpressionEquals(leftInput, rightInput)) {
        return { status: 'equal' };
    }

    const leftHead = weakHeadAt(leftInput, 'left', path, state);
    if (leftHead.status === 'step-limit-exceeded') return leftHead;
    const rightHead = weakHeadAt(rightInput, 'right', path, state);
    if (rightHead.status === 'step-limit-exceeded') return rightHead;

    const left = leftHead.expression;
    const right = rightHead.expression;
    if (kernelExpressionEquals(left, right)) {
        return { status: 'equal' };
    }
    if (left.tag !== right.tag) {
        return mismatch('TAG_MISMATCH', path, left, right);
    }

    switch (left.tag) {
        case 'universe':
            return { status: 'equal' };
        case 'reference':
            return mismatch(
                'REFERENCE_MISMATCH',
                path,
                left,
                right
            );
        case 'bound':
            return mismatch(
                'BOUND_VARIABLE_MISMATCH',
                path,
                left,
                right
            );
        case 'meta':
            return mismatch(
                'METAVARIABLE_MISMATCH',
                path,
                left,
                right
            );
        case 'application': {
            const other = right as typeof left;
            if (left.owner !== other.owner) {
                return mismatch('OWNER_MISMATCH', path, left, other);
            }
            if (left.arguments.length !== other.arguments.length) {
                return mismatch('ARITY_MISMATCH', path, left, other);
            }
            for (let index = 0; index < left.arguments.length; index++) {
                const leftArgument = left.arguments[index];
                const rightArgument = other.arguments[index];
                const argumentPath = childPath(
                    path,
                    `application:${left.owner}:argument:${index}`
                );
                if (leftArgument.plicity !== rightArgument.plicity) {
                    return mismatch(
                        'PLICITY_MISMATCH',
                        argumentPath,
                        leftArgument.value,
                        rightArgument.value
                    );
                }
                const outcome = compareAt(
                    leftArgument.value,
                    rightArgument.value,
                    argumentPath,
                    state
                );
                if (outcome.status !== 'equal') return outcome;
            }
            return { status: 'equal' };
        }
        case 'call': {
            const other = right as typeof left;
            if (left.arguments.length !== other.arguments.length) {
                return mismatch('ARITY_MISMATCH', path, left, other);
            }
            const callee = compareAt(
                left.callee,
                other.callee,
                childPath(path, 'call:callee'),
                state
            );
            if (callee.status !== 'equal') return callee;

            for (let index = 0; index < left.arguments.length; index++) {
                const leftArgument = left.arguments[index];
                const rightArgument = other.arguments[index];
                const argumentPath = childPath(
                    path,
                    `call:argument:${index}`
                );
                if (leftArgument.plicity !== rightArgument.plicity) {
                    return mismatch(
                        'PLICITY_MISMATCH',
                        argumentPath,
                        leftArgument.value,
                        rightArgument.value
                    );
                }
                const outcome = compareAt(
                    leftArgument.value,
                    rightArgument.value,
                    argumentPath,
                    state
                );
                if (outcome.status !== 'equal') return outcome;
            }
            return { status: 'equal' };
        }
        case 'pi':
        case 'lambda': {
            const other = right as typeof left;
            if (
                left.binder.mode.plicity !==
                    other.binder.mode.plicity ||
                left.binder.mode.variation !==
                    other.binder.mode.variation
            ) {
                return mismatch(
                    'BINDER_MODE_MISMATCH',
                    childPath(path, `${left.tag}:binder-mode`),
                    left,
                    other
                );
            }
            const binderType = compareAt(
                left.binder.type,
                other.binder.type,
                childPath(path, `${left.tag}:binder-type`),
                state
            );
            if (binderType.status !== 'equal') return binderType;
            return compareAt(
                left.body,
                other.body,
                childPath(path, `${left.tag}:body`),
                state
            );
        }
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
};

const freezeTrace = (
    trace: readonly CoreRuntimeComparisonTraceEntry[]
): readonly CoreRuntimeComparisonTraceEntry[] => Object.freeze(
    trace.map(entry => Object.freeze({
        ...entry,
        path: freezePath(entry.path)
    }))
);

/**
 * Decide equality in the structural-plus-reviewed-runtime fragment.
 *
 * `stepLimit` is global across left/right weak-head work and every recursively
 * compared child. The first mismatch or exhaustion path is deterministic.
 */
export function coreRuntimeDefinitionalCompare(
    left: KernelExpression,
    right: KernelExpression,
    stepLimit: number
): CoreRuntimeComparisonResult {
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new CoreRuntimeEvaluationError(
            'INVALID_STEP_LIMIT',
            left.provenance,
            `Runtime comparison step limit must be a nonnegative safe ` +
            `integer; received ${stepLimit}`
        );
    }

    const state: MutableComparisonState = {
        stepLimit,
        trace: []
    };
    const outcome = compareAt(left, right, ['$'], state);
    const base = {
        steps: state.trace.length,
        trace: freezeTrace(state.trace)
    };
    switch (outcome.status) {
        case 'equal':
            return Object.freeze({
                status: 'equal',
                ...base
            });
        case 'not-equal':
            return Object.freeze({
                status: 'not-equal',
                ...base,
                mismatch: outcome.mismatch
            });
        case 'step-limit-exceeded':
            return Object.freeze({
                status: 'step-limit-exceeded',
                ...base,
                side: outcome.side,
                path: freezePath(outcome.path),
                expression: outcome.expression,
                nextRuleId: outcome.nextRuleId
            });
        default: {
            const exhaustive: never = outcome;
            return exhaustive;
        }
    }
}

const fullProjectionOwners = new Set<CoreOwnerId>(
    Object.values(PROJECTION_PAIR_SCHEMAS).map(pair => pair.full)
);

/**
 * Global termination measure for the exact reviewed runtime rules.
 *
 * Every compiled rule removes one full projection owner and duplicates no
 * captured subtree, so each accepted rewrite strictly decreases this count
 * by at least one. Non-left-linear matches may discard additional copies.
 */
export function coreRuntimeFullProjectionCount(
    expression: KernelExpression
): number {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return 0;
        case 'meta':
            return expression.spine.reduce(
                (count, item) =>
                    count + coreRuntimeFullProjectionCount(item),
                0
            );
        case 'application':
            return (
                fullProjectionOwners.has(expression.owner) ? 1 : 0
            ) + expression.arguments.reduce(
                (count, argument) =>
                    count +
                    coreRuntimeFullProjectionCount(argument.value),
                0
            );
        case 'call':
            return coreRuntimeFullProjectionCount(expression.callee) +
                expression.arguments.reduce(
                    (count, argument) =>
                        count +
                        coreRuntimeFullProjectionCount(argument.value),
                    0
                );
        case 'pi':
        case 'lambda':
            return coreRuntimeFullProjectionCount(
                expression.binder.type
            ) + coreRuntimeFullProjectionCount(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}
