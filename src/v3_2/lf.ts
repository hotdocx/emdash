/**
 * Candidate outer λΠ logical-framework computation for explicit Core.
 *
 * LF-1A intentionally provides only bounded weak-head beta. It is not
 * imported by the browser product entry point and does not alter the frozen
 * `emdash-v3.2-mvp-1` runtime program or definitional comparator.
 */

import {
    KernelArgument,
    KernelCall,
    KernelExpression,
    Provenance,
    Plicity,
    kernelCall,
    kernelInstantiate,
    provenance
} from './kernel';

export type CoreLfBetaIrreducibleReason =
    | 'not-a-call'
    | 'empty-call'
    | 'head-not-lambda';

export interface CoreLfBetaHeadReduction {
    readonly status: 'reduced';
    readonly before: KernelExpression;
    readonly after: KernelExpression;
    readonly binderPlicity: Plicity;
    readonly argumentPlicity: Plicity;
    readonly residualArgumentCount: number;
}

export interface CoreLfBetaHeadIrreducible {
    readonly status: 'irreducible';
    readonly expression: KernelExpression;
    readonly head: KernelExpression;
    readonly reason: CoreLfBetaIrreducibleReason;
}

export interface CoreLfBetaHeadStuck {
    readonly status: 'stuck';
    readonly expression: KernelExpression;
    readonly head: KernelExpression;
    readonly reason: 'plicity-mismatch';
    readonly expectedPlicity: Plicity;
    readonly actualPlicity: Plicity;
}

export type CoreLfBetaHeadResult =
    | CoreLfBetaHeadReduction
    | CoreLfBetaHeadIrreducible
    | CoreLfBetaHeadStuck;

export interface CoreLfBetaTraceEntry {
    readonly step: number;
    readonly kind: 'beta';
    readonly before: KernelExpression;
    readonly after: KernelExpression;
    readonly binderPlicity: Plicity;
    readonly argumentPlicity: Plicity;
    readonly residualArgumentCount: number;
}

export interface CoreLfBetaRedexSummary {
    readonly binderPlicity: Plicity;
    readonly argumentPlicity: Plicity;
    readonly residualArgumentCount: number;
}

interface CoreLfBetaWeakHeadBase {
    readonly expression: KernelExpression;
    readonly steps: number;
    readonly trace: readonly CoreLfBetaTraceEntry[];
}

export interface CoreLfBetaWeakHeadNormal
    extends CoreLfBetaWeakHeadBase {
    readonly status: 'weak-head-normal';
    readonly reason: CoreLfBetaIrreducibleReason;
}

export interface CoreLfBetaWeakHeadStuck
    extends CoreLfBetaWeakHeadBase {
    readonly status: 'stuck';
    readonly reason: 'plicity-mismatch';
    readonly expectedPlicity: Plicity;
    readonly actualPlicity: Plicity;
}

export interface CoreLfBetaWeakHeadStepLimit
    extends CoreLfBetaWeakHeadBase {
    readonly status: 'step-limit-exceeded';
    readonly next: CoreLfBetaRedexSummary;
}

export type CoreLfBetaWeakHeadResult =
    | CoreLfBetaWeakHeadNormal
    | CoreLfBetaWeakHeadStuck
    | CoreLfBetaWeakHeadStepLimit;

export type CoreLfEvaluationErrorCode = 'INVALID_STEP_LIMIT';

export class CoreLfEvaluationError extends Error {
    constructor(
        public readonly code: CoreLfEvaluationErrorCode,
        public readonly provenance: Provenance,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfEvaluationError';
    }
}

interface CoreLfCallSpine {
    readonly head: KernelExpression;
    readonly arguments: readonly KernelArgument[];
    readonly hasEmptyCall: boolean;
}

/**
 * Read nested calls as one left-associated elimination spine.
 *
 * Flattening is an administrative view, not a computation step. An empty
 * call cannot be built through `kernelCall`, but detecting one here keeps the
 * evaluator total over structurally supplied `KernelCall` values.
 */
const decomposeCallSpine = (
    expression: KernelCall
): CoreLfCallSpine => {
    let current: KernelExpression = expression;
    const segments: (readonly KernelArgument[])[] = [];
    let hasEmptyCall = false;

    while (current.tag === 'call') {
        if (current.arguments.length === 0) hasEmptyCall = true;
        segments.unshift(current.arguments);
        current = current.callee;
    }

    return {
        head: current,
        arguments: Object.freeze(segments.flat()),
        hasEmptyCall
    };
};

const residualCallProvenance = (
    expression: KernelExpression
): Provenance => provenance(
    'derived',
    'outer LF beta residual call spine',
    expression.provenance.span
);

/**
 * Contract one beta redex at the weak head of an explicit Core call.
 *
 * The first argument is consumed only when its plicity matches the lambda
 * binder. Any residual ordered call spine is rebuilt around the instantiated
 * body. No argument, binder body, semantic-owner application, or definition
 * is otherwise evaluated.
 */
export function coreLfBetaReduceHead(
    expression: KernelExpression
): CoreLfBetaHeadResult {
    if (expression.tag !== 'call') {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: expression,
            reason: 'not-a-call'
        });
    }

    const spine = decomposeCallSpine(expression);
    if (spine.hasEmptyCall || spine.arguments.length === 0) {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'empty-call'
        });
    }
    if (spine.head.tag !== 'lambda') {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'head-not-lambda'
        });
    }

    const argument = spine.arguments[0];
    const expectedPlicity = spine.head.binder.mode.plicity;
    if (argument.plicity !== expectedPlicity) {
        return Object.freeze({
            status: 'stuck',
            expression,
            head: spine.head,
            reason: 'plicity-mismatch',
            expectedPlicity,
            actualPlicity: argument.plicity
        });
    }

    const instantiated = kernelInstantiate(
        spine.head.body,
        argument.value
    );
    const residualArguments = spine.arguments.slice(1);
    const after = residualArguments.length === 0
        ? instantiated
        : kernelCall(
            instantiated,
            residualArguments.map(residual => ({
                plicity: residual.plicity,
                value: residual.value,
                provenance: residual.provenance
            })),
            residualCallProvenance(expression)
        );

    return Object.freeze({
        status: 'reduced',
        before: expression,
        after,
        binderPlicity: expectedPlicity,
        argumentPlicity: argument.plicity,
        residualArgumentCount: residualArguments.length
    });
}

const frozenTrace = (
    trace: readonly CoreLfBetaTraceEntry[]
): readonly CoreLfBetaTraceEntry[] =>
    Object.freeze(trace.map(entry => Object.freeze({ ...entry })));

const redexSummary = (
    reduction: CoreLfBetaHeadReduction
): CoreLfBetaRedexSummary => Object.freeze({
    binderPlicity: reduction.binderPlicity,
    argumentPlicity: reduction.argumentPlicity,
    residualArgumentCount: reduction.residualArgumentCount
});

/**
 * Repeatedly contract weak-head beta under one explicit global step bound.
 *
 * A zero bound distinguishes a term already at beta weak-head normal form
 * from a reducible term. Plicity mismatch is a structured stuck result and
 * does not consume a beta step. Step-limit exhaustion also returns normally,
 * including a summary of the next available redex.
 */
export function coreLfBetaWeakHead(
    expression: KernelExpression,
    stepLimit: number
): CoreLfBetaWeakHeadResult {
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new CoreLfEvaluationError(
            'INVALID_STEP_LIMIT',
            expression.provenance,
            `Outer LF beta step limit must be a nonnegative safe integer; ` +
            `received ${stepLimit}`
        );
    }

    let current = expression;
    const trace: CoreLfBetaTraceEntry[] = [];

    while (true) {
        const reduction = coreLfBetaReduceHead(current);
        if (reduction.status === 'irreducible') {
            return Object.freeze({
                status: 'weak-head-normal',
                expression: current,
                steps: trace.length,
                trace: frozenTrace(trace),
                reason: reduction.reason
            });
        }
        if (reduction.status === 'stuck') {
            return Object.freeze({
                status: 'stuck',
                expression: current,
                steps: trace.length,
                trace: frozenTrace(trace),
                reason: reduction.reason,
                expectedPlicity: reduction.expectedPlicity,
                actualPlicity: reduction.actualPlicity
            });
        }
        if (trace.length === stepLimit) {
            return Object.freeze({
                status: 'step-limit-exceeded',
                expression: current,
                steps: trace.length,
                trace: frozenTrace(trace),
                next: redexSummary(reduction)
            });
        }

        trace.push(Object.freeze({
            step: trace.length,
            kind: 'beta',
            before: reduction.before,
            after: reduction.after,
            binderPlicity: reduction.binderPlicity,
            argumentPlicity: reduction.argumentPlicity,
            residualArgumentCount: reduction.residualArgumentCount
        }));
        current = reduction.after;
    }
}
