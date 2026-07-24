/**
 * Deterministic head rewriting for the reviewed emdash v3.2 runtime program.
 *
 * This module executes only `CORE_MVP_RUNTIME_PROGRAM`. Matching an individual
 * compiled candidate is exposed for structural diagnostics, but it does not
 * grant that candidate product authority. Definitional comparison and H-04
 * trust claims remain outside this TSK-2B boundary.
 */

import {
    KernelExpression,
    Provenance,
    kernelApplication,
    kernelExpressionEquals,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS
} from './schema';
import {
    CORE_MVP_RUNTIME_PROGRAM,
    CoreCompiledRulePattern,
    CoreCompiledRuntimeRule
} from './runtime';

export interface CoreRuntimeMatch {
    readonly ruleId: string;
    /**
     * `bindings[slot]` is the exact Core subtree captured for that compiled
     * variable slot. The array is immutable; captured expressions are not
     * mutated or recursively frozen.
     */
    readonly bindings: readonly KernelExpression[];
}

export interface CoreRuntimeHeadRewrite {
    readonly status: 'rewritten';
    readonly ruleId: string;
    readonly ruleIndex: number;
    readonly before: KernelExpression;
    readonly after: KernelExpression;
    readonly match: CoreRuntimeMatch;
}

export interface CoreRuntimeHeadIrreducible {
    readonly status: 'irreducible';
    readonly expression: KernelExpression;
}

export type CoreRuntimeHeadRewriteResult =
    | CoreRuntimeHeadRewrite
    | CoreRuntimeHeadIrreducible;

export interface CoreRuntimeWeakHeadTraceEntry {
    readonly step: number;
    readonly ruleId: string;
    readonly before: KernelExpression;
    readonly after: KernelExpression;
}

export interface CoreRuntimeWeakHeadNormal {
    readonly status: 'weak-head-normal';
    readonly expression: KernelExpression;
    readonly steps: number;
    readonly trace: readonly CoreRuntimeWeakHeadTraceEntry[];
}

export interface CoreRuntimeWeakHeadStepLimit {
    readonly status: 'step-limit-exceeded';
    readonly expression: KernelExpression;
    readonly steps: number;
    readonly trace: readonly CoreRuntimeWeakHeadTraceEntry[];
    readonly nextRuleId: string;
}

export type CoreRuntimeWeakHeadResult =
    | CoreRuntimeWeakHeadNormal
    | CoreRuntimeWeakHeadStepLimit;

export type CoreRuntimeEvaluationErrorCode =
    | 'INVALID_STEP_LIMIT'
    | 'INCOMPLETE_RUNTIME_MATCH';

export class CoreRuntimeEvaluationError extends Error {
    constructor(
        public readonly code: CoreRuntimeEvaluationErrorCode,
        public readonly provenance: Provenance,
        message: string
    ) {
        super(message);
        this.name = 'CoreRuntimeEvaluationError';
    }
}

const matchPattern = (
    pattern: CoreCompiledRulePattern,
    expression: KernelExpression,
    bindings: (KernelExpression | undefined)[]
): boolean => {
    switch (pattern.tag) {
        case 'variable': {
            const existing = bindings[pattern.slot];
            if (existing === undefined) {
                bindings[pattern.slot] = expression;
                return true;
            }
            return kernelExpressionEquals(existing, expression);
        }
        case 'owner-application': {
            if (
                expression.tag !== 'application' ||
                expression.owner !== pattern.owner ||
                expression.arguments.length !== pattern.arguments.length
            ) {
                return false;
            }

            const schema = CORE_OWNER_SCHEMAS[pattern.owner];
            return pattern.arguments.every((argumentPattern, index) => {
                const argument = expression.arguments[index];
                return argument.plicity === schema.slots[index].plicity &&
                    matchPattern(
                        argumentPattern,
                        argument.value,
                        bindings
                    );
            });
        }
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

/**
 * Structurally match one compiled rule without granting it executable product
 * membership. Repeated variable slots use alpha-invariant Core equality and
 * therefore ignore binder hints and provenance while preserving semantic
 * owner, plicity, binder-mode, free-name, and meta-session distinctions.
 */
export function coreRuntimeMatchRule(
    expression: KernelExpression,
    rule: CoreCompiledRuntimeRule
): CoreRuntimeMatch | undefined {
    const bindings: (KernelExpression | undefined)[] =
        rule.variables.map(() => undefined);
    if (!matchPattern(rule.left, expression, bindings)) return undefined;
    if (bindings.some(binding => binding === undefined)) return undefined;

    return Object.freeze({
        ruleId: rule.id,
        bindings: Object.freeze(
            bindings.slice() as KernelExpression[]
        )
    });
}

const rewrittenProvenance = (
    rule: CoreCompiledRuntimeRule,
    redex: KernelExpression
): Provenance => provenance(
    'derived',
    `runtime rewrite ${rule.id}`,
    redex.provenance.span
);

const instantiatePattern = (
    pattern: CoreCompiledRulePattern,
    match: CoreRuntimeMatch,
    rule: CoreCompiledRuntimeRule,
    redex: KernelExpression
): KernelExpression => {
    switch (pattern.tag) {
        case 'variable': {
            const binding = match.bindings[pattern.slot];
            if (binding === undefined) {
                throw new CoreRuntimeEvaluationError(
                    'INCOMPLETE_RUNTIME_MATCH',
                    redex.provenance,
                    `Runtime rule '${rule.id}' has no binding for slot ` +
                    pattern.slot
                );
            }
            return binding;
        }
        case 'owner-application':
            return kernelApplication(
                pattern.owner,
                pattern.arguments.map(argument => ({
                    value: instantiatePattern(
                        argument,
                        match,
                        rule,
                        redex
                    )
                })),
                rewrittenProvenance(rule, redex)
            );
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

/**
 * Apply at most one reviewed runtime rule at the root of `expression`.
 *
 * Rule buckets and indices come only from the content-hashed H-03 program.
 * An irreducible result returns the original expression by identity.
 */
export function coreRuntimeRewriteHead(
    expression: KernelExpression
): CoreRuntimeHeadRewriteResult {
    if (expression.tag !== 'application') {
        return Object.freeze({
            status: 'irreducible',
            expression
        });
    }

    const ruleIndices =
        CORE_MVP_RUNTIME_PROGRAM.ruleIndicesByRoot[expression.owner] ?? [];
    for (const ruleIndex of ruleIndices) {
        const rule = CORE_MVP_RUNTIME_PROGRAM.rules[ruleIndex];
        const match = coreRuntimeMatchRule(expression, rule);
        if (!match) continue;

        return Object.freeze({
            status: 'rewritten',
            ruleId: rule.id,
            ruleIndex,
            before: expression,
            after: instantiatePattern(
                rule.right,
                match,
                rule,
                expression
            ),
            match
        });
    }

    return Object.freeze({
        status: 'irreducible',
        expression
    });
}

const frozenTrace = (
    trace: readonly CoreRuntimeWeakHeadTraceEntry[]
): readonly CoreRuntimeWeakHeadTraceEntry[] =>
    Object.freeze(trace.map(entry => Object.freeze({ ...entry })));

/**
 * Repeatedly rewrite only the expression head under an explicit step bound.
 *
 * Arguments, binders, and generic-call callees are deliberately not traversed
 * in TSK-2B. A zero bound can still distinguish an already irreducible head
 * from a reducible head whose next reviewed rule would exceed the bound.
 */
export function coreRuntimeWeakHead(
    expression: KernelExpression,
    stepLimit: number
): CoreRuntimeWeakHeadResult {
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new CoreRuntimeEvaluationError(
            'INVALID_STEP_LIMIT',
            expression.provenance,
            `Runtime weak-head step limit must be a nonnegative safe ` +
            `integer; received ${stepLimit}`
        );
    }

    let current = expression;
    const trace: CoreRuntimeWeakHeadTraceEntry[] = [];

    while (true) {
        const rewrite = coreRuntimeRewriteHead(current);
        if (rewrite.status === 'irreducible') {
            return Object.freeze({
                status: 'weak-head-normal',
                expression: current,
                steps: trace.length,
                trace: frozenTrace(trace)
            });
        }
        if (trace.length === stepLimit) {
            return Object.freeze({
                status: 'step-limit-exceeded',
                expression: current,
                steps: trace.length,
                trace: frozenTrace(trace),
                nextRuleId: rewrite.ruleId
            });
        }

        trace.push({
            step: trace.length,
            ruleId: rewrite.ruleId,
            before: rewrite.before,
            after: rewrite.after
        });
        current = rewrite.after;
    }
}
