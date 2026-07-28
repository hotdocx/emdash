/**
 * Combined candidate conversion for the outer λΠ LF.
 *
 * This module interleaves session zonking, generic beta, transparent delta,
 * and the exact reviewed semantic runtime program. The four mechanisms share
 * one explicit trace budget. It remains a candidate path and does not change
 * the frozen MVP comparator.
 */

import {
    KernelExpression,
    Plicity,
    kernelExpressionEquals
} from './kernel';
import {
    CoreLfEvaluationError,
    coreLfBetaReduceHead
} from './lf';
import {
    CoreLfDeclarationEnvironment,
    CoreLfDeltaIrreducibleReason,
    coreLfDeltaReduceHead
} from './lf_declarations';
import {
    CoreRuntimeHeadRewriteResult,
    coreRuntimeRewriteHead
} from './evaluator';
import {
    CoreElaborationSession
} from './session';

export type CoreLfCombinedReduction =
    | {
        readonly kind: 'zonk';
        readonly before: KernelExpression;
        readonly after: KernelExpression;
    }
    | {
        readonly kind: 'beta';
        readonly before: KernelExpression;
        readonly after: KernelExpression;
        readonly binderPlicity: Plicity;
        readonly argumentPlicity: Plicity;
        readonly residualArgumentCount: number;
    }
    | {
        readonly kind: 'delta';
        readonly before: KernelExpression;
        readonly after: KernelExpression;
        readonly declarationName: string;
        readonly declarationOrdinal: number;
    }
    | {
        readonly kind: 'runtime';
        readonly before: KernelExpression;
        readonly after: KernelExpression;
        readonly ruleId: string;
        readonly ruleIndex: number;
    };

/**
 * One immutable, catalog-owned runtime component.
 *
 * This is deliberately not a rule-registration API. Candidate catalogs may
 * supply a concrete reviewed program, while the ordinary LF profile omits
 * the component and therefore retains its exact pre-DIRECTED semantics.
 */
export interface CoreLfCatalogRuntime {
    readonly revision: string;
    readonly ruleIds: readonly string[];
    rewriteHead(
        expression: KernelExpression
    ): CoreRuntimeHeadRewriteResult;
}

export type CoreLfCombinedTraceEntry = CoreLfCombinedReduction & {
    readonly step: number;
};

export type CoreLfCombinedNextStep =
    | { readonly kind: 'zonk' }
    | {
        readonly kind: 'beta';
        readonly binderPlicity: Plicity;
        readonly argumentPlicity: Plicity;
        readonly residualArgumentCount: number;
    }
    | {
        readonly kind: 'delta';
        readonly declarationName: string;
        readonly declarationOrdinal: number;
    }
    | {
        readonly kind: 'runtime';
        readonly ruleId: string;
        readonly ruleIndex: number;
    };

export type CoreLfCombinedNormalReason =
    | 'no-head-reduction'
    | 'empty-call';

export interface CoreLfCombinedHeadReduced {
    readonly status: 'reduced';
    readonly reduction: CoreLfCombinedReduction;
}

export interface CoreLfCombinedHeadIrreducible {
    readonly status: 'irreducible';
    readonly expression: KernelExpression;
    readonly reason: CoreLfCombinedNormalReason;
    readonly deltaReason?: CoreLfDeltaIrreducibleReason;
}

export interface CoreLfCombinedHeadStuck {
    readonly status: 'stuck';
    readonly expression: KernelExpression;
    readonly reason: 'plicity-mismatch';
    readonly expectedPlicity: Plicity;
    readonly actualPlicity: Plicity;
}

export type CoreLfCombinedHeadResult =
    | CoreLfCombinedHeadReduced
    | CoreLfCombinedHeadIrreducible
    | CoreLfCombinedHeadStuck;

interface CoreLfCombinedWeakHeadBase {
    readonly expression: KernelExpression;
    readonly steps: number;
    readonly trace: readonly CoreLfCombinedTraceEntry[];
}

export interface CoreLfCombinedWeakHeadNormal
    extends CoreLfCombinedWeakHeadBase {
    readonly status: 'weak-head-normal';
    readonly reason: CoreLfCombinedNormalReason;
    readonly deltaReason?: CoreLfDeltaIrreducibleReason;
}

export interface CoreLfCombinedWeakHeadStuck
    extends CoreLfCombinedWeakHeadBase {
    readonly status: 'stuck';
    readonly reason: 'plicity-mismatch';
    readonly expectedPlicity: Plicity;
    readonly actualPlicity: Plicity;
}

export interface CoreLfCombinedWeakHeadStepLimit
    extends CoreLfCombinedWeakHeadBase {
    readonly status: 'step-limit-exceeded';
    readonly next: CoreLfCombinedNextStep;
}

export type CoreLfCombinedWeakHeadResult =
    | CoreLfCombinedWeakHeadNormal
    | CoreLfCombinedWeakHeadStuck
    | CoreLfCombinedWeakHeadStepLimit;

export type CoreLfConversionErrorCode = 'FOREIGN_DECLARATION_ENVIRONMENT';

export class CoreLfConversionError extends Error {
    constructor(
        public readonly code: CoreLfConversionErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfConversionError';
    }
}

const assertCompatibleSession = (
    environment: CoreLfDeclarationEnvironment,
    session?: CoreElaborationSession
): void => {
    if (
        session !== undefined &&
        session.environment !== environment.coreEnvironment
    ) {
        throw new CoreLfConversionError(
            'FOREIGN_DECLARATION_ENVIRONMENT',
            'Core LF conversion session belongs to a different declaration ' +
            'environment'
        );
    }
};

/**
 * Select the next weak-head transition in the fixed candidate order:
 * zonk, beta, delta, then reviewed semantic runtime.
 */
export function coreLfCombinedReduceHead(
    environment: CoreLfDeclarationEnvironment,
    expression: KernelExpression,
    session?: CoreElaborationSession,
    catalogRuntime?: CoreLfCatalogRuntime
): CoreLfCombinedHeadResult {
    assertCompatibleSession(environment, session);

    if (session !== undefined) {
        const zonked = session.zonk(expression);
        if (!kernelExpressionEquals(zonked, expression)) {
            return Object.freeze({
                status: 'reduced',
                reduction: Object.freeze({
                    kind: 'zonk',
                    before: expression,
                    after: zonked
                })
            });
        }
    }

    const beta = coreLfBetaReduceHead(expression);
    if (beta.status === 'reduced') {
        return Object.freeze({
            status: 'reduced',
            reduction: Object.freeze({
                kind: 'beta',
                before: beta.before,
                after: beta.after,
                binderPlicity: beta.binderPlicity,
                argumentPlicity: beta.argumentPlicity,
                residualArgumentCount: beta.residualArgumentCount
            })
        });
    }
    if (beta.status === 'stuck') {
        return Object.freeze({
            status: 'stuck',
            expression,
            reason: beta.reason,
            expectedPlicity: beta.expectedPlicity,
            actualPlicity: beta.actualPlicity
        });
    }
    if (beta.reason === 'empty-call') {
        return Object.freeze({
            status: 'irreducible',
            expression,
            reason: 'empty-call'
        });
    }

    const delta = coreLfDeltaReduceHead(environment, expression);
    if (delta.status === 'unfolded') {
        return Object.freeze({
            status: 'reduced',
            reduction: Object.freeze({
                kind: 'delta',
                before: delta.before,
                after: delta.after,
                declarationName: delta.declarationName,
                declarationOrdinal: delta.declarationOrdinal
            })
        });
    }
    if (delta.reason === 'empty-call') {
        return Object.freeze({
            status: 'irreducible',
            expression,
            reason: 'empty-call',
            deltaReason: delta.reason
        });
    }

    const catalogRewrite = catalogRuntime?.rewriteHead(expression);
    if (catalogRewrite?.status === 'rewritten') {
        return Object.freeze({
            status: 'reduced',
            reduction: Object.freeze({
                kind: 'runtime',
                before: catalogRewrite.before,
                after: catalogRewrite.after,
                ruleId: catalogRewrite.ruleId,
                ruleIndex: catalogRewrite.ruleIndex
            })
        });
    }

    const runtime = coreRuntimeRewriteHead(expression);
    if (runtime.status === 'rewritten') {
        return Object.freeze({
            status: 'reduced',
            reduction: Object.freeze({
                kind: 'runtime',
                before: runtime.before,
                after: runtime.after,
                ruleId: runtime.ruleId,
                ruleIndex: runtime.ruleIndex
            })
        });
    }

    return Object.freeze({
        status: 'irreducible',
        expression,
        reason: 'no-head-reduction',
        deltaReason: delta.reason
    });
}

const nextStep = (
    reduction: CoreLfCombinedReduction
): CoreLfCombinedNextStep => {
    switch (reduction.kind) {
        case 'zonk':
            return Object.freeze({ kind: 'zonk' });
        case 'beta':
            return Object.freeze({
                kind: 'beta',
                binderPlicity: reduction.binderPlicity,
                argumentPlicity: reduction.argumentPlicity,
                residualArgumentCount: reduction.residualArgumentCount
            });
        case 'delta':
            return Object.freeze({
                kind: 'delta',
                declarationName: reduction.declarationName,
                declarationOrdinal: reduction.declarationOrdinal
            });
        case 'runtime':
            return Object.freeze({
                kind: 'runtime',
                ruleId: reduction.ruleId,
                ruleIndex: reduction.ruleIndex
            });
        default: {
            const exhaustive: never = reduction;
            return exhaustive;
        }
    }
};

const freezeCombinedTrace = (
    trace: readonly CoreLfCombinedTraceEntry[]
): readonly CoreLfCombinedTraceEntry[] =>
    Object.freeze(trace.map(entry => Object.freeze({ ...entry })));

/**
 * Reduce a combined candidate weak head under one shared operation budget.
 */
export function coreLfCombinedWeakHead(
    environment: CoreLfDeclarationEnvironment,
    expression: KernelExpression,
    stepLimit: number,
    session?: CoreElaborationSession,
    catalogRuntime?: CoreLfCatalogRuntime
): CoreLfCombinedWeakHeadResult {
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new CoreLfEvaluationError(
            'INVALID_STEP_LIMIT',
            expression.provenance,
            `Combined Core LF step limit must be a nonnegative safe integer; ` +
            `received ${stepLimit}`
        );
    }
    assertCompatibleSession(environment, session);

    let current = expression;
    const trace: CoreLfCombinedTraceEntry[] = [];

    while (true) {
        const head = coreLfCombinedReduceHead(
            environment,
            current,
            session,
            catalogRuntime
        );
        if (head.status === 'irreducible') {
            return Object.freeze({
                status: 'weak-head-normal',
                expression: current,
                steps: trace.length,
                trace: freezeCombinedTrace(trace),
                reason: head.reason,
                deltaReason: head.deltaReason
            });
        }
        if (head.status === 'stuck') {
            return Object.freeze({
                status: 'stuck',
                expression: current,
                steps: trace.length,
                trace: freezeCombinedTrace(trace),
                reason: head.reason,
                expectedPlicity: head.expectedPlicity,
                actualPlicity: head.actualPlicity
            });
        }
        if (trace.length === stepLimit) {
            return Object.freeze({
                status: 'step-limit-exceeded',
                expression: current,
                steps: trace.length,
                trace: freezeCombinedTrace(trace),
                next: nextStep(head.reduction)
            });
        }

        trace.push(Object.freeze({
            ...head.reduction,
            step: trace.length
        }) as CoreLfCombinedTraceEntry);
        current = head.reduction.after;
    }
}

export type CoreLfComparisonSide = 'left' | 'right';

export interface CoreLfComparisonTraceEntry {
    readonly step: number;
    readonly side: CoreLfComparisonSide;
    readonly path: readonly string[];
    readonly reduction: CoreLfCombinedTraceEntry;
}

export type CoreLfComparisonMismatchCode =
    | 'TAG_MISMATCH'
    | 'REFERENCE_MISMATCH'
    | 'BOUND_VARIABLE_MISMATCH'
    | 'METAVARIABLE_MISMATCH'
    | 'OWNER_MISMATCH'
    | 'ARITY_MISMATCH'
    | 'PLICITY_MISMATCH'
    | 'BINDER_MODE_MISMATCH';

export interface CoreLfComparisonMismatch {
    readonly code: CoreLfComparisonMismatchCode;
    readonly path: readonly string[];
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly expectedPlicity?: Plicity;
    readonly actualPlicity?: Plicity;
}

interface CoreLfComparisonBase {
    readonly steps: number;
    readonly trace: readonly CoreLfComparisonTraceEntry[];
}

export interface CoreLfComparisonEqual extends CoreLfComparisonBase {
    readonly status: 'equal';
}

export interface CoreLfComparisonNotEqual extends CoreLfComparisonBase {
    readonly status: 'not-equal';
    readonly normalizedLeft: KernelExpression;
    readonly normalizedRight: KernelExpression;
    readonly mismatch: CoreLfComparisonMismatch;
}

export interface CoreLfComparisonStepLimit extends CoreLfComparisonBase {
    readonly status: 'step-limit-exceeded';
    readonly side: CoreLfComparisonSide;
    readonly path: readonly string[];
    readonly expression: KernelExpression;
    readonly next: CoreLfCombinedNextStep;
}

export type CoreLfComparisonResult =
    | CoreLfComparisonEqual
    | CoreLfComparisonNotEqual
    | CoreLfComparisonStepLimit;

interface MutableCoreLfComparisonState {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly session?: CoreElaborationSession;
    readonly catalogRuntime?: CoreLfCatalogRuntime;
    readonly stepLimit: number;
    readonly trace: CoreLfComparisonTraceEntry[];
}

type InternalCoreLfComparisonOutcome =
    | {
        readonly status: 'equal';
        readonly normalizedLeft: KernelExpression;
        readonly normalizedRight: KernelExpression;
    }
    | {
        readonly status: 'not-equal';
        readonly mismatch: CoreLfComparisonMismatch;
        readonly normalizedLeft: KernelExpression;
        readonly normalizedRight: KernelExpression;
    }
    | {
        readonly status: 'step-limit-exceeded';
        readonly side: CoreLfComparisonSide;
        readonly path: readonly string[];
        readonly expression: KernelExpression;
        readonly next: CoreLfCombinedNextStep;
    };

type CoreLfComparisonHead =
    | {
        readonly status: 'weak-head-normal';
        readonly expression: KernelExpression;
    }
    | {
        readonly status: 'plicity-stuck';
        readonly expression: KernelExpression;
        readonly expectedPlicity: Plicity;
        readonly actualPlicity: Plicity;
    }
    | Extract<
        InternalCoreLfComparisonOutcome,
        { readonly status: 'step-limit-exceeded' }
    >;

const freezePath = (path: readonly string[]): readonly string[] =>
    Object.freeze([...path]);

const appendComparisonTrace = (
    state: MutableCoreLfComparisonState,
    side: CoreLfComparisonSide,
    path: readonly string[],
    entries: readonly CoreLfCombinedTraceEntry[]
): void => {
    for (const entry of entries) {
        state.trace.push({
            step: state.trace.length,
            side,
            path: freezePath(path),
            reduction: entry
        });
    }
};

const comparisonWeakHeadAt = (
    expression: KernelExpression,
    side: CoreLfComparisonSide,
    path: readonly string[],
    state: MutableCoreLfComparisonState
): CoreLfComparisonHead => {
    const result = coreLfCombinedWeakHead(
        state.environment,
        expression,
        state.stepLimit - state.trace.length,
        state.session,
        state.catalogRuntime
    );
    appendComparisonTrace(state, side, path, result.trace);

    if (result.status === 'step-limit-exceeded') {
        return {
            status: 'step-limit-exceeded',
            side,
            path: freezePath(path),
            expression: result.expression,
            next: result.next
        };
    }
    if (result.status === 'stuck') {
        return {
            status: 'plicity-stuck',
            expression: result.expression,
            expectedPlicity: result.expectedPlicity,
            actualPlicity: result.actualPlicity
        };
    }
    return {
        status: 'weak-head-normal',
        expression: result.expression
    };
};

const comparisonMismatch = (
    code: CoreLfComparisonMismatchCode,
    path: readonly string[],
    left: KernelExpression,
    right: KernelExpression,
    plicity?: {
        readonly expectedPlicity: Plicity;
        readonly actualPlicity: Plicity;
    }
): InternalCoreLfComparisonOutcome => ({
    status: 'not-equal',
    normalizedLeft: left,
    normalizedRight: right,
    mismatch: Object.freeze({
        code,
        path: freezePath(path),
        left,
        right,
        expectedPlicity: plicity?.expectedPlicity,
        actualPlicity: plicity?.actualPlicity
    })
});

const comparisonEqual = (
    normalizedLeft: KernelExpression,
    normalizedRight: KernelExpression
): InternalCoreLfComparisonOutcome => ({
    status: 'equal',
    normalizedLeft,
    normalizedRight
});

const freezeArguments = <
    T extends {
        readonly plicity: Plicity;
        readonly value: KernelExpression;
    }
>(
    arguments_: readonly T[]
): readonly T[] => Object.freeze(
    arguments_.map(argument => Object.freeze({ ...argument }))
);

const replaceArgument = <
    T extends {
        readonly arguments: readonly {
            readonly plicity: Plicity;
            readonly value: KernelExpression;
        }[];
    }
>(
    expression: T,
    index: number,
    value: KernelExpression
): T => Object.freeze({
    ...expression,
    arguments: freezeArguments(
        expression.arguments.map((argument, argumentIndex) =>
            argumentIndex === index
                ? { ...argument, value }
                : argument
        )
    )
}) as T;

const replaceCallCallee = (
    expression: Extract<KernelExpression, { readonly tag: 'call' }>,
    callee: KernelExpression
): Extract<KernelExpression, { readonly tag: 'call' }> =>
    Object.freeze({
        ...expression,
        callee,
        arguments: freezeArguments(expression.arguments)
    });

type CoreLfBinderExpression = Extract<
    KernelExpression,
    { readonly tag: 'pi' | 'lambda' }
>;

const replaceBinderType = (
    expression: CoreLfBinderExpression,
    type: KernelExpression
): CoreLfBinderExpression => Object.freeze({
    ...expression,
    binder: Object.freeze({
        ...expression.binder,
        type
    })
});

const replaceBinderBody = (
    expression: CoreLfBinderExpression,
    body: KernelExpression
): CoreLfBinderExpression => Object.freeze({
    ...expression,
    body
});

const replaceMetaSpine = (
    expression: Extract<KernelExpression, { readonly tag: 'meta' }>,
    index: number,
    value: KernelExpression
): Extract<KernelExpression, { readonly tag: 'meta' }> =>
    Object.freeze({
        ...expression,
        spine: Object.freeze(expression.spine.map(
            (entry, entryIndex) => entryIndex === index ? value : entry
        ))
    });

const childPath = (
    path: readonly string[],
    segment: string
): readonly string[] => [...path, segment];

type CoreLfDescendantReduction =
    | { readonly status: 'unchanged' }
    | {
        readonly status: 'reduced';
        readonly expression: KernelExpression;
    }
    | Extract<
        InternalCoreLfComparisonOutcome,
        { readonly status: 'step-limit-exceeded' }
    >;

const reduceCoreLfChildAt = (
    expression: KernelExpression,
    side: CoreLfComparisonSide,
    path: readonly string[],
    state: MutableCoreLfComparisonState
): CoreLfDescendantReduction => {
    const head = comparisonWeakHeadAt(
        expression,
        side,
        path,
        state
    );
    if (head.status === 'step-limit-exceeded') return head;
    if (!kernelExpressionEquals(head.expression, expression)) {
        return {
            status: 'reduced',
            expression: head.expression
        };
    }
    return reduceOneCoreLfDescendantAt(
        head.expression,
        side,
        path,
        state
    );
};

/**
 * Find the first deterministic reduction strictly below one weak-head-normal
 * expression. This is the bounded fallback used when rigid heads differ:
 * normalizing a nested child may expose a reviewed redex at its parent.
 */
const reduceOneCoreLfDescendantAt = (
    expression: KernelExpression,
    side: CoreLfComparisonSide,
    path: readonly string[],
    state: MutableCoreLfComparisonState
): CoreLfDescendantReduction => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return { status: 'unchanged' };
        case 'meta': {
            for (let index = 0; index < expression.spine.length; index++) {
                const reduction = reduceCoreLfChildAt(
                    expression.spine[index],
                    side,
                    childPath(path, `meta:spine:${index}`),
                    state
                );
                if (reduction.status === 'step-limit-exceeded') {
                    return reduction;
                }
                if (reduction.status === 'reduced') {
                    return {
                        status: 'reduced',
                        expression: replaceMetaSpine(
                            expression,
                            index,
                            reduction.expression
                        )
                    };
                }
            }
            return { status: 'unchanged' };
        }
        case 'application': {
            for (
                let index = 0;
                index < expression.arguments.length;
                index++
            ) {
                const reduction = reduceCoreLfChildAt(
                    expression.arguments[index].value,
                    side,
                    childPath(
                        path,
                        `application:${expression.owner}:argument:${index}`
                    ),
                    state
                );
                if (reduction.status === 'step-limit-exceeded') {
                    return reduction;
                }
                if (reduction.status === 'reduced') {
                    return {
                        status: 'reduced',
                        expression: replaceArgument(
                            expression,
                            index,
                            reduction.expression
                        )
                    };
                }
            }
            return { status: 'unchanged' };
        }
        case 'call': {
            const callee = reduceCoreLfChildAt(
                expression.callee,
                side,
                childPath(path, 'call:callee'),
                state
            );
            if (callee.status === 'step-limit-exceeded') return callee;
            if (callee.status === 'reduced') {
                return {
                    status: 'reduced',
                    expression: replaceCallCallee(
                        expression,
                        callee.expression
                    )
                };
            }
            for (
                let index = 0;
                index < expression.arguments.length;
                index++
            ) {
                const reduction = reduceCoreLfChildAt(
                    expression.arguments[index].value,
                    side,
                    childPath(path, `call:argument:${index}`),
                    state
                );
                if (reduction.status === 'step-limit-exceeded') {
                    return reduction;
                }
                if (reduction.status === 'reduced') {
                    return {
                        status: 'reduced',
                        expression: replaceArgument(
                            expression,
                            index,
                            reduction.expression
                        )
                    };
                }
            }
            return { status: 'unchanged' };
        }
        case 'pi':
        case 'lambda': {
            const binderType = reduceCoreLfChildAt(
                expression.binder.type,
                side,
                childPath(path, `${expression.tag}:binder-type`),
                state
            );
            if (binderType.status === 'step-limit-exceeded') {
                return binderType;
            }
            if (binderType.status === 'reduced') {
                return {
                    status: 'reduced',
                    expression: replaceBinderType(
                        expression,
                        binderType.expression
                    )
                };
            }
            const body = reduceCoreLfChildAt(
                expression.body,
                side,
                childPath(path, `${expression.tag}:body`),
                state
            );
            if (body.status === 'step-limit-exceeded') return body;
            if (body.status === 'reduced') {
                return {
                    status: 'reduced',
                    expression: replaceBinderBody(
                        expression,
                        body.expression
                    )
                };
            }
            return { status: 'unchanged' };
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const retryCoreLfComparisonAfterDescendants = (
    left: KernelExpression,
    right: KernelExpression,
    path: readonly string[],
    state: MutableCoreLfComparisonState,
    fallback: InternalCoreLfComparisonOutcome
): InternalCoreLfComparisonOutcome => {
    if (fallback.status === 'step-limit-exceeded') return fallback;
    const leftReduction = reduceOneCoreLfDescendantAt(
        left,
        'left',
        path,
        state
    );
    if (leftReduction.status === 'step-limit-exceeded') {
        return leftReduction;
    }
    if (leftReduction.status === 'reduced') {
        return compareCoreLfAt(
            leftReduction.expression,
            right,
            path,
            state
        );
    }

    const rightReduction = reduceOneCoreLfDescendantAt(
        right,
        'right',
        path,
        state
    );
    if (rightReduction.status === 'step-limit-exceeded') {
        return rightReduction;
    }
    if (rightReduction.status === 'reduced') {
        return compareCoreLfAt(
            left,
            rightReduction.expression,
            path,
            state
        );
    }
    return fallback;
};

const compareCoreLfAt = (
    leftInput: KernelExpression,
    rightInput: KernelExpression,
    path: readonly string[],
    state: MutableCoreLfComparisonState
): InternalCoreLfComparisonOutcome => {
    if (kernelExpressionEquals(leftInput, rightInput)) {
        return comparisonEqual(leftInput, rightInput);
    }

    const leftHead = comparisonWeakHeadAt(
        leftInput,
        'left',
        path,
        state
    );
    if (leftHead.status === 'step-limit-exceeded') return leftHead;
    if (leftHead.status === 'plicity-stuck') {
        return comparisonMismatch(
            'PLICITY_MISMATCH',
            childPath(path, 'left:weak-head-plicity'),
            leftHead.expression,
            rightInput,
            leftHead
        );
    }

    const rightHead = comparisonWeakHeadAt(
        rightInput,
        'right',
        path,
        state
    );
    if (rightHead.status === 'step-limit-exceeded') return rightHead;
    if (rightHead.status === 'plicity-stuck') {
        return comparisonMismatch(
            'PLICITY_MISMATCH',
            childPath(path, 'right:weak-head-plicity'),
            leftHead.expression,
            rightHead.expression,
            rightHead
        );
    }

    const left = leftHead.expression;
    const right = rightHead.expression;
    if (kernelExpressionEquals(left, right)) {
        return comparisonEqual(left, right);
    }
    if (left.tag !== right.tag) {
        return retryCoreLfComparisonAfterDescendants(
            left,
            right,
            path,
            state,
            comparisonMismatch('TAG_MISMATCH', path, left, right)
        );
    }

    switch (left.tag) {
        case 'universe':
            return comparisonEqual(left, right);
        case 'reference':
            return retryCoreLfComparisonAfterDescendants(
                left,
                right,
                path,
                state,
                comparisonMismatch(
                    'REFERENCE_MISMATCH',
                    path,
                    left,
                    right
                )
            );
        case 'bound':
            return retryCoreLfComparisonAfterDescendants(
                left,
                right,
                path,
                state,
                comparisonMismatch(
                    'BOUND_VARIABLE_MISMATCH',
                    path,
                    left,
                    right
                )
            );
        case 'meta':
            return retryCoreLfComparisonAfterDescendants(
                left,
                right,
                path,
                state,
                comparisonMismatch(
                    'METAVARIABLE_MISMATCH',
                    path,
                    left,
                    right
                )
            );
        case 'application': {
            const other = right as typeof left;
            if (left.owner !== other.owner) {
                return retryCoreLfComparisonAfterDescendants(
                    left,
                    other,
                    path,
                    state,
                    comparisonMismatch(
                        'OWNER_MISMATCH',
                        path,
                        left,
                        other
                    )
                );
            }
            if (left.arguments.length !== other.arguments.length) {
                return retryCoreLfComparisonAfterDescendants(
                    left,
                    other,
                    path,
                    state,
                    comparisonMismatch(
                        'ARITY_MISMATCH',
                        path,
                        left,
                        other
                    )
                );
            }
            let normalizedLeft = left;
            let normalizedRight = other;
            for (
                let index = 0;
                index < normalizedLeft.arguments.length;
                index++
            ) {
                const leftArgument = normalizedLeft.arguments[index];
                const rightArgument = normalizedRight.arguments[index];
                const argumentPath = childPath(
                    path,
                    `application:${left.owner}:argument:${index}`
                );
                if (leftArgument.plicity !== rightArgument.plicity) {
                    return comparisonMismatch(
                        'PLICITY_MISMATCH',
                        argumentPath,
                        leftArgument.value,
                        rightArgument.value,
                        {
                            expectedPlicity: leftArgument.plicity,
                            actualPlicity: rightArgument.plicity
                        }
                    );
                }
                const outcome = compareCoreLfAt(
                    leftArgument.value,
                    rightArgument.value,
                    argumentPath,
                    state
                );
                if (outcome.status === 'step-limit-exceeded') {
                    return outcome;
                }
                normalizedLeft = replaceArgument(
                    normalizedLeft,
                    index,
                    outcome.normalizedLeft
                );
                normalizedRight = replaceArgument(
                    normalizedRight,
                    index,
                    outcome.normalizedRight
                );
                if (outcome.status === 'not-equal') {
                    if (
                        !kernelExpressionEquals(normalizedLeft, left) ||
                        !kernelExpressionEquals(normalizedRight, other)
                    ) {
                        return compareCoreLfAt(
                            normalizedLeft,
                            normalizedRight,
                            path,
                            state
                        );
                    }
                    return retryCoreLfComparisonAfterDescendants(
                        normalizedLeft,
                        normalizedRight,
                        path,
                        state,
                        {
                            ...outcome,
                            normalizedLeft,
                            normalizedRight
                        }
                    );
                }
            }
            return comparisonEqual(
                normalizedLeft,
                normalizedRight
            );
        }
        case 'call': {
            const other = right as typeof left;
            if (left.arguments.length !== other.arguments.length) {
                return retryCoreLfComparisonAfterDescendants(
                    left,
                    other,
                    path,
                    state,
                    comparisonMismatch(
                        'ARITY_MISMATCH',
                        path,
                        left,
                        other
                    )
                );
            }
            let normalizedLeft = left;
            let normalizedRight = other;
            const callee = compareCoreLfAt(
                normalizedLeft.callee,
                normalizedRight.callee,
                childPath(path, 'call:callee'),
                state
            );
            if (callee.status === 'step-limit-exceeded') return callee;
            normalizedLeft = replaceCallCallee(
                normalizedLeft,
                callee.normalizedLeft
            );
            normalizedRight = replaceCallCallee(
                normalizedRight,
                callee.normalizedRight
            );
            if (callee.status === 'not-equal') {
                if (
                    !kernelExpressionEquals(normalizedLeft, left) ||
                    !kernelExpressionEquals(normalizedRight, other)
                ) {
                    return compareCoreLfAt(
                        normalizedLeft,
                        normalizedRight,
                        path,
                        state
                    );
                }
                return retryCoreLfComparisonAfterDescendants(
                    normalizedLeft,
                    normalizedRight,
                    path,
                    state,
                    {
                        ...callee,
                        normalizedLeft,
                        normalizedRight
                    }
                );
            }

            for (
                let index = 0;
                index < normalizedLeft.arguments.length;
                index++
            ) {
                const leftArgument = normalizedLeft.arguments[index];
                const rightArgument = normalizedRight.arguments[index];
                const argumentPath = childPath(
                    path,
                    `call:argument:${index}`
                );
                if (leftArgument.plicity !== rightArgument.plicity) {
                    return comparisonMismatch(
                        'PLICITY_MISMATCH',
                        argumentPath,
                        leftArgument.value,
                        rightArgument.value,
                        {
                            expectedPlicity: leftArgument.plicity,
                            actualPlicity: rightArgument.plicity
                        }
                    );
                }
                const outcome = compareCoreLfAt(
                    leftArgument.value,
                    rightArgument.value,
                    argumentPath,
                    state
                );
                if (outcome.status === 'step-limit-exceeded') {
                    return outcome;
                }
                normalizedLeft = replaceArgument(
                    normalizedLeft,
                    index,
                    outcome.normalizedLeft
                );
                normalizedRight = replaceArgument(
                    normalizedRight,
                    index,
                    outcome.normalizedRight
                );
                if (outcome.status === 'not-equal') {
                    if (
                        !kernelExpressionEquals(normalizedLeft, left) ||
                        !kernelExpressionEquals(normalizedRight, other)
                    ) {
                        return compareCoreLfAt(
                            normalizedLeft,
                            normalizedRight,
                            path,
                            state
                        );
                    }
                    return retryCoreLfComparisonAfterDescendants(
                        normalizedLeft,
                        normalizedRight,
                        path,
                        state,
                        {
                            ...outcome,
                            normalizedLeft,
                            normalizedRight
                        }
                    );
                }
            }
            return comparisonEqual(
                normalizedLeft,
                normalizedRight
            );
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
                return comparisonMismatch(
                    'BINDER_MODE_MISMATCH',
                    childPath(path, `${left.tag}:binder-mode`),
                    left,
                    other
                );
            }
            let normalizedLeft = left;
            let normalizedRight = other;
            const binderType = compareCoreLfAt(
                left.binder.type,
                other.binder.type,
                childPath(path, `${left.tag}:binder-type`),
                state
            );
            if (binderType.status === 'step-limit-exceeded') {
                return binderType;
            }
            normalizedLeft = replaceBinderType(
                normalizedLeft,
                binderType.normalizedLeft
            );
            normalizedRight = replaceBinderType(
                normalizedRight,
                binderType.normalizedRight
            );
            if (binderType.status === 'not-equal') {
                if (
                    !kernelExpressionEquals(normalizedLeft, left) ||
                    !kernelExpressionEquals(normalizedRight, other)
                ) {
                    return compareCoreLfAt(
                        normalizedLeft,
                        normalizedRight,
                        path,
                        state
                    );
                }
                return retryCoreLfComparisonAfterDescendants(
                    normalizedLeft,
                    normalizedRight,
                    path,
                    state,
                    {
                        ...binderType,
                        normalizedLeft,
                        normalizedRight
                    }
                );
            }
            const body = compareCoreLfAt(
                normalizedLeft.body,
                normalizedRight.body,
                childPath(path, `${left.tag}:body`),
                state
            );
            if (body.status === 'step-limit-exceeded') return body;
            normalizedLeft = replaceBinderBody(
                normalizedLeft,
                body.normalizedLeft
            );
            normalizedRight = replaceBinderBody(
                normalizedRight,
                body.normalizedRight
            );
            if (body.status === 'not-equal') {
                if (
                    !kernelExpressionEquals(normalizedLeft, left) ||
                    !kernelExpressionEquals(normalizedRight, other)
                ) {
                    return compareCoreLfAt(
                        normalizedLeft,
                        normalizedRight,
                        path,
                        state
                    );
                }
                return retryCoreLfComparisonAfterDescendants(
                    normalizedLeft,
                    normalizedRight,
                    path,
                    state,
                    {
                        ...body,
                        normalizedLeft,
                        normalizedRight
                    }
                );
            }
            return comparisonEqual(
                normalizedLeft,
                normalizedRight
            );
        }
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
};

const freezeComparisonTrace = (
    trace: readonly CoreLfComparisonTraceEntry[]
): readonly CoreLfComparisonTraceEntry[] => Object.freeze(
    trace.map(entry => Object.freeze({
        ...entry,
        path: freezePath(entry.path)
    }))
);

/**
 * Decide candidate definitional equality with one global operation budget
 * across both sides and all recursively compared children.
 */
export function coreLfDefinitionalCompare(
    environment: CoreLfDeclarationEnvironment,
    left: KernelExpression,
    right: KernelExpression,
    stepLimit: number,
    session?: CoreElaborationSession,
    catalogRuntime?: CoreLfCatalogRuntime
): CoreLfComparisonResult {
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new CoreLfEvaluationError(
            'INVALID_STEP_LIMIT',
            left.provenance,
            `Combined Core LF comparison step limit must be a nonnegative ` +
            `safe integer; received ${stepLimit}`
        );
    }
    assertCompatibleSession(environment, session);

    const state: MutableCoreLfComparisonState = {
        environment,
        session,
        catalogRuntime,
        stepLimit,
        trace: []
    };
    const outcome = compareCoreLfAt(left, right, ['$'], state);
    const base = {
        steps: state.trace.length,
        trace: freezeComparisonTrace(state.trace)
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
                normalizedLeft: outcome.normalizedLeft,
                normalizedRight: outcome.normalizedRight,
                mismatch: outcome.mismatch
            });
        case 'step-limit-exceeded':
            return Object.freeze({
                status: 'step-limit-exceeded',
                ...base,
                side: outcome.side,
                path: freezePath(outcome.path),
                expression: outcome.expression,
                next: outcome.next
            });
        default: {
            const exhaustive: never = outcome;
            return exhaustive;
        }
    }
}
