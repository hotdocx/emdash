/**
 * Deterministic backend-neutral serialization of explicit emdash Core.
 *
 * This format is an inspection/conformance artifact, not a parser contract.
 * It deliberately omits source provenance and binder display hints, retains
 * semantic owner identities and plicities, and assigns encounter-order names
 * to contextual metavariable sessions. Consequently equal locally nameless
 * terms serialize identically even when their source spans or binder hints
 * differ.
 */

import {
    KernelArgument,
    KernelExpression,
    kernelAssertScoped
} from './kernel';

export const CORE_EXPLICIT_SERIALIZATION_REVISION =
    'EMDASH-CORE-SEXP-1' as const;

export interface CoreExplicitSerializationOptions {
    /**
     * Optional presentation labels for free Core declarations.
     *
     * The keys are Core declaration identities. Labels affect only this
     * inspection format; they never rewrite the expression or select a
     * backend symbol.
     */
    readonly freeReferenceLabels?: Readonly<Record<string, string>>;
}

interface CoreSerializationState {
    readonly freeReferenceLabels: ReadonlyMap<string, string>;
    readonly metaSessions: Map<symbol, number>;
}

const quoted = (value: string): string => JSON.stringify(value);

const serializeArguments = (
    arguments_: readonly KernelArgument[],
    state: CoreSerializationState
): string => arguments_.map(argument =>
    `(${argument.plicity} ${serializeExpression(argument.value, state)})`
).join(' ');

const serializeExpression = (
    expression: KernelExpression,
    state: CoreSerializationState
): string => {
    switch (expression.tag) {
        case 'universe':
            return '(universe)';
        case 'reference':
            return `(free ${quoted(
                state.freeReferenceLabels.get(expression.name) ??
                    expression.name
            )})`;
        case 'bound':
            return `(bound ${expression.index})`;
        case 'meta': {
            let session = state.metaSessions.get(
                expression.identity.session
            );
            if (session === undefined) {
                session = state.metaSessions.size;
                state.metaSessions.set(
                    expression.identity.session,
                    session
                );
            }
            const spine = expression.spine.map(argument =>
                serializeExpression(argument, state)
            ).join(' ');
            return spine.length === 0
                ? `(meta ${session} ${expression.identity.index})`
                : `(meta ${session} ${expression.identity.index} ` +
                    `(spine ${spine}))`;
        }
        case 'application': {
            const arguments_ = serializeArguments(
                expression.arguments,
                state
            );
            return arguments_.length === 0
                ? `(owner ${quoted(expression.owner)})`
                : `(owner ${quoted(expression.owner)} ${arguments_})`;
        }
        case 'call': {
            const callee = serializeExpression(
                expression.callee,
                state
            );
            const arguments_ = serializeArguments(
                expression.arguments,
                state
            );
            return `(call ${callee} ${arguments_})`;
        }
        case 'pi':
        case 'lambda': {
            const head = expression.tag;
            const type = serializeExpression(
                expression.binder.type,
                state
            );
            const body = serializeExpression(
                expression.body,
                state
            );
            return `(${head} ` +
                `(binder ${expression.binder.mode.plicity} ` +
                `${expression.binder.mode.variation} ${type}) ${body})`;
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

/**
 * Produce the canonical one-line `EMDASH-CORE-SEXP-1` inspection form.
 */
export function serializeCoreExpression(
    expression: KernelExpression,
    options: CoreExplicitSerializationOptions = {}
): string {
    kernelAssertScoped(expression);
    const labels = new Map<string, string>();
    for (const [name, label] of Object.entries(
        options.freeReferenceLabels ?? {}
    )) {
        if (name.length === 0 || label.length === 0) {
            throw new Error(
                'Explicit Core free-reference labels must be nonempty'
            );
        }
        labels.set(name, label);
    }
    return serializeExpression(expression, {
        freeReferenceLabels: labels,
        metaSessions: new Map()
    });
}
