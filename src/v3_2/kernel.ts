/**
 * Minimal backend-neutral explicit emdash Core IR.
 *
 * This module deliberately does not import the legacy root `Term` union or a
 * backend symbol catalog. Applications reference semantic owner schemas and
 * record every slot plus source provenance without claiming to typecheck the
 * full active kernel.
 */

import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export { CoreOwnerId, Plicity } from './schema';

export type VariationMode = 'functorial' | 'natural' | 'object-only';

export interface BinderMode {
    plicity: Plicity;
    variation: VariationMode;
}

export const binderMode = (
    plicity: Plicity,
    variation: VariationMode
): BinderMode => ({ plicity, variation });

export interface SourcePosition {
    line: number;
    column: number;
}

export interface SourceSpan {
    file: string;
    start: SourcePosition;
    end: SourcePosition;
}

export const sourceSpan = (
    file: string,
    startLine: number,
    startColumn: number,
    endLine: number = startLine,
    endColumn: number = startColumn
): SourceSpan => ({
    file,
    start: { line: startLine, column: startColumn },
    end: { line: endLine, column: endColumn }
});

export type ProvenanceOrigin = 'surface' | 'recovered' | 'derived';

export interface Provenance {
    origin: ProvenanceOrigin;
    span?: SourceSpan;
    detail: string;
}

export const provenance = (
    origin: ProvenanceOrigin,
    detail: string,
    span?: SourceSpan
): Provenance => ({ origin, detail, span });

export interface KernelReference {
    tag: 'reference';
    namespace: 'free';
    name: string;
    provenance: Provenance;
}

export interface KernelBoundVariable {
    tag: 'bound';
    /**
     * De Bruijn index: zero names the nearest enclosing Pi/lambda binder.
     */
    index: number;
    provenance: Provenance;
}

export interface KernelArgument {
    plicity: Plicity;
    value: KernelExpression;
    provenance: Provenance;
}

export interface KernelApplication {
    tag: 'application';
    owner: CoreOwnerId;
    arguments: readonly KernelArgument[];
    provenance: Provenance;
}

export interface KernelBinder {
    /**
     * A diagnostic/display hint only. Bound occurrences use De Bruijn indices.
     */
    name: string;
    type: KernelExpression;
    mode: BinderMode;
    provenance: Provenance;
}

export interface KernelPi {
    tag: 'pi';
    binder: KernelBinder;
    body: KernelExpression;
    provenance: Provenance;
}

export interface KernelLambda {
    tag: 'lambda';
    binder: KernelBinder;
    body: KernelExpression;
    provenance: Provenance;
}

export type KernelExpression =
    | KernelReference
    | KernelBoundVariable
    | KernelApplication
    | KernelPi
    | KernelLambda;

const SAFE_IDENTIFIER = /^[A-Za-z][A-Za-z0-9_]*$/;

export function assertSafeIdentifier(name: string, role: string): void {
    if (!SAFE_IDENTIFIER.test(name)) {
        throw new Error(
            `${role} '${name}' is not a portable emdash Core identifier`
        );
    }
}

export const kernelFree = (
    name: string,
    nodeProvenance: Provenance
): KernelReference => {
    assertSafeIdentifier(name, 'Free declaration name');
    return {
        tag: 'reference',
        namespace: 'free',
        name,
        provenance: nodeProvenance
    };
};

export type KernelScopeErrorCode =
    | 'INVALID_BOUND_INDEX'
    | 'INVALID_SHIFT'
    | 'BOUND_INDEX_ESCAPE'
    | 'DANGLING_BOUND_VARIABLE';

export class KernelScopeError extends Error {
    constructor(
        public readonly code: KernelScopeErrorCode,
        public readonly provenance: Provenance,
        message: string
    ) {
        super(message);
        this.name = 'KernelScopeError';
    }
}

const isNonnegativeInteger = (value: number): boolean =>
    Number.isSafeInteger(value) && value >= 0;

export const kernelBound = (
    index: number,
    nodeProvenance: Provenance
): KernelBoundVariable => {
    if (!isNonnegativeInteger(index)) {
        throw new KernelScopeError(
            'INVALID_BOUND_INDEX',
            nodeProvenance,
            `Core bound-variable index must be a nonnegative safe integer; ` +
            `received ${index}`
        );
    }
    return {
        tag: 'bound',
        index,
        provenance: nodeProvenance
    };
};

export const kernelBinder = (
    name: string,
    type: KernelExpression,
    mode: BinderMode,
    nodeProvenance: Provenance
): KernelBinder => ({
    name,
    type,
    mode,
    provenance: nodeProvenance
});

export interface KernelArgumentInput {
    value: KernelExpression;
    provenance?: Provenance;
}

export function kernelApplication(
    owner: CoreOwnerId,
    inputs: readonly KernelArgumentInput[],
    nodeProvenance: Provenance
): KernelApplication {
    const schema = CORE_OWNER_SCHEMAS[owner];
    if (inputs.length !== schema.slots.length) {
        throw new Error(
            `Core owner ${owner} expects ${schema.slots.length} arguments, ` +
            `received ${inputs.length}`
        );
    }

    return {
        tag: 'application',
        owner,
        arguments: inputs.map((input, index) => ({
            plicity: schema.slots[index].plicity,
            value: input.value,
            provenance: input.provenance ?? input.value.provenance
        })),
        provenance: nodeProvenance
    };
}

export const kernelPi = (
    binder: KernelBinder,
    body: KernelExpression,
    nodeProvenance: Provenance
): KernelPi => ({
    tag: 'pi',
    binder,
    body,
    provenance: nodeProvenance
});

export const kernelLambda = (
    binder: KernelBinder,
    body: KernelExpression,
    nodeProvenance: Provenance
): KernelLambda => ({
    tag: 'lambda',
    binder,
    body,
    provenance: nodeProvenance
});

function shiftAt(
    expression: KernelExpression,
    amount: number,
    cutoff: number
): KernelExpression {
    switch (expression.tag) {
        case 'reference':
            return expression;
        case 'bound': {
            if (expression.index < cutoff) return expression;
            const shifted = expression.index + amount;
            if (!Number.isSafeInteger(shifted)) {
                throw new KernelScopeError(
                    'INVALID_SHIFT',
                    expression.provenance,
                    `Shifting Core bound-variable index ${expression.index} ` +
                    `by ${amount} exceeds the safe integer range`
                );
            }
            if (shifted < 0) {
                throw new KernelScopeError(
                    'BOUND_INDEX_ESCAPE',
                    expression.provenance,
                    `Shifting Core bound-variable index ${expression.index} ` +
                    `by ${amount} below cutoff ${cutoff} would escape scope`
                );
            }
            return shifted === expression.index
                ? expression
                : { ...expression, index: shifted };
        }
        case 'application':
            return {
                ...expression,
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: shiftAt(argument.value, amount, cutoff)
                }))
            };
        case 'pi':
        case 'lambda':
            return {
                ...expression,
                binder: {
                    ...expression.binder,
                    type: shiftAt(expression.binder.type, amount, cutoff)
                },
                body: shiftAt(expression.body, amount, cutoff + 1)
            };
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

/**
 * Shift every bound index at or above `cutoff`.
 *
 * A negative shift that would move an occurrence below zero is rejected
 * instead of manufacturing a dangling variable.
 */
export function kernelShift(
    expression: KernelExpression,
    amount: number,
    cutoff = 0
): KernelExpression {
    if (!Number.isSafeInteger(amount) || !isNonnegativeInteger(cutoff)) {
        throw new KernelScopeError(
            'INVALID_SHIFT',
            expression.provenance,
            `Core shift requires an integer amount and nonnegative cutoff; ` +
            `received amount ${amount}, cutoff ${cutoff}`
        );
    }
    return shiftAt(expression, amount, cutoff);
}

function substituteAt(
    expression: KernelExpression,
    targetIndex: number,
    replacement: KernelExpression,
    depth: number
): KernelExpression {
    switch (expression.tag) {
        case 'reference':
            return expression;
        case 'bound':
            return expression.index === targetIndex + depth
                ? shiftAt(replacement, depth, 0)
                : expression;
        case 'application':
            return {
                ...expression,
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: substituteAt(
                        argument.value,
                        targetIndex,
                        replacement,
                        depth
                    )
                }))
            };
        case 'pi':
        case 'lambda':
            return {
                ...expression,
                binder: {
                    ...expression.binder,
                    type: substituteAt(
                        expression.binder.type,
                        targetIndex,
                        replacement,
                        depth
                    )
                },
                body: substituteAt(
                    expression.body,
                    targetIndex,
                    replacement,
                    depth + 1
                )
            };
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

/**
 * Capture-safely replace an open De Bruijn index without removing its binder.
 */
export function kernelSubstitute(
    expression: KernelExpression,
    targetIndex: number,
    replacement: KernelExpression
): KernelExpression {
    if (!isNonnegativeInteger(targetIndex)) {
        throw new KernelScopeError(
            'INVALID_BOUND_INDEX',
            expression.provenance,
            `Core substitution index must be a nonnegative safe integer; ` +
            `received ${targetIndex}`
        );
    }
    return substituteAt(expression, targetIndex, replacement, 0);
}

/**
 * Instantiate the nearest binder in an open body and remove that binder.
 */
export function kernelInstantiate(
    body: KernelExpression,
    replacement: KernelExpression
): KernelExpression {
    const liftedReplacement = kernelShift(replacement, 1);
    const substituted = kernelSubstitute(body, 0, liftedReplacement);
    return kernelShift(substituted, -1);
}

/**
 * Reject any bound occurrence that has no binder in the supplied ambient
 * depth. Backends use depth zero so malformed open terms cannot be emitted.
 */
export function kernelAssertScoped(
    expression: KernelExpression,
    ambientDepth = 0
): void {
    if (!isNonnegativeInteger(ambientDepth)) {
        throw new KernelScopeError(
            'INVALID_BOUND_INDEX',
            expression.provenance,
            `Core ambient depth must be a nonnegative safe integer; ` +
            `received ${ambientDepth}`
        );
    }

    const visit = (current: KernelExpression, depth: number): void => {
        switch (current.tag) {
            case 'reference':
                return;
            case 'bound':
                if (current.index >= depth) {
                    throw new KernelScopeError(
                        'DANGLING_BOUND_VARIABLE',
                        current.provenance,
                        `Core bound-variable index ${current.index} is ` +
                        `dangling at binder depth ${depth}`
                    );
                }
                return;
            case 'application':
                current.arguments.forEach(argument =>
                    visit(argument.value, depth)
                );
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type, depth);
                visit(current.body, depth + 1);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };

    visit(expression, ambientDepth);
}

export function kernelExpressionEquals(
    left: KernelExpression,
    right: KernelExpression
): boolean {
    if (left.tag !== right.tag) return false;

    switch (left.tag) {
        case 'reference': {
            const other = right as KernelReference;
            return left.namespace === other.namespace && left.name === other.name;
        }
        case 'bound': {
            const other = right as KernelBoundVariable;
            return left.index === other.index;
        }
        case 'application': {
            const other = right as KernelApplication;
            return left.owner === other.owner &&
                left.arguments.length === other.arguments.length &&
                left.arguments.every((argument, index) =>
                    argument.plicity === other.arguments[index].plicity &&
                    kernelExpressionEquals(
                        argument.value,
                        other.arguments[index].value
                    )
                );
        }
        case 'pi':
        case 'lambda': {
            const other = right as KernelPi | KernelLambda;
            return left.binder.mode.plicity === other.binder.mode.plicity &&
                left.binder.mode.variation === other.binder.mode.variation &&
                kernelExpressionEquals(left.binder.type, other.binder.type) &&
                kernelExpressionEquals(left.body, other.body);
        }
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
}

export function formatSourceSpan(span: SourceSpan): string {
    return `${span.file}:${span.start.line}:${span.start.column}`;
}
