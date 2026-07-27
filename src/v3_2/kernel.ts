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

export type { CoreOwnerId, Plicity } from './schema';

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

/**
 * The backend-neutral meta-level universe. The current Lambdapi conformance
 * backend renders this as `TYPE`.
 */
export interface KernelUniverse {
    tag: 'universe';
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

/**
 * Session identity is intentionally opaque and process-local. The numeric
 * index is deterministic within that session; the symbol prevents accidental
 * cross-session equality without introducing a global counter.
 */
export interface KernelMetaIdentity {
    readonly session: symbol;
    readonly index: number;
}

/**
 * A contextual metavariable occurrence `?m[spine]`.
 *
 * `spine[i]` is the current-scope image of De Bruijn index `i` from the
 * metavariable's creation scope. Solving state lives in the owning session,
 * never in this Core node.
 */
export interface KernelMetaVariable {
    tag: 'meta';
    identity: KernelMetaIdentity;
    spine: readonly KernelExpression[];
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

/**
 * Generic dependent function application.
 *
 * Semantic-owner applications remain separate `application` nodes so their
 * owner identity and fixed telescope stay explicit. A `call` applies an
 * arbitrary Core expression and is the Pi-elimination form used by the
 * checker.
 */
export interface KernelCall {
    tag: 'call';
    callee: KernelExpression;
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
    | KernelUniverse
    | KernelReference
    | KernelBoundVariable
    | KernelMetaVariable
    | KernelApplication
    | KernelCall
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

export const kernelUniverse = (
    nodeProvenance: Provenance
): KernelUniverse => ({
    tag: 'universe',
    provenance: nodeProvenance
});

export type KernelScopeErrorCode =
    | 'INVALID_BOUND_INDEX'
    | 'INVALID_SHIFT'
    | 'INVALID_AMBIENT_INDEX_MAP'
    | 'BOUND_INDEX_ESCAPE'
    | 'DANGLING_BOUND_VARIABLE'
    | 'DROPPED_BOUND_VARIABLE';

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

export const kernelMeta = (
    identity: KernelMetaIdentity,
    spine: readonly KernelExpression[],
    nodeProvenance: Provenance
): KernelMetaVariable => {
    if (!isNonnegativeInteger(identity.index)) {
        throw new KernelScopeError(
            'INVALID_BOUND_INDEX',
            nodeProvenance,
            `Core metavariable index must be a nonnegative safe integer; ` +
            `received ${identity.index}`
        );
    }
    return {
        tag: 'meta',
        identity,
        spine: Object.freeze([...spine]),
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

export interface KernelCallArgumentInput extends KernelArgumentInput {
    plicity: Plicity;
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

export function kernelCall(
    callee: KernelExpression,
    inputs: readonly KernelCallArgumentInput[],
    nodeProvenance: Provenance
): KernelCall {
    if (inputs.length === 0) {
        throw new Error('Core generic call requires at least one argument');
    }
    return {
        tag: 'call',
        callee,
        arguments: Object.freeze(inputs.map(input => Object.freeze({
            plicity: input.plicity,
            value: input.value,
            provenance: input.provenance ?? input.value.provenance
        }))),
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
        case 'universe':
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
        case 'meta':
            return {
                ...expression,
                spine: expression.spine.map(item =>
                    shiftAt(item, amount, cutoff)
                )
            };
        case 'application':
            return {
                ...expression,
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: shiftAt(argument.value, amount, cutoff)
                }))
            };
        case 'call':
            return {
                ...expression,
                callee: shiftAt(expression.callee, amount, cutoff),
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

export type KernelAmbientIndexImage = number | null;

function remapAmbientIndicesAt(
    expression: KernelExpression,
    indexMap: readonly KernelAmbientIndexImage[],
    internalDepth: number
): KernelExpression {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
            return expression;
        case 'bound': {
            if (expression.index < internalDepth) return expression;

            const sourceIndex = expression.index - internalDepth;
            const targetIndex = indexMap[sourceIndex];
            if (targetIndex === null) {
                throw new KernelScopeError(
                    'DROPPED_BOUND_VARIABLE',
                    expression.provenance,
                    `Core ambient bound-variable index ${sourceIndex} is ` +
                    'used but its index map marks it as unavailable'
                );
            }
            if (targetIndex === undefined) {
                throw new KernelScopeError(
                    'INVALID_AMBIENT_INDEX_MAP',
                    expression.provenance,
                    `Core ambient bound-variable index ${sourceIndex} has ` +
                    `no image in an index map of length ${indexMap.length}`
                );
            }

            const mappedIndex = targetIndex + internalDepth;
            if (!Number.isSafeInteger(mappedIndex)) {
                throw new KernelScopeError(
                    'INVALID_AMBIENT_INDEX_MAP',
                    expression.provenance,
                    `Mapping Core ambient bound-variable index ` +
                    `${sourceIndex} beneath ${internalDepth} internal ` +
                    'binders exceeds the safe integer range'
                );
            }
            return mappedIndex === expression.index
                ? expression
                : { ...expression, index: mappedIndex };
        }
        case 'meta':
            return {
                ...expression,
                spine: expression.spine.map(item =>
                    remapAmbientIndicesAt(item, indexMap, internalDepth)
                )
            };
        case 'application':
            return {
                ...expression,
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: remapAmbientIndicesAt(
                        argument.value,
                        indexMap,
                        internalDepth
                    )
                }))
            };
        case 'call':
            return {
                ...expression,
                callee: remapAmbientIndicesAt(
                    expression.callee,
                    indexMap,
                    internalDepth
                ),
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: remapAmbientIndicesAt(
                        argument.value,
                        indexMap,
                        internalDepth
                    )
                }))
            };
        case 'pi':
        case 'lambda':
            return {
                ...expression,
                binder: {
                    ...expression.binder,
                    type: remapAmbientIndicesAt(
                        expression.binder.type,
                        indexMap,
                        internalDepth
                    )
                },
                body: remapAmbientIndicesAt(
                    expression.body,
                    indexMap,
                    internalDepth + 1
                )
            };
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

/**
 * Apply a scope-level map to an expression's ambient De Bruijn indices.
 *
 * `indexMap[i]` is the target-scope image of source ambient index `i`.
 * Repeated images express contraction; permutations express exchange; and a
 * larger target depth expresses weakening. A `null` image is allowed only
 * when that source variable is unused. Unlike term substitution, this
 * operation preserves each occurrence's provenance.
 *
 * This is a meta-level Core operation. It does not construct an internal
 * categorical reindexing owner such as a displayed pullback.
 */
export function kernelRemapAmbientIndices(
    expression: KernelExpression,
    targetDepth: number,
    indexMap: readonly KernelAmbientIndexImage[]
): KernelExpression {
    if (!isNonnegativeInteger(targetDepth)) {
        throw new KernelScopeError(
            'INVALID_AMBIENT_INDEX_MAP',
            expression.provenance,
            `Core ambient index map requires a nonnegative target depth; ` +
            `received ${targetDepth}`
        );
    }

    for (let sourceIndex = 0; sourceIndex < indexMap.length; sourceIndex++) {
        const targetIndex = indexMap[sourceIndex];
        if (targetIndex === null) continue;
        if (
            !isNonnegativeInteger(targetIndex) ||
            targetIndex >= targetDepth
        ) {
            throw new KernelScopeError(
                'INVALID_AMBIENT_INDEX_MAP',
                expression.provenance,
                `Core ambient index map image for source index ` +
                `${sourceIndex} must be null or an index below target ` +
                `depth ${targetDepth}; received ${String(targetIndex)}`
            );
        }
    }

    kernelAssertScoped(expression, indexMap.length);
    const result = remapAmbientIndicesAt(expression, indexMap, 0);
    kernelAssertScoped(result, targetDepth);
    return result;
}

function substituteAt(
    expression: KernelExpression,
    targetIndex: number,
    replacement: KernelExpression,
    depth: number
): KernelExpression {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
            return expression;
        case 'bound':
            return expression.index === targetIndex + depth
                ? shiftAt(replacement, depth, 0)
                : expression;
        case 'meta':
            return {
                ...expression,
                spine: expression.spine.map(item =>
                    substituteAt(
                        item,
                        targetIndex,
                        replacement,
                        depth
                    )
                )
            };
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
        case 'call':
            return {
                ...expression,
                callee: substituteAt(
                    expression.callee,
                    targetIndex,
                    replacement,
                    depth
                ),
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

function instantiateSpineAt(
    expression: KernelExpression,
    spine: readonly KernelExpression[],
    depth: number
): KernelExpression {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
            return expression;
        case 'bound': {
            if (expression.index < depth) return expression;
            const sourceIndex = expression.index - depth;
            const replacement = spine[sourceIndex];
            if (!replacement) {
                throw new KernelScopeError(
                    'DANGLING_BOUND_VARIABLE',
                    expression.provenance,
                    `Core ambient bound-variable index ${sourceIndex} has ` +
                    `no image in a substitution spine of length ` +
                    `${spine.length}`
                );
            }
            return shiftAt(replacement, depth, 0);
        }
        case 'meta':
            return {
                ...expression,
                spine: expression.spine.map(item =>
                    instantiateSpineAt(item, spine, depth)
                )
            };
        case 'application':
            return {
                ...expression,
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: instantiateSpineAt(
                        argument.value,
                        spine,
                        depth
                    )
                }))
            };
        case 'call':
            return {
                ...expression,
                callee: instantiateSpineAt(
                    expression.callee,
                    spine,
                    depth
                ),
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: instantiateSpineAt(
                        argument.value,
                        spine,
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
                    type: instantiateSpineAt(
                        expression.binder.type,
                        spine,
                        depth
                    )
                },
                body: instantiateSpineAt(
                    expression.body,
                    spine,
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
 * Apply a simultaneous substitution for an expression's ambient scope.
 *
 * The source expression is checked at ambient depth `spine.length`.
 * Replacements are simultaneous and are shifted only when crossing binders
 * internal to the source expression.
 */
export function kernelInstantiateSpine(
    expression: KernelExpression,
    spine: readonly KernelExpression[]
): KernelExpression {
    kernelAssertScoped(expression, spine.length);
    return instantiateSpineAt(expression, spine, 0);
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
            case 'universe':
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
            case 'meta':
                current.spine.forEach(item => visit(item, depth));
                return;
            case 'application':
                current.arguments.forEach(argument =>
                    visit(argument.value, depth)
                );
                return;
            case 'call':
                visit(current.callee, depth);
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

/**
 * One ambient De Bruijn dependency together with every stored occurrence.
 *
 * `index` is nearest-first in the ambient scope supplied to
 * `kernelAmbientDependencies`. Occurrences bound by Pi/lambda nodes inside
 * the inspected expression are excluded.
 */
export interface KernelAmbientDependency {
    readonly index: number;
    readonly occurrences: readonly Provenance[];
}

/**
 * Inspect the ambient variables used by a scoped expression.
 *
 * This is dependency evidence for contextual planning. It does not rewrite
 * the expression, infer semantic dependencies absent from Core, or construct
 * a categorical weakening/pullback owner.
 */
export function kernelAmbientDependencies(
    expression: KernelExpression,
    ambientDepth: number
): readonly KernelAmbientDependency[] {
    kernelAssertScoped(expression, ambientDepth);
    const occurrences = new Map<number, Provenance[]>();

    const visit = (
        current: KernelExpression,
        internalDepth: number
    ): void => {
        switch (current.tag) {
            case 'universe':
            case 'reference':
                return;
            case 'bound': {
                if (current.index < internalDepth) return;
                const ambientIndex = current.index - internalDepth;
                const existing = occurrences.get(ambientIndex);
                if (existing) {
                    existing.push(current.provenance);
                } else {
                    occurrences.set(
                        ambientIndex,
                        [current.provenance]
                    );
                }
                return;
            }
            case 'meta':
                current.spine.forEach(item =>
                    visit(item, internalDepth)
                );
                return;
            case 'application':
                current.arguments.forEach(argument =>
                    visit(argument.value, internalDepth)
                );
                return;
            case 'call':
                visit(current.callee, internalDepth);
                current.arguments.forEach(argument =>
                    visit(argument.value, internalDepth)
                );
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type, internalDepth);
                visit(current.body, internalDepth + 1);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };

    visit(expression, 0);
    return Object.freeze(
        [...occurrences.entries()]
            .sort(([left], [right]) => left - right)
            .map(([index, dependencyOccurrences]) =>
                Object.freeze({
                    index,
                    occurrences: Object.freeze([
                        ...dependencyOccurrences
                    ])
                })
            )
    );
}

export function kernelExpressionEquals(
    left: KernelExpression,
    right: KernelExpression
): boolean {
    if (left.tag !== right.tag) return false;

    switch (left.tag) {
        case 'universe':
            return true;
        case 'reference': {
            const other = right as KernelReference;
            return left.namespace === other.namespace && left.name === other.name;
        }
        case 'bound': {
            const other = right as KernelBoundVariable;
            return left.index === other.index;
        }
        case 'meta': {
            const other = right as KernelMetaVariable;
            return left.identity.session === other.identity.session &&
                left.identity.index === other.identity.index &&
                left.spine.length === other.spine.length &&
                left.spine.every((item, index) =>
                    kernelExpressionEquals(item, other.spine[index])
                );
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
        case 'call': {
            const other = right as KernelCall;
            return kernelExpressionEquals(left.callee, other.callee) &&
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
