/**
 * Generic typed runtime-rule compiler and matcher for SCALE-0D.
 *
 * Rules arrive through CoreLfModuleSpec and a separate policy overlay.
 * Qualified symbols resolve through an already compiled declaration context;
 * no semantic owner name or mutable registration table appears here.
 */

import {
    isCoreKind
} from './checker';
import {
    CoreLfChecker,
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfCatalogRuntime
} from './lf_conversion';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferRuntimeRule
} from './lf_transfer';
import {
    CoreLfCompiledDeclaration
} from './lf_transfer_compiler';
import {
    CoreRuntimeHeadRewriteResult,
    CoreRuntimeMatch,
    CoreRuntimeWeakHeadResult,
    CoreRuntimeWeakHeadTraceEntry
} from './evaluator';
import {
    BinderMode,
    KernelExpression,
    Provenance,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelRemapAmbientIndices,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export interface CoreLfRuntimeDeclarationContext {
    readonly environment: CoreLfDeclarationEnvironment;
    declaration(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledDeclaration | undefined;
}

export type CoreLfCompiledRuntimeExpression =
    | {
        readonly tag: 'universe';
    }
    | {
        readonly tag: 'bound';
        readonly index: number;
    }
    | {
        readonly tag: 'reference';
        readonly name: string;
    }
    | {
        readonly tag: 'application';
        readonly owner: CoreOwnerId;
        readonly arguments:
            readonly CoreLfCompiledRuntimeArgument[];
    }
    | {
        readonly tag: 'call';
        readonly callee: CoreLfCompiledRuntimeExpression;
        readonly arguments:
            readonly CoreLfCompiledRuntimeArgument[];
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly binder: {
            readonly hint: string;
            readonly mode: BinderMode;
            readonly type: CoreLfCompiledRuntimeExpression;
        };
        readonly body: CoreLfCompiledRuntimeExpression;
    }
    | {
        readonly tag: 'capture';
        readonly slot: number;
        readonly name: string;
        readonly allowedBoundIndices?: readonly number[];
    }
    | {
        readonly tag: 'wildcard';
    };

export interface CoreLfCompiledRuntimeArgument {
    readonly plicity: Plicity;
    readonly value: CoreLfCompiledRuntimeExpression;
}

export interface CoreLfCompiledRuntimeVariable {
    readonly slot: number;
    readonly name: string;
    readonly type: CoreLfCompiledRuntimeExpression;
}

export type CoreLfRuntimeSubjectValidation =
    | {
        readonly kind: 'typescript-checked';
    }
    | {
        readonly kind: 'external-oracle-required';
        readonly authorityPath: string;
        readonly evidence: string;
        readonly diagnostic: string;
    };

export interface CoreLfCompiledRuntimeRule {
    readonly order: number;
    readonly id: string;
    readonly groupId: string;
    readonly clauseOrder: number;
    readonly sourceOwner: CoreLfQualifiedSymbol;
    readonly variables: readonly CoreLfCompiledRuntimeVariable[];
    readonly left: CoreLfCompiledRuntimeExpression;
    readonly right: CoreLfCompiledRuntimeExpression;
    readonly checkedWithEarlierRuleIds: readonly string[];
    readonly subjectValidation: CoreLfRuntimeSubjectValidation;
    readonly provenance: Provenance;
}

export interface CoreLfRuntimeSubjectReductionOracle {
    readonly authorityPath: string;
    readonly ruleIds: readonly string[];
    readonly evidence: string;
}

export interface CoreLfRuntimeCompilerOptions {
    readonly comparisonStepLimit?: number;
    /**
     * Exact, fail-closed exception for a reviewed rule whose standalone
     * TypeScript subject reduction remains explicitly unclaimed. The
     * compiler still checks its typed variable telescope and all structural
     * runtime invariants. Every listed rule must fail only the final
     * TypeScript subject check; stale or unused exceptions are rejected.
     */
    readonly subjectReductionOracle?:
        CoreLfRuntimeSubjectReductionOracle;
}

export type CoreLfRuntimeFragmentDependencyRelation =
    | 'dependency-module'
    | 'earlier-fragment';

export type CoreLfRuntimeCompilerErrorCode =
    | 'INVALID_RUNTIME_CONTEXT'
    | 'INCOMPLETE_RUNTIME_POLICY'
    | 'UNSUPPORTED_MODULE_CONTENT'
    | 'UNRESOLVED_RUNTIME_SYMBOL'
    | 'INVALID_RUNTIME_APPLICATION'
    | 'INVALID_RUNTIME_GROUP'
    | 'SOURCE_OWNER_MISMATCH'
    | 'UNKNOWN_RUNTIME_CAPTURE'
    | 'UNSUPPORTED_RUNTIME_PATTERN'
    | 'UNSUPPORTED_HIGHER_ORDER_PATTERN'
    | 'INVALID_RUNTIME_VARIABLE_TYPE'
    | 'INVALID_RUNTIME_RULE_TYPE'
    | 'INVALID_RUNTIME_SUBJECT_ORACLE'
    | 'INVALID_RUNTIME_DEPENDENCY'
    | 'DUPLICATE_RUNTIME_RULE_ID'
    | 'CYCLIC_RUNTIME_DEPENDENCY'
    | 'INCOMPLETE_RUNTIME_MATCH'
    | 'CAPTURE_SCOPE_ESCAPE'
    | 'INVALID_RUNTIME_STEP_LIMIT';

export class CoreLfRuntimeCompilerError extends Error {
    constructor(
        public readonly code: CoreLfRuntimeCompilerErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfRuntimeCompilerError';
    }
}

type RuntimeExpressionPurpose = 'variable-type' | 'pattern' | 'template';

interface RuntimeCompilationState {
    readonly context: CoreLfRuntimeDeclarationContext;
    readonly captures: ReadonlyMap<string, number>;
    readonly maximumCaptureSlot: number;
    readonly purpose: RuntimeExpressionPurpose;
}

interface CapturedRuntimeValue {
    readonly expression: KernelExpression;
    readonly sourceDepth: number;
}

interface InternalRuntimeMatch {
    readonly publicMatch: CoreRuntimeMatch;
    readonly captures: readonly CapturedRuntimeValue[];
    readonly ambientDepth: number;
}

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const fail = (
    code: CoreLfRuntimeCompilerErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfRuntimeCompilerError(
        code,
        path,
        message,
        underlying
    );
};

const errorText = (error: unknown): string =>
    error instanceof Error ? error.message : String(error);

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const derivedProvenance = (
    rule: Pick<CoreLfTransferRuntimeRule, 'id' | 'provenance'>,
    detail: string,
    source?: Provenance
): Provenance => deepFreeze(provenance(
    'recovered',
    `transfer runtime rule ${rule.id} ${detail} from ` +
        `${rule.provenance.authorityPath}: ` +
        rule.provenance.sourceFragment,
    source?.span
));

const leadingPiPlicities = (
    type: KernelExpression
): readonly Plicity[] => {
    const plicities: Plicity[] = [];
    let current = type;
    while (current.tag === 'pi') {
        plicities.push(current.binder.mode.plicity);
        current = current.body;
    }
    return plicities;
};

const declarationFor = (
    context: CoreLfRuntimeDeclarationContext,
    symbol: CoreLfQualifiedSymbol,
    path: string
): CoreLfCompiledDeclaration => {
    const declaration = context.declaration(symbol);
    if (
        declaration === undefined ||
        declaration.status === 'excluded'
    ) {
        return fail(
            'UNRESOLVED_RUNTIME_SYMBOL',
            path,
            `Runtime expression refers to unavailable declaration ` +
                `'${displaySymbol(symbol)}'`
        );
    }
    return declaration;
};

const compileGlobal = (
    symbol: CoreLfQualifiedSymbol,
    state: RuntimeCompilationState,
    path: string
): CoreLfCompiledRuntimeExpression => {
    const declaration = declarationFor(state.context, symbol, path);
    if (declaration.link.kind === 'free-declaration') {
        return deepFreeze({
            tag: 'reference',
            name: declaration.link.coreName
        });
    }
    const schema = CORE_OWNER_SCHEMAS[declaration.link.owner];
    if (schema.slots.length !== 0) {
        return fail(
            'INVALID_RUNTIME_APPLICATION',
            path,
            `Intrinsic owner '${declaration.link.owner}' requires ` +
                `${schema.slots.length} arguments`
        );
    }
    return deepFreeze({
        tag: 'application',
        owner: declaration.link.owner,
        arguments: []
    });
};

const compileRuntimeExpression = (
    expression: CoreLfTransferExpression,
    state: RuntimeCompilationState,
    path: string
): CoreLfCompiledRuntimeExpression => {
    const descend = (
        child: CoreLfTransferExpression,
        childPath: string,
        changes: Partial<RuntimeCompilationState> = {}
    ): CoreLfCompiledRuntimeExpression => compileRuntimeExpression(
        child,
        { ...state, ...changes },
        childPath
    );

    switch (expression.tag) {
        case 'type':
            return deepFreeze({ tag: 'universe' });
        case 'bound':
            return deepFreeze({
                tag: 'bound',
                index: expression.index
            });
        case 'global':
            return compileGlobal(expression.symbol, state, path);
        case 'capture': {
            const slot = state.captures.get(expression.name);
            if (
                slot === undefined ||
                slot > state.maximumCaptureSlot
            ) {
                return fail(
                    'UNKNOWN_RUNTIME_CAPTURE',
                    path,
                    `Runtime ${state.purpose} refers to unavailable capture ` +
                        `'${expression.name}'`
                );
            }
            if (
                expression.allowedBoundIndices !== undefined
            ) {
                return fail(
                    'UNSUPPORTED_HIGHER_ORDER_PATTERN',
                    path,
                    `Runtime ${state.purpose} capture '${expression.name}' ` +
                        'requires higher-order binder matching'
                );
            }
            return deepFreeze({
                tag: 'capture',
                slot,
                name: expression.name
            });
        }
        case 'wildcard':
            return fail(
                'UNSUPPORTED_RUNTIME_PATTERN',
                path,
                'Typed runtime compilation does not yet support wildcards'
            );
        case 'call': {
            if (expression.callee.tag === 'global') {
                const declaration = declarationFor(
                    state.context,
                    expression.callee.symbol,
                    `${path}.callee`
                );
                const arguments_ = expression.arguments.map(
                    (argument, index) => deepFreeze({
                        plicity: argument.plicity,
                        value: descend(
                            argument.value,
                            `${path}.arguments[${index}].value`
                        )
                    })
                );
                const link = declaration.link;
                if (link.kind === 'core-owner') {
                    const schema =
                        CORE_OWNER_SCHEMAS[link.owner];
                    if (arguments_.length !== schema.slots.length) {
                        return fail(
                            'INVALID_RUNTIME_APPLICATION',
                            path,
                            `Intrinsic owner '${link.owner}' ` +
                                `expects ${schema.slots.length} arguments, ` +
                                `received ${arguments_.length}`
                        );
                    }
                    arguments_.forEach((argument, index) => {
                        if (
                            argument.plicity !==
                            schema.slots[index].plicity
                        ) {
                            fail(
                                'INVALID_RUNTIME_APPLICATION',
                                `${path}.arguments[${index}].plicity`,
                                `Intrinsic owner ` +
                                    `'${link.owner}' argument ` +
                                    `${index} must be ` +
                                    schema.slots[index].plicity
                            );
                        }
                    });
                    return deepFreeze({
                        tag: 'application',
                        owner: link.owner,
                        arguments: arguments_
                    });
                }

                const plicities =
                    leadingPiPlicities(declaration.type);
                if (arguments_.length > plicities.length) {
                    return fail(
                        'INVALID_RUNTIME_APPLICATION',
                        path,
                        `Free declaration '${link.coreName}' ` +
                            `receives ${arguments_.length} arguments but its ` +
                            `signature exposes ${plicities.length}`
                    );
                }
                arguments_.forEach((argument, index) => {
                    if (argument.plicity !== plicities[index]) {
                        fail(
                            'INVALID_RUNTIME_APPLICATION',
                            `${path}.arguments[${index}].plicity`,
                            `Free declaration ` +
                                `'${link.coreName}' argument ` +
                                `${index} must be ${plicities[index]}`
                        );
                    }
                });
                return deepFreeze({
                    tag: 'call',
                    callee: {
                        tag: 'reference',
                        name: link.coreName
                    },
                    arguments: arguments_
                });
            }
            return deepFreeze({
                tag: 'call',
                callee: descend(
                    expression.callee,
                    `${path}.callee`
                ),
                arguments: expression.arguments.map(
                    (argument, index) => deepFreeze({
                        plicity: argument.plicity,
                        value: descend(
                            argument.value,
                            `${path}.arguments[${index}].value`
                        )
                    })
                )
            });
        }
        case 'pi':
        case 'lambda':
            return deepFreeze({
                tag: expression.tag,
                binder: {
                    hint: expression.binder.hint,
                    mode: { ...expression.binder.mode },
                    type: descend(
                        expression.binder.type,
                        `${path}.binder.type`
                    )
                },
                body: descend(
                    expression.body,
                    `${path}.body`
                )
            });
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const expressionRootSymbol = (
    expression: CoreLfTransferExpression
): CoreLfQualifiedSymbol | undefined => {
    switch (expression.tag) {
        case 'global':
            return expression.symbol;
        case 'call':
            return expressionRootSymbol(expression.callee);
        case 'type':
        case 'bound':
        case 'pi':
        case 'lambda':
        case 'capture':
        case 'wildcard':
            return undefined;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const instantiateCompiledExpression = (
    expression: CoreLfCompiledRuntimeExpression,
    captures: readonly CapturedRuntimeValue[],
    rule: Pick<CoreLfTransferRuntimeRule, 'id' | 'provenance'>,
    redex: KernelExpression,
    ambientDepth: number,
    localDepth = 0
): KernelExpression => {
    const nodeProvenance = derivedProvenance(
        rule,
        `instantiate ${expression.tag}`,
        redex.provenance
    );
    const instantiate = (
        child: CoreLfCompiledRuntimeExpression,
        childLocalDepth = localDepth
    ): KernelExpression => instantiateCompiledExpression(
        child,
        captures,
        rule,
        redex,
        ambientDepth,
        childLocalDepth
    );

    switch (expression.tag) {
        case 'universe':
            return kernelUniverse(nodeProvenance);
        case 'bound':
            return kernelBound(expression.index, nodeProvenance);
        case 'reference':
            return kernelFree(expression.name, nodeProvenance);
        case 'application':
            return kernelApplication(
                expression.owner,
                expression.arguments.map(argument => ({
                    value: instantiate(argument.value)
                })),
                nodeProvenance
            );
        case 'call':
            return kernelCall(
                instantiate(expression.callee),
                expression.arguments.map(argument => ({
                    plicity: argument.plicity,
                    value: instantiate(argument.value)
                })),
                nodeProvenance
            );
        case 'pi':
        case 'lambda': {
            const binder = kernelBinder(
                expression.binder.hint,
                instantiate(expression.binder.type),
                expression.binder.mode,
                nodeProvenance
            );
            const body = instantiate(
                expression.body,
                localDepth + 1
            );
            return expression.tag === 'pi'
                ? kernelPi(binder, body, nodeProvenance)
                : kernelLambda(binder, body, nodeProvenance);
        }
        case 'capture': {
            const capture = captures[expression.slot];
            if (capture === undefined) {
                return fail(
                    'INCOMPLETE_RUNTIME_MATCH',
                    `runtimeRules.${rule.id}`,
                    `Runtime rule '${rule.id}' has no capture for ` +
                        `'${expression.name}'`
                );
            }
            if (capture.sourceDepth !== ambientDepth) {
                return fail(
                    'CAPTURE_SCOPE_ESCAPE',
                    `runtimeRules.${rule.id}`,
                    `Runtime rule '${rule.id}' cannot instantiate capture ` +
                        `'${expression.name}' from ambient depth ` +
                        `${capture.sourceDepth} in ambient depth ` +
                        `${ambientDepth}`
                );
            }
            const indexMap = Array.from(
                { length: capture.sourceDepth },
                (_, index) => index + localDepth
            );
            try {
                return kernelRemapAmbientIndices(
                    capture.expression,
                    ambientDepth + localDepth,
                    indexMap
                );
            } catch (error: unknown) {
                return fail(
                    'CAPTURE_SCOPE_ESCAPE',
                    `runtimeRules.${rule.id}`,
                    `Runtime rule '${rule.id}' cannot move capture ` +
                        `'${expression.name}' from depth ` +
                        `${capture.sourceDepth} to ` +
                        `${ambientDepth + localDepth}: ` +
                        errorText(error),
                    error instanceof Error ? error : undefined
                );
            }
        }
        case 'wildcard':
            return fail(
                'UNSUPPORTED_RUNTIME_PATTERN',
                `runtimeRules.${rule.id}`,
                'A wildcard cannot occur in a runtime template'
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const requiredAmbientDepthAt = (
    expression: KernelExpression,
    internalDepth: number
): number => {
    const required = (
        child: KernelExpression,
        childInternalDepth = internalDepth
    ): number => requiredAmbientDepthAt(
        child,
        childInternalDepth
    );
    switch (expression.tag) {
        case 'universe':
        case 'reference':
            return 0;
        case 'bound':
            return expression.index < internalDepth
                ? 0
                : expression.index - internalDepth + 1;
        case 'meta':
            return expression.spine.reduce(
                (maximum, item) =>
                    Math.max(maximum, required(item)),
                0
            );
        case 'application':
            return expression.arguments.reduce(
                (maximum, argument) =>
                    Math.max(maximum, required(argument.value)),
                0
            );
        case 'call':
            return expression.arguments.reduce(
                (maximum, argument) =>
                    Math.max(maximum, required(argument.value)),
                required(expression.callee)
            );
        case 'pi':
        case 'lambda':
            return Math.max(
                required(expression.binder.type),
                required(expression.body, internalDepth + 1)
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const requiredAmbientDepth = (
    expression: KernelExpression
): number => requiredAmbientDepthAt(expression, 0);

const patternMatches = (
    pattern: CoreLfCompiledRuntimeExpression,
    expression: KernelExpression,
    bindings: (CapturedRuntimeValue | undefined)[],
    ambientDepth: number,
    localDepth: number
): boolean => {
    switch (pattern.tag) {
        case 'universe':
            return expression.tag === 'universe';
        case 'bound':
            return expression.tag === 'bound' &&
                expression.index === pattern.index;
        case 'reference':
            return expression.tag === 'reference' &&
                expression.name === pattern.name;
        case 'application':
            return expression.tag === 'application' &&
                expression.owner === pattern.owner &&
                expression.arguments.length === pattern.arguments.length &&
                pattern.arguments.every((argument, index) =>
                    expression.arguments[index].plicity ===
                        argument.plicity &&
                    patternMatches(
                        argument.value,
                        expression.arguments[index].value,
                        bindings,
                        ambientDepth,
                        localDepth
                    )
                );
        case 'call':
            return expression.tag === 'call' &&
                expression.arguments.length === pattern.arguments.length &&
                patternMatches(
                    pattern.callee,
                    expression.callee,
                    bindings,
                    ambientDepth,
                    localDepth
                ) &&
                pattern.arguments.every((argument, index) =>
                    expression.arguments[index].plicity ===
                        argument.plicity &&
                    patternMatches(
                        argument.value,
                        expression.arguments[index].value,
                        bindings,
                        ambientDepth,
                        localDepth
                    )
                );
        case 'pi':
        case 'lambda':
            return expression.tag === pattern.tag &&
                expression.binder.mode.plicity ===
                    pattern.binder.mode.plicity &&
                expression.binder.mode.variation ===
                    pattern.binder.mode.variation &&
                patternMatches(
                    pattern.binder.type,
                    expression.binder.type,
                    bindings,
                    ambientDepth,
                    localDepth
                ) &&
                patternMatches(
                    pattern.body,
                    expression.body,
                    bindings,
                    ambientDepth,
                    localDepth + 1
                );
        case 'capture': {
            try {
                kernelAssertScoped(
                    expression,
                    ambientDepth + localDepth
                );
            } catch {
                return false;
            }
            /*
             * Rule variables live outside every binder written in the rule
             * pattern. A capture encountered below such binders is still
             * first-order when the candidate does not mention any of them:
             * drop those rule-local indices and store one canonical value
             * at the redex's ambient depth. Captures that may depend on
             * selected binders use
             * allowedBoundIndices and remain an explicit later boundary.
             */
            let canonical: KernelExpression;
            try {
                canonical = kernelRemapAmbientIndices(
                    expression,
                    ambientDepth,
                    Array.from(
                        {
                            length:
                                ambientDepth + localDepth
                        },
                        (_, index) =>
                            index < localDepth
                                ? null
                                : index - localDepth
                    )
                );
            } catch {
                return false;
            }
            const existing = bindings[pattern.slot];
            if (existing === undefined) {
                bindings[pattern.slot] = {
                    expression: canonical,
                    sourceDepth: ambientDepth
                };
                return true;
            }
            return existing.sourceDepth === ambientDepth &&
                kernelExpressionEquals(existing.expression, canonical);
        }
        case 'wildcard':
            return true;
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

const internalMatch = (
    expression: KernelExpression,
    rule: CoreLfCompiledRuntimeRule
): InternalRuntimeMatch | undefined => {
    const ambientDepth = requiredAmbientDepth(expression);
    const bindings: (CapturedRuntimeValue | undefined)[] =
        rule.variables.map(() => undefined);
    if (!patternMatches(
        rule.left,
        expression,
        bindings,
        ambientDepth,
        0
    )) {
        return undefined;
    }
    if (bindings.some(binding => binding === undefined)) {
        return fail(
            'INCOMPLETE_RUNTIME_MATCH',
            `runtimeRules.${rule.id}`,
            `Runtime rule '${rule.id}' did not bind every variable`
        );
    }
    const captures = bindings as CapturedRuntimeValue[];
    return {
        ambientDepth,
        captures: Object.freeze(captures.map(capture =>
            Object.freeze({ ...capture })
        )),
        publicMatch: Object.freeze({
            ruleId: rule.id,
            bindings: Object.freeze(
                captures.map(capture => capture.expression)
            )
        })
    };
};

const frozenTrace = (
    trace: readonly CoreRuntimeWeakHeadTraceEntry[]
): readonly CoreRuntimeWeakHeadTraceEntry[] =>
    Object.freeze(trace.map(entry => Object.freeze({ ...entry })));

/**
 * One immutable, closed runtime component compiled from reviewed IR.
 */
export class CoreLfCompiledRuntimeProgram
implements CoreLfCatalogRuntime {
    readonly revision: string;
    readonly rules: readonly CoreLfCompiledRuntimeRule[];
    readonly ruleIds: readonly string[];

    constructor(
        public readonly module: CoreLfModuleSpec,
        public readonly policy: CoreLfTransferPolicyOverlay,
        rules: readonly CoreLfCompiledRuntimeRule[],
        public readonly comparisonStepLimit:
            number = CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
    ) {
        this.revision =
            `${module.revision}+${policy.revision}`;
        this.rules = Object.freeze(rules.map(rule => deepFreeze({
            ...rule,
            sourceOwner: { ...rule.sourceOwner },
            variables: rule.variables.map(variable => ({ ...variable })),
            checkedWithEarlierRuleIds: [
                ...rule.checkedWithEarlierRuleIds
            ]
        })));
        this.ruleIds = Object.freeze(this.rules.map(rule => rule.id));
        Object.freeze(this);
    }

    rule(id: string): CoreLfCompiledRuntimeRule | undefined {
        return this.rules.find(rule => rule.id === id);
    }

    matchRule(
        expression: KernelExpression,
        rule: CoreLfCompiledRuntimeRule
    ): CoreRuntimeMatch | undefined {
        return internalMatch(expression, rule)?.publicMatch;
    }

    instantiateRuleLeft(
        rule: CoreLfCompiledRuntimeRule,
        bindings: readonly KernelExpression[],
        nodeProvenance: Provenance
    ): KernelExpression {
        if (bindings.length !== rule.variables.length) {
            return fail(
                'INCOMPLETE_RUNTIME_MATCH',
                `runtimeRules.${rule.id}`,
                `Runtime rule '${rule.id}' expects ` +
                    `${rule.variables.length} bindings, received ` +
                    bindings.length
            );
        }
        bindings.forEach(binding => kernelAssertScoped(binding));
        const sourceRule = this.module.runtimeRules.find(
            candidate => candidate.id === rule.id
        );
        if (sourceRule === undefined) {
            return fail(
                'INVALID_RUNTIME_CONTEXT',
                `runtimeRules.${rule.id}`,
                `Compiled runtime rule '${rule.id}' has no source record`
            );
        }
        return instantiateCompiledExpression(
            rule.left,
            bindings.map(expression => ({
                expression,
                sourceDepth: 0
            })),
            sourceRule,
            kernelUniverse(nodeProvenance),
            0
        );
    }

    rewriteHead(
        expression: KernelExpression
    ): CoreRuntimeHeadRewriteResult {
        for (let ruleIndex = 0; ruleIndex < this.rules.length; ruleIndex++) {
            const rule = this.rules[ruleIndex];
            const match = internalMatch(expression, rule);
            if (match === undefined) continue;
            const sourceRule =
                this.module.runtimeRules[ruleIndex];
            return Object.freeze({
                status: 'rewritten',
                ruleId: rule.id,
                ruleIndex,
                before: expression,
                after: instantiateCompiledExpression(
                    rule.right,
                    match.captures,
                    sourceRule,
                    expression,
                    match.ambientDepth
                ),
                match: match.publicMatch
            });
        }
        return Object.freeze({
            status: 'irreducible',
            expression
        });
    }

    weakHead(
        expression: KernelExpression,
        stepLimit: number
    ): CoreRuntimeWeakHeadResult {
        if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
            return fail(
                'INVALID_RUNTIME_STEP_LIMIT',
                'stepLimit',
                `Runtime weak-head step limit must be a nonnegative safe ` +
                    `integer; received ${stepLimit}`
            );
        }
        let current = expression;
        const trace: CoreRuntimeWeakHeadTraceEntry[] = [];
        while (true) {
            const rewrite = this.rewriteHead(current);
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
}

const runtimeFragmentKey = (
    program: CoreLfCompiledRuntimeProgram
): string =>
    `${program.module.moduleId}\u0000` +
    `${program.module.fragmentId}\u0000${program.revision}`;

/**
 * Immutable, dependency-first composition of already compiled local runtime
 * fragments. It implements only the generic catalog-runtime seam; local
 * programs and their source/policy ownership remain independently visible.
 */
export class CoreLfComposedRuntimeProgram
implements CoreLfCatalogRuntime {
    readonly revision: string;
    readonly fragments: readonly CoreLfCompiledRuntimeProgram[];
    readonly ruleIds: readonly string[];

    constructor(
        fragments: readonly CoreLfCompiledRuntimeProgram[]
    ) {
        const fragmentKeys = new Set<string>();
        const ruleIds = new Set<string>();
        fragments.forEach((fragment, fragmentIndex) => {
            const key = runtimeFragmentKey(fragment);
            if (fragmentKeys.has(key)) {
                fail(
                    'INVALID_RUNTIME_DEPENDENCY',
                    `fragments[${fragmentIndex}]`,
                    `Runtime fragment '${fragment.module.moduleId}/` +
                        `${fragment.module.fragmentId}' is duplicated`
                );
            }
            fragmentKeys.add(key);
            fragment.ruleIds.forEach((ruleId, ruleIndex) => {
                if (ruleIds.has(ruleId)) {
                    fail(
                        'DUPLICATE_RUNTIME_RULE_ID',
                        `fragments[${fragmentIndex}].rules[${ruleIndex}]`,
                        `Composed runtime rule ID '${ruleId}' is duplicated`
                    );
                }
                ruleIds.add(ruleId);
            });
        });
        this.fragments = Object.freeze([...fragments]);
        this.ruleIds = Object.freeze([...ruleIds]);
        this.revision = [
            'composed-runtime-1',
            ...this.fragments.map(fragment =>
                `${fragment.module.moduleId}/` +
                `${fragment.module.fragmentId}@${fragment.revision}`
            )
        ].join('+');
        Object.freeze(this);
    }

    rewriteHead(
        expression: KernelExpression
    ): CoreRuntimeHeadRewriteResult {
        let ruleOffset = 0;
        for (const fragment of this.fragments) {
            const result = fragment.rewriteHead(expression);
            if (result.status === 'rewritten') {
                return Object.freeze({
                    ...result,
                    ruleIndex: ruleOffset + result.ruleIndex
                });
            }
            ruleOffset += fragment.ruleIds.length;
        }
        return Object.freeze({
            status: 'irreducible',
            expression
        });
    }
}

const exactRuntimeFragments = (
    runtime: CoreLfCatalogRuntime
): readonly CoreLfCompiledRuntimeProgram[] | undefined => {
    if (runtime instanceof CoreLfCompiledRuntimeProgram) {
        return [runtime];
    }
    if (runtime instanceof CoreLfComposedRuntimeProgram) {
        return runtime.fragments;
    }
    return undefined;
};

/**
 * Whether `runtime` is the same immutable runtime as `prefix`, or extends it
 * by appending exact compiled fragment objects.
 *
 * An absent prefix is the empty source-time runtime. Foreign catalog runtime
 * implementations are comparable only by object identity: their internal
 * rule lineage is deliberately not guessed from public rule IDs.
 */
export function coreLfRuntimeHasExactPrefix(
    runtime: CoreLfCatalogRuntime | undefined,
    prefix: CoreLfCatalogRuntime | undefined
): boolean {
    if (prefix === undefined) return true;
    if (runtime === prefix) return true;
    if (runtime === undefined) return false;

    const runtimeFragments = exactRuntimeFragments(runtime);
    const prefixFragments = exactRuntimeFragments(prefix);
    if (
        runtimeFragments === undefined ||
        prefixFragments === undefined ||
        prefixFragments.length > runtimeFragments.length
    ) {
        return false;
    }
    return prefixFragments.every(
        (fragment, index) => runtimeFragments[index] === fragment
    );
}

export interface CoreLfRuntimeFragmentDependency {
    readonly relation: CoreLfRuntimeFragmentDependencyRelation;
    readonly fragment: CoreLfCompiledRuntimeFragment;
}

export interface CoreLfRuntimeFragmentCompilerOptions
    extends CoreLfRuntimeCompilerOptions {
    readonly dependencies:
        readonly CoreLfRuntimeFragmentDependency[];
}

/**
 * One local program plus its immutable, transitively flattened runtime
 * closure. Direct dependency evidence stays separate from the flattened
 * execution component so module/fragment ownership remains reviewable.
 */
export class CoreLfCompiledRuntimeFragment {
    readonly identity: string;
    readonly dependencies:
        readonly CoreLfRuntimeFragmentDependency[];

    constructor(
        public readonly localProgram: CoreLfCompiledRuntimeProgram,
        dependencies: readonly CoreLfRuntimeFragmentDependency[],
        public readonly runtime: CoreLfComposedRuntimeProgram
    ) {
        this.identity = runtimeFragmentKey(localProgram);
        this.dependencies = Object.freeze(
            dependencies.map(dependency => Object.freeze({
                relation: dependency.relation,
                fragment: dependency.fragment
            }))
        );
        Object.freeze(this);
    }

    get module(): CoreLfModuleSpec {
        return this.localProgram.module;
    }

    get policy(): CoreLfTransferPolicyOverlay {
        return this.localProgram.policy;
    }
}

const runtimePolicyMap = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay
): ReadonlySet<string> => {
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        return fail(
            'INCOMPLETE_RUNTIME_POLICY',
            'policy',
            'Runtime policy targets a foreign transfer module'
        );
    }
    const ids = new Set<string>();
    policy.entries.forEach((entry, index) => {
        if (
            entry.target.kind !== 'runtime-rule' ||
            entry.policy !== 'runtime-rewrite'
        ) {
            return fail(
                'INCOMPLETE_RUNTIME_POLICY',
                `policy.entries[${index}]`,
                'Runtime compiler requires runtime-rewrite policy entries'
            );
        }
        if (ids.has(entry.target.id)) {
            return fail(
                'INCOMPLETE_RUNTIME_POLICY',
                `policy.entries[${index}]`,
                `Duplicate runtime policy for '${entry.target.id}'`
            );
        }
        ids.add(entry.target.id);
    });
    const missing = module.runtimeRules.filter(rule => !ids.has(rule.id));
    if (
        missing.length > 0 ||
        ids.size !== module.runtimeRules.length
    ) {
        return fail(
            'INCOMPLETE_RUNTIME_POLICY',
            'policy.entries',
            'Runtime policy must cover every rule exactly once'
        );
    }
    return ids;
};

const validateGroups = (module: CoreLfModuleSpec): void => {
    const groups = new Map<string, number>();
    const closedGroups = new Set<string>();
    let activeGroup: string | undefined;
    module.runtimeRules.forEach((rule, index) => {
        if (rule.groupId !== activeGroup) {
            if (activeGroup !== undefined) {
                closedGroups.add(activeGroup);
            }
            if (closedGroups.has(rule.groupId)) {
                fail(
                    'INVALID_RUNTIME_GROUP',
                    `module.runtimeRules[${index}].groupId`,
                    `Runtime group '${rule.groupId}' is not contiguous`
                );
            }
            activeGroup = rule.groupId;
        }
        const expected = groups.get(rule.groupId) ?? 0;
        if (rule.clauseOrder !== expected) {
            fail(
                'INVALID_RUNTIME_GROUP',
                `module.runtimeRules[${index}].clauseOrder`,
                `Runtime group '${rule.groupId}' expected clause ` +
                    `${expected}, received ${rule.clauseOrder}`
            );
        }
        groups.set(rule.groupId, expected + 1);
    });
};

const checkingCaptureValues = (
    references: readonly KernelExpression[]
): readonly CapturedRuntimeValue[] =>
    references.map(expression => ({
        expression,
        sourceDepth: 0
    }));

const runtimePrefix = (
    prior: CoreLfCatalogRuntime | undefined,
    local: CoreLfCompiledRuntimeProgram
): CoreLfCatalogRuntime => {
    if (prior === undefined) return local;
    const ruleIds = Object.freeze([
        ...prior.ruleIds,
        ...local.ruleIds
    ]);
    return Object.freeze({
        revision: `${prior.revision}+${local.revision}`,
        ruleIds,
        rewriteHead(
            expression: KernelExpression
        ): CoreRuntimeHeadRewriteResult {
            const priorResult = prior.rewriteHead(expression);
            if (priorResult.status === 'rewritten') {
                return priorResult;
            }
            const localResult = local.rewriteHead(expression);
            if (localResult.status === 'irreducible') {
                return localResult;
            }
            return Object.freeze({
                ...localResult,
                ruleIndex:
                    prior.ruleIds.length + localResult.ruleIndex
            });
        }
    });
};

const compileRule = (
    source: CoreLfTransferRuntimeRule,
    context: CoreLfRuntimeDeclarationContext,
    earlierRules: readonly CoreLfCompiledRuntimeRule[],
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    comparisonStepLimit: number,
    subjectReductionOracle:
        CoreLfRuntimeSubjectReductionOracle | undefined,
    priorRuntime: CoreLfCatalogRuntime | undefined,
    priorRuleIds: readonly string[]
): CoreLfCompiledRuntimeRule => {
    const captures = new Map(
        source.variables.map((variable, slot) => [
            variable.name,
            slot
        ])
    );
    const baseState = {
        context,
        captures
    };
    const variables = source.variables.map((variable, slot) => ({
        slot,
        name: variable.name,
        type: compileRuntimeExpression(
            variable.type,
            {
                ...baseState,
                purpose: 'variable-type' as const,
                maximumCaptureSlot: slot - 1
            },
            `runtimeRules.${source.id}.variables[${slot}].type`
        )
    }));
    const left = compileRuntimeExpression(
        source.left,
        {
            ...baseState,
            purpose: 'pattern',
            maximumCaptureSlot: variables.length - 1
        },
        `runtimeRules.${source.id}.left`
    );
    const right = compileRuntimeExpression(
        source.right,
        {
            ...baseState,
            purpose: 'template',
            maximumCaptureSlot: variables.length - 1
        },
        `runtimeRules.${source.id}.right`
    );
    const root = expressionRootSymbol(source.left);
    if (root === undefined || !sameSymbol(root, source.sourceOwner)) {
        return fail(
            'SOURCE_OWNER_MISMATCH',
            `runtimeRules.${source.id}.sourceOwner`,
            `Runtime rule '${source.id}' source owner does not match its ` +
                'rigid left head'
        );
    }

    const localPrefix = new CoreLfCompiledRuntimeProgram(
        module,
        policy,
        earlierRules,
        comparisonStepLimit
    );
    const checkingRuntime = runtimePrefix(
        priorRuntime,
        localPrefix
    );
    let ruleEnvironment = context.environment;
    const checkingReferences: KernelExpression[] = [];
    for (const variable of variables) {
        const checkingName =
            `runtime_${source.order}_${variable.slot}_${variable.name}`;
        if (ruleEnvironment.lookup(checkingName) !== undefined) {
            return fail(
                'INVALID_RUNTIME_CONTEXT',
                `runtimeRules.${source.id}.variables[${variable.slot}]`,
                `Synthetic rule declaration '${checkingName}' collides ` +
                    'with the declaration context'
            );
        }
        const type = instantiateCompiledExpression(
            variable.type,
            checkingCaptureValues(checkingReferences),
            source,
            kernelUniverse(derivedProvenance(
                source,
                `variable ${variable.name} type`
            )),
            0
        );
        try {
            /*
             * Validate the new telescope entry against exactly the earlier
             * compiled rule prefix. Do not revalidate the precompiled
             * declaration context under that smaller prefix: its own
             * checker factory retains the runtime that established it.
             */
            const typeChecker = createCoreLfChecker(
                ruleEnvironment,
                comparisonStepLimit,
                checkingRuntime
            );
            const inferredType = typeChecker.infer(
                typeChecker.rootContext,
                type
            ).type;
            if (!isCoreKind(inferredType)) {
                typeChecker.check(
                    typeChecker.rootContext,
                    type,
                    kernelUniverse(derivedProvenance(
                        source,
                        `variable ${variable.name} sort`
                    ))
                );
            }
            ruleEnvironment = ruleEnvironment.extend({
                name: checkingName,
                type,
                mode: {
                    plicity: 'explicit',
                    variation: 'functorial'
                },
                provenance: derivedProvenance(
                    source,
                    `variable ${variable.name}`
                ),
                transparency: 'opaque'
            });
        } catch (error: unknown) {
            return fail(
                'INVALID_RUNTIME_VARIABLE_TYPE',
                `runtimeRules.${source.id}.variables[${variable.slot}]`,
                `Runtime variable '${variable.name}' has an invalid type: ` +
                    errorText(error),
                error instanceof Error ? error : undefined
            );
        }
        checkingReferences.push(kernelFree(
            checkingName,
            derivedProvenance(
                source,
                `variable ${variable.name} reference`
            )
        ));
    }

    const checkingValues =
        checkingCaptureValues(checkingReferences);
    const syntheticRedex = kernelUniverse(
        derivedProvenance(source, 'typing witness')
    );
    const leftTerm = instantiateCompiledExpression(
        left,
        checkingValues,
        source,
        syntheticRedex,
        0
    );
    const rightTerm = instantiateCompiledExpression(
        right,
        checkingValues,
        source,
        syntheticRedex,
        0
    );
    let subjectValidation: CoreLfRuntimeSubjectValidation;
    try {
        const checker: CoreLfChecker = createCoreLfChecker(
            ruleEnvironment,
            comparisonStepLimit,
            checkingRuntime
        );
        const inferred = checker.infer(
            checker.rootContext,
            leftTerm
        );
        if (isCoreKind(inferred.type)) {
            return fail(
                'INVALID_RUNTIME_RULE_TYPE',
                `runtimeRules.${source.id}.left`,
                `Runtime rule '${source.id}' left side has KIND`
            );
        }
        checker.check(
            checker.rootContext,
            rightTerm,
            inferred.type
        );
        subjectValidation = deepFreeze({
            kind: 'typescript-checked'
        });
    } catch (error: unknown) {
        if (error instanceof CoreLfRuntimeCompilerError) throw error;
        if (
            subjectReductionOracle?.ruleIds.includes(source.id)
        ) {
            subjectValidation = deepFreeze({
                kind: 'external-oracle-required',
                authorityPath:
                    subjectReductionOracle.authorityPath,
                evidence: subjectReductionOracle.evidence,
                diagnostic: errorText(error)
            });
        } else {
            return fail(
                'INVALID_RUNTIME_RULE_TYPE',
                `runtimeRules.${source.id}`,
                `Runtime rule '${source.id}' is not type preserving against ` +
                    `its earlier compiled prefix: ${errorText(error)}`,
                error instanceof Error ? error : undefined
            );
        }
    }

    return deepFreeze({
        order: source.order,
        id: source.id,
        groupId: source.groupId,
        clauseOrder: source.clauseOrder,
        sourceOwner: { ...source.sourceOwner },
        variables,
        left,
        right,
        checkedWithEarlierRuleIds: [
            ...priorRuleIds,
            ...earlierRules.map(rule => rule.id)
        ],
        subjectValidation,
        provenance: derivedProvenance(source, 'compiled')
    });
};

const validateSubjectReductionOracle = (
    module: CoreLfModuleSpec,
    oracle: CoreLfRuntimeSubjectReductionOracle | undefined
): void => {
    if (oracle === undefined) return;
    if (
        oracle.authorityPath !== module.authorityPath ||
        oracle.evidence.trim().length === 0
    ) {
        return fail(
            'INVALID_RUNTIME_SUBJECT_ORACLE',
            'options.subjectReductionOracle',
            'A runtime subject-reduction oracle must name the module ' +
                'authority path and nonempty reviewed evidence'
        );
    }
    const known = new Map(
        module.runtimeRules.map(rule => [rule.id, rule.order])
    );
    const seen = new Set<string>();
    let previousOrder = -1;
    oracle.ruleIds.forEach((id, index) => {
        const order = known.get(id);
        if (
            order === undefined ||
            seen.has(id) ||
            order <= previousOrder
        ) {
            fail(
                'INVALID_RUNTIME_SUBJECT_ORACLE',
                `options.subjectReductionOracle.ruleIds[${index}]`,
                'Runtime subject-reduction oracle IDs must be unique, ' +
                    'known, and in module order'
            );
        }
        seen.add(id);
        previousOrder = order;
    });
};

const compileCoreLfRuntimeProgramWithPrefix = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    context: CoreLfRuntimeDeclarationContext,
    options: CoreLfRuntimeCompilerOptions,
    priorRuntime: CoreLfCatalogRuntime | undefined,
    priorRuleIds: readonly string[]
): CoreLfCompiledRuntimeProgram => {
    if (
        (priorRuntime === undefined && priorRuleIds.length !== 0) ||
        (priorRuntime !== undefined && (
            priorRuntime.ruleIds.length !== priorRuleIds.length ||
            priorRuntime.ruleIds.some(
                (id, index) => id !== priorRuleIds[index]
            )
        ))
    ) {
        return fail(
            'INVALID_RUNTIME_DEPENDENCY',
            'priorRuntime',
            'Runtime prefix IDs do not match the supplied prior runtime'
        );
    }
    if (
        module.declarations.length > 0 ||
        module.inductives.length > 0 ||
        module.proofRules.length > 0
    ) {
        return fail(
            'UNSUPPORTED_MODULE_CONTENT',
            'module',
            'Runtime compiler accepts a runtime-only module fragment'
        );
    }
    runtimePolicyMap(module, policy);
    validateGroups(module);
    validateSubjectReductionOracle(
        module,
        options.subjectReductionOracle
    );
    const comparisonStepLimit =
        options.comparisonStepLimit ??
        CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT;
    if (
        !Number.isSafeInteger(comparisonStepLimit) ||
        comparisonStepLimit < 0
    ) {
        return fail(
            'INVALID_RUNTIME_STEP_LIMIT',
            'options.comparisonStepLimit',
            'Runtime comparison budget must be a nonnegative safe integer'
        );
    }

    const externalKeys = new Set(
        module.externalSymbols.map(external =>
            symbolKey(external.symbol)
        )
    );
    for (const symbol of module.referencedSymbols) {
        if (
            !externalKeys.has(symbolKey(symbol)) ||
            context.declaration(symbol) === undefined
        ) {
            return fail(
                'INVALID_RUNTIME_CONTEXT',
                'module.referencedSymbols',
                `Runtime declaration context does not resolve ` +
                    `'${displaySymbol(symbol)}'`
            );
        }
    }

    const rules: CoreLfCompiledRuntimeRule[] = [];
    for (const source of module.runtimeRules) {
        rules.push(compileRule(
            source,
            context,
            rules,
            module,
            policy,
            comparisonStepLimit,
            options.subjectReductionOracle,
            priorRuntime,
            priorRuleIds
        ));
    }
    const usedOracleRuleIds = rules
        .filter(rule =>
            rule.subjectValidation.kind ===
                'external-oracle-required'
        )
        .map(rule => rule.id);
    const requestedOracleRuleIds =
        options.subjectReductionOracle?.ruleIds ?? [];
    if (
        usedOracleRuleIds.length !== requestedOracleRuleIds.length ||
        usedOracleRuleIds.some(
            (id, index) => id !== requestedOracleRuleIds[index]
        )
    ) {
        return fail(
            'INVALID_RUNTIME_SUBJECT_ORACLE',
            'options.subjectReductionOracle.ruleIds',
            'Every runtime subject-reduction oracle exception must be ' +
                'necessary under the current TypeScript checker'
        );
    }
    return new CoreLfCompiledRuntimeProgram(
        module,
        policy,
        rules,
        comparisonStepLimit
    );
};

/**
 * Compile and type-check one independent runtime-only transfer fragment.
 */
export function compileCoreLfRuntimeProgram(
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    context: CoreLfRuntimeDeclarationContext,
    options: CoreLfRuntimeCompilerOptions = {}
): CoreLfCompiledRuntimeProgram {
    return compileCoreLfRuntimeProgramWithPrefix(
        module,
        policy,
        context,
        options,
        undefined,
        []
    );
}

const moduleFragmentKey = (module: CoreLfModuleSpec): string =>
    `${module.moduleId}\u0000${module.fragmentId}`;

const validateDirectRuntimeDependencies = (
    module: CoreLfModuleSpec,
    dependencies: readonly CoreLfRuntimeFragmentDependency[]
): void => {
    const direct = new Set<string>();
    const consumerKey = moduleFragmentKey(module);
    let previousModuleDependencyIndex = -1;
    let sawEarlierFragment = false;

    dependencies.forEach((dependency, index) => {
        const path = `options.dependencies[${index}]`;
        const dependencyModule = dependency.fragment.module;
        if (direct.has(dependency.fragment.identity)) {
            fail(
                'INVALID_RUNTIME_DEPENDENCY',
                path,
                `Direct runtime dependency '${dependencyModule.moduleId}/` +
                    `${dependencyModule.fragmentId}' is duplicated`
            );
        }
        direct.add(dependency.fragment.identity);

        if (dependency.relation === 'dependency-module') {
            const dependencyIndex = module.dependencies.indexOf(
                dependencyModule.moduleId
            );
            if (
                dependencyModule.moduleId === module.moduleId ||
                dependencyIndex < 0 ||
                sawEarlierFragment ||
                dependencyIndex < previousModuleDependencyIndex
            ) {
                fail(
                    'INVALID_RUNTIME_DEPENDENCY',
                    `${path}.relation`,
                    `Runtime dependency '${dependencyModule.moduleId}/` +
                        `${dependencyModule.fragmentId}' is not in consumer ` +
                        'module-dependency order'
                );
            }
            previousModuleDependencyIndex = dependencyIndex;
        } else if (dependency.relation === 'earlier-fragment') {
            if (
                dependencyModule.moduleId !== module.moduleId ||
                dependencyModule.fragmentId === module.fragmentId
            ) {
                fail(
                    'INVALID_RUNTIME_DEPENDENCY',
                    `${path}.relation`,
                    `Earlier runtime fragment must be a distinct fragment ` +
                        `of module '${module.moduleId}'`
                );
            }
            sawEarlierFragment = true;
        } else {
            const exhaustive: never = dependency.relation;
            return exhaustive;
        }

        if (
            dependency.fragment.runtime.fragments.some(
                fragment =>
                    moduleFragmentKey(fragment.module) === consumerKey
            )
        ) {
            fail(
                'CYCLIC_RUNTIME_DEPENDENCY',
                path,
                `Runtime dependency closure already contains consumer ` +
                    `'${module.moduleId}/${module.fragmentId}'`
            );
        }
    });
};

const flattenedRuntimeDependencies = (
    dependencies: readonly CoreLfRuntimeFragmentDependency[]
): readonly CoreLfCompiledRuntimeProgram[] => {
    const programs: CoreLfCompiledRuntimeProgram[] = [];
    const byIdentity = new Map<string, CoreLfCompiledRuntimeProgram>();
    dependencies.forEach((dependency, dependencyIndex) => {
        dependency.fragment.runtime.fragments.forEach(
            (program, closureIndex) => {
                const key = runtimeFragmentKey(program);
                const existing = byIdentity.get(key);
                if (existing === program) return;
                if (existing !== undefined) {
                    fail(
                        'INVALID_RUNTIME_DEPENDENCY',
                        `options.dependencies[${dependencyIndex}]` +
                            `.closure[${closureIndex}]`,
                        `Runtime dependency closure supplies two distinct ` +
                            `artifacts for '${program.module.moduleId}/` +
                            `${program.module.fragmentId}'`
                    );
                }
                byIdentity.set(key, program);
                programs.push(program);
            }
        );
    });
    return Object.freeze(programs);
};

/**
 * Compile a local runtime fragment against an explicit dependency prefix and
 * return both the local artifact and its transitively flattened executable
 * closure. Dependency modules precede same-module earlier fragments, and all
 * prior rules precede the local rule order.
 */
export function compileCoreLfRuntimeFragment(
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    context: CoreLfRuntimeDeclarationContext,
    options: CoreLfRuntimeFragmentCompilerOptions
): CoreLfCompiledRuntimeFragment {
    validateDirectRuntimeDependencies(
        module,
        options.dependencies
    );
    const priorPrograms = flattenedRuntimeDependencies(
        options.dependencies
    );
    const priorRuntime = priorPrograms.length === 0
        ? undefined
        : new CoreLfComposedRuntimeProgram(priorPrograms);
    const localRuleIds = new Set(
        module.runtimeRules.map(rule => rule.id)
    );
    priorRuntime?.ruleIds.forEach((ruleId, index) => {
        if (localRuleIds.has(ruleId)) {
            fail(
                'DUPLICATE_RUNTIME_RULE_ID',
                `options.dependencies.rules[${index}]`,
                `Local runtime rule ID '${ruleId}' duplicates a prior rule`
            );
        }
    });
    const localProgram = compileCoreLfRuntimeProgramWithPrefix(
        module,
        policy,
        context,
        {
            comparisonStepLimit: options.comparisonStepLimit,
            subjectReductionOracle:
                options.subjectReductionOracle
        },
        priorRuntime,
        priorRuntime?.ruleIds ?? []
    );
    const runtime = new CoreLfComposedRuntimeProgram([
        ...priorPrograms,
        localProgram
    ]);
    return new CoreLfCompiledRuntimeFragment(
        localProgram,
        options.dependencies,
        runtime
    );
}
