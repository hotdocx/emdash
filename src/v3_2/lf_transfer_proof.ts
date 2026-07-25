/**
 * Generic typed proof-time unification compiler, bounded comparison engine,
 * and final-signature composition for
 * SCALE-0E/SCALE-MIXED-PHASE-1B/1C.
 *
 * This is deliberately separate from runtime conversion. Proof rules match
 * one equality problem symmetrically and replace it with an ordered list of
 * new equality problems. They never become evaluator rewrites.
 */

import {
    isCoreKind
} from './checker';
import {
    CoreContext
} from './context';
import {
    CoreLfChecker,
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfCatalogRuntime,
    CoreLfCombinedNextStep,
    CoreLfCombinedTraceEntry,
    CoreLfComparisonMismatch,
    coreLfCombinedWeakHead,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferExpression,
    CoreLfTransferExternalSymbol,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferProofRule,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclaration
} from './lf_transfer_compiler';
import {
    coreLfRuntimeHasExactPrefix
} from './lf_transfer_runtime';
import {
    BinderMode,
    KernelExpression,
    KernelMetaVariable,
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
import {
    CoreConstraintReason,
    CoreConstraintStep,
    CoreElaborationSession,
    CoreMetaEntry
} from './session';

export interface CoreLfProofDeclarationContext {
    readonly environment: CoreLfDeclarationEnvironment;
    declaration(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledDeclaration | undefined;
}

export type CoreLfCompiledProofExpression =
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
        readonly arguments: readonly CoreLfCompiledProofArgument[];
    }
    | {
        readonly tag: 'call';
        readonly callee: CoreLfCompiledProofExpression;
        readonly arguments: readonly CoreLfCompiledProofArgument[];
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly binder: {
            readonly hint: string;
            readonly mode: BinderMode;
            readonly type: CoreLfCompiledProofExpression;
        };
        readonly body: CoreLfCompiledProofExpression;
    }
    | {
        readonly tag: 'capture';
        readonly slot: number;
        readonly name: string;
    }
    | {
        readonly tag: 'wildcard';
    };

export interface CoreLfCompiledProofArgument {
    readonly plicity: Plicity;
    readonly value: CoreLfCompiledProofExpression;
}

export interface CoreLfCompiledProofVariable {
    readonly slot: number;
    readonly name: string;
    readonly role: 'matched' | 'fresh-constraint';
    readonly type: CoreLfCompiledProofExpression;
}

export interface CoreLfCompiledProofProblem {
    readonly left: CoreLfCompiledProofExpression;
    readonly right: CoreLfCompiledProofExpression;
}

/**
 * A source-ordered equality that was safe to reflect as a transparent
 * checking-only alias. The target capture is always later than every capture
 * in the replacement, so rebuilding the synthetic rule telescope stays
 * acyclic and preserves its original dependency order.
 */
export interface CoreLfProofGeneratedConstraintAlias {
    readonly constraintIndex: number;
    readonly variableSlot: number;
    readonly variableName: string;
    readonly replacement: CoreLfCompiledProofExpression;
}

export type CoreLfProofTypingValidation =
    | {
        readonly kind: 'typescript-checked';
        readonly generatedConstraintAliases:
            readonly CoreLfProofGeneratedConstraintAlias[];
    }
    | {
        readonly kind: 'external-oracle-required';
        readonly authorityPath: string;
        readonly evidence: string;
        readonly diagnostic: string;
    };

export interface CoreLfCompiledProofRule {
    readonly order: number;
    readonly id: string;
    readonly sourceOwner: CoreLfQualifiedSymbol;
    readonly variables: readonly CoreLfCompiledProofVariable[];
    readonly problem: CoreLfCompiledProofProblem;
    readonly generatedConstraints:
        readonly CoreLfCompiledProofProblem[];
    readonly checkedWithEarlierRuleIds: readonly string[];
    readonly typingValidation: CoreLfProofTypingValidation;
    readonly provenance: Provenance;
}

export interface CoreLfProofTypingOracle {
    readonly authorityPath: string;
    readonly ruleIds: readonly string[];
    readonly evidence: string;
}

export interface CoreLfProofCompilerOptions {
    readonly comparisonStepLimit?: number;
    /**
     * Runtime conversion remains a separate immutable dependency. It may be
     * used while checking rule types and while normalizing comparison
     * problems, but proof rules never enter this runtime component.
     */
    readonly runtimeProgram?: CoreLfCatalogRuntime;
    /**
     * Exact, self-invalidating exception for an active Lambdapi rule whose
     * generated constraints remain outside the generic source-ordered
     * checking-alias envelope. Structural validation and variable-telescope
     * checking still run. Every listed exception must actually be needed.
     */
    readonly typingOracle?: CoreLfProofTypingOracle;
}

export type CoreLfProofCompilerErrorCode =
    | 'INVALID_PROOF_CONTEXT'
    | 'INCOMPLETE_PROOF_POLICY'
    | 'UNSUPPORTED_MODULE_CONTENT'
    | 'UNRESOLVED_PROOF_SYMBOL'
    | 'INVALID_PROOF_APPLICATION'
    | 'UNKNOWN_PROOF_CAPTURE'
    | 'UNSUPPORTED_PROOF_PATTERN'
    | 'UNSUPPORTED_HIGHER_ORDER_PATTERN'
    | 'INVALID_PROOF_VARIABLE_TYPE'
    | 'INVALID_PROOF_RULE_TYPE'
    | 'INVALID_PROOF_TYPING_ORACLE'
    | 'INVALID_PROOF_COMPOSITION'
    | 'INCOMPLETE_PROOF_MATCH'
    | 'PROOF_CAPTURE_SCOPE_ESCAPE'
    | 'INVALID_PROOF_STEP_LIMIT';

export class CoreLfProofCompilerError extends Error {
    constructor(
        public readonly code: CoreLfProofCompilerErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfProofCompilerError';
    }
}

export type CoreLfProofOrientation = 'forward' | 'symmetric';

export interface CoreLfProofBinding {
    readonly name: string;
    readonly value: KernelExpression;
}

export interface CoreLfProofRuleApplication {
    readonly ruleId: string;
    readonly ruleIndex: number;
    readonly orientation: CoreLfProofOrientation;
    readonly bindings: readonly CoreLfProofBinding[];
    readonly freshMetavariables: readonly {
        readonly name: string;
        readonly meta: KernelMetaVariable;
    }[];
    readonly generatedProblems: readonly {
        readonly left: KernelExpression;
        readonly right: KernelExpression;
    }[];
}

export type CoreLfProofComparisonTraceEntry =
    | {
        readonly step: number;
        readonly kind: 'reduction';
        readonly problemId: number;
        readonly side: 'left' | 'right';
        readonly reduction: CoreLfCombinedTraceEntry;
    }
    | {
        readonly step: number;
        readonly kind: 'meta-assignment';
        readonly problemId: number;
        readonly reason: CoreConstraintReason;
    }
    | {
        readonly step: number;
        readonly kind: 'proof-rule';
        readonly problemId: number;
        readonly ruleId: string;
        readonly ruleIndex: number;
        readonly orientation: CoreLfProofOrientation;
        readonly generatedProblemIds: readonly number[];
    };

interface CoreLfProofComparisonBase {
    readonly steps: number;
    readonly trace: readonly CoreLfProofComparisonTraceEntry[];
    readonly ruleApplications: readonly CoreLfProofRuleApplication[];
    readonly resolutionOrder: readonly number[];
    readonly metavariables: readonly CoreMetaEntry[];
}

export interface CoreLfProofComparisonSolved
    extends CoreLfProofComparisonBase {
    readonly status: 'solved';
    readonly left: KernelExpression;
    readonly right: KernelExpression;
}

export interface CoreLfProofComparisonStuck
    extends CoreLfProofComparisonBase {
    readonly status: 'stuck';
    readonly problemId: number;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly reason:
        | 'no-proof-rule'
        | 'plicity-mismatch'
        | 'meta-assignment-rejected';
    readonly mismatch?: CoreLfComparisonMismatch;
    readonly constraintReason?: CoreConstraintReason;
}

export type CoreLfProofNextStep =
    | {
        readonly kind: 'conversion';
        readonly side: 'left' | 'right';
        readonly next: CoreLfCombinedNextStep;
    }
    | {
        readonly kind: 'meta-assignment';
    }
    | {
        readonly kind: 'proof-rule';
        readonly ruleId: string;
        readonly orientation: CoreLfProofOrientation;
    };

export interface CoreLfProofComparisonStepLimit
    extends CoreLfProofComparisonBase {
    readonly status: 'step-limit-exceeded';
    readonly problemId: number;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly next: CoreLfProofNextStep;
}

export type CoreLfProofComparisonResult =
    | CoreLfProofComparisonSolved
    | CoreLfProofComparisonStuck
    | CoreLfProofComparisonStepLimit;

export interface CoreLfProofComparisonOptions {
    readonly stepLimit?: number;
    readonly session?: CoreElaborationSession;
}

type ProofExpressionPurpose =
    | 'variable-type'
    | 'pattern'
    | 'template';

interface ProofCompilationState {
    readonly context: CoreLfProofDeclarationContext;
    readonly captures: ReadonlyMap<string, number>;
    readonly maximumCaptureSlot: number;
    readonly purpose: ProofExpressionPurpose;
}

interface CapturedProofValue {
    readonly expression: KernelExpression;
    readonly sourceDepth: number;
}

interface InternalProofMatch {
    readonly orientation: CoreLfProofOrientation;
    readonly captures:
        readonly (CapturedProofValue | undefined)[];
}

interface PendingProofProblem {
    readonly id: number;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
}

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const fail = (
    code: CoreLfProofCompilerErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfProofCompilerError(
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
    rule: Pick<CoreLfTransferProofRule, 'id' | 'provenance'>,
    detail: string,
    source?: Provenance
): Provenance => deepFreeze(provenance(
    'recovered',
    `transfer proof rule ${rule.id} ${detail} from ` +
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
    context: CoreLfProofDeclarationContext,
    symbol: CoreLfQualifiedSymbol,
    path: string
): CoreLfCompiledDeclaration => {
    const declaration = context.declaration(symbol);
    if (
        declaration === undefined ||
        declaration.status === 'excluded'
    ) {
        return fail(
            'UNRESOLVED_PROOF_SYMBOL',
            path,
            `Proof expression refers to unavailable declaration ` +
                `'${displaySymbol(symbol)}'`
        );
    }
    return declaration;
};

const compileGlobal = (
    symbol: CoreLfQualifiedSymbol,
    state: ProofCompilationState,
    path: string
): CoreLfCompiledProofExpression => {
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
            'INVALID_PROOF_APPLICATION',
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

const compileProofExpression = (
    expression: CoreLfTransferExpression,
    state: ProofCompilationState,
    path: string
): CoreLfCompiledProofExpression => {
    const descend = (
        child: CoreLfTransferExpression,
        childPath: string
    ): CoreLfCompiledProofExpression => compileProofExpression(
        child,
        state,
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
                    'UNKNOWN_PROOF_CAPTURE',
                    path,
                    `Proof ${state.purpose} refers to unavailable capture ` +
                        `'${expression.name}'`
                );
            }
            if (expression.allowedBoundIndices !== undefined) {
                return fail(
                    'UNSUPPORTED_HIGHER_ORDER_PATTERN',
                    path,
                    `Proof ${state.purpose} capture '${expression.name}' ` +
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
                'UNSUPPORTED_PROOF_PATTERN',
                path,
                'Typed proof compilation does not yet support wildcards'
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
                    const schema = CORE_OWNER_SCHEMAS[link.owner];
                    if (arguments_.length !== schema.slots.length) {
                        return fail(
                            'INVALID_PROOF_APPLICATION',
                            path,
                            `Intrinsic owner '${link.owner}' expects ` +
                                `${schema.slots.length} arguments, received ` +
                                arguments_.length
                        );
                    }
                    arguments_.forEach((argument, index) => {
                        if (
                            argument.plicity !==
                            schema.slots[index].plicity
                        ) {
                            fail(
                                'INVALID_PROOF_APPLICATION',
                                `${path}.arguments[${index}].plicity`,
                                `Intrinsic owner '${link.owner}' argument ` +
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
                        'INVALID_PROOF_APPLICATION',
                        path,
                        `Free declaration '${link.coreName}' receives ` +
                            `${arguments_.length} arguments but its ` +
                            `signature exposes ${plicities.length}`
                    );
                }
                arguments_.forEach((argument, index) => {
                    if (argument.plicity !== plicities[index]) {
                        fail(
                            'INVALID_PROOF_APPLICATION',
                            `${path}.arguments[${index}].plicity`,
                            `Free declaration '${link.coreName}' argument ` +
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
                    }))
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

const instantiateCompiledExpression = (
    expression: CoreLfCompiledProofExpression,
    captures: readonly (CapturedProofValue | undefined)[],
    rule: CoreLfTransferProofRule,
    witness: KernelExpression,
    ambientDepth: number,
    localDepth = 0
): KernelExpression => {
    const nodeProvenance = derivedProvenance(
        rule,
        `instantiate ${expression.tag}`,
        witness.provenance
    );
    const instantiate = (
        child: CoreLfCompiledProofExpression,
        childLocalDepth = localDepth
    ): KernelExpression => instantiateCompiledExpression(
        child,
        captures,
        rule,
        witness,
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
                    'INCOMPLETE_PROOF_MATCH',
                    `proofRules.${rule.id}`,
                    `Proof rule '${rule.id}' has no capture for ` +
                        `'${expression.name}'`
                );
            }
            if (capture.sourceDepth !== ambientDepth) {
                return fail(
                    'PROOF_CAPTURE_SCOPE_ESCAPE',
                    `proofRules.${rule.id}`,
                    `Proof rule '${rule.id}' cannot instantiate capture ` +
                        `'${expression.name}' from ambient depth ` +
                        `${capture.sourceDepth} in ambient depth ` +
                        ambientDepth
                );
            }
            try {
                return kernelRemapAmbientIndices(
                    capture.expression,
                    ambientDepth + localDepth,
                    Array.from(
                        { length: ambientDepth },
                        (_, index) => index + localDepth
                    )
                );
            } catch (error: unknown) {
                return fail(
                    'PROOF_CAPTURE_SCOPE_ESCAPE',
                    `proofRules.${rule.id}`,
                    `Proof rule '${rule.id}' cannot move capture ` +
                        `'${expression.name}' beneath ${localDepth} ` +
                        `rule-local binder(s): ${errorText(error)}`,
                    error instanceof Error ? error : undefined
                );
            }
        }
        case 'wildcard':
            return fail(
                'UNSUPPORTED_PROOF_PATTERN',
                `proofRules.${rule.id}`,
                'A wildcard cannot occur in a generated proof constraint'
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const patternMatches = (
    pattern: CoreLfCompiledProofExpression,
    expression: KernelExpression,
    bindings: (CapturedProofValue | undefined)[],
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
            let canonical: KernelExpression;
            try {
                canonical = kernelRemapAmbientIndices(
                    expression,
                    ambientDepth,
                    Array.from(
                        { length: ambientDepth + localDepth },
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

const matchOrientation = (
    left: KernelExpression,
    right: KernelExpression,
    rule: CoreLfCompiledProofRule,
    orientation: CoreLfProofOrientation,
    ambientDepth: number
): InternalProofMatch | undefined => {
    const bindings: (CapturedProofValue | undefined)[] =
        rule.variables.map(() => undefined);
    const firstPattern = orientation === 'forward'
        ? rule.problem.left
        : rule.problem.right;
    const secondPattern = orientation === 'forward'
        ? rule.problem.right
        : rule.problem.left;
    if (
        !patternMatches(
            firstPattern,
            left,
            bindings,
            ambientDepth,
            0
        ) ||
        !patternMatches(
            secondPattern,
            right,
            bindings,
            ambientDepth,
            0
        )
    ) {
        return undefined;
    }
    for (const variable of rule.variables) {
        const binding = bindings[variable.slot];
        if (
            (variable.role === 'matched' && binding === undefined) ||
            (variable.role === 'fresh-constraint' &&
                binding !== undefined)
        ) {
            return fail(
                'INCOMPLETE_PROOF_MATCH',
                `proofRules.${rule.id}`,
                `Proof rule '${rule.id}' produced an invalid ` +
                    `${variable.role} binding for '${variable.name}'`
            );
        }
    }
    return {
        orientation,
        captures: bindings
    };
};

const proofPolicySet = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay
): ReadonlySet<string> => {
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        return fail(
            'INCOMPLETE_PROOF_POLICY',
            'policy',
            'Proof policy targets a foreign transfer module'
        );
    }
    const ids = new Set<string>();
    policy.entries.forEach((entry, index) => {
        if (
            entry.target.kind !== 'proof-rule' ||
            entry.policy !== 'proof-unification'
        ) {
            return fail(
                'INCOMPLETE_PROOF_POLICY',
                `policy.entries[${index}]`,
                'Proof compiler requires proof-unification policy entries'
            );
        }
        if (ids.has(entry.target.id)) {
            return fail(
                'INCOMPLETE_PROOF_POLICY',
                `policy.entries[${index}]`,
                `Duplicate proof policy for '${entry.target.id}'`
            );
        }
        ids.add(entry.target.id);
    });
    const missing = module.proofRules.filter(rule => !ids.has(rule.id));
    if (
        missing.length > 0 ||
        ids.size !== module.proofRules.length
    ) {
        return fail(
            'INCOMPLETE_PROOF_POLICY',
            'policy.entries',
            'Proof policy must cover every rule exactly once'
        );
    }
    return ids;
};

const checkingCaptureValues = (
    references: readonly KernelExpression[]
): readonly CapturedProofValue[] =>
    references.map(expression => ({
        expression,
        sourceDepth: 0
    }));

const substituteProofCheckingAliases = (
    expression: CoreLfCompiledProofExpression,
    aliases:
        ReadonlyMap<number, CoreLfCompiledProofExpression>
): CoreLfCompiledProofExpression => {
    const substitute = (
        child: CoreLfCompiledProofExpression
    ): CoreLfCompiledProofExpression =>
        substituteProofCheckingAliases(child, aliases);

    switch (expression.tag) {
        case 'universe':
        case 'bound':
        case 'reference':
        case 'wildcard':
            return expression;
        case 'capture': {
            const replacement = aliases.get(expression.slot);
            return replacement === undefined
                ? expression
                : substitute(replacement);
        }
        case 'application':
            return deepFreeze({
                ...expression,
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: substitute(argument.value)
                }))
            });
        case 'call':
            return deepFreeze({
                ...expression,
                callee: substitute(expression.callee),
                arguments: expression.arguments.map(argument => ({
                    ...argument,
                    value: substitute(argument.value)
                }))
            });
        case 'pi':
        case 'lambda':
            return deepFreeze({
                ...expression,
                binder: {
                    ...expression.binder,
                    mode: { ...expression.binder.mode },
                    type: substitute(expression.binder.type)
                },
                body: substitute(expression.body)
            });
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const proofCaptureSlots = (
    expression: CoreLfCompiledProofExpression
): readonly number[] => {
    const slots = new Set<number>();
    const visit = (
        current: CoreLfCompiledProofExpression
    ): void => {
        switch (current.tag) {
            case 'universe':
            case 'bound':
            case 'reference':
            case 'wildcard':
                return;
            case 'capture':
                slots.add(current.slot);
                return;
            case 'application':
                current.arguments.forEach(argument =>
                    visit(argument.value)
                );
                return;
            case 'call':
                visit(current.callee);
                current.arguments.forEach(argument =>
                    visit(argument.value)
                );
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type);
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };
    visit(expression);
    return Object.freeze([...slots].sort((left, right) => left - right));
};

const checkingAliasCandidate = (
    constraint: CoreLfCompiledProofProblem,
    constraintIndex: number,
    variables: readonly CoreLfCompiledProofVariable[],
    aliases:
        ReadonlyMap<number, CoreLfCompiledProofExpression>
): CoreLfProofGeneratedConstraintAlias | undefined => {
    const left = substituteProofCheckingAliases(
        constraint.left,
        aliases
    );
    const right = substituteProofCheckingAliases(
        constraint.right,
        aliases
    );
    const candidates = [
        { target: left, replacement: right },
        { target: right, replacement: left }
    ];
    for (const candidate of candidates) {
        if (
            candidate.target.tag !== 'capture' ||
            aliases.has(candidate.target.slot)
        ) {
            continue;
        }
        const targetSlot = candidate.target.slot;
        const replacementSlots =
            proofCaptureSlots(candidate.replacement);
        if (
            replacementSlots.some(
                slot => slot >= targetSlot
            )
        ) {
            continue;
        }
        const variable = variables[targetSlot];
        if (variable === undefined) continue;
        return deepFreeze({
            constraintIndex,
            variableSlot: variable.slot,
            variableName: variable.name,
            replacement: candidate.replacement
        });
    }
    return undefined;
};

const ensureComparable = (
    checker: CoreLfChecker,
    left: KernelExpression,
    right: KernelExpression,
    role: string
): void => {
    const inferredLeft = checker.infer(
        checker.rootContext,
        left
    ).type;
    const inferredRight = checker.infer(
        checker.rootContext,
        right
    ).type;
    if (
        isCoreKind(inferredLeft) ||
        isCoreKind(inferredRight)
    ) {
        if (
            isCoreKind(inferredLeft) &&
            isCoreKind(inferredRight)
        ) {
            return;
        }
        throw new Error(
            `${role} compares a kind-level expression with a term`
        );
    }
    checker.check(
        checker.rootContext,
        right,
        inferredLeft
    );
};

const compileRule = (
    source: CoreLfTransferProofRule,
    context: CoreLfProofDeclarationContext,
    earlierRules: readonly CoreLfCompiledProofRule[],
    comparisonStepLimit: number,
    runtimeProgram: CoreLfCatalogRuntime | undefined,
    typingOracle: CoreLfProofTypingOracle | undefined
): CoreLfCompiledProofRule => {
    const captures = new Map(
        source.variables.map((variable, slot) => [
            variable.name,
            slot
        ])
    );
    const baseState = { context, captures };
    const variables = source.variables.map((variable, slot) => ({
        slot,
        name: variable.name,
        role: variable.role,
        type: compileProofExpression(
            variable.type,
            {
                ...baseState,
                purpose: 'variable-type' as const,
                maximumCaptureSlot: slot - 1
            },
            `proofRules.${source.id}.variables[${slot}].type`
        )
    }));
    const problem = deepFreeze({
        left: compileProofExpression(
            source.problem.left,
            {
                ...baseState,
                purpose: 'pattern',
                maximumCaptureSlot: variables.length - 1
            },
            `proofRules.${source.id}.problem.left`
        ),
        right: compileProofExpression(
            source.problem.right,
            {
                ...baseState,
                purpose: 'pattern',
                maximumCaptureSlot: variables.length - 1
            },
            `proofRules.${source.id}.problem.right`
        )
    });
    const generatedConstraints = source.generatedConstraints.map(
        (constraint, index) => deepFreeze({
            left: compileProofExpression(
                constraint.left,
                {
                    ...baseState,
                    purpose: 'template',
                    maximumCaptureSlot: variables.length - 1
                },
                `proofRules.${source.id}.generatedConstraints[${index}].left`
            ),
            right: compileProofExpression(
                constraint.right,
                {
                    ...baseState,
                    purpose: 'template',
                    maximumCaptureSlot: variables.length - 1
                },
                `proofRules.${source.id}.generatedConstraints[${index}].right`
            )
        })
    );

    let ruleEnvironment = context.environment;
    const checkingReferences: KernelExpression[] = [];
    const checkingNames = variables.map(variable =>
        `proof_${source.order}_${variable.slot}_${variable.name}`
    );
    for (const variable of variables) {
        const checkingName = checkingNames[variable.slot];
        if (ruleEnvironment.lookup(checkingName) !== undefined) {
            return fail(
                'INVALID_PROOF_CONTEXT',
                `proofRules.${source.id}.variables[${variable.slot}]`,
                `Synthetic proof declaration '${checkingName}' collides ` +
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
            const checker = createCoreLfChecker(
                ruleEnvironment,
                comparisonStepLimit,
                runtimeProgram
            );
            const inferredType = checker.infer(
                checker.rootContext,
                type
            ).type;
            if (!isCoreKind(inferredType)) {
                checker.check(
                    checker.rootContext,
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
                'INVALID_PROOF_VARIABLE_TYPE',
                `proofRules.${source.id}.variables[${variable.slot}]`,
                `Proof variable '${variable.name}' has an invalid type: ` +
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
    const witness = kernelUniverse(
        derivedProvenance(source, 'typing witness')
    );
    const checkingEnvironmentWithAliases = (
        aliases:
            ReadonlyMap<number, CoreLfCompiledProofExpression>
    ): CoreLfDeclarationEnvironment => {
        let environment = context.environment;
        const references: KernelExpression[] = [];
        for (const variable of variables) {
            const checkingName = checkingNames[variable.slot];
            const values = checkingCaptureValues(references);
            const type = instantiateCompiledExpression(
                variable.type,
                values,
                source,
                witness,
                0
            );
            const alias = aliases.get(variable.slot);
            const body = alias === undefined
                ? undefined
                : instantiateCompiledExpression(
                    alias,
                    values,
                    source,
                    witness,
                    0
                );
            environment = environment.extend({
                name: checkingName,
                type,
                mode: {
                    plicity: 'explicit',
                    variation: 'functorial'
                },
                provenance: derivedProvenance(
                    source,
                    `variable ${variable.name} checking alias`
                ),
                body,
                transparency:
                    alias === undefined ? 'opaque' : 'transparent'
            });
            references.push(kernelFree(
                checkingName,
                derivedProvenance(
                    source,
                    `variable ${variable.name} checking alias reference`
                )
            ));
        }
        return environment;
    };
    const instantiateChecking = (
        expression: CoreLfCompiledProofExpression
    ): KernelExpression => instantiateCompiledExpression(
        expression,
        checkingValues,
        source,
        witness,
        0
    );
    let typingValidation: CoreLfProofTypingValidation;
    try {
        ensureComparable(
            createCoreLfChecker(
                ruleEnvironment,
                comparisonStepLimit,
                runtimeProgram
            ),
            instantiateChecking(problem.left),
            instantiateChecking(problem.right),
            `Proof rule '${source.id}' problem`
        );
        const checkingAliases =
            new Map<number, CoreLfCompiledProofExpression>();
        const generatedConstraintAliases:
            CoreLfProofGeneratedConstraintAlias[] = [];
        let generatedConstraintEnvironment = ruleEnvironment;
        generatedConstraints.forEach((constraint, index) => {
            ensureComparable(
                createCoreLfChecker(
                    generatedConstraintEnvironment,
                    comparisonStepLimit,
                    runtimeProgram
                ),
                instantiateChecking(constraint.left),
                instantiateChecking(constraint.right),
                `Proof rule '${source.id}' generated constraint ${index}`
            );
            const alias = checkingAliasCandidate(
                constraint,
                index,
                variables,
                checkingAliases
            );
            if (alias === undefined) return;
            checkingAliases.set(
                alias.variableSlot,
                alias.replacement
            );
            generatedConstraintAliases.push(alias);
            generatedConstraintEnvironment =
                checkingEnvironmentWithAliases(checkingAliases);
        });
        typingValidation = deepFreeze({
            kind: 'typescript-checked',
            generatedConstraintAliases
        });
    } catch (error: unknown) {
        if (error instanceof CoreLfProofCompilerError) throw error;
        if (typingOracle?.ruleIds.includes(source.id)) {
            typingValidation = deepFreeze({
                kind: 'external-oracle-required',
                authorityPath: typingOracle.authorityPath,
                evidence: typingOracle.evidence,
                diagnostic: errorText(error)
            });
        } else {
            return fail(
                'INVALID_PROOF_RULE_TYPE',
                `proofRules.${source.id}`,
                `Proof rule '${source.id}' is not well typed: ` +
                    errorText(error),
                error instanceof Error ? error : undefined
            );
        }
    }

    return deepFreeze({
        order: source.order,
        id: source.id,
        sourceOwner: { ...source.sourceOwner },
        variables,
        problem,
        generatedConstraints,
        checkedWithEarlierRuleIds: earlierRules.map(rule => rule.id),
        typingValidation,
        provenance: derivedProvenance(source, 'compiled')
    });
};

const validateTypingOracle = (
    module: CoreLfModuleSpec,
    oracle: CoreLfProofTypingOracle | undefined
): void => {
    if (oracle === undefined) return;
    if (
        oracle.authorityPath !== module.authorityPath ||
        oracle.evidence.trim().length === 0
    ) {
        return fail(
            'INVALID_PROOF_TYPING_ORACLE',
            'options.typingOracle',
            'A proof typing oracle must name the module authority path and ' +
                'nonempty reviewed evidence'
        );
    }
    const known = new Map(
        module.proofRules.map(rule => [rule.id, rule.order])
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
                'INVALID_PROOF_TYPING_ORACLE',
                `options.typingOracle.ruleIds[${index}]`,
                'Proof typing-oracle IDs must be unique, known, and in ' +
                    'module order'
            );
        }
        seen.add(id);
        previousOrder = order;
    });
};

class DirectAssignmentRollback extends Error {
    constructor(public readonly step: CoreConstraintStep) {
        super('rollback non-solving direct assignment');
    }
}

const freezeTrace = (
    trace: readonly CoreLfProofComparisonTraceEntry[]
): readonly CoreLfProofComparisonTraceEntry[] =>
    Object.freeze(trace.map(entry => deepFreeze({ ...entry })));

const freezeApplication = (
    application: CoreLfProofRuleApplication
): CoreLfProofRuleApplication => deepFreeze({
    ...application,
    bindings: application.bindings.map(binding => ({ ...binding })),
    freshMetavariables: application.freshMetavariables.map(
        fresh => ({ ...fresh })
    ),
    generatedProblems: application.generatedProblems.map(
        problem => ({ ...problem })
    )
});

/**
 * One immutable proof-only program. It owns no mutable rule registry and has
 * no evaluator interface.
 */
export class CoreLfCompiledProofProgram {
    readonly revision: string;
    readonly rules: readonly CoreLfCompiledProofRule[];
    readonly ruleIds: readonly string[];

    constructor(
        public readonly module: CoreLfModuleSpec,
        public readonly policy: CoreLfTransferPolicyOverlay,
        public readonly declarations: CoreLfProofDeclarationContext,
        rules: readonly CoreLfCompiledProofRule[],
        public readonly comparisonStepLimit =
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
        public readonly runtimeProgram?: CoreLfCatalogRuntime
    ) {
        this.revision = `${module.revision}+${policy.revision}`;
        this.rules = Object.freeze(rules.map(rule => deepFreeze({
            ...rule,
            sourceOwner: { ...rule.sourceOwner },
            variables: rule.variables.map(variable => ({ ...variable })),
            generatedConstraints: rule.generatedConstraints.map(
                constraint => ({ ...constraint })
            ),
            checkedWithEarlierRuleIds: [
                ...rule.checkedWithEarlierRuleIds
            ]
        })));
        this.ruleIds = Object.freeze(this.rules.map(rule => rule.id));
        Object.freeze(this);
    }

    rule(id: string): CoreLfCompiledProofRule | undefined {
        return this.rules.find(rule => rule.id === id);
    }

    private sourceRule(
        rule: CoreLfCompiledProofRule
    ): CoreLfTransferProofRule {
        const source = this.module.proofRules.find(
            candidate => candidate.id === rule.id
        );
        if (source === undefined) {
            return fail(
                'INVALID_PROOF_CONTEXT',
                `proofRules.${rule.id}`,
                `Compiled proof rule '${rule.id}' has no source record`
            );
        }
        return source;
    }

    private applyMatch(
        context: CoreContext,
        session: CoreElaborationSession,
        left: KernelExpression,
        rule: CoreLfCompiledProofRule,
        ruleIndex: number,
        match: InternalProofMatch
    ): CoreLfProofRuleApplication {
        const source = this.sourceRule(rule);
        const captures = [...match.captures];
        const freshMetavariables: {
            name: string;
            meta: KernelMetaVariable;
        }[] = [];
        for (const variable of rule.variables) {
            if (variable.role !== 'fresh-constraint') continue;
            const type = instantiateCompiledExpression(
                variable.type,
                captures,
                source,
                left,
                context.depth
            );
            context.assertScoped(type);
            const meta = session.freshMeta(
                context,
                type,
                derivedProvenance(
                    source,
                    `fresh constraint ${variable.name}`,
                    left.provenance
                )
            );
            captures[variable.slot] = {
                expression: meta,
                sourceDepth: context.depth
            };
            freshMetavariables.push({
                name: variable.name,
                meta
            });
        }
        const generatedProblems = rule.generatedConstraints.map(
            constraint => {
                const problem = {
                    left: instantiateCompiledExpression(
                        constraint.left,
                        captures,
                        source,
                        left,
                        context.depth
                    ),
                    right: instantiateCompiledExpression(
                        constraint.right,
                        captures,
                        source,
                        left,
                        context.depth
                    )
                };
                context.assertScoped(problem.left);
                context.assertScoped(problem.right);
                return problem;
            }
        );
        const bindings = rule.variables
            .filter(variable => variable.role === 'matched')
            .map(variable => {
                const capture = captures[variable.slot];
                if (capture === undefined) {
                    return fail(
                        'INCOMPLETE_PROOF_MATCH',
                        `proofRules.${rule.id}`,
                        `Proof rule '${rule.id}' did not bind matched ` +
                            `variable '${variable.name}'`
                    );
                }
                return {
                    name: variable.name,
                    value: capture.expression
                };
            });
        return freezeApplication({
            ruleId: rule.id,
            ruleIndex,
            orientation: match.orientation,
            bindings,
            freshMetavariables,
            generatedProblems
        });
    }

    compare(
        left: KernelExpression,
        right: KernelExpression,
        options: CoreLfProofComparisonOptions = {}
    ): CoreLfProofComparisonResult {
        return this.compareAt(
            CoreContext.empty(
                this.declarations.environment.coreEnvironment
            ),
            left,
            right,
            options
        );
    }

    compareAt(
        context: CoreContext,
        leftInput: KernelExpression,
        rightInput: KernelExpression,
        options: CoreLfProofComparisonOptions = {}
    ): CoreLfProofComparisonResult {
        if (
            context.environment !==
                this.declarations.environment.coreEnvironment
        ) {
            return fail(
                'INVALID_PROOF_CONTEXT',
                'context',
                'Proof comparison context belongs to a foreign declaration ' +
                    'environment'
            );
        }
        context.assertScoped(leftInput);
        context.assertScoped(rightInput);
        const stepLimit =
            options.stepLimit ?? this.comparisonStepLimit;
        if (
            !Number.isSafeInteger(stepLimit) ||
            stepLimit < 0
        ) {
            return fail(
                'INVALID_PROOF_STEP_LIMIT',
                'options.stepLimit',
                'Proof comparison budget must be a nonnegative safe integer'
            );
        }
        const session = options.session ??
            new CoreElaborationSession(context.environment);
        if (session.environment !== context.environment) {
            return fail(
                'INVALID_PROOF_CONTEXT',
                'options.session',
                'Proof comparison session belongs to a foreign declaration ' +
                    'environment'
            );
        }

        const queue: PendingProofProblem[] = [{
            id: 0,
            left: leftInput,
            right: rightInput
        }];
        let nextProblemId = 1;
        let steps = 0;
        const trace: CoreLfProofComparisonTraceEntry[] = [];
        const applications: CoreLfProofRuleApplication[] = [];
        const resolutionOrder: number[] = [];

        const base = (): CoreLfProofComparisonBase => ({
            steps,
            trace: freezeTrace(trace),
            ruleApplications: Object.freeze(
                applications.map(freezeApplication)
            ),
            resolutionOrder: Object.freeze([...resolutionOrder]),
            metavariables: Object.freeze([...session.metavariables])
        });

        const appendReductions = (
            problemId: number,
            side: 'left' | 'right',
            reductions: readonly CoreLfCombinedTraceEntry[]
        ): void => {
            reductions.forEach(reduction => {
                trace.push(deepFreeze({
                    step: steps,
                    kind: 'reduction' as const,
                    problemId,
                    side,
                    reduction
                }));
                steps++;
            });
        };

        while (queue.length > 0) {
            const pending = queue.shift()!;
            const leftHead = coreLfCombinedWeakHead(
                this.declarations.environment,
                pending.left,
                stepLimit - steps,
                session,
                this.runtimeProgram
            );
            appendReductions(
                pending.id,
                'left',
                leftHead.trace
            );
            if (leftHead.status === 'step-limit-exceeded') {
                return Object.freeze({
                    status: 'step-limit-exceeded',
                    problemId: pending.id,
                    left: leftHead.expression,
                    right: pending.right,
                    next: {
                        kind: 'conversion' as const,
                        side: 'left' as const,
                        next: leftHead.next
                    },
                    ...base()
                });
            }
            if (leftHead.status === 'stuck') {
                return Object.freeze({
                    status: 'stuck',
                    problemId: pending.id,
                    left: leftHead.expression,
                    right: pending.right,
                    reason: 'plicity-mismatch',
                    ...base()
                });
            }

            const rightHead = coreLfCombinedWeakHead(
                this.declarations.environment,
                pending.right,
                stepLimit - steps,
                session,
                this.runtimeProgram
            );
            appendReductions(
                pending.id,
                'right',
                rightHead.trace
            );
            if (rightHead.status === 'step-limit-exceeded') {
                return Object.freeze({
                    status: 'step-limit-exceeded',
                    problemId: pending.id,
                    left: leftHead.expression,
                    right: rightHead.expression,
                    next: {
                        kind: 'conversion' as const,
                        side: 'right' as const,
                        next: rightHead.next
                    },
                    ...base()
                });
            }
            if (rightHead.status === 'stuck') {
                return Object.freeze({
                    status: 'stuck',
                    problemId: pending.id,
                    left: leftHead.expression,
                    right: rightHead.expression,
                    reason: 'plicity-mismatch',
                    ...base()
                });
            }

            const left = leftHead.expression;
            const right = rightHead.expression;
            if (kernelExpressionEquals(left, right)) {
                resolutionOrder.push(pending.id);
                continue;
            }

            if (left.tag === 'meta' || right.tag === 'meta') {
                if (steps === stepLimit) {
                    return Object.freeze({
                        status: 'step-limit-exceeded',
                        problemId: pending.id,
                        left,
                        right,
                        next: {
                            kind: 'meta-assignment' as const
                        },
                        ...base()
                    });
                }
                try {
                    const assignment = session.withTransaction(() => {
                        const constraint = session.addConstraint(
                            context,
                            left,
                            right,
                            provenance(
                                'derived',
                                `proof problem ${pending.id} direct assignment`
                            )
                        );
                        const step =
                            session.stepConstraint(constraint.id);
                        if (step.outcome !== 'solved') {
                            throw new DirectAssignmentRollback(step);
                        }
                        return step;
                    });
                    trace.push(deepFreeze({
                        step: steps,
                        kind: 'meta-assignment' as const,
                        problemId: pending.id,
                        reason: assignment.reason
                    }));
                    steps++;
                    resolutionOrder.push(pending.id);
                    continue;
                } catch (error: unknown) {
                    if (!(error instanceof DirectAssignmentRollback)) {
                        throw error;
                    }
                    if (error.step.outcome === 'rejected') {
                        return Object.freeze({
                            status: 'stuck',
                            problemId: pending.id,
                            left,
                            right,
                            reason: 'meta-assignment-rejected',
                            constraintReason: error.step.reason,
                            ...base()
                        });
                    }
                }
            }

            const conversion = coreLfDefinitionalCompare(
                this.declarations.environment,
                left,
                right,
                stepLimit - steps,
                session,
                this.runtimeProgram
            );
            conversion.trace.forEach(entry =>
                appendReductions(
                    pending.id,
                    entry.side,
                    [entry.reduction]
                )
            );
            if (conversion.status === 'equal') {
                resolutionOrder.push(pending.id);
                continue;
            }
            if (conversion.status === 'step-limit-exceeded') {
                return Object.freeze({
                    status: 'step-limit-exceeded',
                    problemId: pending.id,
                    left,
                    right,
                    next: {
                        kind: 'conversion' as const,
                        side: conversion.side,
                        next: conversion.next
                    },
                    ...base()
                });
            }

            let selected:
                | {
                    readonly rule: CoreLfCompiledProofRule;
                    readonly ruleIndex: number;
                    readonly match: InternalProofMatch;
                }
                | undefined;
            for (
                let ruleIndex = 0;
                ruleIndex < this.rules.length;
                ruleIndex++
            ) {
                const rule = this.rules[ruleIndex];
                const forward = matchOrientation(
                    left,
                    right,
                    rule,
                    'forward',
                    context.depth
                );
                if (forward !== undefined) {
                    selected = { rule, ruleIndex, match: forward };
                    break;
                }
                const symmetric = matchOrientation(
                    left,
                    right,
                    rule,
                    'symmetric',
                    context.depth
                );
                if (symmetric !== undefined) {
                    selected = { rule, ruleIndex, match: symmetric };
                    break;
                }
            }
            if (selected === undefined) {
                return Object.freeze({
                    status: 'stuck',
                    problemId: pending.id,
                    left,
                    right,
                    reason: 'no-proof-rule',
                    mismatch: conversion.mismatch,
                    ...base()
                });
            }
            if (steps === stepLimit) {
                return Object.freeze({
                    status: 'step-limit-exceeded',
                    problemId: pending.id,
                    left,
                    right,
                    next: {
                        kind: 'proof-rule' as const,
                        ruleId: selected.rule.id,
                        orientation: selected.match.orientation
                    },
                    ...base()
                });
            }

            const application = this.applyMatch(
                context,
                session,
                left,
                selected.rule,
                selected.ruleIndex,
                selected.match
            );
            const generatedPending =
                application.generatedProblems.map(problem => ({
                    id: nextProblemId++,
                    left: problem.left,
                    right: problem.right
                }));
            trace.push(deepFreeze({
                step: steps,
                kind: 'proof-rule' as const,
                problemId: pending.id,
                ruleId: application.ruleId,
                ruleIndex: application.ruleIndex,
                orientation: application.orientation,
                generatedProblemIds:
                    generatedPending.map(problem => problem.id)
            }));
            steps++;
            applications.push(application);
            resolutionOrder.push(pending.id);
            queue.unshift(...generatedPending);
        }

        return Object.freeze({
            status: 'solved',
            left: session.zonk(leftInput),
            right: session.zonk(rightInput),
            ...base()
        });
    }
}

export interface CoreLfProofProgramCompositionOptions {
    /**
     * One explicit budget for the composed queue. If omitted, every source
     * program must already carry the same limit.
     */
    readonly comparisonStepLimit?: number;
    /**
     * Runtime visible when the completed proof program is executed. Every
     * source program's exact compile-time runtime must be an immutable prefix
     * of this program. When omitted, the first source runtime is used.
     */
    readonly executionRuntimeProgram?: CoreLfCatalogRuntime;
}

export interface CoreLfComposedProofPhase {
    readonly index: number;
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly ruleIds: readonly string[];
    readonly precedingRuleIds: readonly string[];
}

/**
 * Immutable composition of source-separated proof programs.
 *
 * Source programs retain their exact compilation evidence. The executable
 * view flattens their rules once, preserving source priority, one comparison
 * queue, one metavariable session, and one step budget. It uses one explicit
 * completed-signature runtime that must extend every exact source-time
 * runtime by immutable fragment identity.
 */
export class CoreLfComposedProofProgram {
    readonly revision: string;
    readonly phases: readonly CoreLfComposedProofPhase[];
    readonly rules: readonly CoreLfCompiledProofRule[];
    readonly ruleIds: readonly string[];
    readonly comparisonStepLimit: number;

    constructor(
        public readonly programs:
            readonly CoreLfCompiledProofProgram[],
        public readonly program: CoreLfCompiledProofProgram
    ) {
        const precedingRuleIds: string[] = [];
        this.phases = Object.freeze(programs.map(
            (source, index) => {
                const phase = deepFreeze({
                    index,
                    moduleId: source.module.moduleId,
                    fragmentId: source.module.fragmentId,
                    ruleIds: [...source.ruleIds],
                    precedingRuleIds: [...precedingRuleIds]
                });
                precedingRuleIds.push(...source.ruleIds);
                return phase;
            }
        ));
        this.revision = [
            'composed-proof-1',
            ...programs.map(source =>
                `${source.module.moduleId}/` +
                `${source.module.fragmentId}@${source.revision}`
            ),
            `runtime@${program.runtimeProgram?.revision ?? 'none'}`,
            `budget@${program.comparisonStepLimit}`
        ].join('+');
        this.rules = program.rules;
        this.ruleIds = program.ruleIds;
        this.comparisonStepLimit = program.comparisonStepLimit;
        Object.freeze(this);
    }

    get declarations(): CoreLfProofDeclarationContext {
        return this.program.declarations;
    }

    get runtimeProgram(): CoreLfCatalogRuntime | undefined {
        return this.program.runtimeProgram;
    }

    rule(id: string): CoreLfCompiledProofRule | undefined {
        return this.program.rule(id);
    }

    compare(
        left: KernelExpression,
        right: KernelExpression,
        options: CoreLfProofComparisonOptions = {}
    ): CoreLfProofComparisonResult {
        return this.program.compare(left, right, options);
    }

    compareAt(
        context: CoreContext,
        left: KernelExpression,
        right: KernelExpression,
        options: CoreLfProofComparisonOptions = {}
    ): CoreLfProofComparisonResult {
        return this.program.compareAt(
            context,
            left,
            right,
            options
        );
    }
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const proofCompositionModule = (
    programs: readonly CoreLfCompiledProofProgram[]
): CoreLfModuleSpec => {
    const first = programs[0].module;
    const externalByKey = new Map<
        string,
        CoreLfTransferExternalSymbol
    >();
    const proofRules: CoreLfTransferProofRule[] = [];
    let previousOrder = -1;
    const ruleIds = new Set<string>();

    programs.forEach((program, programIndex) => {
        const module = program.module;
        if (
            module.moduleId !== first.moduleId ||
            module.authorityPath !== first.authorityPath ||
            module.sourceSha256 !== first.sourceSha256 ||
            !sameData(module.dependencies, first.dependencies) ||
            !sameData(module.canonicalExport, first.canonicalExport)
        ) {
            fail(
                'INVALID_PROOF_COMPOSITION',
                `programs[${programIndex}].module`,
                'Composed proof phases must come from one pinned source ' +
                    'module and dependency view'
            );
        }
        if (
            program.rules.length !== module.proofRules.length ||
            program.ruleIds.some(
                (id, index) => id !== module.proofRules[index].id
            )
        ) {
            fail(
                'INVALID_PROOF_COMPOSITION',
                `programs[${programIndex}].rules`,
                'Compiled proof phase does not preserve its source rules'
            );
        }
        module.externalSymbols.forEach((external, externalIndex) => {
            const key = symbolKey(external.symbol);
            const existing = externalByKey.get(key);
            if (
                existing !== undefined &&
                existing.availability !== external.availability
            ) {
                fail(
                    'INVALID_PROOF_COMPOSITION',
                    `programs[${programIndex}].module.externalSymbols[` +
                        `${externalIndex}]`,
                    `Proof phases disagree on availability of ` +
                        `'${displaySymbol(external.symbol)}'`
                );
            }
            externalByKey.set(key, external);
        });
        module.proofRules.forEach((rule, ruleIndex) => {
            if (
                rule.order <= previousOrder ||
                ruleIds.has(rule.id)
            ) {
                fail(
                    'INVALID_PROOF_COMPOSITION',
                    `programs[${programIndex}].module.proofRules[` +
                        `${ruleIndex}]`,
                    'Composed proof rules must have unique IDs and strict ' +
                        'global source order'
                );
            }
            previousOrder = rule.order;
            ruleIds.add(rule.id);
            proofRules.push(rule);
        });
    });

    return createCoreLfModuleSpec({
        revision: `${first.revision}+proof-composition-1`,
        moduleId: first.moduleId,
        fragmentId: `${first.fragmentId}-proof-composition`,
        authorityPath: first.authorityPath,
        sourceSha256: first.sourceSha256,
        ...(first.canonicalExport === undefined
            ? {}
            : { canonicalExport: first.canonicalExport }),
        dependencies: first.dependencies,
        externalSymbols: [...externalByKey.values()],
        declarations: [],
        inductives: [],
        runtimeRules: [],
        proofRules
    });
};

/**
 * Compose one or more already checked proof phases under one exact
 * completed-signature runtime and one comparison budget.
 */
export function composeCoreLfProofPrograms(
    programs: readonly CoreLfCompiledProofProgram[],
    declarations: CoreLfProofDeclarationContext,
    options: CoreLfProofProgramCompositionOptions = {}
): CoreLfComposedProofProgram {
    if (programs.length === 0) {
        return fail(
            'INVALID_PROOF_COMPOSITION',
            'programs',
            'Proof composition requires at least one source program'
        );
    }
    const runtimeProgram =
        options.executionRuntimeProgram ??
        programs[0].runtimeProgram;
    programs.forEach((program, programIndex) => {
        if (
            !coreLfRuntimeHasExactPrefix(
                runtimeProgram,
                program.runtimeProgram
            )
        ) {
            fail(
                'INVALID_PROOF_COMPOSITION',
                `programs[${programIndex}].runtimeProgram`,
                'Completed proof runtime does not extend the exact ' +
                    `source-time prefix of phase ${programIndex}`
            );
        }
    });
    const sourceLimits = new Set(
        programs.map(program => program.comparisonStepLimit)
    );
    if (
        options.comparisonStepLimit === undefined &&
        sourceLimits.size !== 1
    ) {
        return fail(
            'INVALID_PROOF_COMPOSITION',
            'programs.comparisonStepLimit',
            'Proof phases have different budgets and no composed budget'
        );
    }
    const comparisonStepLimit =
        options.comparisonStepLimit ??
        programs[0].comparisonStepLimit;
    if (
        !Number.isSafeInteger(comparisonStepLimit) ||
        comparisonStepLimit < 0
    ) {
        return fail(
            'INVALID_PROOF_COMPOSITION',
            'options.comparisonStepLimit',
            'Composed proof budget must be a nonnegative safe integer'
        );
    }

    const module = proofCompositionModule(programs);
    module.referencedSymbols.forEach((symbol, index) => {
        const declaration = declarations.declaration(symbol);
        if (
            declaration === undefined ||
            declaration.status === 'excluded'
        ) {
            fail(
                'INVALID_PROOF_COMPOSITION',
                `module.referencedSymbols[${index}]`,
                `Final declaration context does not resolve ` +
                    `'${displaySymbol(symbol)}'`
            );
        }
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: `${module.revision}+policy-1`,
        moduleRevision: module.revision,
        entries: programs.flatMap(program =>
            program.policy.entries
        ).map((entry, order) => ({
            ...entry,
            order
        }))
    });
    const executable = new CoreLfCompiledProofProgram(
        module,
        policy,
        declarations,
        programs.flatMap(program => program.rules),
        comparisonStepLimit,
        runtimeProgram
    );
    return new CoreLfComposedProofProgram(
        Object.freeze([...programs]),
        executable
    );
}

/**
 * Compile and type-check a proof-only transfer fragment.
 */
export function compileCoreLfProofProgram(
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    context: CoreLfProofDeclarationContext,
    options: CoreLfProofCompilerOptions = {}
): CoreLfCompiledProofProgram {
    if (
        module.declarations.length > 0 ||
        module.inductives.length > 0 ||
        module.runtimeRules.length > 0
    ) {
        return fail(
            'UNSUPPORTED_MODULE_CONTENT',
            'module',
            'Proof compiler accepts a proof-only module fragment'
        );
    }
    proofPolicySet(module, policy);
    validateTypingOracle(module, options.typingOracle);
    const comparisonStepLimit =
        options.comparisonStepLimit ??
        CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT;
    if (
        !Number.isSafeInteger(comparisonStepLimit) ||
        comparisonStepLimit < 0
    ) {
        return fail(
            'INVALID_PROOF_STEP_LIMIT',
            'options.comparisonStepLimit',
            'Proof comparison budget must be a nonnegative safe integer'
        );
    }

    const externalKeys = new Set(
        module.externalSymbols.map(external =>
            symbolKey(external.symbol)
        )
    );
    for (const symbol of module.referencedSymbols) {
        const declaration = context.declaration(symbol);
        if (
            !externalKeys.has(symbolKey(symbol)) ||
            declaration === undefined ||
            declaration.status === 'excluded'
        ) {
            return fail(
                'INVALID_PROOF_CONTEXT',
                'module.referencedSymbols',
                `Proof declaration context does not resolve ` +
                    `'${displaySymbol(symbol)}'`
            );
        }
    }

    const rules: CoreLfCompiledProofRule[] = [];
    for (const source of module.proofRules) {
        rules.push(compileRule(
            source,
            context,
            rules,
            comparisonStepLimit,
            options.runtimeProgram,
            options.typingOracle
        ));
    }
    const usedOracleRuleIds = rules
        .filter(rule =>
            rule.typingValidation.kind ===
                'external-oracle-required'
        )
        .map(rule => rule.id);
    const requestedOracleRuleIds =
        options.typingOracle?.ruleIds ?? [];
    if (
        usedOracleRuleIds.length !== requestedOracleRuleIds.length ||
        usedOracleRuleIds.some(
            (id, index) => id !== requestedOracleRuleIds[index]
        )
    ) {
        return fail(
            'INVALID_PROOF_TYPING_ORACLE',
            'options.typingOracle.ruleIds',
            'Every proof typing-oracle exception must be necessary under ' +
                'the current TypeScript checker'
        );
    }
    return new CoreLfCompiledProofProgram(
        module,
        policy,
        context,
        rules,
        comparisonStepLimit,
        options.runtimeProgram
    );
}
