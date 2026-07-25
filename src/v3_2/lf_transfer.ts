/**
 * Shared immutable transfer IR and typed construction boundary for SCALE-0B.
 *
 * The IR is independent of Lambdapi syntax and semantic owner names. It can
 * be constructed directly with the scoped TypeScript builder and may later
 * be produced by a separately reviewed acquisition adapter.
 */

import {
    BinderMode,
    Plicity,
    assertSafeIdentifier,
    binderMode
} from './kernel';
import {
    validateCoreLfScaleArchitectureReview
} from './scale_architecture_review';

export interface CoreLfQualifiedSymbol {
    readonly moduleId: string;
    readonly name: string;
}

export interface CoreLfTransferArgument {
    readonly plicity: Plicity;
    readonly value: CoreLfTransferExpression;
}

export interface CoreLfTransferBinder {
    readonly hint: string;
    readonly mode: BinderMode;
    readonly type: CoreLfTransferExpression;
}

/**
 * One shared syntax covers declarations, runtime patterns/templates, and
 * proof-time problems. Context-specific validation rejects `capture` and
 * `wildcard` nodes wherever they are not meaningful.
 */
export type CoreLfTransferExpression =
    | {
        readonly tag: 'type';
    }
    | {
        readonly tag: 'bound';
        readonly index: number;
    }
    | {
        readonly tag: 'global';
        readonly symbol: CoreLfQualifiedSymbol;
    }
    | {
        readonly tag: 'call';
        readonly callee: CoreLfTransferExpression;
        readonly arguments: readonly CoreLfTransferArgument[];
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly binder: CoreLfTransferBinder;
        readonly body: CoreLfTransferExpression;
    }
    | {
        readonly tag: 'capture';
        readonly name: string;
        /**
         * Undefined retains the rule engine's ordinary contextual scope.
         * An explicit list models restricted higher-order pattern scope.
         */
        readonly allowedBoundIndices?: readonly number[];
    }
    | {
        readonly tag: 'wildcard';
    };

export type CoreLfTransferBody =
    | {
        readonly kind: 'absent';
    }
    | {
        readonly kind: 'explicit-term';
        readonly term: CoreLfTransferExpression;
    }
    | {
        readonly kind: 'checked-tactic-source';
        readonly canonicalSource: string;
    };

export type CoreLfTransferVisibility =
    | 'public'
    | 'protected'
    | 'private';

export type CoreLfTransferRigidity =
    | 'ordinary'
    | 'constant'
    | 'injective';

export interface CoreLfTransferModifiers {
    readonly visibility: CoreLfTransferVisibility;
    readonly rigidity: CoreLfTransferRigidity;
    readonly sourceOpacity: 'transparent' | 'opaque';
    readonly generatedBy?: CoreLfQualifiedSymbol;
}

export interface CoreLfTransferProvenance {
    readonly authorityPath: string;
    readonly sourceFragment: string;
    readonly canonicalCommandOrdinal?: number;
}

export interface CoreLfTransferDeclaration {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly type: CoreLfTransferExpression;
    readonly body: CoreLfTransferBody;
    readonly modifiers: CoreLfTransferModifiers;
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfTransferTelescopeBinder {
    readonly hint: string;
    readonly mode: BinderMode;
    /**
     * Locally nameless type at the depth of all earlier telescope binders.
     */
    readonly type: CoreLfTransferExpression;
}

export interface CoreLfTransferConstructor {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    /**
     * Optional constructor-local modes for the inductive parameters.
     * Lambdapi permits a constructor to expose a parameter with different
     * plicity while its result still applies the inductive head according to
     * the head's parameter plicity.
     */
    readonly parameterModes?: readonly BinderMode[];
    readonly binders: readonly CoreLfTransferTelescopeBinder[];
    readonly result: CoreLfTransferExpression;
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfTransferInductiveBlock {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly parameters: readonly CoreLfTransferTelescopeBinder[];
    readonly indices: readonly CoreLfTransferTelescopeBinder[];
    readonly sort: CoreLfTransferExpression;
    readonly constructors: readonly CoreLfTransferConstructor[];
    readonly generatedSymbols: readonly CoreLfQualifiedSymbol[];
    readonly modifiers: CoreLfTransferModifiers;
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfTransferRuleVariable {
    readonly name: string;
    readonly type: CoreLfTransferExpression;
}

export interface CoreLfTransferRuntimeRule {
    readonly order: number;
    readonly id: string;
    readonly groupId: string;
    readonly clauseOrder: number;
    readonly sourceOwner: CoreLfQualifiedSymbol;
    readonly variables: readonly CoreLfTransferRuleVariable[];
    readonly left: CoreLfTransferExpression;
    readonly right: CoreLfTransferExpression;
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfTransferProofVariable
    extends CoreLfTransferRuleVariable {
    readonly role: 'matched' | 'fresh-constraint';
}

export interface CoreLfTransferProofProblem {
    readonly left: CoreLfTransferExpression;
    readonly right: CoreLfTransferExpression;
}

export interface CoreLfTransferProofRule {
    readonly order: number;
    readonly id: string;
    readonly sourceOwner: CoreLfQualifiedSymbol;
    readonly variables: readonly CoreLfTransferProofVariable[];
    readonly problem: CoreLfTransferProofProblem;
    readonly generatedConstraints:
        readonly CoreLfTransferProofProblem[];
    readonly provenance: CoreLfTransferProvenance;
}

export type CoreLfTransferExternalAvailability =
    | 'dependency-module'
    | 'existing-core'
    | 'earlier-fragment';

export interface CoreLfTransferExternalSymbol {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly availability: CoreLfTransferExternalAvailability;
}

export interface CoreLfCanonicalExportEvidence {
    readonly exporterVersion: string;
    readonly sha256: string;
}

export interface CoreLfModuleSpecInput {
    readonly revision: string;
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport?: CoreLfCanonicalExportEvidence;
    readonly dependencies: readonly string[];
    readonly externalSymbols: readonly CoreLfTransferExternalSymbol[];
    readonly declarations: readonly CoreLfTransferDeclaration[];
    readonly inductives: readonly CoreLfTransferInductiveBlock[];
    readonly runtimeRules: readonly CoreLfTransferRuntimeRule[];
    readonly proofRules: readonly CoreLfTransferProofRule[];
}

export interface CoreLfModuleSpec extends CoreLfModuleSpecInput {
    readonly referencedSymbols: readonly CoreLfQualifiedSymbol[];
}

export type CoreLfTransferPolicyClass =
    | 'opaque-signature'
    | 'checked-transparent-definition'
    | 'runtime-rewrite'
    | 'proof-unification'
    | 'theorem-body'
    | 'conformance-only'
    | 'excluded';

export type CoreLfTransferPolicyTarget =
    | {
        readonly kind: 'declaration' | 'inductive';
        readonly symbol: CoreLfQualifiedSymbol;
    }
    | {
        readonly kind: 'runtime-rule' | 'proof-rule';
        readonly id: string;
    };

export interface CoreLfTransferPolicyEntry {
    readonly order: number;
    readonly target: CoreLfTransferPolicyTarget;
    readonly policy: CoreLfTransferPolicyClass;
    readonly evidence: string;
}

export interface CoreLfTransferPolicyOverlayInput {
    readonly revision: string;
    readonly moduleRevision: string;
    readonly entries: readonly CoreLfTransferPolicyEntry[];
}

export interface CoreLfTransferPolicyOverlay
    extends CoreLfTransferPolicyOverlayInput {
    readonly moduleId: string;
    readonly fragmentId: string;
}

export type CoreLfTransferErrorCode =
    | 'INVALID_IDENTIFIER'
    | 'INVALID_HASH'
    | 'INVALID_PATH'
    | 'INVALID_ORDER'
    | 'DUPLICATE_IDENTITY'
    | 'INVALID_BUILDER_EXPRESSION'
    | 'FOREIGN_BUILDER_EXPRESSION'
    | 'ESCAPED_BINDER_TOKEN'
    | 'INVALID_EXPRESSION'
    | 'INVALID_SCOPE'
    | 'INVALID_CAPTURE'
    | 'INVALID_BODY'
    | 'INVALID_PROVENANCE'
    | 'INVALID_DEPENDENCY'
    | 'UNRESOLVED_GLOBAL'
    | 'INVALID_RULE'
    | 'INVALID_POLICY';

export class CoreLfTransferError extends Error {
    constructor(
        public readonly code: CoreLfTransferErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfTransferError';
    }
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const REVISION_ID = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const RULE_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;
const SHA256 = /^sha256:[0-9a-f]{64}$/u;

const fail = (
    code: CoreLfTransferErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfTransferError(code, path, message);
};

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

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) {
        return value.map(cloneData) as T;
    }
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value as Record<string, unknown>).map(
                ([key, entry]) => [key, cloneData(entry)]
            )
        ) as T;
    }
    return value;
};

const validateModuleId = (value: string, path: string): void => {
    if (!MODULE_ID.test(value)) {
        fail(
            'INVALID_IDENTIFIER',
            path,
            `Invalid Core LF transfer module ID '${value}'`
        );
    }
};

const validateRevision = (value: string, path: string): void => {
    if (!REVISION_ID.test(value)) {
        fail(
            'INVALID_IDENTIFIER',
            path,
            `Invalid Core LF transfer revision '${value}'`
        );
    }
};

const validateRuleId = (value: string, path: string): void => {
    if (!RULE_ID.test(value)) {
        fail(
            'INVALID_IDENTIFIER',
            path,
            `Invalid Core LF transfer rule ID '${value}'`
        );
    }
};

const validateSymbolName = (value: string, path: string): void => {
    if (
        value.length === 0 ||
        value.trim() !== value ||
        /[\s\u0000-\u001f\u007f]/u.test(value)
    ) {
        fail(
            'INVALID_IDENTIFIER',
            path,
            `Invalid Core LF transfer symbol name '${value}'`
        );
    }
};

const validateBinderHint = (value: string, path: string): void => {
    try {
        assertSafeIdentifier(value, 'Core LF transfer binder hint');
    } catch (error: unknown) {
        fail(
            'INVALID_IDENTIFIER',
            path,
            error instanceof Error
                ? error.message
                : `Invalid Core LF transfer binder hint '${value}'`
        );
    }
};

const validateCaptureName = (value: string, path: string): void => {
    if (!/^[A-Za-z][A-Za-z0-9_]*$/u.test(value)) {
        fail(
            'INVALID_IDENTIFIER',
            path,
            `Invalid Core LF transfer capture name '${value}'`
        );
    }
};

const validatePath = (value: string, path: string): void => {
    if (
        value.length === 0 ||
        value.startsWith('/') ||
        value.includes('\\') ||
        value.split('/').some(segment =>
            segment.length === 0 ||
            segment === '.' ||
            segment === '..'
        )
    ) {
        fail(
            'INVALID_PATH',
            path,
            `Core LF transfer authority path must be a normalized ` +
                `repository-relative path; received '${value}'`
        );
    }
};

const validateSha256 = (value: string, path: string): void => {
    if (!SHA256.test(value)) {
        fail(
            'INVALID_HASH',
            path,
            `Core LF transfer hash must be 'sha256:' followed by 64 ` +
                `lowercase hexadecimal characters`
        );
    }
};

const validateOrder = (value: number, path: string): void => {
    if (!Number.isSafeInteger(value) || value < 0) {
        fail(
            'INVALID_ORDER',
            path,
            `Core LF transfer order must be a nonnegative safe integer`
        );
    }
};

const validateMode = (mode: BinderMode, path: string): void => {
    if (
        (mode.plicity !== 'explicit' && mode.plicity !== 'implicit') ||
        (
            mode.variation !== 'functorial' &&
            mode.variation !== 'natural' &&
            mode.variation !== 'object-only'
        )
    ) {
        fail(
            'INVALID_EXPRESSION',
            path,
            'Core LF transfer binder has an invalid mode'
        );
    }
};

export function coreLfQualifiedSymbol(
    moduleId: string,
    name: string
): CoreLfQualifiedSymbol {
    validateModuleId(moduleId, 'symbol.moduleId');
    validateSymbolName(name, 'symbol.name');
    return Object.freeze({ moduleId, name });
}

export const coreLfTransferAbsentBody =
    (): CoreLfTransferBody => Object.freeze({ kind: 'absent' });

export const coreLfTransferExplicitBody = (
    term: CoreLfTransferExpression
): CoreLfTransferBody => deepFreeze({
    kind: 'explicit-term',
    term: cloneData(term)
});

export const coreLfTransferTacticBody = (
    canonicalSource: string
): CoreLfTransferBody => {
    if (canonicalSource.trim().length === 0) {
        fail(
            'INVALID_BODY',
            'body.canonicalSource',
            'Checked tactic source cannot be empty'
        );
    }
    return Object.freeze({
        kind: 'checked-tactic-source',
        canonicalSource
    });
};

const CORE_LF_TRANSFER_BUILDER_EXPRESSION =
    Symbol('CoreLfTransferBuilderExpression');
const CORE_LF_TRANSFER_BINDER_TOKEN =
    Symbol('CoreLfTransferBinderToken');

export interface CoreLfTransferBuilderExpression {
    readonly [CORE_LF_TRANSFER_BUILDER_EXPRESSION]: true;
}

export interface CoreLfTransferBinderToken
    extends CoreLfTransferBuilderExpression {
    readonly [CORE_LF_TRANSFER_BINDER_TOKEN]: true;
}

export interface CoreLfTransferBuilderArgument {
    readonly plicity: Plicity;
    readonly value: CoreLfTransferBuilderExpression;
}

type CoreLfTransferBuilderNode =
    | {
        readonly tag: 'type';
    }
    | {
        readonly tag: 'global';
        readonly symbol: CoreLfQualifiedSymbol;
    }
    | {
        readonly tag: 'capture';
        readonly name: string;
        readonly allowedBoundIndices?: readonly number[];
    }
    | {
        readonly tag: 'wildcard';
    }
    | {
        readonly tag: 'token';
        readonly ordinal: number;
        readonly hint: string;
    }
    | {
        readonly tag: 'call';
        readonly callee: InternalCoreLfTransferBuilderExpression;
        readonly arguments: readonly {
            readonly plicity: Plicity;
            readonly value: InternalCoreLfTransferBuilderExpression;
        }[];
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly hint: string;
        readonly mode: BinderMode;
        readonly type: InternalCoreLfTransferBuilderExpression;
        readonly token: InternalCoreLfTransferBuilderExpression;
        readonly body: InternalCoreLfTransferBuilderExpression;
    }
    | {
        readonly tag: 'let';
        readonly hint: string;
        readonly mode: BinderMode;
        readonly type: InternalCoreLfTransferBuilderExpression;
        readonly value: InternalCoreLfTransferBuilderExpression;
        readonly token: InternalCoreLfTransferBuilderExpression;
        readonly body: InternalCoreLfTransferBuilderExpression;
    };

interface InternalCoreLfTransferBuilderExpression
    extends CoreLfTransferBuilderExpression {
    readonly builderIdentity: symbol;
    readonly node: CoreLfTransferBuilderNode;
    readonly [CORE_LF_TRANSFER_BINDER_TOKEN]?: true;
}

type BuilderLoweringPurpose = 'term' | 'pattern' | 'template';

/**
 * HOAS-like construction whose callbacks execute once and whose result is
 * explicit locally nameless transfer syntax. No callback enters the IR.
 */
export class CoreLfTransferScopedBuilder {
    private readonly builderIdentity =
        Symbol('CoreLfTransferScopedBuilder');
    private nextTokenOrdinal = 0;

    private makeExpression(
        node: CoreLfTransferBuilderNode,
        binderToken = false
    ): InternalCoreLfTransferBuilderExpression {
        return Object.freeze({
            [CORE_LF_TRANSFER_BUILDER_EXPRESSION]: true as const,
            ...(binderToken
                ? { [CORE_LF_TRANSFER_BINDER_TOKEN]: true as const }
                : {}),
            builderIdentity: this.builderIdentity,
            node: deepFreeze(node)
        });
    }

    private requireExpression(
        value: CoreLfTransferBuilderExpression,
        path: string
    ): InternalCoreLfTransferBuilderExpression {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreLfTransferBuilderExpression)[
                CORE_LF_TRANSFER_BUILDER_EXPRESSION
            ] !== true
        ) {
            fail(
                'INVALID_BUILDER_EXPRESSION',
                path,
                'Transfer builder received an invalid expression'
            );
        }
        const expression =
            value as InternalCoreLfTransferBuilderExpression;
        if (expression.builderIdentity !== this.builderIdentity) {
            fail(
                'FOREIGN_BUILDER_EXPRESSION',
                path,
                'Transfer builder expression belongs to another builder'
            );
        }
        return expression;
    }

    private token(hint: string):
    InternalCoreLfTransferBuilderExpression {
        return this.makeExpression({
            tag: 'token',
            ordinal: this.nextTokenOrdinal++,
            hint
        }, true);
    }

    private bind(
        tag: 'pi' | 'lambda',
        hint: string,
        type: CoreLfTransferBuilderExpression,
        body: (
            token: CoreLfTransferBinderToken
        ) => CoreLfTransferBuilderExpression,
        mode: BinderMode
    ): CoreLfTransferBuilderExpression {
        validateBinderHint(hint, `${tag}.binder.hint`);
        validateMode(mode, `${tag}.binder.mode`);
        const checkedType = this.requireExpression(
            type,
            `${tag}.binder.type`
        );
        const token = this.token(hint);
        const checkedBody = this.requireExpression(
            body(token as CoreLfTransferBinderToken),
            `${tag}.body`
        );
        return this.makeExpression({
            tag,
            hint,
            mode: Object.freeze({ ...mode }),
            type: checkedType,
            token,
            body: checkedBody
        });
    }

    type(): CoreLfTransferBuilderExpression {
        return this.makeExpression({ tag: 'type' });
    }

    global(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfTransferBuilderExpression {
        validateModuleId(symbol.moduleId, 'global.symbol.moduleId');
        validateSymbolName(symbol.name, 'global.symbol.name');
        return this.makeExpression({
            tag: 'global',
            symbol: Object.freeze({ ...symbol })
        });
    }

    capture(
        name: string,
        allowedBoundIndices?: readonly number[]
    ): CoreLfTransferBuilderExpression {
        validateCaptureName(name, 'capture.name');
        return this.makeExpression({
            tag: 'capture',
            name,
            ...(allowedBoundIndices === undefined
                ? {}
                : {
                    allowedBoundIndices:
                        Object.freeze([...allowedBoundIndices])
                })
        });
    }

    wildcard(): CoreLfTransferBuilderExpression {
        return this.makeExpression({ tag: 'wildcard' });
    }

    call(
        callee: CoreLfTransferBuilderExpression,
        arguments_: readonly CoreLfTransferBuilderArgument[]
    ): CoreLfTransferBuilderExpression {
        if (arguments_.length === 0) {
            fail(
                'INVALID_BUILDER_EXPRESSION',
                'call.arguments',
                'Transfer builder call requires at least one argument'
            );
        }
        return this.makeExpression({
            tag: 'call',
            callee: this.requireExpression(callee, 'call.callee'),
            arguments: Object.freeze(arguments_.map((argument, index) => {
                if (
                    argument.plicity !== 'explicit' &&
                    argument.plicity !== 'implicit'
                ) {
                    fail(
                        'INVALID_BUILDER_EXPRESSION',
                        `call.arguments[${index}].plicity`,
                        'Transfer builder call has invalid plicity'
                    );
                }
                return Object.freeze({
                    plicity: argument.plicity,
                    value: this.requireExpression(
                        argument.value,
                        `call.arguments[${index}].value`
                    )
                });
            }))
        });
    }

    apply(
        callee: CoreLfTransferBuilderExpression,
        value: CoreLfTransferBuilderExpression,
        plicity: Plicity = 'explicit'
    ): CoreLfTransferBuilderExpression {
        return this.call(callee, [{ plicity, value }]);
    }

    pi(
        hint: string,
        type: CoreLfTransferBuilderExpression,
        body: (
            token: CoreLfTransferBinderToken
        ) => CoreLfTransferBuilderExpression,
        mode: BinderMode = binderMode('explicit', 'functorial')
    ): CoreLfTransferBuilderExpression {
        return this.bind('pi', hint, type, body, mode);
    }

    lam(
        hint: string,
        type: CoreLfTransferBuilderExpression,
        body: (
            token: CoreLfTransferBinderToken
        ) => CoreLfTransferBuilderExpression,
        mode: BinderMode = binderMode('explicit', 'functorial')
    ): CoreLfTransferBuilderExpression {
        return this.bind('lambda', hint, type, body, mode);
    }

    let_(
        hint: string,
        type: CoreLfTransferBuilderExpression,
        value: CoreLfTransferBuilderExpression,
        body: (
            token: CoreLfTransferBinderToken
        ) => CoreLfTransferBuilderExpression,
        mode: BinderMode = binderMode('explicit', 'functorial')
    ): CoreLfTransferBuilderExpression {
        validateBinderHint(hint, 'let.binder.hint');
        validateMode(mode, 'let.binder.mode');
        const token = this.token(hint);
        return this.makeExpression({
            tag: 'let',
            hint,
            mode: Object.freeze({ ...mode }),
            type: this.requireExpression(type, 'let.binder.type'),
            value: this.requireExpression(value, 'let.value'),
            token,
            body: this.requireExpression(
                body(token as CoreLfTransferBinderToken),
                'let.body'
            )
        });
    }

    private lower(
        value: CoreLfTransferBuilderExpression,
        purpose: BuilderLoweringPurpose
    ): CoreLfTransferExpression {
        const expression = this.requireExpression(value, `lower.${purpose}`);

        const visit = (
            current: InternalCoreLfTransferBuilderExpression,
            scope: readonly InternalCoreLfTransferBuilderExpression[]
        ): CoreLfTransferExpression => {
            switch (current.node.tag) {
                case 'type':
                    return { tag: 'type' };
                case 'global':
                    return {
                        tag: 'global',
                        symbol: { ...current.node.symbol }
                    };
                case 'capture':
                    if (purpose === 'term') {
                        fail(
                            'INVALID_BUILDER_EXPRESSION',
                            'lower.term',
                            'Declaration term cannot contain a rule capture'
                        );
                    }
                    return {
                        tag: 'capture',
                        name: current.node.name,
                        ...(current.node.allowedBoundIndices === undefined
                            ? {}
                            : {
                                allowedBoundIndices: [
                                    ...current.node.allowedBoundIndices
                                ]
                            })
                    };
                case 'wildcard':
                    if (purpose !== 'pattern') {
                        fail(
                            'INVALID_BUILDER_EXPRESSION',
                            `lower.${purpose}`,
                            'Wildcard is permitted only in a match pattern'
                        );
                    }
                    return { tag: 'wildcard' };
                case 'token': {
                    const position = scope.lastIndexOf(current);
                    if (position < 0) {
                        fail(
                            'ESCAPED_BINDER_TOKEN',
                            `lower.${purpose}`,
                            `Transfer binder token '${current.node.hint}' ` +
                                'escaped its binder body'
                        );
                    }
                    return {
                        tag: 'bound',
                        index: scope.length - position - 1
                    };
                }
                case 'call':
                    return {
                        tag: 'call',
                        callee: visit(current.node.callee, scope),
                        arguments: current.node.arguments.map(argument => ({
                            plicity: argument.plicity,
                            value: visit(argument.value, scope)
                        }))
                    };
                case 'pi':
                case 'lambda':
                    return {
                        tag: current.node.tag,
                        binder: {
                            hint: current.node.hint,
                            mode: { ...current.node.mode },
                            type: visit(current.node.type, scope)
                        },
                        body: visit(
                            current.node.body,
                            [...scope, current.node.token]
                        )
                    };
                case 'let': {
                    const lambda: CoreLfTransferExpression = {
                        tag: 'lambda',
                        binder: {
                            hint: current.node.hint,
                            mode: { ...current.node.mode },
                            type: visit(current.node.type, scope)
                        },
                        body: visit(
                            current.node.body,
                            [...scope, current.node.token]
                        )
                    };
                    return {
                        tag: 'call',
                        callee: lambda,
                        arguments: [{
                            plicity: current.node.mode.plicity,
                            value: visit(current.node.value, scope)
                        }]
                    };
                }
                default: {
                    const exhaustive: never = current.node;
                    return exhaustive;
                }
            }
        };

        return deepFreeze(visit(expression, []));
    }

    term(
        expression: CoreLfTransferBuilderExpression
    ): CoreLfTransferExpression {
        return this.lower(expression, 'term');
    }

    pattern(
        expression: CoreLfTransferBuilderExpression
    ): CoreLfTransferExpression {
        return this.lower(expression, 'pattern');
    }

    template(
        expression: CoreLfTransferBuilderExpression
    ): CoreLfTransferExpression {
        return this.lower(expression, 'template');
    }
}

interface ExpressionValidationContext {
    readonly purpose: BuilderLoweringPurpose;
    readonly depth: number;
    readonly captures: ReadonlyMap<
        string,
        'matched' | 'fresh-constraint'
    >;
    readonly captureOccurrences: Map<string, number>;
    readonly referencedSymbols: Map<string, CoreLfQualifiedSymbol>;
}

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const validateSymbol = (
    symbol: CoreLfQualifiedSymbol,
    path: string
): void => {
    validateModuleId(symbol.moduleId, `${path}.moduleId`);
    validateSymbolName(symbol.name, `${path}.name`);
};

const validateExpression = (
    expression: CoreLfTransferExpression,
    context: ExpressionValidationContext,
    path: string
): void => {
    if (typeof expression !== 'object' || expression === null) {
        fail(
            'INVALID_EXPRESSION',
            path,
            'Core LF transfer expression must be an object'
        );
    }

    switch (expression.tag) {
        case 'type':
            return;
        case 'bound':
            if (
                !Number.isSafeInteger(expression.index) ||
                expression.index < 0 ||
                expression.index >= context.depth
            ) {
                fail(
                    'INVALID_SCOPE',
                    `${path}.index`,
                    `Bound index ${expression.index} escapes depth ` +
                        context.depth
                );
            }
            return;
        case 'global':
            validateSymbol(expression.symbol, `${path}.symbol`);
            context.referencedSymbols.set(
                symbolKey(expression.symbol),
                expression.symbol
            );
            return;
        case 'call':
            if (
                !Array.isArray(expression.arguments) ||
                expression.arguments.length === 0
            ) {
                fail(
                    'INVALID_EXPRESSION',
                    `${path}.arguments`,
                    'Core LF transfer call requires an argument'
                );
            }
            validateExpression(
                expression.callee,
                context,
                `${path}.callee`
            );
            expression.arguments.forEach((argument, index) => {
                if (
                    argument.plicity !== 'explicit' &&
                    argument.plicity !== 'implicit'
                ) {
                    fail(
                        'INVALID_EXPRESSION',
                        `${path}.arguments[${index}].plicity`,
                        'Core LF transfer argument has invalid plicity'
                    );
                }
                validateExpression(
                    argument.value,
                    context,
                    `${path}.arguments[${index}].value`
                );
            });
            return;
        case 'pi':
        case 'lambda':
            validateBinderHint(
                expression.binder.hint,
                `${path}.binder.hint`
            );
            validateMode(
                expression.binder.mode,
                `${path}.binder.mode`
            );
            validateExpression(
                expression.binder.type,
                context,
                `${path}.binder.type`
            );
            validateExpression(
                expression.body,
                {
                    ...context,
                    depth: context.depth + 1
                },
                `${path}.body`
            );
            return;
        case 'capture': {
            if (context.purpose === 'term') {
                fail(
                    'INVALID_CAPTURE',
                    path,
                    'Declaration term cannot contain a rule capture'
                );
            }
            validateCaptureName(expression.name, `${path}.name`);
            const role = context.captures.get(expression.name);
            if (role === undefined) {
                fail(
                    'INVALID_CAPTURE',
                    path,
                    `Undeclared rule capture '${expression.name}'`
                );
            }
            if (context.purpose === 'pattern' && role !== 'matched') {
                fail(
                    'INVALID_CAPTURE',
                    path,
                    `Fresh proof variable '${expression.name}' cannot ` +
                        'occur in a match problem'
                );
            }
            if (expression.allowedBoundIndices !== undefined) {
                const seen = new Set<number>();
                expression.allowedBoundIndices.forEach((index, position) => {
                    if (
                        !Number.isSafeInteger(index) ||
                        index < 0 ||
                        index >= context.depth ||
                        seen.has(index)
                    ) {
                        fail(
                            'INVALID_SCOPE',
                            `${path}.allowedBoundIndices[${position}]`,
                            'Restricted capture scope must contain distinct ' +
                                'in-scope bound indices'
                        );
                    }
                    seen.add(index);
                });
            }
            context.captureOccurrences.set(
                expression.name,
                (context.captureOccurrences.get(expression.name) ?? 0) + 1
            );
            return;
        }
        case 'wildcard':
            if (context.purpose !== 'pattern') {
                fail(
                    'INVALID_CAPTURE',
                    path,
                    'Wildcard is permitted only in a match pattern'
                );
            }
            return;
        default:
            fail(
                'INVALID_EXPRESSION',
                path,
                `Unsupported Core LF transfer expression tag ` +
                    `'${String(
                        (expression as { tag?: unknown }).tag
                    )}'`
            );
    }
};

const validateProvenance = (
    provenance: CoreLfTransferProvenance,
    authorityPath: string,
    path: string
): void => {
    validatePath(provenance.authorityPath, `${path}.authorityPath`);
    if (provenance.authorityPath !== authorityPath) {
        fail(
            'INVALID_PROVENANCE',
            `${path}.authorityPath`,
            'Transfer item authority path differs from its module fragment'
        );
    }
    if (provenance.sourceFragment.trim().length === 0) {
        fail(
            'INVALID_PROVENANCE',
            `${path}.sourceFragment`,
            'Transfer item requires nonempty relocatable source evidence'
        );
    }
    if (
        provenance.canonicalCommandOrdinal !== undefined &&
        (
            !Number.isSafeInteger(provenance.canonicalCommandOrdinal) ||
            provenance.canonicalCommandOrdinal < 0
        )
    ) {
        fail(
            'INVALID_PROVENANCE',
            `${path}.canonicalCommandOrdinal`,
            'Canonical command ordinal must be nonnegative'
        );
    }
};

const validateModifiers = (
    modifiers: CoreLfTransferModifiers,
    path: string
): void => {
    if (
        !['public', 'protected', 'private'].includes(
            modifiers.visibility
        ) ||
        !['ordinary', 'constant', 'injective'].includes(
            modifiers.rigidity
        ) ||
        !['transparent', 'opaque'].includes(modifiers.sourceOpacity)
    ) {
        fail(
            'INVALID_EXPRESSION',
            path,
            'Transfer declaration has invalid source modifiers'
        );
    }
    if (modifiers.generatedBy !== undefined) {
        validateSymbol(modifiers.generatedBy, `${path}.generatedBy`);
    }
};

const validateTelescope = (
    binders: readonly CoreLfTransferTelescopeBinder[],
    initialDepth: number,
    context: Omit<ExpressionValidationContext, 'depth'>,
    path: string
): number => {
    let depth = initialDepth;
    binders.forEach((binder, index) => {
        validateBinderHint(binder.hint, `${path}[${index}].hint`);
        validateMode(binder.mode, `${path}[${index}].mode`);
        validateExpression(
            binder.type,
            { ...context, depth },
            `${path}[${index}].type`
        );
        depth++;
    });
    return depth;
};

const validateRuleVariables = (
    variables: readonly (
        CoreLfTransferRuleVariable | CoreLfTransferProofVariable
    )[],
    roles: ReadonlyMap<string, 'matched' | 'fresh-constraint'>,
    baseContext: Pick<
        ExpressionValidationContext,
        'referencedSymbols'
    >,
    path: string
): void => {
    const available = new Map<
        string,
        'matched' | 'fresh-constraint'
    >();
    variables.forEach((variable, index) => {
        validateCaptureName(variable.name, `${path}[${index}].name`);
        if (available.has(variable.name)) {
            fail(
                'DUPLICATE_IDENTITY',
                `${path}[${index}].name`,
                `Duplicate rule variable '${variable.name}'`
            );
        }
        validateExpression(
            variable.type,
            {
                ...baseContext,
                purpose: 'template',
                depth: 0,
                captures: available,
                captureOccurrences: new Map<string, number>()
            },
            `${path}[${index}].type`
        );
        const role = roles.get(variable.name);
        if (role === undefined) {
            fail(
                'INVALID_RULE',
                `${path}[${index}]`,
                `Rule variable '${variable.name}' has no role`
            );
        }
        available.set(variable.name, role);
    });
};

const validateStrictOrders = (
    values: readonly { readonly order: number }[],
    path: string
): void => {
    let previous = -1;
    values.forEach((value, index) => {
        validateOrder(value.order, `${path}[${index}].order`);
        if (value.order <= previous) {
            fail(
                'INVALID_ORDER',
                `${path}[${index}].order`,
                'Transfer items must be strictly ordered'
            );
        }
        previous = value.order;
    });
};

const assertUnique = (
    values: readonly string[],
    path: string,
    description: string
): void => {
    const seen = new Set<string>();
    values.forEach((value, index) => {
        if (seen.has(value)) {
            fail(
                'DUPLICATE_IDENTITY',
                `${path}[${index}]`,
                `Duplicate ${description} '${value}'`
            );
        }
        seen.add(value);
    });
};

/**
 * Validate and deeply freeze one directly authored module or module fragment.
 *
 * This is representation validation only. It does not type-check a
 * declaration, install a rule, or grant product authority.
 */
export function createCoreLfModuleSpec(
    input: CoreLfModuleSpecInput
): CoreLfModuleSpec {
    validateCoreLfScaleArchitectureReview();
    validateRevision(input.revision, 'module.revision');
    validateModuleId(input.moduleId, 'module.moduleId');
    validateRevision(input.fragmentId, 'module.fragmentId');
    validatePath(input.authorityPath, 'module.authorityPath');
    validateSha256(input.sourceSha256, 'module.sourceSha256');
    if (input.canonicalExport !== undefined) {
        if (input.canonicalExport.exporterVersion.trim().length === 0) {
            fail(
                'INVALID_IDENTIFIER',
                'module.canonicalExport.exporterVersion',
                'Canonical exporter version cannot be empty'
            );
        }
        validateSha256(
            input.canonicalExport.sha256,
            'module.canonicalExport.sha256'
        );
    }

    assertUnique(
        input.dependencies,
        'module.dependencies',
        'module dependency'
    );
    input.dependencies.forEach((dependency, index) => {
        validateModuleId(dependency, `module.dependencies[${index}]`);
        if (dependency === input.moduleId) {
            fail(
                'INVALID_DEPENDENCY',
                `module.dependencies[${index}]`,
                'A transfer module cannot import itself'
            );
        }
    });

    const externalKeys = input.externalSymbols.map((external, index) => {
        validateSymbol(
            external.symbol,
            `module.externalSymbols[${index}].symbol`
        );
        if (
            external.availability === 'dependency-module' &&
            !input.dependencies.includes(external.symbol.moduleId)
        ) {
            fail(
                'INVALID_DEPENDENCY',
                `module.externalSymbols[${index}]`,
                `External '${external.symbol.name}' names dependency ` +
                    `'${external.symbol.moduleId}' that is not imported`
            );
        }
        if (
            external.availability === 'earlier-fragment' &&
            external.symbol.moduleId !== input.moduleId
        ) {
            fail(
                'INVALID_DEPENDENCY',
                `module.externalSymbols[${index}]`,
                'Earlier-fragment external must belong to the same module'
            );
        }
        return symbolKey(external.symbol);
    });
    assertUnique(
        externalKeys,
        'module.externalSymbols',
        'external symbol'
    );

    validateStrictOrders(input.declarations, 'module.declarations');
    validateStrictOrders(input.inductives, 'module.inductives');
    validateStrictOrders(input.runtimeRules, 'module.runtimeRules');
    validateStrictOrders(input.proofRules, 'module.proofRules');

    const allTopLevelOrders = [
        ...input.declarations.map(entry => entry.order),
        ...input.inductives.map(entry => entry.order),
        ...input.runtimeRules.map(entry => entry.order),
        ...input.proofRules.map(entry => entry.order)
    ];
    assertUnique(
        allTopLevelOrders.map(String),
        'module.topLevelOrders',
        'top-level transfer order'
    );

    const localSymbols = new Map<string, CoreLfQualifiedSymbol>();
    const addLocal = (
        symbol: CoreLfQualifiedSymbol,
        path: string
    ): void => {
        validateSymbol(symbol, path);
        if (symbol.moduleId !== input.moduleId) {
            fail(
                'INVALID_DEPENDENCY',
                path,
                'Local transfer symbol belongs to a foreign module'
            );
        }
        const key = symbolKey(symbol);
        if (localSymbols.has(key)) {
            fail(
                'DUPLICATE_IDENTITY',
                path,
                `Duplicate local transfer symbol '${symbol.name}'`
            );
        }
        localSymbols.set(key, symbol);
    };

    input.declarations.forEach((declaration, index) =>
        addLocal(
            declaration.symbol,
            `module.declarations[${index}].symbol`
        )
    );
    input.inductives.forEach((block, blockIndex) => {
        addLocal(
            block.symbol,
            `module.inductives[${blockIndex}].symbol`
        );
        block.constructors.forEach((constructor, constructorIndex) =>
            addLocal(
                constructor.symbol,
                `module.inductives[${blockIndex}].constructors[` +
                    `${constructorIndex}].symbol`
            )
        );
        block.generatedSymbols.forEach((symbol, generatedIndex) =>
            addLocal(
                symbol,
                `module.inductives[${blockIndex}].generatedSymbols[` +
                    `${generatedIndex}]`
            )
        );
    });

    const referencedSymbols = new Map<string, CoreLfQualifiedSymbol>();
    const noCaptures = new Map<
        string,
        'matched' | 'fresh-constraint'
    >();
    const baseContext = {
        captures: noCaptures,
        captureOccurrences: new Map<string, number>(),
        referencedSymbols
    };

    input.declarations.forEach((declaration, index) => {
        const path = `module.declarations[${index}]`;
        validateProvenance(
            declaration.provenance,
            input.authorityPath,
            `${path}.provenance`
        );
        validateModifiers(declaration.modifiers, `${path}.modifiers`);
        if (declaration.modifiers.generatedBy !== undefined) {
            referencedSymbols.set(
                symbolKey(declaration.modifiers.generatedBy),
                declaration.modifiers.generatedBy
            );
        }
        validateExpression(
            declaration.type,
            { ...baseContext, purpose: 'term', depth: 0 },
            `${path}.type`
        );
        switch (declaration.body.kind) {
            case 'absent':
                break;
            case 'explicit-term':
                validateExpression(
                    declaration.body.term,
                    { ...baseContext, purpose: 'term', depth: 0 },
                    `${path}.body.term`
                );
                break;
            case 'checked-tactic-source':
                if (
                    declaration.body.canonicalSource.trim().length === 0
                ) {
                    fail(
                        'INVALID_BODY',
                        `${path}.body.canonicalSource`,
                        'Checked tactic source cannot be empty'
                    );
                }
                break;
            default:
                fail(
                    'INVALID_BODY',
                    `${path}.body`,
                    'Unsupported transfer declaration body kind'
                );
        }
    });

    input.inductives.forEach((block, blockIndex) => {
        const path = `module.inductives[${blockIndex}]`;
        validateProvenance(
            block.provenance,
            input.authorityPath,
            `${path}.provenance`
        );
        validateModifiers(block.modifiers, `${path}.modifiers`);
        if (block.modifiers.generatedBy !== undefined) {
            referencedSymbols.set(
                symbolKey(block.modifiers.generatedBy),
                block.modifiers.generatedBy
            );
        }
        validateStrictOrders(block.constructors, `${path}.constructors`);
        const telescopeContext = {
            purpose: 'term' as const,
            captures: noCaptures,
            captureOccurrences: new Map<string, number>(),
            referencedSymbols
        };
        const parameterDepth = validateTelescope(
            block.parameters,
            0,
            telescopeContext,
            `${path}.parameters`
        );
        const totalDepth = validateTelescope(
            block.indices,
            parameterDepth,
            telescopeContext,
            `${path}.indices`
        );
        validateExpression(
            block.sort,
            { ...telescopeContext, depth: totalDepth },
            `${path}.sort`
        );
        block.constructors.forEach((constructor, constructorIndex) => {
            const constructorPath =
                `${path}.constructors[${constructorIndex}]`;
            validateProvenance(
                constructor.provenance,
                input.authorityPath,
                `${constructorPath}.provenance`
            );
            if (
                constructor.parameterModes !== undefined &&
                constructor.parameterModes.length !==
                    block.parameters.length
            ) {
                fail(
                    'INVALID_EXPRESSION',
                    `${constructorPath}.parameterModes`,
                    'Constructor parameter modes must cover every ' +
                        'inductive parameter exactly once'
                );
            }
            constructor.parameterModes?.forEach((mode, modeIndex) =>
                validateMode(
                    mode,
                    `${constructorPath}.parameterModes[${modeIndex}]`
                )
            );
            const constructorDepth = validateTelescope(
                constructor.binders,
                parameterDepth,
                telescopeContext,
                `${constructorPath}.binders`
            );
            validateExpression(
                constructor.result,
                { ...telescopeContext, depth: constructorDepth },
                `${constructorPath}.result`
            );
        });
    });

    const runtimeIds: string[] = [];
    input.runtimeRules.forEach((rule, index) => {
        const path = `module.runtimeRules[${index}]`;
        validateRuleId(rule.id, `${path}.id`);
        validateRuleId(rule.groupId, `${path}.groupId`);
        validateOrder(rule.clauseOrder, `${path}.clauseOrder`);
        validateSymbol(rule.sourceOwner, `${path}.sourceOwner`);
        referencedSymbols.set(
            symbolKey(rule.sourceOwner),
            rule.sourceOwner
        );
        validateProvenance(
            rule.provenance,
            input.authorityPath,
            `${path}.provenance`
        );
        runtimeIds.push(rule.id);
        const roles = new Map(
            rule.variables.map(variable => [
                variable.name,
                'matched' as const
            ])
        );
        const occurrences = new Map<string, number>();
        const ruleBase = {
            captureOccurrences: occurrences,
            referencedSymbols
        };
        validateRuleVariables(
            rule.variables,
            roles,
            ruleBase,
            `${path}.variables`
        );
        validateExpression(
            rule.left,
            {
                ...ruleBase,
                purpose: 'pattern',
                depth: 0,
                captures: roles
            },
            `${path}.left`
        );
        if (
            rule.left.tag === 'capture' ||
            rule.left.tag === 'wildcard' ||
            rule.left.tag === 'bound' ||
            rule.left.tag === 'type'
        ) {
            fail(
                'INVALID_RULE',
                `${path}.left`,
                'Runtime rule left side must have a rigid head'
            );
        }
        rule.variables.forEach((variable, variableIndex) => {
            if ((occurrences.get(variable.name) ?? 0) === 0) {
                fail(
                    'INVALID_RULE',
                    `${path}.variables[${variableIndex}]`,
                    `Runtime variable '${variable.name}' is not bound by ` +
                        'the left pattern'
                );
            }
        });
        validateExpression(
            rule.right,
            {
                ...ruleBase,
                purpose: 'template',
                depth: 0,
                captures: roles
            },
            `${path}.right`
        );
    });
    assertUnique(runtimeIds, 'module.runtimeRules', 'runtime rule ID');

    const proofIds: string[] = [];
    input.proofRules.forEach((rule, index) => {
        const path = `module.proofRules[${index}]`;
        validateRuleId(rule.id, `${path}.id`);
        validateSymbol(rule.sourceOwner, `${path}.sourceOwner`);
        referencedSymbols.set(
            symbolKey(rule.sourceOwner),
            rule.sourceOwner
        );
        validateProvenance(
            rule.provenance,
            input.authorityPath,
            `${path}.provenance`
        );
        if (rule.generatedConstraints.length === 0) {
            fail(
                'INVALID_RULE',
                `${path}.generatedConstraints`,
                'Proof-time rule must generate at least one constraint'
            );
        }
        proofIds.push(rule.id);
        const roles = new Map(
            rule.variables.map(variable => [
                variable.name,
                variable.role
            ])
        );
        const occurrences = new Map<string, number>();
        const ruleBase = {
            captureOccurrences: occurrences,
            referencedSymbols
        };
        validateRuleVariables(
            rule.variables,
            roles,
            ruleBase,
            `${path}.variables`
        );
        validateExpression(
            rule.problem.left,
            {
                ...ruleBase,
                purpose: 'pattern',
                depth: 0,
                captures: roles
            },
            `${path}.problem.left`
        );
        validateExpression(
            rule.problem.right,
            {
                ...ruleBase,
                purpose: 'pattern',
                depth: 0,
                captures: roles
            },
            `${path}.problem.right`
        );
        rule.variables.forEach((variable, variableIndex) => {
            const count = occurrences.get(variable.name) ?? 0;
            if (variable.role === 'matched' && count === 0) {
                fail(
                    'INVALID_RULE',
                    `${path}.variables[${variableIndex}]`,
                    `Matched proof variable '${variable.name}' does not ` +
                        'occur in the proof problem'
                );
            }
            if (variable.role === 'fresh-constraint' && count !== 0) {
                fail(
                    'INVALID_RULE',
                    `${path}.variables[${variableIndex}]`,
                    `Fresh proof variable '${variable.name}' occurs in the ` +
                        'proof problem'
                );
            }
        });
        const beforeConstraints = new Map(occurrences);
        rule.generatedConstraints.forEach((constraint, constraintIndex) => {
            validateExpression(
                constraint.left,
                {
                    ...ruleBase,
                    purpose: 'template',
                    depth: 0,
                    captures: roles
                },
                `${path}.generatedConstraints[${constraintIndex}].left`
            );
            validateExpression(
                constraint.right,
                {
                    ...ruleBase,
                    purpose: 'template',
                    depth: 0,
                    captures: roles
                },
                `${path}.generatedConstraints[${constraintIndex}].right`
            );
        });
        rule.variables.forEach((variable, variableIndex) => {
            if (
                variable.role === 'fresh-constraint' &&
                (occurrences.get(variable.name) ?? 0) ===
                    (beforeConstraints.get(variable.name) ?? 0)
            ) {
                fail(
                    'INVALID_RULE',
                    `${path}.variables[${variableIndex}]`,
                    `Fresh proof variable '${variable.name}' is unused by ` +
                        'generated constraints'
                );
            }
        });
    });
    assertUnique(proofIds, 'module.proofRules', 'proof rule ID');

    const available = new Set([
        ...localSymbols.keys(),
        ...externalKeys
    ]);
    referencedSymbols.forEach((symbol, key) => {
        if (!available.has(key)) {
            fail(
                'UNRESOLVED_GLOBAL',
                'module.referencedSymbols',
                `Transfer fragment does not declare external global ` +
                    `'${symbol.moduleId}.${symbol.name}'`
            );
        }
    });

    const spec = cloneData<CoreLfModuleSpec>({
        ...input,
        referencedSymbols: [...referencedSymbols.values()]
    });
    return deepFreeze(spec);
}

const policyTargetKey = (
    target: CoreLfTransferPolicyTarget
): string => {
    switch (target.kind) {
        case 'declaration':
        case 'inductive':
            return `${target.kind}:${symbolKey(target.symbol)}`;
        case 'runtime-rule':
        case 'proof-rule':
            return `${target.kind}:${target.id}`;
        default: {
            const exhaustive: never = target;
            return exhaustive;
        }
    }
};

/**
 * Validate a policy independently from source ingestion and freeze it.
 */
export function createCoreLfTransferPolicyOverlay(
    module: CoreLfModuleSpec,
    input: CoreLfTransferPolicyOverlayInput
): CoreLfTransferPolicyOverlay {
    validateCoreLfScaleArchitectureReview();
    validateRevision(input.revision, 'policy.revision');
    if (input.moduleRevision !== module.revision) {
        fail(
            'INVALID_POLICY',
            'policy.moduleRevision',
            'Transfer policy targets a different module revision'
        );
    }
    validateStrictOrders(input.entries, 'policy.entries');

    const declarations = new Set(
        module.declarations.map(entry => symbolKey(entry.symbol))
    );
    const inductives = new Set(
        module.inductives.map(entry => symbolKey(entry.symbol))
    );
    const runtimeRules = new Set(
        module.runtimeRules.map(entry => entry.id)
    );
    const proofRules = new Set(module.proofRules.map(entry => entry.id));
    const targetKeys: string[] = [];

    input.entries.forEach((entry, index) => {
        const path = `policy.entries[${index}]`;
        if (entry.evidence.trim().length === 0) {
            fail(
                'INVALID_POLICY',
                `${path}.evidence`,
                'Transfer policy entry requires review evidence'
            );
        }
        targetKeys.push(policyTargetKey(entry.target));
        switch (entry.target.kind) {
            case 'declaration':
                validateSymbol(entry.target.symbol, `${path}.target.symbol`);
                if (!declarations.has(symbolKey(entry.target.symbol))) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.target`,
                        'Policy targets an unknown declaration'
                    );
                }
                if (
                    ![
                        'opaque-signature',
                        'checked-transparent-definition',
                        'theorem-body',
                        'conformance-only',
                        'excluded'
                    ].includes(entry.policy)
                ) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.policy`,
                        'Declaration has an incompatible policy class'
                    );
                }
                break;
            case 'inductive':
                validateSymbol(entry.target.symbol, `${path}.target.symbol`);
                if (!inductives.has(symbolKey(entry.target.symbol))) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.target`,
                        'Policy targets an unknown inductive block'
                    );
                }
                if (
                    ![
                        'opaque-signature',
                        'conformance-only',
                        'excluded'
                    ].includes(entry.policy)
                ) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.policy`,
                        'Inductive block has an incompatible policy class'
                    );
                }
                break;
            case 'runtime-rule':
                validateRuleId(entry.target.id, `${path}.target.id`);
                if (!runtimeRules.has(entry.target.id)) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.target`,
                        'Policy targets an unknown runtime rule'
                    );
                }
                if (
                    ![
                        'runtime-rewrite',
                        'conformance-only',
                        'excluded'
                    ].includes(entry.policy)
                ) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.policy`,
                        'Runtime rule has an incompatible policy class'
                    );
                }
                break;
            case 'proof-rule':
                validateRuleId(entry.target.id, `${path}.target.id`);
                if (!proofRules.has(entry.target.id)) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.target`,
                        'Policy targets an unknown proof-time rule'
                    );
                }
                if (
                    ![
                        'proof-unification',
                        'conformance-only',
                        'excluded'
                    ].includes(entry.policy)
                ) {
                    fail(
                        'INVALID_POLICY',
                        `${path}.policy`,
                        'Proof-time rule has an incompatible policy class'
                    );
                }
                break;
            default: {
                const exhaustive: never = entry.target;
                return exhaustive;
            }
        }
    });
    assertUnique(targetKeys, 'policy.entries', 'policy target');

    return deepFreeze(cloneData({
        ...input,
        moduleId: module.moduleId,
        fragmentId: module.fragmentId
    }));
}
