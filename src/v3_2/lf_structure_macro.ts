/**
 * Direct-TypeScript outer-LF parameterized dependent structure macro.
 *
 * The host-only declaration expands before explicit Core to an opaque
 * parameterized carrier, one injective constructor, ordinary named
 * projections, and one subject-reducing runtime beta per projection. It
 * deliberately generates no eliminator, eta law, recursive occurrence, or
 * source-level inductive node.
 */

import { BinderMode } from './kernel';
import {
    CoreLfQualifiedSymbol,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferExternalAvailability,
    CoreLfTransferProvenance,
    CoreLfTransferRuntimeRule,
    coreLfTransferAbsentBody
} from './lf_transfer';

const RESOLVED_GLOBAL = Symbol('CoreLfStructureResolvedGlobal');
const STRUCTURE_EXPRESSION = Symbol('CoreLfStructureExpression');
const STRUCTURE_BINDER_TOKEN = Symbol('CoreLfStructureBinderToken');
const STRUCTURE_PARAMETER_TOKEN = Symbol('CoreLfStructureParameterToken');
const STRUCTURE_FIELD_TOKEN = Symbol('CoreLfStructureFieldToken');

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const OUTPUT_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u;
const MAX_ORDER = Number.MAX_SAFE_INTEGER;

export type CoreLfStructureMacroErrorCode =
    | 'INVALID_SCOPE'
    | 'UNAVAILABLE_GLOBAL'
    | 'FOREIGN_GLOBAL'
    | 'FORWARD_GLOBAL'
    | 'FOREIGN_EXPRESSION'
    | 'ESCAPED_BINDER'
    | 'DUPLICATE_SYMBOL'
    | 'INVALID_COMMAND'
    | 'INVALID_PARAMETER'
    | 'INVALID_FIELD'
    | 'INVALID_CONSTRUCTION'
    | 'FOREIGN_ARGUMENT'
    | 'DUPLICATE_ARGUMENT'
    | 'MISSING_ARGUMENT'
    | 'UNSUPPORTED_EMISSION';

export class CoreLfStructureMacroError extends Error {
    constructor(
        public readonly code: CoreLfStructureMacroErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfStructureMacroError';
    }
}

export interface CoreLfStructureAvailableGlobalInput {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly type: CoreLfTransferExpression;
    readonly availability: CoreLfTransferExternalAvailability;
    /** Required only for a same-module earlier-fragment declaration. */
    readonly order?: number;
}

export interface CoreLfResolvedStructureGlobal {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly type: CoreLfTransferExpression;
    readonly availability: CoreLfTransferExternalAvailability;
    readonly order?: number;
    readonly [RESOLVED_GLOBAL]: true;
}

interface InternalResolvedGlobal extends CoreLfResolvedStructureGlobal {
    readonly scopeIdentity: symbol;
}

/** Host-only expression accepted while declaring dependent field types. */
export interface CoreLfStructureExpression {
    readonly [STRUCTURE_EXPRESSION]: true;
}

export interface CoreLfStructureBinderToken
extends CoreLfStructureExpression {
    readonly [STRUCTURE_BINDER_TOKEN]: true;
}

export interface CoreLfStructureParameterToken
extends CoreLfStructureExpression {
    readonly [STRUCTURE_PARAMETER_TOKEN]: true;
    readonly ordinal: number;
    readonly binderName: string;
}

export interface CoreLfStructureFieldToken
extends CoreLfStructureExpression {
    readonly [STRUCTURE_FIELD_TOKEN]: true;
    readonly ordinal: number;
    readonly binderName: string;
    readonly projectionName: string;
}

export interface CoreLfStructureExpressionArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: CoreLfStructureExpression;
}

export interface CoreLfStructureFieldInput {
    /** Constructor binder and runtime-capture name. */
    readonly binderName: string;
    readonly projectionName: string;
    readonly mode: BinderMode;
    readonly type: CoreLfStructureExpression;
}

export interface CoreLfStructureParameterModes {
    readonly carrier: BinderMode;
    readonly constructor: BinderMode;
    readonly projection: BinderMode;
}

export interface CoreLfStructureParameterInput {
    readonly binderName: string;
    readonly modes: CoreLfStructureParameterModes;
    /** May reference only parameters declared earlier in this callback. */
    readonly type: CoreLfStructureExpression;
}

/**
 * Callback-once macro builder. Parameter and field handles are expressions
 * only inside the current declaration. Parameters may occur in later
 * parameter and field types; fields may occur solely in later field types.
 */
export interface CoreLfStructureFieldBuilder {
    type(): CoreLfStructureExpression;

    global(
        value: CoreLfResolvedStructureGlobal
    ): CoreLfStructureExpression;

    call(
        callee: CoreLfStructureExpression,
        arguments_: readonly CoreLfStructureExpressionArgument[]
    ): CoreLfStructureExpression;

    apply(
        callee: CoreLfStructureExpression,
        value: CoreLfStructureExpression,
        plicity?: 'explicit' | 'implicit'
    ): CoreLfStructureExpression;

    pi(
        hint: string,
        type: CoreLfStructureExpression,
        body: (
            token: CoreLfStructureBinderToken
        ) => CoreLfStructureExpression,
        mode?: BinderMode
    ): CoreLfStructureExpression;

    lam(
        hint: string,
        type: CoreLfStructureExpression,
        body: (
            token: CoreLfStructureBinderToken
        ) => CoreLfStructureExpression,
        mode?: BinderMode
    ): CoreLfStructureExpression;

    /** Declare one parameter before all fields in this structure. */
    parameter(
        input: CoreLfStructureParameterInput
    ): CoreLfStructureParameterToken;

    field(input: CoreLfStructureFieldInput): CoreLfStructureFieldToken;
}

export interface CoreLfStructureDeclarationCommand {
    readonly kind: 'structure-declaration';
    /** First source order occupied by the generated package. */
    readonly order: number;
    readonly carrierName: string;
    readonly constructorName: string;
    readonly fields: (builder: CoreLfStructureFieldBuilder) => void;
    readonly provenance: CoreLfTransferProvenance;
}

export type CoreLfDeclareStructureInput = Omit<
    CoreLfStructureDeclarationCommand,
    'kind'
>;

export interface CoreLfStructureProjectionHandle {
    readonly ordinal: number;
    readonly binderName: string;
    readonly structure: CoreLfQualifiedSymbol;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly fieldMode: BinderMode;
    readonly betaRuleId: string;
}

export interface CoreLfStructureParameterHandle {
    readonly ordinal: number;
    readonly binderName: string;
    readonly structure: CoreLfQualifiedSymbol;
    readonly modes: CoreLfStructureParameterModes;
}

export interface CoreLfStructureHandle {
    readonly carrier: CoreLfQualifiedSymbol;
    readonly carrierTerm: CoreLfTransferExpression;
    readonly constructor: CoreLfQualifiedSymbol;
    readonly constructorTerm: CoreLfTransferExpression;
    readonly parameters: readonly CoreLfStructureParameterHandle[];
    readonly projections: readonly CoreLfStructureProjectionHandle[];
}

export interface CoreLfStructureNamedParameterArgument {
    readonly parameter: CoreLfStructureParameterHandle;
    readonly value: CoreLfTransferExpression;
}

export interface CoreLfStructureNamedFieldArgument {
    readonly field: CoreLfStructureProjectionHandle;
    readonly value: CoreLfTransferExpression;
}

export interface CoreLfNamedStructureConstructionInput {
    readonly structure: CoreLfStructureHandle;
    readonly parameters:
        readonly CoreLfStructureNamedParameterArgument[];
    readonly fields: readonly CoreLfStructureNamedFieldArgument[];
}

export interface CoreLfStructureDeclarationExpansion {
    readonly kind: 'expanded-structure-declaration';
    readonly sourceOrders: readonly number[];
    readonly declarations: readonly CoreLfTransferDeclaration[];
    readonly runtimeRules: readonly CoreLfTransferRuntimeRule[];
    readonly handle: CoreLfStructureHandle;
    readonly nextOrder: number;
}

export interface CoreLfStructureLambdapiEmissionOptions {
    readonly backendName: (symbol: CoreLfQualifiedSymbol) => string;
}

type StructureNode =
    | {
        readonly tag: 'type';
    }
    | {
        readonly tag: 'global';
        readonly symbol: CoreLfQualifiedSymbol;
    }
    | {
        readonly tag: 'field';
        readonly ordinal: number;
        readonly binderName: string;
        readonly projectionName: string;
    }
    | {
        readonly tag: 'parameter';
        readonly ordinal: number;
        readonly binderName: string;
    }
    | {
        readonly tag: 'token';
        readonly ordinal: number;
        readonly hint: string;
    }
    | {
        readonly tag: 'call';
        readonly callee: InternalStructureExpression;
        readonly arguments: readonly {
            readonly plicity: 'explicit' | 'implicit';
            readonly value: InternalStructureExpression;
        }[];
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly hint: string;
        readonly mode: BinderMode;
        readonly type: InternalStructureExpression;
        readonly token: InternalStructureExpression;
        readonly body: InternalStructureExpression;
    };

interface InternalStructureExpression extends CoreLfStructureExpression {
    readonly builderIdentity: symbol;
    readonly node: StructureNode;
    readonly [STRUCTURE_BINDER_TOKEN]?: true;
    readonly [STRUCTURE_PARAMETER_TOKEN]?: true;
    readonly [STRUCTURE_FIELD_TOKEN]?: true;
    readonly ordinal?: number;
    readonly binderName?: string;
    readonly projectionName?: string;
}

interface InternalStructureParameter {
    readonly ordinal: number;
    readonly binderName: string;
    readonly modes: CoreLfStructureParameterModes;
    readonly type: InternalStructureExpression;
}

interface InternalStructureField {
    readonly ordinal: number;
    readonly binderName: string;
    readonly projectionName: string;
    readonly mode: BinderMode;
    readonly type: InternalStructureExpression;
}

type StructureLowering =
    | {
        readonly kind: 'binder';
        readonly subject: 'parameter' | 'field';
        readonly subjectIndex: number;
        readonly parameters: readonly InternalStructureParameter[];
    }
    | {
        readonly kind: 'projection';
        readonly subjectIndex: number;
        readonly parameters: readonly InternalStructureParameter[];
        readonly projections: readonly CoreLfQualifiedSymbol[];
    }
    | {
        readonly kind: 'capture';
        readonly subject: 'parameter' | 'field';
        readonly subjectIndex: number;
        readonly parameters: readonly InternalStructureParameter[];
        readonly fields: readonly InternalStructureField[];
    };

const fail = (
    code: CoreLfStructureMacroErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfStructureMacroError(code, path, message);
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

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const validateSymbol = (
    symbol: CoreLfQualifiedSymbol,
    path: string
): void => {
    if (
        typeof symbol !== 'object' ||
        symbol === null ||
        !MODULE_ID.test(symbol.moduleId) ||
        typeof symbol.name !== 'string' ||
        symbol.name.length === 0 ||
        symbol.name.trim() !== symbol.name ||
        /[\s\u0000-\u001f\u007f]/u.test(symbol.name)
    ) {
        fail(
            'INVALID_SCOPE',
            path,
            'Structure macro scope contains an invalid qualified symbol'
        );
    }
};

const validateOutputName = (
    name: string,
    path: string,
    code: 'INVALID_COMMAND' | 'INVALID_FIELD' = 'INVALID_COMMAND'
): void => {
    if (typeof name !== 'string' || !OUTPUT_NAME.test(name)) {
        fail(
            code,
            path,
            `Invalid generated structure name '${String(name)}'`
        );
    }
};

const validateBinderName = (name: string, path: string): void => {
    if (typeof name !== 'string' || !OUTPUT_NAME.test(name)) {
        fail(
            'INVALID_FIELD',
            path,
            `Invalid structure binder name '${String(name)}'`
        );
    }
};

const validateMode = (mode: BinderMode, path: string): void => {
    if (
        typeof mode !== 'object' ||
        mode === null ||
        (
            mode.plicity !== 'explicit' &&
            mode.plicity !== 'implicit'
        ) ||
        (
            mode.variation !== 'functorial' &&
            mode.variation !== 'natural' &&
            mode.variation !== 'object-only'
        )
    ) {
        fail(
            'INVALID_FIELD',
            path,
            'Structure binder mode is invalid'
        );
    }
};

const validateParameterModes = (
    modes: CoreLfStructureParameterModes,
    path: string
): void => {
    if (typeof modes !== 'object' || modes === null) {
        fail(
            'INVALID_PARAMETER',
            path,
            'Structure parameter modes must be an object'
        );
    }
    for (const owner of ['carrier', 'constructor', 'projection'] as const) {
        try {
            validateMode(modes[owner], `${path}.${owner}`);
        } catch (error) {
            if (error instanceof CoreLfStructureMacroError) {
                fail('INVALID_PARAMETER', error.path, error.message);
            }
            throw error;
        }
    }
};

const validateProvenance = (
    provenance: CoreLfTransferProvenance,
    path: string
): void => {
    if (
        typeof provenance !== 'object' ||
        provenance === null ||
        typeof provenance.authorityPath !== 'string' ||
        provenance.authorityPath.length === 0 ||
        typeof provenance.sourceFragment !== 'string' ||
        provenance.sourceFragment.length === 0 ||
        (
            provenance.canonicalCommandOrdinal !== undefined &&
            (
                !Number.isSafeInteger(
                    provenance.canonicalCommandOrdinal
                ) ||
                provenance.canonicalCommandOrdinal < 0
            )
        )
    ) {
        fail(
            'INVALID_COMMAND',
            path,
            'Structure command provenance cannot be empty'
        );
    }
};

const cloneExpression = (
    expression: CoreLfTransferExpression,
    path: string,
    depth = 0
): CoreLfTransferExpression => {
    switch (expression.tag) {
        case 'type':
            return { tag: 'type' };
        case 'global':
            validateSymbol(expression.symbol, `${path}.symbol`);
            return {
                tag: 'global',
                symbol: { ...expression.symbol }
            };
        case 'bound':
            if (
                !Number.isSafeInteger(expression.index) ||
                expression.index < 0 ||
                expression.index >= depth
            ) {
                return fail(
                    'INVALID_SCOPE',
                    path,
                    'Available global type contains a dangling bound index'
                );
            }
            return { tag: 'bound', index: expression.index };
        case 'call':
            if (expression.arguments.length === 0) {
                return fail(
                    'INVALID_SCOPE',
                    `${path}.arguments`,
                    'Available global type contains an empty call'
                );
            }
            return {
                tag: 'call',
                callee: cloneExpression(
                    expression.callee,
                    `${path}.callee`,
                    depth
                ),
                arguments: expression.arguments.map((argument, index) => {
                    if (
                        argument.plicity !== 'explicit' &&
                        argument.plicity !== 'implicit'
                    ) {
                        return fail(
                            'INVALID_SCOPE',
                            `${path}.arguments[${index}].plicity`,
                            'Available global type has invalid plicity'
                        );
                    }
                    return {
                        plicity: argument.plicity,
                        value: cloneExpression(
                            argument.value,
                            `${path}.arguments[${index}].value`,
                            depth
                        )
                    };
                })
            };
        case 'pi':
        case 'lambda':
            validateMode(expression.binder.mode, `${path}.binder.mode`);
            return {
                tag: expression.tag,
                binder: {
                    hint: expression.binder.hint,
                    mode: { ...expression.binder.mode },
                    type: cloneExpression(
                        expression.binder.type,
                        `${path}.binder.type`,
                        depth
                    )
                },
                body: cloneExpression(
                    expression.body,
                    `${path}.body`,
                    depth + 1
                )
            };
        case 'capture':
        case 'wildcard':
            return fail(
                'INVALID_SCOPE',
                path,
                'Available global type cannot contain rule syntax'
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const globalExpression = (
    symbol: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({
    tag: 'global',
    symbol: { ...symbol }
});

const callExpression = (
    callee: CoreLfTransferExpression,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => ({
    tag: 'call',
    callee,
    arguments: arguments_.map(argument => ({
        plicity: argument.plicity,
        value: argument.value
    }))
});

const callGlobal = (
    symbol: CoreLfQualifiedSymbol,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => callExpression(
    globalExpression(symbol),
    arguments_
);

const explicit = (value: CoreLfTransferExpression) => ({
    plicity: 'explicit' as const,
    value
});

class InternalFieldBuilder implements CoreLfStructureFieldBuilder {
    private readonly builderIdentity = Symbol(
        'CoreLfStructureFieldBuilder'
    );
    private readonly parameters: InternalStructureParameter[] = [];
    private readonly fields: InternalStructureField[] = [];
    private readonly binderNames = new Set<string>();
    private readonly projectionNames = new Set<string>();
    private nextTokenOrdinal = 0;
    private fieldsStarted = false;
    private sealed = false;

    constructor(
        private readonly requireGlobal: (
            value: CoreLfResolvedStructureGlobal,
            path: string
        ) => InternalResolvedGlobal
    ) {}

    private requireOpen(path: string): void {
        if (this.sealed) {
            fail(
                'INVALID_FIELD',
                path,
                'Structure field builder is already sealed'
            );
        }
    }

    private makeExpression(
        node: StructureNode,
        kind?: 'binder' | 'parameter' | 'field'
    ): InternalStructureExpression {
        return Object.freeze({
            [STRUCTURE_EXPRESSION]: true as const,
            ...(kind === 'binder'
                ? { [STRUCTURE_BINDER_TOKEN]: true as const }
                : {}),
            ...(kind === 'parameter'
                ? { [STRUCTURE_PARAMETER_TOKEN]: true as const }
                : {}),
            ...(kind === 'field'
                ? { [STRUCTURE_FIELD_TOKEN]: true as const }
                : {}),
            builderIdentity: this.builderIdentity,
            node: deepFreeze(node),
            ...(node.tag === 'parameter' || node.tag === 'field'
                ? {
                    ordinal: node.ordinal,
                    binderName: node.binderName,
                    ...(node.tag === 'field'
                        ? { projectionName: node.projectionName }
                        : {})
                }
                : {})
        });
    }

    private requireExpression(
        value: CoreLfStructureExpression,
        path: string
    ): InternalStructureExpression {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalStructureExpression)[
                STRUCTURE_EXPRESSION
            ] !== true ||
            (value as InternalStructureExpression).builderIdentity !==
                this.builderIdentity
        ) {
            return fail(
                'FOREIGN_EXPRESSION',
                path,
                'Structure expression belongs to another field builder'
            );
        }
        return value as InternalStructureExpression;
    }

    private token(hint: string): InternalStructureExpression {
        return this.makeExpression({
            tag: 'token',
            ordinal: this.nextTokenOrdinal++,
            hint
        }, 'binder');
    }

    private bind(
        tag: 'pi' | 'lambda',
        hint: string,
        type: CoreLfStructureExpression,
        body: (
            token: CoreLfStructureBinderToken
        ) => CoreLfStructureExpression,
        mode: BinderMode
    ): CoreLfStructureExpression {
        this.requireOpen(tag);
        validateBinderName(hint, `${tag}.binder.hint`);
        validateMode(mode, `${tag}.binder.mode`);
        if (typeof body !== 'function') {
            return fail(
                'INVALID_FIELD',
                `${tag}.body`,
                'Structure binder body must be a callback'
            );
        }
        const checkedType = this.requireExpression(
            type,
            `${tag}.binder.type`
        );
        const token = this.token(hint);
        const checkedBody = this.requireExpression(
            body(token as CoreLfStructureBinderToken),
            `${tag}.body`
        );
        return this.makeExpression({
            tag,
            hint,
            mode: { ...mode },
            type: checkedType,
            token,
            body: checkedBody
        });
    }

    type(): CoreLfStructureExpression {
        this.requireOpen('type');
        return this.makeExpression({ tag: 'type' });
    }

    global(
        value: CoreLfResolvedStructureGlobal
    ): CoreLfStructureExpression {
        this.requireOpen('global');
        const resolved = this.requireGlobal(value, 'global.value');
        return this.makeExpression({
            tag: 'global',
            symbol: { ...resolved.symbol }
        });
    }

    call(
        callee: CoreLfStructureExpression,
        arguments_: readonly CoreLfStructureExpressionArgument[]
    ): CoreLfStructureExpression {
        this.requireOpen('call');
        if (!Array.isArray(arguments_) || arguments_.length === 0) {
            return fail(
                'INVALID_FIELD',
                'call.arguments',
                'Structure call requires at least one argument'
            );
        }
        return this.makeExpression({
            tag: 'call',
            callee: this.requireExpression(callee, 'call.callee'),
            arguments: arguments_.map((argument, index) => {
                if (
                    typeof argument !== 'object' ||
                    argument === null ||
                    (
                        argument.plicity !== 'explicit' &&
                        argument.plicity !== 'implicit'
                    )
                ) {
                    return fail(
                        'INVALID_FIELD',
                        `call.arguments[${index}]`,
                        'Structure call argument has invalid plicity'
                    );
                }
                return {
                    plicity: argument.plicity,
                    value: this.requireExpression(
                        argument.value,
                        `call.arguments[${index}].value`
                    )
                };
            })
        });
    }

    apply(
        callee: CoreLfStructureExpression,
        value: CoreLfStructureExpression,
        plicity: 'explicit' | 'implicit' = 'explicit'
    ): CoreLfStructureExpression {
        return this.call(callee, [{ plicity, value }]);
    }

    pi(
        hint: string,
        type: CoreLfStructureExpression,
        body: (
            token: CoreLfStructureBinderToken
        ) => CoreLfStructureExpression,
        mode: BinderMode = {
            plicity: 'explicit',
            variation: 'functorial'
        }
    ): CoreLfStructureExpression {
        return this.bind('pi', hint, type, body, mode);
    }

    lam(
        hint: string,
        type: CoreLfStructureExpression,
        body: (
            token: CoreLfStructureBinderToken
        ) => CoreLfStructureExpression,
        mode: BinderMode = {
            plicity: 'explicit',
            variation: 'functorial'
        }
    ): CoreLfStructureExpression {
        return this.bind('lambda', hint, type, body, mode);
    }

    parameter(
        input: CoreLfStructureParameterInput
    ): CoreLfStructureParameterToken {
        this.requireOpen('parameter');
        const index = this.parameters.length;
        const path = `command.parameters[${index}]`;
        if (this.fieldsStarted) {
            return fail(
                'INVALID_PARAMETER',
                path,
                'Structure parameters must be declared before every field'
            );
        }
        if (typeof input !== 'object' || input === null) {
            return fail(
                'INVALID_PARAMETER',
                path,
                'Structure parameter must be an object'
            );
        }
        if (
            typeof input.binderName !== 'string' ||
            !OUTPUT_NAME.test(input.binderName)
        ) {
            return fail(
                'INVALID_PARAMETER',
                `${path}.binderName`,
                `Invalid structure parameter binder ` +
                    `'${String(input.binderName)}'`
            );
        }
        validateParameterModes(input.modes, `${path}.modes`);
        if (this.binderNames.has(input.binderName)) {
            return fail(
                'INVALID_PARAMETER',
                `${path}.binderName`,
                `Duplicate structure binder '${input.binderName}'`
            );
        }
        const type = this.requireExpression(input.type, `${path}.type`);
        this.binderNames.add(input.binderName);
        const parameter: InternalStructureParameter = deepFreeze({
            ordinal: index,
            binderName: input.binderName,
            modes: {
                carrier: { ...input.modes.carrier },
                constructor: { ...input.modes.constructor },
                projection: { ...input.modes.projection }
            },
            type
        });
        this.parameters.push(parameter);
        return this.makeExpression({
            tag: 'parameter',
            ordinal: parameter.ordinal,
            binderName: parameter.binderName
        }, 'parameter') as CoreLfStructureParameterToken;
    }

    field(input: CoreLfStructureFieldInput): CoreLfStructureFieldToken {
        this.requireOpen('field');
        this.fieldsStarted = true;
        const index = this.fields.length;
        const path = `command.fields[${index}]`;
        if (typeof input !== 'object' || input === null) {
            return fail(
                'INVALID_FIELD',
                path,
                'Structure field must be an object'
            );
        }
        validateBinderName(input.binderName, `${path}.binderName`);
        validateOutputName(
            input.projectionName,
            `${path}.projectionName`,
            'INVALID_FIELD'
        );
        validateMode(input.mode, `${path}.mode`);
        if (this.binderNames.has(input.binderName)) {
            return fail(
                'INVALID_FIELD',
                `${path}.binderName`,
                `Duplicate structure binder '${input.binderName}'`
            );
        }
        if (this.projectionNames.has(input.projectionName)) {
            return fail(
                'DUPLICATE_SYMBOL',
                `${path}.projectionName`,
                `Duplicate projection '${input.projectionName}'`
            );
        }
        const type = this.requireExpression(input.type, `${path}.type`);
        this.binderNames.add(input.binderName);
        this.projectionNames.add(input.projectionName);
        const field: InternalStructureField = deepFreeze({
            ordinal: index,
            binderName: input.binderName,
            projectionName: input.projectionName,
            mode: { ...input.mode },
            type
        });
        this.fields.push(field);
        return this.makeExpression({
            tag: 'field',
            ordinal: field.ordinal,
            binderName: field.binderName,
            projectionName: field.projectionName
        }, 'field') as CoreLfStructureFieldToken;
    }

    finish(): {
        readonly parameters: readonly InternalStructureParameter[];
        readonly fields: readonly InternalStructureField[];
    } {
        this.sealed = true;
        if (this.fields.length === 0) {
            return fail(
                'INVALID_COMMAND',
                'command.fields',
                'First structure slice requires at least one field'
            );
        }
        return deepFreeze({
            parameters: [...this.parameters],
            fields: [...this.fields]
        });
    }
}

const lowerStructureExpression = (
    expression: InternalStructureExpression,
    lowering: StructureLowering
): CoreLfTransferExpression => {
    const subjectPath = (): string => {
        if (lowering.kind === 'projection') {
            return `command.fields[${lowering.subjectIndex}].type`;
        }
        return lowering.subject === 'parameter'
            ? `command.parameters[${lowering.subjectIndex}].type`
            : `command.fields[${lowering.subjectIndex}].type`;
    };
    const visit = (
        current: InternalStructureExpression,
        scope: readonly InternalStructureExpression[]
    ): CoreLfTransferExpression => {
        switch (current.node.tag) {
            case 'type':
                return { tag: 'type' };
            case 'global':
                return globalExpression(current.node.symbol);
            case 'parameter': {
                const ordinal = current.node.ordinal;
                if (
                    lowering.kind !== 'projection' &&
                    lowering.subject === 'parameter' &&
                    ordinal >= lowering.subjectIndex
                ) {
                    return fail(
                        'INVALID_PARAMETER',
                        subjectPath(),
                        `Parameter '${current.node.binderName}' is not ` +
                            'earlier than the parameter whose type ' +
                            'references it'
                    );
                }
                switch (lowering.kind) {
                    case 'binder':
                        return {
                            tag: 'bound',
                            index:
                                scope.length +
                                (lowering.subject === 'parameter'
                                    ? lowering.subjectIndex
                                    : lowering.subjectIndex +
                                        lowering.parameters.length) -
                                ordinal -
                                1
                        };
                    case 'projection':
                        return {
                            tag: 'bound',
                            index:
                                scope.length +
                                lowering.parameters.length -
                                ordinal
                        };
                    case 'capture':
                        return {
                            tag: 'capture',
                            name:
                                lowering.parameters[ordinal].binderName
                        };
                    default: {
                        const exhaustive: never = lowering;
                        return exhaustive;
                    }
                }
            }
            case 'field': {
                const ordinal = current.node.ordinal;
                if (
                    lowering.kind !== 'projection' &&
                    lowering.subject === 'parameter'
                ) {
                    return fail(
                        'INVALID_PARAMETER',
                        subjectPath(),
                        'A structure parameter type cannot reference a field'
                    );
                }
                const fieldIndex = lowering.subjectIndex;
                if (ordinal >= fieldIndex) {
                    return fail(
                        'INVALID_FIELD',
                        subjectPath(),
                        `Field '${current.node.binderName}' is not earlier ` +
                            'than the field whose type references it'
                    );
                }
                switch (lowering.kind) {
                    case 'binder':
                        return {
                            tag: 'bound',
                            index:
                                scope.length +
                                fieldIndex -
                                ordinal -
                                1
                        };
                    case 'projection': {
                        const parameterArguments = lowering.parameters.map(
                            parameter => ({
                                plicity:
                                    parameter.modes.projection.plicity,
                                value: {
                                    tag: 'bound' as const,
                                    index:
                                        scope.length +
                                        lowering.parameters.length -
                                        parameter.ordinal
                                }
                            })
                        );
                        return callGlobal(
                            lowering.projections[ordinal],
                            [...parameterArguments, explicit({
                                tag: 'bound',
                                index: scope.length
                            })]
                        );
                    }
                    case 'capture':
                        return {
                            tag: 'capture',
                            name: lowering.fields[ordinal].binderName
                        };
                    default: {
                        const exhaustive: never = lowering;
                        return exhaustive;
                    }
                }
            }
            case 'token': {
                const position = scope.lastIndexOf(current);
                if (position < 0) {
                    return fail(
                        'ESCAPED_BINDER',
                        subjectPath(),
                        `Structure binder token '${current.node.hint}' ` +
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
            default: {
                const exhaustive: never = current.node;
                return exhaustive;
            }
        }
    };
    return deepFreeze(visit(expression, []));
};

const wrapFields = (
    fields: readonly InternalStructureField[],
    types: readonly CoreLfTransferExpression[],
    result: CoreLfTransferExpression
): CoreLfTransferExpression =>
    fields.reduceRight<CoreLfTransferExpression>(
        (body, field, index) => ({
            tag: 'pi',
            binder: {
                hint: field.binderName,
                mode: { ...field.mode },
                type: types[index]
            },
            body
        }),
        result
    );

type StructureParameterModeOwner = keyof CoreLfStructureParameterModes;

const wrapParameters = (
    parameters: readonly InternalStructureParameter[],
    types: readonly CoreLfTransferExpression[],
    owner: StructureParameterModeOwner,
    result: CoreLfTransferExpression
): CoreLfTransferExpression =>
    parameters.reduceRight<CoreLfTransferExpression>(
        (body, parameter, index) => ({
            tag: 'pi',
            binder: {
                hint: parameter.binderName,
                mode: { ...parameter.modes[owner] },
                type: types[index]
            },
            body
        }),
        result
    );

const applyBoundParameters = (
    symbol: CoreLfQualifiedSymbol,
    parameters: readonly InternalStructureParameter[],
    owner: StructureParameterModeOwner,
    innerBinderCount: number
): CoreLfTransferExpression => parameters.length === 0
    ? globalExpression(symbol)
    : callGlobal(
        symbol,
        parameters.map(parameter => ({
            plicity: parameter.modes[owner].plicity,
            value: {
                tag: 'bound' as const,
                index:
                    innerBinderCount +
                    parameters.length -
                    parameter.ordinal -
                    1
            }
        }))
    );

const captureParameters = (
    parameters: readonly InternalStructureParameter[],
    owner: StructureParameterModeOwner
) => parameters.map(parameter => ({
    plicity: parameter.modes[owner].plicity,
    value: {
        tag: 'capture' as const,
        name: parameter.binderName
    }
}));

const isQualifiedSymbol = (
    value: unknown
): value is CoreLfQualifiedSymbol =>
    typeof value === 'object' &&
    value !== null &&
    MODULE_ID.test((value as CoreLfQualifiedSymbol).moduleId) &&
    typeof (value as CoreLfQualifiedSymbol).name === 'string' &&
    (value as CoreLfQualifiedSymbol).name.length > 0 &&
    (value as CoreLfQualifiedSymbol).name.trim() ===
        (value as CoreLfQualifiedSymbol).name &&
    !/[\s\u0000-\u001f\u007f]/u.test(
        (value as CoreLfQualifiedSymbol).name
    );

const sameSymbol = (
    left: unknown,
    right: unknown
): boolean =>
    isQualifiedSymbol(left) &&
    isQualifiedSymbol(right) &&
    symbolKey(left) === symbolKey(right);

const isBinderMode = (value: unknown): value is BinderMode =>
    typeof value === 'object' &&
    value !== null &&
    (
        (value as BinderMode).plicity === 'explicit' ||
        (value as BinderMode).plicity === 'implicit'
    ) &&
    (
        (value as BinderMode).variation === 'functorial' ||
        (value as BinderMode).variation === 'natural' ||
        (value as BinderMode).variation === 'object-only'
    );

const sameMode = (left: unknown, right: unknown): boolean =>
    isBinderMode(left) &&
    isBinderMode(right) &&
    left.plicity === right.plicity &&
    left.variation === right.variation;

const validateConstructionHandle = (
    structure: CoreLfStructureHandle
): void => {
    const invalid = (path: string, message: string): never => fail(
        'INVALID_CONSTRUCTION',
        path,
        message
    );
    if (
        typeof structure !== 'object' ||
        structure === null ||
        !Array.isArray(structure.parameters) ||
        !Array.isArray(structure.projections)
    ) {
        return invalid(
            'input.structure',
            'Named construction requires one complete structure handle'
        );
    }
    try {
        validateSymbol(structure.carrier, 'input.structure.carrier');
        validateSymbol(structure.constructor, 'input.structure.constructor');
    } catch (error) {
        if (error instanceof CoreLfStructureMacroError) {
            return invalid(error.path, error.message);
        }
        throw error;
    }
    if (
        structure.carrierTerm?.tag !== 'global' ||
        !isQualifiedSymbol(structure.carrierTerm.symbol) ||
        !sameSymbol(structure.carrierTerm.symbol, structure.carrier) ||
        structure.constructorTerm?.tag !== 'global' ||
        !isQualifiedSymbol(structure.constructorTerm.symbol) ||
        !sameSymbol(
            structure.constructorTerm.symbol,
            structure.constructor
        )
    ) {
        return invalid(
            'input.structure',
            'Structure handle heads do not match its carrier and constructor'
        );
    }
    const parameterNames = new Set<string>();
    structure.parameters.forEach((parameter, index) => {
        const path = `input.structure.parameters[${index}]`;
        if (
            typeof parameter !== 'object' ||
            parameter === null ||
            parameter.ordinal !== index ||
            typeof parameter.binderName !== 'string' ||
            !OUTPUT_NAME.test(parameter.binderName) ||
            !isQualifiedSymbol(parameter.structure) ||
            !sameSymbol(parameter.structure, structure.carrier)
        ) {
            return invalid(path, 'Malformed structure parameter handle');
        }
        if (parameterNames.has(parameter.binderName)) {
            return invalid(path, 'Duplicate structure parameter handle');
        }
        parameterNames.add(parameter.binderName);
        try {
            validateParameterModes(parameter.modes, `${path}.modes`);
        } catch (error) {
            if (error instanceof CoreLfStructureMacroError) {
                return invalid(error.path, error.message);
            }
            throw error;
        }
    });
    if (structure.projections.length === 0) {
        return invalid(
            'input.structure.projections',
            'Named construction requires at least one structure field'
        );
    }
    const fieldNames = new Set<string>();
    const projectionSymbols = new Set<string>();
    structure.projections.forEach((field, index) => {
        const path = `input.structure.projections[${index}]`;
        if (
            typeof field !== 'object' ||
            field === null ||
            field.ordinal !== index ||
            typeof field.binderName !== 'string' ||
            !OUTPUT_NAME.test(field.binderName) ||
            !isQualifiedSymbol(field.structure) ||
            !sameSymbol(field.structure, structure.carrier) ||
            typeof field.betaRuleId !== 'string' ||
            field.betaRuleId.length === 0
        ) {
            return invalid(path, 'Malformed structure field handle');
        }
        try {
            validateSymbol(field.symbol, `${path}.symbol`);
            validateMode(field.fieldMode, `${path}.fieldMode`);
        } catch (error) {
            if (error instanceof CoreLfStructureMacroError) {
                return invalid(error.path, error.message);
            }
            throw error;
        }
        if (
            fieldNames.has(field.binderName) ||
            projectionSymbols.has(symbolKey(field.symbol))
        ) {
            return invalid(path, 'Duplicate structure field handle');
        }
        fieldNames.add(field.binderName);
        projectionSymbols.add(symbolKey(field.symbol));
    });
};

const sameParameterHandle = (
    left: CoreLfStructureParameterHandle,
    right: unknown
): boolean => {
    if (
        typeof right !== 'object' ||
        right === null ||
        typeof (right as CoreLfStructureParameterHandle).modes !== 'object' ||
        (right as CoreLfStructureParameterHandle).modes === null
    ) return false;
    const candidate = right as CoreLfStructureParameterHandle;
    return (
        left.ordinal === candidate.ordinal &&
        left.binderName === candidate.binderName &&
        sameSymbol(left.structure, candidate.structure) &&
        sameMode(left.modes.carrier, candidate.modes.carrier) &&
        sameMode(left.modes.constructor, candidate.modes.constructor) &&
        sameMode(left.modes.projection, candidate.modes.projection)
    );
};

const sameFieldHandle = (
    left: CoreLfStructureProjectionHandle,
    right: unknown
): boolean => {
    if (typeof right !== 'object' || right === null) return false;
    const candidate = right as CoreLfStructureProjectionHandle;
    return (
        left.ordinal === candidate.ordinal &&
        left.binderName === candidate.binderName &&
        sameSymbol(left.structure, candidate.structure) &&
        sameSymbol(left.symbol, candidate.symbol) &&
        sameMode(left.fieldMode, candidate.fieldMode) &&
        left.betaRuleId === candidate.betaRuleId
    );
};

const cloneConstructionValue = (
    value: CoreLfTransferExpression,
    path: string
): CoreLfTransferExpression => {
    if (typeof value !== 'object' || value === null) {
        return fail(
            'INVALID_CONSTRUCTION',
            path,
            'Named structure argument must be a transfer term'
        );
    }
    try {
        return cloneExpression(value, path, MAX_ORDER);
    } catch (error) {
        if (error instanceof CoreLfStructureMacroError) {
            return fail(
                'INVALID_CONSTRUCTION',
                error.path,
                error.message
            );
        }
        return fail(
            'INVALID_CONSTRUCTION',
            path,
            'Named structure argument is not a valid transfer term'
        );
    }
};

/**
 * Assemble one constructor call from order-independent named assignments.
 * The ordinary LF compiler/checker remains responsible for argument types.
 */
export function constructCoreLfNamedStructure(
    input: CoreLfNamedStructureConstructionInput
): CoreLfTransferExpression {
    if (typeof input !== 'object' || input === null) {
        return fail(
            'INVALID_CONSTRUCTION',
            'input',
            'Named structure construction input must be an object'
        );
    }
    validateConstructionHandle(input.structure);
    if (!Array.isArray(input.parameters)) {
        return fail(
            'INVALID_CONSTRUCTION',
            'input.parameters',
            'Named structure parameters must be an array'
        );
    }
    if (!Array.isArray(input.fields)) {
        return fail(
            'INVALID_CONSTRUCTION',
            'input.fields',
            'Named structure fields must be an array'
        );
    }

    const parameterValues: Array<CoreLfTransferExpression | undefined> =
        new Array(input.structure.parameters.length);
    for (let index = 0; index < input.parameters.length; index++) {
        const path = `input.parameters[${index}]`;
        const argument = input.parameters[index];
        if (typeof argument !== 'object' || argument === null) {
            return fail(
                'INVALID_CONSTRUCTION',
                path,
                'Named structure parameter assignment must be an object'
            );
        }
        const supplied = argument.parameter;
        if (typeof supplied !== 'object' || supplied === null) {
            return fail(
                'FOREIGN_ARGUMENT',
                `${path}.parameter`,
                'Parameter handle does not belong to the selected structure'
            );
        }
        const ordinal = supplied.ordinal;
        const canonical = Number.isSafeInteger(ordinal)
            ? input.structure.parameters[ordinal]
            : undefined;
        if (
            canonical === undefined ||
            !sameParameterHandle(canonical, supplied)
        ) {
            return fail(
                'FOREIGN_ARGUMENT',
                `${path}.parameter`,
                'Parameter handle does not belong to the selected structure'
            );
        }
        if (parameterValues[canonical.ordinal] !== undefined) {
            return fail(
                'DUPLICATE_ARGUMENT',
                `${path}.parameter`,
                `Parameter '${canonical.binderName}' was supplied twice`
            );
        }
        parameterValues[canonical.ordinal] = cloneConstructionValue(
            argument.value,
            `${path}.value`
        );
    }
    input.structure.parameters.forEach(parameter => {
        if (parameterValues[parameter.ordinal] === undefined) {
            fail(
                'MISSING_ARGUMENT',
                'input.parameters',
                `Missing parameter '${parameter.binderName}'`
            );
        }
    });

    const fieldValues: Array<CoreLfTransferExpression | undefined> =
        new Array(input.structure.projections.length);
    for (let index = 0; index < input.fields.length; index++) {
        const path = `input.fields[${index}]`;
        const argument = input.fields[index];
        if (typeof argument !== 'object' || argument === null) {
            return fail(
                'INVALID_CONSTRUCTION',
                path,
                'Named structure field assignment must be an object'
            );
        }
        const supplied = argument.field;
        if (typeof supplied !== 'object' || supplied === null) {
            return fail(
                'FOREIGN_ARGUMENT',
                `${path}.field`,
                'Field handle does not belong to the selected structure'
            );
        }
        const ordinal = supplied.ordinal;
        const canonical = Number.isSafeInteger(ordinal)
            ? input.structure.projections[ordinal]
            : undefined;
        if (
            canonical === undefined ||
            !sameFieldHandle(canonical, supplied)
        ) {
            return fail(
                'FOREIGN_ARGUMENT',
                `${path}.field`,
                'Field handle does not belong to the selected structure'
            );
        }
        if (fieldValues[canonical.ordinal] !== undefined) {
            return fail(
                'DUPLICATE_ARGUMENT',
                `${path}.field`,
                `Field '${canonical.binderName}' was supplied twice`
            );
        }
        fieldValues[canonical.ordinal] = cloneConstructionValue(
            argument.value,
            `${path}.value`
        );
    }
    input.structure.projections.forEach(field => {
        if (fieldValues[field.ordinal] === undefined) {
            fail(
                'MISSING_ARGUMENT',
                'input.fields',
                `Missing field '${field.binderName}'`
            );
        }
    });

    return deepFreeze(callGlobal(
        input.structure.constructor,
        [
            ...input.structure.parameters.map(parameter => ({
                plicity: parameter.modes.constructor.plicity,
                value: parameterValues[parameter.ordinal]!
            })),
            ...input.structure.projections.map(field => ({
                plicity: field.fieldMode.plicity,
                value: fieldValues[field.ordinal]!
            }))
        ]
    ));
}

/** Immutable resolution scope for one direct-TypeScript outer LF module. */
export class CoreLfStructureMacroScope {
    private readonly scopeIdentity = Symbol('CoreLfStructureMacroScope');
    private readonly available = new Map<string, InternalResolvedGlobal>();

    constructor(
        public readonly moduleId: string,
        availableGlobals: readonly CoreLfStructureAvailableGlobalInput[]
    ) {
        if (!MODULE_ID.test(moduleId)) {
            return fail(
                'INVALID_SCOPE',
                'scope.moduleId',
                `Invalid outer module ID '${moduleId}'`
            );
        }
        availableGlobals.forEach((entry, index) => {
            const path = `scope.availableGlobals[${index}]`;
            if (typeof entry !== 'object' || entry === null) {
                return fail(
                    'INVALID_SCOPE',
                    path,
                    'Available structure global must be an object'
                );
            }
            validateSymbol(entry.symbol, `${path}.symbol`);
            if (
                entry.availability !== 'dependency-module' &&
                entry.availability !== 'existing-core' &&
                entry.availability !== 'earlier-fragment'
            ) {
                return fail(
                    'INVALID_SCOPE',
                    `${path}.availability`,
                    'Available global has invalid availability'
                );
            }
            if (
                entry.availability === 'earlier-fragment' &&
                (
                    entry.symbol.moduleId !== moduleId ||
                    entry.order === undefined ||
                    !Number.isSafeInteger(entry.order) ||
                    entry.order < 0
                )
            ) {
                return fail(
                    'INVALID_SCOPE',
                    path,
                    'Earlier-fragment global needs a same-module order'
                );
            }
            if (
                entry.availability !== 'earlier-fragment' &&
                entry.order !== undefined
            ) {
                return fail(
                    'INVALID_SCOPE',
                    `${path}.order`,
                    'Only earlier-fragment globals carry source order'
                );
            }
            const key = symbolKey(entry.symbol);
            if (this.available.has(key)) {
                return fail(
                    'DUPLICATE_SYMBOL',
                    `${path}.symbol`,
                    `Duplicate available global ` +
                        `'${displaySymbol(entry.symbol)}'`
                );
            }
            this.available.set(key, deepFreeze({
                [RESOLVED_GLOBAL]: true as const,
                scopeIdentity: this.scopeIdentity,
                symbol: { ...entry.symbol },
                type: cloneExpression(entry.type, `${path}.type`),
                availability: entry.availability,
                ...(entry.order === undefined
                    ? {}
                    : { order: entry.order })
            }));
        });
        Object.freeze(this);
    }

    resolve(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfResolvedStructureGlobal {
        validateSymbol(symbol, 'resolve.symbol');
        const resolved = this.available.get(symbolKey(symbol));
        if (resolved === undefined) {
            return fail(
                'UNAVAILABLE_GLOBAL',
                'resolve.symbol',
                `Global '${displaySymbol(symbol)}' is not available`
            );
        }
        return resolved;
    }

    private requireHandle(
        value: CoreLfResolvedStructureGlobal,
        path: string,
        commandOrder: number
    ): InternalResolvedGlobal {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalResolvedGlobal)[RESOLVED_GLOBAL] !== true ||
            (value as InternalResolvedGlobal).scopeIdentity !==
                this.scopeIdentity
        ) {
            return fail(
                'FOREIGN_GLOBAL',
                path,
                'Structure input is not a global resolved in this scope'
            );
        }
        const resolved = value as InternalResolvedGlobal;
        if (
            resolved.availability === 'earlier-fragment' &&
            resolved.order !== undefined &&
            resolved.order >= commandOrder
        ) {
            return fail(
                'FORWARD_GLOBAL',
                path,
                `Global '${displaySymbol(resolved.symbol)}' occurs at ` +
                    `source order ${resolved.order}, not before ` +
                    commandOrder
            );
        }
        return resolved;
    }

    declareStructure(
        input: CoreLfDeclareStructureInput
    ): CoreLfStructureDeclarationExpansion {
        return this.expand({
            ...input,
            kind: 'structure-declaration'
        });
    }

    expand(
        command: CoreLfStructureDeclarationCommand
    ): CoreLfStructureDeclarationExpansion {
        if (
            typeof command !== 'object' ||
            command === null ||
            command.kind !== 'structure-declaration'
        ) {
            return fail(
                'INVALID_COMMAND',
                'command.kind',
                'Expected a structure-declaration command'
            );
        }
        if (!Number.isSafeInteger(command.order) || command.order < 0) {
            return fail(
                'INVALID_COMMAND',
                'command.order',
                'Structure source order must be a nonnegative safe integer'
            );
        }
        validateOutputName(command.carrierName, 'command.carrierName');
        validateOutputName(
            command.constructorName,
            'command.constructorName'
        );
        validateProvenance(command.provenance, 'command.provenance');
        if (typeof command.fields !== 'function') {
            return fail(
                'INVALID_COMMAND',
                'command.fields',
                'Structure fields must be declared by one callback'
            );
        }

        const builder = new InternalFieldBuilder((value, path) =>
            this.requireHandle(value, path, command.order)
        );
        const callbackResult: unknown = command.fields(builder);
        if (
            typeof callbackResult === 'object' &&
            callbackResult !== null &&
            'then' in callbackResult
        ) {
            return fail(
                'INVALID_COMMAND',
                'command.fields',
                'Structure field callback must be synchronous'
            );
        }
        const { parameters, fields } = builder.finish();
        const commandCount = 2 + fields.length * 2;
        if (command.order > MAX_ORDER - commandCount) {
            return fail(
                'INVALID_COMMAND',
                'command.order',
                'Structure source order cannot reserve its expansion'
            );
        }

        const carrier: CoreLfQualifiedSymbol = {
            moduleId: this.moduleId,
            name: command.carrierName
        };
        const constructor: CoreLfQualifiedSymbol = {
            moduleId: this.moduleId,
            name: command.constructorName
        };
        const projections = fields.map(field => ({
            moduleId: this.moduleId,
            name: field.projectionName
        }));
        const generated = [carrier, constructor, ...projections];
        const generatedKeys = new Set<string>();
        generated.forEach((symbol, index) => {
            const key = symbolKey(symbol);
            if (generatedKeys.has(key) || this.available.has(key)) {
                return fail(
                    'DUPLICATE_SYMBOL',
                    index === 0
                        ? 'command.carrierName'
                        : index === 1
                            ? 'command.constructorName'
                            : `command.fields[${index - 2}].projectionName`,
                    `Global '${displaySymbol(symbol)}' already exists`
                );
            }
            generatedKeys.add(key);
        });

        const provenance = { ...command.provenance };
        const parameterTypes = parameters.map((parameter, parameterIndex) =>
            lowerStructureExpression(parameter.type, {
                kind: 'binder',
                subject: 'parameter',
                subjectIndex: parameterIndex,
                parameters
            })
        );
        const constructorFieldTypes = fields.map((field, fieldIndex) =>
            lowerStructureExpression(field.type, {
                kind: 'binder',
                subject: 'field',
                subjectIndex: fieldIndex,
                parameters
            })
        );
        const carrierTerm = globalExpression(carrier);
        const constructorTerm = globalExpression(constructor);
        const declarations: CoreLfTransferDeclaration[] = [
            {
                order: command.order,
                symbol: carrier,
                type: wrapParameters(
                    parameters,
                    parameterTypes,
                    'carrier',
                    { tag: 'type' }
                ),
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'constant',
                    sourceOpacity: 'opaque'
                },
                provenance
            },
            {
                order: command.order + 1,
                symbol: constructor,
                type: wrapParameters(
                    parameters,
                    parameterTypes,
                    'constructor',
                    wrapFields(
                        fields,
                        constructorFieldTypes,
                        applyBoundParameters(
                            carrier,
                            parameters,
                            'carrier',
                            fields.length
                        )
                    )
                ),
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'injective',
                    sourceOpacity: 'opaque'
                },
                provenance
            },
            ...fields.map((field, fieldIndex) => ({
                order: command.order + 2 + fieldIndex,
                symbol: projections[fieldIndex],
                type: wrapParameters(
                    parameters,
                    parameterTypes,
                    'projection',
                    {
                        tag: 'pi' as const,
                        binder: {
                            hint: 'record',
                            mode: {
                                plicity: 'explicit' as const,
                                variation: 'functorial' as const
                            },
                            type: applyBoundParameters(
                                carrier,
                                parameters,
                                'carrier',
                                0
                            )
                        },
                        body: lowerStructureExpression(field.type, {
                            kind: 'projection' as const,
                            subjectIndex: fieldIndex,
                            parameters,
                            projections
                        })
                    }
                ),
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: 'ordinary' as const,
                    sourceOpacity: 'opaque' as const
                },
                provenance
            }))
        ];

        const constructorPattern = callGlobal(
            constructor,
            [
                ...captureParameters(parameters, 'constructor'),
                ...fields.map(field => ({
                    plicity: field.mode.plicity,
                    value: {
                        tag: 'capture' as const,
                        name: field.binderName
                    }
                }))
            ]
        );
        const runtimeRules = fields.map((field, fieldIndex) => {
            const id =
                `structure.${command.carrierName}.` +
                `${field.projectionName}.beta`;
            return {
                order:
                    command.order + 2 + fields.length + fieldIndex,
                id,
                groupId: id,
                clauseOrder: 0,
                sourceOwner: projections[fieldIndex],
                variables: [
                    ...parameters.map((parameter, parameterIndex) => ({
                        name: parameter.binderName,
                        type: lowerStructureExpression(parameter.type, {
                            kind: 'capture' as const,
                            subject: 'parameter' as const,
                            subjectIndex: parameterIndex,
                            parameters,
                            fields
                        })
                    })),
                    ...fields.map((variable, variableIndex) => ({
                        name: variable.binderName,
                        type: lowerStructureExpression(variable.type, {
                            kind: 'capture' as const,
                            subject: 'field' as const,
                            subjectIndex: variableIndex,
                            parameters,
                            fields
                        })
                    }))
                ],
                left: callGlobal(
                    projections[fieldIndex],
                    [
                        ...captureParameters(parameters, 'projection'),
                        explicit(constructorPattern)
                    ]
                ),
                right: {
                    tag: 'capture' as const,
                    name: field.binderName
                },
                provenance
            };
        });
        const sourceOrders = Array.from(
            { length: commandCount },
            (_unused, index) => command.order + index
        );
        const handleProjections = fields.map((field, index) => ({
            ordinal: field.ordinal,
            binderName: field.binderName,
            structure: { ...carrier },
            symbol: projections[index],
            fieldMode: { ...field.mode },
            betaRuleId: runtimeRules[index].id
        }));
        const handleParameters = parameters.map(parameter => ({
            ordinal: parameter.ordinal,
            binderName: parameter.binderName,
            structure: { ...carrier },
            modes: {
                carrier: { ...parameter.modes.carrier },
                constructor: { ...parameter.modes.constructor },
                projection: { ...parameter.modes.projection }
            }
        }));

        return deepFreeze({
            kind: 'expanded-structure-declaration' as const,
            sourceOrders,
            declarations,
            runtimeRules,
            handle: {
                carrier,
                carrierTerm,
                constructor,
                constructorTerm,
                parameters: handleParameters,
                projections: handleProjections
            },
            nextOrder: command.order + commandCount
        });
    }
}

const backendName = (
    symbol: CoreLfQualifiedSymbol,
    options: CoreLfStructureLambdapiEmissionOptions,
    path: string,
    generated = false
): string => {
    const name = options.backendName(symbol);
    if (
        typeof name !== 'string' ||
        name.length === 0 ||
        name.trim() !== name ||
        /[\s\u0000-\u001f\u007f]/u.test(name) ||
        (generated && !OUTPUT_NAME.test(name))
    ) {
        return fail(
            'UNSUPPORTED_EMISSION',
            path,
            `Invalid Lambdapi backend name '${String(name)}'`
        );
    }
    return name;
};

const freshBinderName = (
    hint: string,
    scope: readonly string[]
): string => {
    if (!scope.includes(hint)) return hint;
    let suffix = 1;
    while (scope.includes(`${hint}_${suffix}`)) suffix++;
    return `${hint}_${suffix}`;
};

const serializeExpression = (
    expression: CoreLfTransferExpression,
    options: CoreLfStructureLambdapiEmissionOptions,
    scope: readonly string[] = [],
    asArgument = false
): string => {
    switch (expression.tag) {
        case 'type':
            return 'TYPE';
        case 'global':
            return backendName(
                expression.symbol,
                options,
                `backendName(${displaySymbol(expression.symbol)})`
            );
        case 'bound': {
            const name = scope[scope.length - expression.index - 1];
            if (name === undefined) {
                return fail(
                    'UNSUPPORTED_EMISSION',
                    'expression.bound',
                    `Cannot emit dangling bound index ${expression.index}`
                );
            }
            return name;
        }
        case 'capture':
            return `$${expression.name}`;
        case 'wildcard':
            return '_';
        case 'call': {
            if (expression.arguments.length === 0) {
                return fail(
                    'UNSUPPORTED_EMISSION',
                    'expression.arguments',
                    'Cannot emit an empty structure call'
                );
            }
            const hasImplicit = expression.arguments.some(
                argument => argument.plicity === 'implicit'
            );
            if (hasImplicit && expression.callee.tag !== 'global') {
                return fail(
                    'UNSUPPORTED_EMISSION',
                    'expression.callee',
                    'Implicit structure calls require a global head'
                );
            }
            const callee = serializeExpression(
                expression.callee,
                options,
                scope,
                expression.callee.tag !== 'global'
            );
            const head = hasImplicit ? `@${callee}` : callee;
            const body = [
                head,
                ...expression.arguments.map(argument =>
                    serializeExpression(
                        argument.value,
                        options,
                        scope,
                        true
                    )
                )
            ].join(' ');
            return asArgument ? `(${body})` : body;
        }
        case 'pi':
        case 'lambda': {
            const name = freshBinderName(expression.binder.hint, scope);
            const type = serializeExpression(
                expression.binder.type,
                options,
                scope
            );
            const binder = expression.binder.mode.plicity === 'implicit'
                ? `[${name} : ${type}]`
                : `(${name} : ${type})`;
            const body = serializeExpression(
                expression.body,
                options,
                [...scope, name]
            );
            const head = expression.tag === 'pi' ? 'Π' : 'λ';
            const result = `${head} ${binder}, ${body}`;
            return asArgument ? `(${result})` : result;
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const declarationKeyword = (
    declaration: CoreLfTransferDeclaration
): string => {
    if (declaration.body.kind !== 'absent') {
        return fail(
            'UNSUPPORTED_EMISSION',
            `declarations.${declaration.symbol.name}.body`,
            'Structure emission supports only opaque generated declarations'
        );
    }
    switch (declaration.modifiers.rigidity) {
        case 'constant':
            return 'constant symbol';
        case 'injective':
            return 'injective symbol';
        case 'ordinary':
            return 'symbol';
        default: {
            const exhaustive: never = declaration.modifiers.rigidity;
            return exhaustive;
        }
    }
};

/** Deterministically serialize only one generated structure package. */
export function emitCoreLfStructureLambdapiFragment(
    expansion: CoreLfStructureDeclarationExpansion,
    options: CoreLfStructureLambdapiEmissionOptions
): string {
    if (
        expansion.kind !== 'expanded-structure-declaration' ||
        expansion.declarations.length < 3 ||
        expansion.runtimeRules.length !==
            expansion.declarations.length - 2
    ) {
        return fail(
            'UNSUPPORTED_EMISSION',
            'expansion',
            'Expected one complete nonempty structure expansion'
        );
    }
    const commands = [
        ...expansion.declarations.map((declaration, index) => {
            const name = backendName(
                declaration.symbol,
                options,
                `expansion.declarations[${index}].symbol`,
                true
            );
            return `${declarationKeyword(declaration)} ${name} : ` +
                `${serializeExpression(declaration.type, options)};`;
        }),
        ...expansion.runtimeRules.map(rule =>
            `rule ${serializeExpression(rule.left, options)} ` +
                `↪ ${serializeExpression(rule.right, options)};`
        )
    ];
    return `${commands.join('\n\n')}\n`;
}
