/**
 * Checked, portable instance-provider metadata and immutable scope snapshots.
 *
 * Providers are derived from existing checked globals or local binders. This
 * layer records finite evidence and precedence only: it performs no goal
 * matching, recursive premise search, ambiguity decision, or call elaboration.
 */

import { CoreContext } from './context';
import {
    CoreLfClassInheritanceLayout,
    validateCoreLfClassInheritanceLayout
} from './lf_class_inheritance';
import {
    CoreLfClassParentConversionHandle
} from './lf_class_inheritance_lowering';
import {
    CoreLfClassParameterRole,
    CoreLfClassReference
} from './lf_class_schema';
import { createCoreLfChecker } from './lf_checker';
import {
    CoreLfMixedDeclarationBaseContext
} from './lf_transfer_mixed';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferProvenance
} from './lf_transfer';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    BinderMode,
    KernelArgument,
    KernelExpression,
    Plicity,
    Provenance,
    SourceSpan,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import { CORE_OWNER_SCHEMAS, CoreOwnerId } from './schema';

export const CORE_LF_INSTANCE_SCOPE_PROFILE = Object.freeze({
    providerRevision: 'emdash-lf-instance-provider-v1' as const,
    registryRevision: 'emdash-lf-instance-registry-v1' as const,
    scopeRevision: 'emdash-lf-instance-scope-v1' as const,
    defaultPriority: 1000 as const,
    precedence:
        'inner-local-frames-then-named-then-imported-and-current-global' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsSearch: false as const
});

export type CoreLfInstanceScopeErrorCode =
    | 'INVALID_PROVIDER'
    | 'UNAVAILABLE_PROVIDER'
    | 'UNSUPPORTED_PROVIDER'
    | 'INVALID_PROVIDER_TYPE'
    | 'INVALID_CLASS_HEAD'
    | 'INVALID_PREMISE'
    | 'DUPLICATE_PREMISE'
    | 'INVALID_SUPERCLASS_PROVIDER'
    | 'INVALID_REGISTRY'
    | 'DUPLICATE_PROVIDER'
    | 'INVALID_SCOPE'
    | 'UNKNOWN_PROVIDER'
    | 'INVALID_LOCAL_FRAME'
    | 'DUPLICATE_LOCAL_FRAME'
    | 'INVALID_NAMED_SCOPE'
    | 'DUPLICATE_NAMED_SCOPE'
    | 'INVALID_IMPORT'
    | 'DUPLICATE_IMPORT'
    | 'INELIGIBLE_PROVIDER'
    | 'NON_PORTABLE_DATA';

export class CoreLfInstanceScopeError extends Error {
    constructor(
        public readonly code: CoreLfInstanceScopeErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfInstanceScopeError';
    }
}

export interface CoreLfInstanceModuleOrigin {
    readonly moduleId: string;
    readonly moduleRevision: string;
    readonly fragmentId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
}

export interface CoreLfInstanceNamedScopeId {
    readonly moduleId: string;
    readonly name: string;
}

export type CoreLfInstanceProviderVisibility =
    | { readonly kind: 'global' }
    | {
        readonly kind: 'named';
        readonly scope: CoreLfInstanceNamedScopeId;
    }
    | {
        readonly kind: 'local';
        readonly frameId: string;
        readonly frameKind: 'section' | 'local';
    };

export interface CoreLfInstanceClassArgument {
    readonly ordinal: number;
    readonly role: CoreLfClassParameterRole;
    readonly plicity: Plicity;
    readonly value: KernelExpression;
}

export interface CoreLfInstanceClassApplication {
    readonly class: CoreLfClassReference;
    readonly coreHeadName: string;
    readonly type: KernelExpression;
    readonly arguments: readonly CoreLfInstanceClassArgument[];
}

interface CoreLfInstanceProviderBinderBase {
    readonly ordinal: number;
    readonly binderName: string;
    readonly mode: BinderMode;
    readonly type: KernelExpression;
}

export interface CoreLfInstanceOrdinaryProviderBinder
extends CoreLfInstanceProviderBinderBase {
    readonly kind: 'ordinary';
}

export interface CoreLfInstancePremiseProviderBinder
extends CoreLfInstanceProviderBinderBase {
    readonly kind: 'instance-premise';
    readonly target: CoreLfInstanceClassApplication;
}

export type CoreLfInstanceProviderBinder =
    | CoreLfInstanceOrdinaryProviderBinder
    | CoreLfInstancePremiseProviderBinder;

export type CoreLfInstanceProviderSource =
    | {
        readonly kind: 'global-declaration';
        readonly symbol: CoreLfQualifiedSymbol;
        readonly coreName: string;
    }
    | {
        readonly kind: 'local-bound';
        readonly binderIndex: number;
    }
    | {
        readonly kind: 'superclass-conversion';
        readonly ordinal: number;
        readonly child: CoreLfClassReference;
        readonly parent: CoreLfClassReference;
        readonly symbol: CoreLfQualifiedSymbol;
        readonly coreName: string;
    };

export interface CoreLfInstanceProviderDeclaration {
    readonly revision:
        typeof CORE_LF_INSTANCE_SCOPE_PROFILE.providerRevision;
    readonly providerId: CoreLfQualifiedSymbol;
    readonly origin: CoreLfInstanceModuleOrigin;
    readonly provenance: CoreLfTransferProvenance;
    readonly priority: number;
    readonly visibility: CoreLfInstanceProviderVisibility;
    readonly ambientDepth: number;
    readonly term: KernelExpression;
    readonly type: KernelExpression;
    readonly telescope: readonly CoreLfInstanceProviderBinder[];
    readonly result: CoreLfInstanceClassApplication;
    readonly source: CoreLfInstanceProviderSource;
}

export interface CoreLfInstancePremiseInput {
    readonly binderOrdinal: number;
    readonly classLayout: CoreLfClassInheritanceLayout;
}

export type CoreLfGlobalInstanceVisibilityInput =
    | 'global'
    | {
        readonly kind: 'named';
        readonly scope: CoreLfInstanceNamedScopeId;
    };

export interface CoreLfDeclareGlobalInstanceProviderInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly module: CoreLfModuleSpec;
    readonly provider: CoreLfQualifiedSymbol;
    readonly resultClass: CoreLfClassInheritanceLayout;
    readonly instancePremises?: readonly CoreLfInstancePremiseInput[];
    readonly priority?: number;
    readonly visibility?: CoreLfGlobalInstanceVisibilityInput;
}

export interface CoreLfDeclareLocalInstanceProviderInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly context: CoreContext;
    readonly module: CoreLfModuleSpec;
    readonly providerId: CoreLfQualifiedSymbol;
    readonly binderIndex: number;
    readonly frameId: string;
    readonly frameKind?: 'section' | 'local';
    readonly resultClass: CoreLfClassInheritanceLayout;
    readonly instancePremises?: readonly CoreLfInstancePremiseInput[];
    readonly priority?: number;
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfDeclareSuperclassInstanceProviderInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly module: CoreLfModuleSpec;
    readonly conversion: CoreLfClassParentConversionHandle;
    readonly childClass: CoreLfClassInheritanceLayout;
    readonly parentClass: CoreLfClassInheritanceLayout;
    readonly priority?: number;
    readonly visibility?: CoreLfGlobalInstanceVisibilityInput;
}

export interface CoreLfInstanceRegistrySnapshot {
    readonly revision:
        typeof CORE_LF_INSTANCE_SCOPE_PROFILE.registryRevision;
    readonly registryRevision: string;
    readonly providers: readonly CoreLfInstanceProviderDeclaration[];
}

export interface CoreLfCreateInstanceRegistryInput {
    readonly revision: string;
    readonly providers: readonly CoreLfInstanceProviderDeclaration[];
}

export interface CoreLfInstanceLocalFrameInput {
    readonly frameId: string;
    readonly kind: 'section' | 'local';
    readonly providers: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfInstanceLocalFrameSnapshot {
    readonly ordinal: number;
    readonly frameId: string;
    readonly kind: 'section' | 'local';
    readonly providers: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfInstanceImportInput {
    readonly moduleId: string;
    readonly moduleRevision: string;
    readonly interfaceRevision: string;
    readonly interfaceSha256: string;
    readonly providers: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfInstanceImportSnapshot
extends CoreLfInstanceImportInput {}

export type CoreLfInstanceCandidateActivation =
    | {
        readonly kind: 'local-frame';
        readonly frameId: string;
        readonly frameKind: 'section' | 'local';
        readonly frameOrdinal: number;
    }
    | {
        readonly kind: 'named-scope';
        readonly scope: CoreLfInstanceNamedScopeId;
        readonly availability:
            | {
                readonly kind: 'current-module';
                readonly moduleId: string;
            }
            | {
                readonly kind: 'imported-interface';
                readonly moduleId: string;
                readonly interfaceRevision: string;
                readonly interfaceSha256: string;
            };
    }
    | {
        readonly kind: 'imported-global';
        readonly moduleId: string;
        readonly interfaceRevision: string;
        readonly interfaceSha256: string;
    }
    | {
        readonly kind: 'current-global';
        readonly moduleId: string;
    };

export interface CoreLfInstanceScopeCandidate {
    readonly providerId: CoreLfQualifiedSymbol;
    readonly tier: 'local' | 'named' | 'ambient';
    readonly rank: number;
    readonly priority: number;
    readonly activation: CoreLfInstanceCandidateActivation;
}

export interface CoreLfCreateInstanceScopeInput {
    readonly revision: string;
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly moduleId: string;
    readonly contextDepth: number;
    /** Source-significant order: outermost frame first. */
    readonly localFrames?: readonly CoreLfInstanceLocalFrameInput[];
    readonly openedNamedScopes?: readonly CoreLfInstanceNamedScopeId[];
    readonly imports?: readonly CoreLfInstanceImportInput[];
}

export interface CoreLfInstanceScopeSnapshot {
    readonly revision:
        typeof CORE_LF_INSTANCE_SCOPE_PROFILE.scopeRevision;
    readonly scopeRevision: string;
    readonly registryRevision: string;
    readonly registryProviderIds: readonly CoreLfQualifiedSymbol[];
    readonly moduleId: string;
    readonly contextDepth: number;
    readonly localFrames: readonly CoreLfInstanceLocalFrameSnapshot[];
    readonly openedNamedScopes: readonly CoreLfInstanceNamedScopeId[];
    readonly imports: readonly CoreLfInstanceImportSnapshot[];
    readonly candidates: readonly CoreLfInstanceScopeCandidate[];
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const OUTPUT_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u;
const REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SHA256 = /^sha256:[0-9a-f]{64}$/u;
const FRAME_ID = /^[A-Za-z0-9][A-Za-z0-9._:/+-]*$/u;

const fail = (
    code: CoreLfInstanceScopeErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfInstanceScopeError(code, path, message, underlying);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

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

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const symbolKey = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}\u0000${value.name}`;

const displaySymbol = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}.${value.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean => symbolKey(left) === symbolKey(right);

const sameClassReference = (
    left: CoreLfClassReference,
    right: CoreLfClassReference
): boolean =>
    sameSymbol(left.classId, right.classId) &&
    left.parameterCount === right.parameterCount;

const qualifiedSymbol = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): CoreLfQualifiedSymbol => {
    if (
        !record(value) ||
        typeof value.moduleId !== 'string' ||
        !MODULE_ID.test(value.moduleId) ||
        typeof value.name !== 'string' ||
        !OUTPUT_NAME.test(value.name)
    ) {
        return fail(code, path, 'Expected one valid exact qualified symbol');
    }
    return { moduleId: value.moduleId, name: value.name };
};

const validateRevision = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): string => {
    if (typeof value !== 'string' || !REVISION.test(value)) {
        return fail(code, path, 'Expected one portable nonempty revision');
    }
    return value;
};

const validateFrameId = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): string => {
    if (typeof value !== 'string' || !FRAME_ID.test(value)) {
        return fail(code, path, 'Expected one portable lexical-frame ID');
    }
    return value;
};

const validateDepth = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): number => {
    if (!Number.isSafeInteger(value) || (value as number) < 0) {
        return fail(code, path, 'Expected a nonnegative safe-integer depth');
    }
    return value as number;
};

const validatePriority = (
    value: unknown,
    path: string
): number => {
    if (!Number.isSafeInteger(value) || (value as number) < 0) {
        return fail(
            'INVALID_PROVIDER',
            path,
            'Instance priority must be a nonnegative safe integer'
        );
    }
    return value as number;
};

const cloneMode = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): BinderMode => {
    if (
        !record(value) ||
        (value.plicity !== 'explicit' && value.plicity !== 'implicit') ||
        (
            value.variation !== 'functorial' &&
            value.variation !== 'natural' &&
            value.variation !== 'object-only'
        )
    ) {
        return fail(code, path, 'Expected one valid Core binder mode');
    }
    return {
        plicity: value.plicity,
        variation: value.variation
    };
};

const sameMode = (left: BinderMode, right: BinderMode): boolean =>
    left.plicity === right.plicity &&
    left.variation === right.variation;

const cloneSourceSpan = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): SourceSpan => {
    if (
        !record(value) ||
        typeof value.file !== 'string' ||
        value.file.length === 0 ||
        !record(value.start) ||
        !record(value.end)
    ) {
        return fail(code, path, 'Expected one valid Core source span');
    }
    const position = (
        entry: Record<string, unknown>,
        entryPath: string
    ) => {
        if (
            !Number.isSafeInteger(entry.line) ||
            (entry.line as number) < 1 ||
            !Number.isSafeInteger(entry.column) ||
            (entry.column as number) < 1
        ) {
            return fail(
                code,
                entryPath,
                'Core source positions must be positive safe integers'
            );
        }
        return {
            line: entry.line as number,
            column: entry.column as number
        };
    };
    return {
        file: value.file,
        start: position(value.start, `${path}.start`),
        end: position(value.end, `${path}.end`)
    };
};

const cloneProvenance = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): Provenance => {
    if (
        !record(value) ||
        (
            value.origin !== 'surface' &&
            value.origin !== 'recovered' &&
            value.origin !== 'derived'
        ) ||
        typeof value.detail !== 'string' ||
        value.detail.length === 0
    ) {
        return fail(code, path, 'Expected one valid Core provenance record');
    }
    return value.span === undefined
        ? { origin: value.origin, detail: value.detail }
        : {
            origin: value.origin,
            detail: value.detail,
            span: cloneSourceSpan(value.span, `${path}.span`, code)
        };
};

const cloneArgument = (
    value: unknown,
    path: string,
    depth: number,
    code: CoreLfInstanceScopeErrorCode
): KernelArgument => {
    if (
        !record(value) ||
        (value.plicity !== 'explicit' && value.plicity !== 'implicit')
    ) {
        return fail(code, path, 'Expected one valid Core argument');
    }
    return {
        plicity: value.plicity,
        value: cloneCoreExpression(value.value, `${path}.value`, depth, code),
        provenance: cloneProvenance(
            value.provenance,
            `${path}.provenance`,
            code
        )
    };
};

const cloneCoreExpression = (
    value: unknown,
    path: string,
    depth: number,
    code: CoreLfInstanceScopeErrorCode
): KernelExpression => {
    if (!record(value) || typeof value.tag !== 'string') {
        return fail(code, path, 'Expected one portable explicit Core term');
    }
    const nodeProvenance = cloneProvenance(
        value.provenance,
        `${path}.provenance`,
        code
    );
    switch (value.tag) {
        case 'universe':
            return { tag: 'universe', provenance: nodeProvenance };
        case 'reference':
            if (
                value.namespace !== 'free' ||
                typeof value.name !== 'string' ||
                !/^[A-Za-z][A-Za-z0-9_]*$/u.test(value.name)
            ) {
                return fail(code, path, 'Invalid free Core reference');
            }
            return {
                tag: 'reference',
                namespace: 'free',
                name: value.name,
                provenance: nodeProvenance
            };
        case 'bound':
            if (
                !Number.isSafeInteger(value.index) ||
                (value.index as number) < 0 ||
                (value.index as number) >= depth
            ) {
                return fail(
                    code,
                    `${path}.index`,
                    `Core bound index escapes ambient depth ${depth}`
                );
            }
            return {
                tag: 'bound',
                index: value.index as number,
                provenance: nodeProvenance
            };
        case 'meta':
            return fail(
                'NON_PORTABLE_DATA',
                path,
                'Instance metadata cannot retain a Core metavariable'
            );
        case 'application': {
            if (
                typeof value.owner !== 'string' ||
                !Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    value.owner
                ) ||
                !Array.isArray(value.arguments)
            ) {
                return fail(code, path, 'Invalid semantic-owner application');
            }
            const owner = value.owner as CoreOwnerId;
            const schema = CORE_OWNER_SCHEMAS[owner];
            if (value.arguments.length !== schema.slots.length) {
                return fail(
                    code,
                    `${path}.arguments`,
                    `Core owner '${owner}' requires ${schema.slots.length} ` +
                        'arguments'
                );
            }
            const arguments_ = value.arguments.map((argument, index) => {
                const cloned = cloneArgument(
                    argument,
                    `${path}.arguments[${index}]`,
                    depth,
                    code
                );
                if (cloned.plicity !== schema.slots[index].plicity) {
                    return fail(
                        code,
                        `${path}.arguments[${index}].plicity`,
                        `Core owner '${owner}' argument plicity is invalid`
                    );
                }
                return cloned;
            });
            return {
                tag: 'application',
                owner,
                arguments: arguments_,
                provenance: nodeProvenance
            };
        }
        case 'call':
            if (!Array.isArray(value.arguments) || value.arguments.length === 0) {
                return fail(
                    code,
                    `${path}.arguments`,
                    'Core generic call requires at least one argument'
                );
            }
            return {
                tag: 'call',
                callee: cloneCoreExpression(
                    value.callee,
                    `${path}.callee`,
                    depth,
                    code
                ),
                arguments: value.arguments.map((argument, index) =>
                    cloneArgument(
                        argument,
                        `${path}.arguments[${index}]`,
                        depth,
                        code
                    )
                ),
                provenance: nodeProvenance
            };
        case 'pi':
        case 'lambda': {
            if (
                !record(value.binder) ||
                typeof value.binder.name !== 'string' ||
                !OUTPUT_NAME.test(value.binder.name)
            ) {
                return fail(code, `${path}.binder`, 'Invalid Core binder');
            }
            const binder = {
                name: value.binder.name,
                type: cloneCoreExpression(
                    value.binder.type,
                    `${path}.binder.type`,
                    depth,
                    code
                ),
                mode: cloneMode(
                    value.binder.mode,
                    `${path}.binder.mode`,
                    code
                ),
                provenance: cloneProvenance(
                    value.binder.provenance,
                    `${path}.binder.provenance`,
                    code
                )
            };
            const body = cloneCoreExpression(
                value.body,
                `${path}.body`,
                depth + 1,
                code
            );
            return value.tag === 'pi'
                ? { tag: 'pi', binder, body, provenance: nodeProvenance }
                : { tag: 'lambda', binder, body, provenance: nodeProvenance };
        }
        default:
            return fail(code, `${path}.tag`, 'Unsupported explicit Core tag');
    }
};

const cloneTransferProvenance = (
    value: unknown,
    path: string,
    authorityPath: string,
    code: CoreLfInstanceScopeErrorCode
): CoreLfTransferProvenance => {
    if (
        !record(value) ||
        typeof value.authorityPath !== 'string' ||
        value.authorityPath !== authorityPath ||
        typeof value.sourceFragment !== 'string' ||
        value.sourceFragment.length === 0 ||
        (
            value.canonicalCommandOrdinal !== undefined &&
            (
                !Number.isSafeInteger(value.canonicalCommandOrdinal) ||
                (value.canonicalCommandOrdinal as number) < 0
            )
        )
    ) {
        return fail(code, path, 'Invalid instance source provenance');
    }
    return {
        authorityPath: value.authorityPath,
        sourceFragment: value.sourceFragment,
        ...(value.canonicalCommandOrdinal === undefined
            ? {}
            : {
                canonicalCommandOrdinal:
                    value.canonicalCommandOrdinal as number
            })
    };
};

const moduleOrigin = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): CoreLfInstanceModuleOrigin => {
    if (
        !record(value) ||
        typeof value.moduleId !== 'string' ||
        !MODULE_ID.test(value.moduleId) ||
        typeof value.moduleRevision !== 'string' ||
        !REVISION.test(value.moduleRevision) ||
        typeof value.fragmentId !== 'string' ||
        !REVISION.test(value.fragmentId) ||
        typeof value.authorityPath !== 'string' ||
        value.authorityPath.length === 0 ||
        typeof value.sourceSha256 !== 'string' ||
        !SHA256.test(value.sourceSha256)
    ) {
        return fail(code, path, 'Invalid exact provider module origin');
    }
    return {
        moduleId: value.moduleId,
        moduleRevision: value.moduleRevision,
        fragmentId: value.fragmentId,
        authorityPath: value.authorityPath,
        sourceSha256: value.sourceSha256
    };
};

const originFromModule = (
    module: unknown,
    path: string
): CoreLfInstanceModuleOrigin => {
    if (!record(module)) {
        return fail(
            'INVALID_PROVIDER',
            path,
            'Provider module identity must be an object'
        );
    }
    return moduleOrigin({
        moduleId: module.moduleId,
        moduleRevision: module.revision,
        fragmentId: module.fragmentId,
        authorityPath: module.authorityPath,
        sourceSha256: module.sourceSha256
    }, path, 'INVALID_PROVIDER');
};

const classReference = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): CoreLfClassReference => {
    if (
        !record(value) ||
        !Number.isSafeInteger(value.parameterCount) ||
        (value.parameterCount as number) < 0
    ) {
        return fail(code, path, 'Expected one valid class reference');
    }
    return {
        classId: qualifiedSymbol(value.classId, `${path}.classId`, code),
        parameterCount: value.parameterCount as number
    };
};

const namedScope = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): CoreLfInstanceNamedScopeId => {
    const scope = qualifiedSymbol(value, path, code);
    return { moduleId: scope.moduleId, name: scope.name };
};

const visibilitySnapshot = (
    value: unknown,
    path: string,
    originModuleId: string,
    code: CoreLfInstanceScopeErrorCode
): CoreLfInstanceProviderVisibility => {
    if (!record(value) || typeof value.kind !== 'string') {
        return fail(code, path, 'Invalid instance-provider visibility');
    }
    switch (value.kind) {
        case 'global':
            return { kind: 'global' };
        case 'named': {
            const scope = namedScope(value.scope, `${path}.scope`, code);
            if (scope.moduleId !== originModuleId) {
                return fail(
                    code,
                    `${path}.scope.moduleId`,
                    'Named instance scope must belong to the provider module'
                );
            }
            return { kind: 'named', scope };
        }
        case 'local':
            if (
                (value.frameKind !== 'section' && value.frameKind !== 'local')
            ) {
                return fail(code, `${path}.frameKind`, 'Invalid local frame kind');
            }
            return {
                kind: 'local',
                frameId: validateFrameId(value.frameId, `${path}.frameId`, code),
                frameKind: value.frameKind
            };
        default:
            return fail(code, `${path}.kind`, 'Invalid provider visibility kind');
    }
};

const classHead = (
    layoutInput: CoreLfClassInheritanceLayout,
    declarations: CoreLfMixedDeclarationBaseContext,
    path: string
): {
    readonly layout: CoreLfClassInheritanceLayout;
    readonly reference: CoreLfClassReference;
    readonly coreName: string;
} => {
    let layout: CoreLfClassInheritanceLayout;
    try {
        layout = validateCoreLfClassInheritanceLayout(layoutInput);
    } catch (error: unknown) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            'Instance class layout is not a completed valid identity layout',
            error instanceof Error ? error : undefined
        );
    }
    const declaration = declarations.declaration(layout.classId);
    if (declaration === undefined) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            `Class '${displaySymbol(layout.classId)}' is unavailable in the ` +
                'checked declaration context'
        );
    }
    if (
        declaration.link.kind !== 'free-declaration' ||
        !sameSymbol(declaration.symbol, layout.classId) ||
        !sameSymbol(declaration.link.symbol, layout.classId) ||
        !declaration.status.startsWith('installed-')
    ) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            `Class '${displaySymbol(layout.classId)}' is not one installed ` +
                'ordinary free declaration'
        );
    }
    return {
        layout,
        reference: {
            classId: { ...layout.classId },
            parameterCount: layout.schema.parameters.length
        },
        coreName: declaration.link.coreName
    };
};

const decomposeClassApplication = (
    typeInput: KernelExpression,
    depth: number,
    layout: CoreLfClassInheritanceLayout,
    declarations: CoreLfMixedDeclarationBaseContext,
    path: string
): CoreLfInstanceClassApplication => {
    const head = classHead(layout, declarations, path);
    const type = cloneCoreExpression(
        typeInput,
        `${path}.type`,
        depth,
        'INVALID_CLASS_HEAD'
    );
    let callee: KernelExpression;
    let arguments_: readonly KernelArgument[];
    if (type.tag === 'call') {
        callee = type.callee;
        arguments_ = type.arguments;
    } else {
        callee = type;
        arguments_ = [];
    }
    if (
        callee.tag !== 'reference' ||
        callee.namespace !== 'free' ||
        callee.name !== head.coreName ||
        arguments_.length !== head.reference.parameterCount
    ) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            `Expected exact class head '${displaySymbol(head.reference.classId)}' ` +
                `with ${head.reference.parameterCount} parameters`
        );
    }
    const argumentsResult = arguments_.map((argument, ordinal) => {
        const parameter = head.layout.schema.parameters[ordinal];
        const expectedPlicity = parameter.parameter.modes.carrier.plicity;
        if (argument.plicity !== expectedPlicity) {
            return fail(
                'INVALID_CLASS_HEAD',
                `${path}.arguments[${ordinal}].plicity`,
                `Class parameter '${parameter.parameter.binderName}' requires ` +
                    `${expectedPlicity} Core plicity`
            );
        }
        return {
            ordinal,
            role: parameter.role,
            plicity: argument.plicity,
            value: cloneCoreExpression(
                argument.value,
                `${path}.arguments[${ordinal}].value`,
                depth,
                'INVALID_CLASS_HEAD'
            )
        };
    });
    return deepFreeze({
        class: head.reference,
        coreHeadName: head.coreName,
        type,
        arguments: argumentsResult
    });
};

const classApplicationSnapshot = (
    value: unknown,
    path: string,
    depth: number,
    code: CoreLfInstanceScopeErrorCode
): CoreLfInstanceClassApplication => {
    if (
        !record(value) ||
        typeof value.coreHeadName !== 'string' ||
        !/^[A-Za-z][A-Za-z0-9_]*$/u.test(value.coreHeadName) ||
        !Array.isArray(value.arguments)
    ) {
        return fail(code, path, 'Invalid portable instance class application');
    }
    const reference = classReference(value.class, `${path}.class`, code);
    if (value.arguments.length !== reference.parameterCount) {
        return fail(
            code,
            `${path}.arguments`,
            'Class argument count differs from its stable class reference'
        );
    }
    const type = cloneCoreExpression(value.type, `${path}.type`, depth, code);
    const arguments_ = value.arguments.map((argument, ordinal) => {
        if (
            !record(argument) ||
            argument.ordinal !== ordinal ||
            (
                argument.role !== 'input' &&
                argument.role !== 'output' &&
                argument.role !== 'semi-output'
            ) ||
            (
                argument.plicity !== 'explicit' &&
                argument.plicity !== 'implicit'
            )
        ) {
            return fail(
                code,
                `${path}.arguments[${ordinal}]`,
                'Invalid ordered class-argument metadata'
            );
        }
        return {
            ordinal,
            role: argument.role as CoreLfClassParameterRole,
            plicity: argument.plicity as Plicity,
            value: cloneCoreExpression(
                argument.value,
                `${path}.arguments[${ordinal}].value`,
                depth,
                code
            )
        };
    });
    let callee: KernelExpression;
    let typeArguments: readonly KernelArgument[];
    if (type.tag === 'call') {
        callee = type.callee;
        typeArguments = type.arguments;
    } else {
        callee = type;
        typeArguments = [];
    }
    if (
        callee.tag !== 'reference' ||
        callee.name !== value.coreHeadName ||
        typeArguments.length !== arguments_.length
    ) {
        return fail(code, path, 'Stored class type has a different Core head');
    }
    typeArguments.forEach((argument, index) => {
        if (
            argument.plicity !== arguments_[index].plicity ||
            !kernelExpressionEquals(
                argument.value,
                arguments_[index].value
            )
        ) {
            fail(
                code,
                `${path}.arguments[${index}]`,
                'Stored class argument differs from the exact class type'
            );
        }
    });
    return {
        class: reference,
        coreHeadName: value.coreHeadName,
        type,
        arguments: arguments_
    };
};

interface ProviderTypeInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly providerId: CoreLfQualifiedSymbol;
    readonly origin: CoreLfInstanceModuleOrigin;
    readonly provenance: CoreLfTransferProvenance;
    readonly priority: number;
    readonly visibility: CoreLfInstanceProviderVisibility;
    readonly ambientDepth: number;
    readonly term: KernelExpression;
    readonly type: KernelExpression;
    readonly resultClass: CoreLfClassInheritanceLayout;
    readonly instancePremises: readonly CoreLfInstancePremiseInput[];
    readonly source: CoreLfInstanceProviderSource;
}

const providerFromCheckedType = (
    input: ProviderTypeInput
): CoreLfInstanceProviderDeclaration => {
    const type = cloneCoreExpression(
        input.type,
        'input.provider.type',
        input.ambientDepth,
        'INVALID_PROVIDER_TYPE'
    );
    const term = cloneCoreExpression(
        input.term,
        'input.provider.term',
        input.ambientDepth,
        'INVALID_PROVIDER_TYPE'
    );
    if (!Array.isArray(input.instancePremises)) {
        return fail(
            'INVALID_PREMISE',
            'input.instancePremises',
            'Instance-premise annotations must be a finite array'
        );
    }
    const premiseLayouts = new Map<number, CoreLfClassInheritanceLayout>();
    input.instancePremises.forEach((premise, index) => {
        const path = `input.instancePremises[${index}]`;
        if (
            !record(premise) ||
            !Number.isSafeInteger(premise.binderOrdinal) ||
            (premise.binderOrdinal as number) < 0
        ) {
            return fail(
                'INVALID_PREMISE',
                path,
                'Premise annotation requires a nonnegative binder ordinal'
            );
        }
        const ordinal = premise.binderOrdinal as number;
        if (premiseLayouts.has(ordinal)) {
            return fail(
                'DUPLICATE_PREMISE',
                `${path}.binderOrdinal`,
                `Provider binder ${ordinal} has two premise annotations`
            );
        }
        let layout: CoreLfClassInheritanceLayout;
        try {
            layout = validateCoreLfClassInheritanceLayout(
                premise.classLayout
            );
        } catch (error: unknown) {
            return fail(
                'INVALID_PREMISE',
                `${path}.classLayout`,
                'Premise class layout is not completed and valid',
                error instanceof Error ? error : undefined
            );
        }
        premiseLayouts.set(ordinal, layout);
    });

    const telescope: CoreLfInstanceProviderBinder[] = [];
    let cursor = type;
    while (cursor.tag === 'pi') {
        const ordinal = telescope.length;
        const premiseLayout = premiseLayouts.get(ordinal);
        const base = {
            ordinal,
            binderName: cursor.binder.name,
            mode: cloneMode(
                cursor.binder.mode,
                `input.provider.type.binders[${ordinal}].mode`,
                'INVALID_PROVIDER_TYPE'
            ),
            type: cloneCoreExpression(
                cursor.binder.type,
                `input.provider.type.binders[${ordinal}].type`,
                input.ambientDepth + ordinal,
                'INVALID_PROVIDER_TYPE'
            )
        };
        if (premiseLayout === undefined) {
            telescope.push({ kind: 'ordinary', ...base });
        } else {
            let target: CoreLfInstanceClassApplication;
            try {
                target = decomposeClassApplication(
                    cursor.binder.type,
                    input.ambientDepth + ordinal,
                    premiseLayout,
                    input.declarations,
                    `input.provider.type.binders[${ordinal}].target`
                );
            } catch (error: unknown) {
                if (
                    error instanceof CoreLfInstanceScopeError &&
                    error.code === 'INVALID_CLASS_HEAD'
                ) {
                    return fail(
                        'INVALID_PREMISE',
                        error.path,
                        error.message,
                        error
                    );
                }
                throw error;
            }
            telescope.push({ kind: 'instance-premise', ...base, target });
        }
        cursor = cursor.body;
    }
    premiseLayouts.forEach((_layout, ordinal) => {
        if (ordinal >= telescope.length) {
            fail(
                'INVALID_PREMISE',
                'input.instancePremises',
                `Premise annotation ${ordinal} does not name a Pi binder`
            );
        }
    });
    const result = decomposeClassApplication(
        cursor,
        input.ambientDepth + telescope.length,
        input.resultClass,
        input.declarations,
        'input.provider.result'
    );
    return deepFreeze({
        revision: CORE_LF_INSTANCE_SCOPE_PROFILE.providerRevision,
        providerId: { ...input.providerId },
        origin: { ...input.origin },
        provenance: { ...input.provenance },
        priority: input.priority,
        visibility: input.visibility,
        ambientDepth: input.ambientDepth,
        term,
        type,
        telescope,
        result,
        source: input.source
    });
};

const globalVisibility = (
    value: CoreLfGlobalInstanceVisibilityInput | undefined,
    moduleId: string
): CoreLfInstanceProviderVisibility => {
    if (value === undefined || value === 'global') return { kind: 'global' };
    if (!record(value) || value.kind !== 'named') {
        return fail(
            'INVALID_PROVIDER',
            'input.visibility',
            'Global provider visibility must be global or one named scope'
        );
    }
    return visibilitySnapshot(
        value,
        'input.visibility',
        moduleId,
        'INVALID_PROVIDER'
    );
};

const sourceDeclaration = (
    module: CoreLfModuleSpec,
    symbol: CoreLfQualifiedSymbol,
    path: string
) => {
    if (!Array.isArray(module.declarations)) {
        return fail(
            'INVALID_PROVIDER',
            'input.module.declarations',
            'Provider module must expose a finite declaration array'
        );
    }
    const matches = module.declarations.filter(candidate =>
        sameSymbol(candidate.symbol, symbol)
    );
    if (matches.length !== 1) {
        return fail(
            'UNAVAILABLE_PROVIDER',
            path,
            `Provider '${displaySymbol(symbol)}' must have one exact source ` +
                'declaration in its module'
        );
    }
    return matches[0];
};

/** Derive one portable provider from an exact checked global declaration. */
export function declareCoreLfGlobalInstanceProvider(
    input: CoreLfDeclareGlobalInstanceProviderInput
): CoreLfInstanceProviderDeclaration {
    if (!record(input)) {
        return fail(
            'INVALID_PROVIDER',
            'input',
            'Global instance-provider input must be an object'
        );
    }
    if (
        input.declarations === null ||
        typeof input.declarations !== 'object' ||
        typeof input.declarations.declaration !== 'function' ||
        input.declarations.environment === undefined
    ) {
        return fail(
            'INVALID_PROVIDER',
            'input.declarations',
            'Global provider requires one checked declaration base'
        );
    }
    const origin = originFromModule(input.module, 'input.module');
    const providerId = qualifiedSymbol(
        input.provider,
        'input.provider',
        'INVALID_PROVIDER'
    );
    if (providerId.moduleId !== origin.moduleId) {
        return fail(
            'INVALID_PROVIDER',
            'input.provider.moduleId',
            'Global provider identity must belong to its source module'
        );
    }
    const declaration = input.declarations?.declaration(providerId);
    if (declaration === undefined) {
        return fail(
            'UNAVAILABLE_PROVIDER',
            'input.provider',
            `Provider '${displaySymbol(providerId)}' is unavailable in the ` +
                'checked declaration context'
        );
    }
    if (
        declaration.link.kind !== 'free-declaration' ||
        !sameSymbol(declaration.symbol, providerId) ||
        !sameSymbol(declaration.link.symbol, providerId) ||
        !declaration.status.startsWith('installed-')
    ) {
        return fail(
            'UNSUPPORTED_PROVIDER',
            'input.provider',
            `Provider '${displaySymbol(providerId)}' is not one installed ` +
                'ordinary free declaration'
        );
    }
    const source = sourceDeclaration(input.module, providerId, 'input.provider');
    const providerProvenance = cloneTransferProvenance(
        source.provenance,
        'input.module.declarations.provider.provenance',
        origin.authorityPath,
        'INVALID_PROVIDER'
    );
    const witnessProvenance = provenance(
        'derived',
        `checked instance provider ${displaySymbol(providerId)}`
    );
    const term = kernelFree(declaration.link.coreName, witnessProvenance);
    try {
        const checker = createCoreLfChecker(input.declarations.environment);
        checker.check(checker.rootContext, term, declaration.type);
    } catch (error: unknown) {
        return fail(
            'INVALID_PROVIDER_TYPE',
            'input.provider',
            `Provider '${displaySymbol(providerId)}' does not check against ` +
                'its compiled type',
            error instanceof Error ? error : undefined
        );
    }
    return providerFromCheckedType({
        declarations: input.declarations,
        providerId,
        origin,
        provenance: providerProvenance,
        priority: validatePriority(
            input.priority ?? CORE_LF_INSTANCE_SCOPE_PROFILE.defaultPriority,
            'input.priority'
        ),
        visibility: globalVisibility(input.visibility, origin.moduleId),
        ambientDepth: 0,
        term,
        type: declaration.type,
        resultClass: input.resultClass,
        instancePremises: input.instancePremises ?? [],
        source: {
            kind: 'global-declaration',
            symbol: providerId,
            coreName: declaration.link.coreName
        }
    });
}

/** Derive one portable local provider from an exact checked Core binder. */
export function declareCoreLfLocalInstanceProvider(
    input: CoreLfDeclareLocalInstanceProviderInput
): CoreLfInstanceProviderDeclaration {
    if (!record(input)) {
        return fail(
            'INVALID_PROVIDER',
            'input',
            'Local instance-provider input must be an object'
        );
    }
    if (
        input.declarations === null ||
        typeof input.declarations !== 'object' ||
        typeof input.declarations.declaration !== 'function' ||
        input.declarations.environment === undefined
    ) {
        return fail(
            'INVALID_PROVIDER',
            'input.declarations',
            'Local provider requires one checked declaration base'
        );
    }
    if (
        !(input.context instanceof CoreContext) ||
        input.context.environment !==
            input.declarations?.environment.coreEnvironment
    ) {
        return fail(
            'INVALID_PROVIDER',
            'input.context',
            'Local provider context must use the supplied declaration environment'
        );
    }
    const origin = originFromModule(input.module, 'input.module');
    const providerId = qualifiedSymbol(
        input.providerId,
        'input.providerId',
        'INVALID_PROVIDER'
    );
    if (providerId.moduleId !== origin.moduleId) {
        return fail(
            'INVALID_PROVIDER',
            'input.providerId.moduleId',
            'Local provider identity must belong to its source module'
        );
    }
    const binderIndex = validateDepth(
        input.binderIndex,
        'input.binderIndex',
        'INVALID_PROVIDER'
    );
    const lookup = input.context.lookupIndex(
        binderIndex,
        provenance(
            'derived',
            `checked local instance provider ${displaySymbol(providerId)}`
        )
    );
    if (lookup === undefined) {
        return fail(
            'UNAVAILABLE_PROVIDER',
            'input.binderIndex',
            `Local provider binder ${binderIndex} is outside context depth ` +
                `${input.context.depth}`
        );
    }
    try {
        const checker = createCoreLfChecker(input.declarations.environment);
        checker.check(input.context, lookup.term, lookup.type);
    } catch (error: unknown) {
        return fail(
            'INVALID_PROVIDER_TYPE',
            'input.binderIndex',
            'Local provider binder does not check against its derived type',
            error instanceof Error ? error : undefined
        );
    }
    const frameKind = input.frameKind ?? 'local';
    if (frameKind !== 'section' && frameKind !== 'local') {
        return fail(
            'INVALID_PROVIDER',
            'input.frameKind',
            'Local provider frame kind must be section or local'
        );
    }
    const frameId = validateFrameId(
        input.frameId,
        'input.frameId',
        'INVALID_PROVIDER'
    );
    return providerFromCheckedType({
        declarations: input.declarations,
        providerId,
        origin,
        provenance: cloneTransferProvenance(
            input.provenance,
            'input.provenance',
            origin.authorityPath,
            'INVALID_PROVIDER'
        ),
        priority: validatePriority(
            input.priority ?? CORE_LF_INSTANCE_SCOPE_PROFILE.defaultPriority,
            'input.priority'
        ),
        visibility: {
            kind: 'local',
            frameId,
            frameKind
        },
        ambientDepth: input.context.depth,
        term: lookup.term,
        type: lookup.type,
        resultClass: input.resultClass,
        instancePremises: input.instancePremises ?? [],
        source: { kind: 'local-bound', binderIndex }
    });
}

/** Register one checked direct-parent conversion as superclass evidence. */
export function declareCoreLfSuperclassInstanceProvider(
    input: CoreLfDeclareSuperclassInstanceProviderInput
): CoreLfInstanceProviderDeclaration {
    if (!record(input) || !record(input.conversion)) {
        return fail(
            'INVALID_SUPERCLASS_PROVIDER',
            'input',
            'Superclass-provider input requires one conversion handle'
        );
    }
    let child: CoreLfClassInheritanceLayout;
    let parent: CoreLfClassInheritanceLayout;
    try {
        child = validateCoreLfClassInheritanceLayout(input.childClass);
        parent = validateCoreLfClassInheritanceLayout(input.parentClass);
    } catch (error: unknown) {
        return fail(
            'INVALID_SUPERCLASS_PROVIDER',
            'input',
            'Superclass provider requires completed child and parent layouts',
            error instanceof Error ? error : undefined
        );
    }
    const childReference: CoreLfClassReference = {
        classId: child.classId,
        parameterCount: child.schema.parameters.length
    };
    const parentReference: CoreLfClassReference = {
        classId: parent.classId,
        parameterCount: parent.schema.parameters.length
    };
    if (
        !Array.isArray(input.conversion.parameters) ||
        !record(input.conversion.term)
    ) {
        return fail(
            'INVALID_SUPERCLASS_PROVIDER',
            'input.conversion',
            'Direct conversion handle has malformed parameters or term'
        );
    }
    let conversionChild: CoreLfClassReference;
    let conversionParent: CoreLfClassReference;
    let conversionSymbol: CoreLfQualifiedSymbol;
    try {
        conversionChild = classReference(
            input.conversion.child,
            'input.conversion.child',
            'INVALID_SUPERCLASS_PROVIDER'
        );
        conversionParent = classReference(
            input.conversion.parent,
            'input.conversion.parent',
            'INVALID_SUPERCLASS_PROVIDER'
        );
        conversionSymbol = qualifiedSymbol(
            input.conversion.symbol,
            'input.conversion.symbol',
            'INVALID_SUPERCLASS_PROVIDER'
        );
    } catch (error: unknown) {
        if (error instanceof CoreLfInstanceScopeError) throw error;
        return fail(
            'INVALID_SUPERCLASS_PROVIDER',
            'input.conversion',
            'Malformed direct conversion identity',
            error instanceof Error ? error : undefined
        );
    }
    const ordinal = input.conversion.ordinal;
    const directParent = Number.isSafeInteger(ordinal) && ordinal >= 0
        ? child.schema.directParents[ordinal]
        : undefined;
    if (
        directParent === undefined ||
        !sameClassReference(conversionChild, childReference) ||
        !sameClassReference(conversionParent, parentReference) ||
        !sameClassReference(directParent.parent, parentReference) ||
        input.conversion.parameters.length !== childReference.parameterCount ||
        input.conversion.term.tag !== 'global' ||
        !sameSymbol(input.conversion.term.symbol, conversionSymbol)
    ) {
        return fail(
            'INVALID_SUPERCLASS_PROVIDER',
            'input.conversion',
            'Conversion is not the exact requested direct child-parent handle'
        );
    }
    let provider: CoreLfInstanceProviderDeclaration;
    try {
        provider = declareCoreLfGlobalInstanceProvider({
            declarations: input.declarations,
            module: input.module,
            provider: conversionSymbol,
            resultClass: parent,
            instancePremises: [{
                binderOrdinal: input.conversion.parameters.length,
                classLayout: child
            }],
            priority: input.priority,
            visibility: input.visibility
        });
    } catch (error: unknown) {
        if (error instanceof CoreLfInstanceScopeError) {
            return fail(
                'INVALID_SUPERCLASS_PROVIDER',
                error.path,
                error.message,
                error
            );
        }
        throw error;
    }
    if (provider.source.kind !== 'global-declaration') {
        return fail(
            'INVALID_SUPERCLASS_PROVIDER',
            'input.conversion',
            'Checked conversion did not produce a global provider'
        );
    }
    return deepFreeze({
        ...provider,
        source: {
            kind: 'superclass-conversion' as const,
            ordinal,
            child: childReference,
            parent: parentReference,
            symbol: { ...provider.providerId },
            coreName: provider.source.coreName
        }
    });
}

const providerSourceSnapshot = (
    value: unknown,
    path: string,
    providerId: CoreLfQualifiedSymbol,
    term: KernelExpression,
    result: CoreLfInstanceClassApplication,
    telescope: readonly CoreLfInstanceProviderBinder[],
    visibility: CoreLfInstanceProviderVisibility,
    ambientDepth: number
): CoreLfInstanceProviderSource => {
    if (!record(value) || typeof value.kind !== 'string') {
        return fail('INVALID_PROVIDER', path, 'Invalid provider source');
    }
    switch (value.kind) {
        case 'global-declaration': {
            const symbol = qualifiedSymbol(
                value.symbol,
                `${path}.symbol`,
                'INVALID_PROVIDER'
            );
            if (
                !sameSymbol(symbol, providerId) ||
                typeof value.coreName !== 'string' ||
                !/^[A-Za-z][A-Za-z0-9_]*$/u.test(value.coreName) ||
                term.tag !== 'reference' ||
                term.name !== value.coreName ||
                visibility.kind === 'local' ||
                ambientDepth !== 0
            ) {
                return fail(
                    'INVALID_PROVIDER',
                    path,
                    'Global provider source disagrees with its identity, term, or visibility'
                );
            }
            return {
                kind: 'global-declaration',
                symbol,
                coreName: value.coreName
            };
        }
        case 'local-bound': {
            const binderIndex = validateDepth(
                value.binderIndex,
                `${path}.binderIndex`,
                'INVALID_PROVIDER'
            );
            if (
                visibility.kind !== 'local' ||
                ambientDepth === 0 ||
                binderIndex >= ambientDepth ||
                term.tag !== 'bound' ||
                term.index !== binderIndex
            ) {
                return fail(
                    'INVALID_PROVIDER',
                    path,
                    'Local provider source disagrees with its exact bound evidence'
                );
            }
            return { kind: 'local-bound', binderIndex };
        }
        case 'superclass-conversion': {
            const symbol = qualifiedSymbol(
                value.symbol,
                `${path}.symbol`,
                'INVALID_PROVIDER'
            );
            const child = classReference(
                value.child,
                `${path}.child`,
                'INVALID_PROVIDER'
            );
            const parent = classReference(
                value.parent,
                `${path}.parent`,
                'INVALID_PROVIDER'
            );
            const ordinal = validateDepth(
                value.ordinal,
                `${path}.ordinal`,
                'INVALID_PROVIDER'
            );
            const premises = telescope.filter(
                (binder): binder is CoreLfInstancePremiseProviderBinder =>
                    binder.kind === 'instance-premise'
            );
            if (
                !sameSymbol(symbol, providerId) ||
                typeof value.coreName !== 'string' ||
                !/^[A-Za-z][A-Za-z0-9_]*$/u.test(value.coreName) ||
                term.tag !== 'reference' ||
                term.name !== value.coreName ||
                visibility.kind === 'local' ||
                ambientDepth !== 0 ||
                !sameClassReference(parent, result.class) ||
                premises.length !== 1 ||
                !sameClassReference(premises[0].target.class, child)
            ) {
                return fail(
                    'INVALID_PROVIDER',
                    path,
                    'Superclass source disagrees with its direct conversion metadata'
                );
            }
            return {
                kind: 'superclass-conversion',
                ordinal,
                child,
                parent,
                symbol,
                coreName: value.coreName
            };
        }
        default:
            return fail(
                'INVALID_PROVIDER',
                `${path}.kind`,
                'Unknown provider source kind'
            );
    }
};

const providerSnapshot = (
    value: unknown,
    path: string
): CoreLfInstanceProviderDeclaration => {
    if (
        !record(value) ||
        value.revision !== CORE_LF_INSTANCE_SCOPE_PROFILE.providerRevision ||
        !Array.isArray(value.telescope)
    ) {
        return fail(
            'INVALID_PROVIDER',
            path,
            'Invalid portable instance-provider snapshot'
        );
    }
    const providerId = qualifiedSymbol(
        value.providerId,
        `${path}.providerId`,
        'INVALID_PROVIDER'
    );
    const origin = moduleOrigin(
        value.origin,
        `${path}.origin`,
        'INVALID_PROVIDER'
    );
    if (providerId.moduleId !== origin.moduleId) {
        return fail(
            'INVALID_PROVIDER',
            `${path}.providerId.moduleId`,
            'Provider identity and module origin disagree'
        );
    }
    const provenanceSnapshot = cloneTransferProvenance(
        value.provenance,
        `${path}.provenance`,
        origin.authorityPath,
        'INVALID_PROVIDER'
    );
    const priority = validatePriority(value.priority, `${path}.priority`);
    const visibility = visibilitySnapshot(
        value.visibility,
        `${path}.visibility`,
        origin.moduleId,
        'INVALID_PROVIDER'
    );
    const ambientDepth = validateDepth(
        value.ambientDepth,
        `${path}.ambientDepth`,
        'INVALID_PROVIDER'
    );
    const type = cloneCoreExpression(
        value.type,
        `${path}.type`,
        ambientDepth,
        'INVALID_PROVIDER'
    );
    const term = cloneCoreExpression(
        value.term,
        `${path}.term`,
        ambientDepth,
        'INVALID_PROVIDER'
    );

    const telescope: CoreLfInstanceProviderBinder[] = [];
    let cursor = type;
    value.telescope.forEach((binderValue, ordinal) => {
        const binderPath = `${path}.telescope[${ordinal}]`;
        if (
            cursor.tag !== 'pi' ||
            !record(binderValue) ||
            binderValue.ordinal !== ordinal ||
            typeof binderValue.binderName !== 'string' ||
            !OUTPUT_NAME.test(binderValue.binderName) ||
            (
                binderValue.kind !== 'ordinary' &&
                binderValue.kind !== 'instance-premise'
            )
        ) {
            return fail(
                'INVALID_PROVIDER',
                binderPath,
                'Provider telescope differs from its exact Pi type'
            );
        }
        const mode = cloneMode(
            binderValue.mode,
            `${binderPath}.mode`,
            'INVALID_PROVIDER'
        );
        const binderType = cloneCoreExpression(
            binderValue.type,
            `${binderPath}.type`,
            ambientDepth + ordinal,
            'INVALID_PROVIDER'
        );
        if (
            binderValue.binderName !== cursor.binder.name ||
            !sameMode(mode, cursor.binder.mode) ||
            !kernelExpressionEquals(binderType, cursor.binder.type)
        ) {
            return fail(
                'INVALID_PROVIDER',
                binderPath,
                'Provider binder metadata differs from its exact Pi binder'
            );
        }
        if (binderValue.kind === 'ordinary') {
            telescope.push({
                kind: 'ordinary',
                ordinal,
                binderName: binderValue.binderName,
                mode,
                type: binderType
            });
        } else {
            const target = classApplicationSnapshot(
                binderValue.target,
                `${binderPath}.target`,
                ambientDepth + ordinal,
                'INVALID_PROVIDER'
            );
            if (!kernelExpressionEquals(target.type, binderType)) {
                return fail(
                    'INVALID_PROVIDER',
                    `${binderPath}.target`,
                    'Premise target differs from its exact Pi binder type'
                );
            }
            telescope.push({
                kind: 'instance-premise',
                ordinal,
                binderName: binderValue.binderName,
                mode,
                type: binderType,
                target
            });
        }
        cursor = cursor.body;
    });
    if (cursor.tag === 'pi') {
        return fail(
            'INVALID_PROVIDER',
            `${path}.telescope`,
            'Provider snapshot omitted one or more Pi binders'
        );
    }
    const result = classApplicationSnapshot(
        value.result,
        `${path}.result`,
        ambientDepth + telescope.length,
        'INVALID_PROVIDER'
    );
    if (!kernelExpressionEquals(result.type, cursor)) {
        return fail(
            'INVALID_PROVIDER',
            `${path}.result`,
            'Provider result differs from the final body of its Pi type'
        );
    }
    const source = providerSourceSnapshot(
        value.source,
        `${path}.source`,
        providerId,
        term,
        result,
        telescope,
        visibility,
        ambientDepth
    );
    return deepFreeze({
        revision: CORE_LF_INSTANCE_SCOPE_PROFILE.providerRevision,
        providerId,
        origin,
        provenance: provenanceSnapshot,
        priority,
        visibility,
        ambientDepth,
        term,
        type,
        telescope,
        result,
        source
    });
};

/** Revalidate and canonicalize a finite provider registry. */
export function createCoreLfInstanceRegistrySnapshot(
    input: CoreLfCreateInstanceRegistryInput
): CoreLfInstanceRegistrySnapshot {
    if (!record(input) || !Array.isArray(input.providers)) {
        return fail(
            'INVALID_REGISTRY',
            'input',
            'Instance registry input requires a finite provider array'
        );
    }
    const registryRevision = validateRevision(
        input.revision,
        'input.revision',
        'INVALID_REGISTRY'
    );
    const providers = input.providers
        .map((provider, index) => providerSnapshot(
            provider,
            `input.providers[${index}]`
        ))
        .sort((left, right) => compareText(
            symbolKey(left.providerId),
            symbolKey(right.providerId)
        ));
    for (let index = 1; index < providers.length; index++) {
        if (
            symbolKey(providers[index - 1].providerId) ===
            symbolKey(providers[index].providerId)
        ) {
            return fail(
                'DUPLICATE_PROVIDER',
                `input.providers[${index}]`,
                `Provider '${displaySymbol(providers[index].providerId)}' ` +
                    'is repeated in the registry'
            );
        }
    }
    return deepFreeze({
        revision: CORE_LF_INSTANCE_SCOPE_PROFILE.registryRevision,
        registryRevision,
        providers
    });
}

/** Canonical portable JSON for one immutable provider registry. */
export const serializeCoreLfInstanceRegistrySnapshot = (
    snapshot: CoreLfInstanceRegistrySnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    createCoreLfInstanceRegistrySnapshot({
        revision: snapshot.registryRevision,
        providers: snapshot.providers
    }),
    'instanceRegistrySnapshot'
);

const providerMap = (
    registry: CoreLfInstanceRegistrySnapshot
): ReadonlyMap<string, CoreLfInstanceProviderDeclaration> => new Map(
    registry.providers.map(provider => [
        symbolKey(provider.providerId),
        provider
    ])
);

const symbolList = (
    value: unknown,
    path: string,
    code: CoreLfInstanceScopeErrorCode
): readonly CoreLfQualifiedSymbol[] => {
    if (!Array.isArray(value)) {
        return fail(code, path, 'Expected a finite provider-ID array');
    }
    const symbols = value
        .map((entry, index) => qualifiedSymbol(
            entry,
            `${path}[${index}]`,
            code
        ))
        .sort((left, right) => compareText(symbolKey(left), symbolKey(right)));
    for (let index = 1; index < symbols.length; index++) {
        if (symbolKey(symbols[index - 1]) === symbolKey(symbols[index])) {
            return fail(
                code,
                `${path}[${index}]`,
                `Provider '${displaySymbol(symbols[index])}' is repeated`
            );
        }
    }
    return symbols;
};

const importSnapshot = (
    value: unknown,
    path: string,
    currentModuleId: string,
    providers: ReadonlyMap<string, CoreLfInstanceProviderDeclaration>
): CoreLfInstanceImportSnapshot => {
    if (
        !record(value) ||
        typeof value.moduleId !== 'string' ||
        !MODULE_ID.test(value.moduleId) ||
        value.moduleId === currentModuleId ||
        typeof value.interfaceSha256 !== 'string' ||
        !SHA256.test(value.interfaceSha256)
    ) {
        return fail(
            'INVALID_IMPORT',
            path,
            'Invalid pinned imported instance interface'
        );
    }
    const moduleRevision = validateRevision(
        value.moduleRevision,
        `${path}.moduleRevision`,
        'INVALID_IMPORT'
    );
    const interfaceRevision = validateRevision(
        value.interfaceRevision,
        `${path}.interfaceRevision`,
        'INVALID_IMPORT'
    );
    const providerIds = symbolList(
        value.providers,
        `${path}.providers`,
        'INVALID_IMPORT'
    );
    providerIds.forEach((providerId, index) => {
        const provider = providers.get(symbolKey(providerId));
        if (provider === undefined) {
            return fail(
                'UNKNOWN_PROVIDER',
                `${path}.providers[${index}]`,
                `Imported provider '${displaySymbol(providerId)}' is absent ` +
                    'from the immutable registry'
            );
        }
        if (
            provider.origin.moduleId !== value.moduleId ||
            provider.origin.moduleRevision !== moduleRevision ||
            provider.visibility.kind === 'local'
        ) {
            return fail(
                'INELIGIBLE_PROVIDER',
                `${path}.providers[${index}]`,
                `Provider '${displaySymbol(providerId)}' is not exportable ` +
                    'from the pinned module revision'
            );
        }
    });
    return {
        moduleId: value.moduleId,
        moduleRevision,
        interfaceRevision,
        interfaceSha256: value.interfaceSha256,
        providers: providerIds
    };
};

const localFramesSnapshot = (
    value: unknown,
    currentModuleId: string,
    contextDepth: number,
    providers: ReadonlyMap<string, CoreLfInstanceProviderDeclaration>
): readonly CoreLfInstanceLocalFrameSnapshot[] => {
    if (!Array.isArray(value)) {
        return fail(
            'INVALID_LOCAL_FRAME',
            'input.localFrames',
            'Local instance frames must be a finite array'
        );
    }
    const frameIds = new Set<string>();
    const activatedProviders = new Set<string>();
    return value.map((frame, ordinal) => {
        const path = `input.localFrames[${ordinal}]`;
        if (
            !record(frame) ||
            (frame.kind !== 'section' && frame.kind !== 'local')
        ) {
            return fail(
                'INVALID_LOCAL_FRAME',
                path,
                'Local frame must identify section or local scope'
            );
        }
        const frameId = validateFrameId(
            frame.frameId,
            `${path}.frameId`,
            'INVALID_LOCAL_FRAME'
        );
        if (frameIds.has(frameId)) {
            return fail(
                'DUPLICATE_LOCAL_FRAME',
                `${path}.frameId`,
                `Lexical frame '${frameId}' is repeated`
            );
        }
        frameIds.add(frameId);
        const providerIds = symbolList(
            frame.providers,
            `${path}.providers`,
            'INVALID_LOCAL_FRAME'
        );
        providerIds.forEach((providerId, index) => {
            const key = symbolKey(providerId);
            const provider = providers.get(key);
            if (provider === undefined) {
                return fail(
                    'UNKNOWN_PROVIDER',
                    `${path}.providers[${index}]`,
                    `Local provider '${displaySymbol(providerId)}' is absent ` +
                        'from the immutable registry'
                );
            }
            if (activatedProviders.has(key)) {
                return fail(
                    'INELIGIBLE_PROVIDER',
                    `${path}.providers[${index}]`,
                    `Local provider '${displaySymbol(providerId)}' appears in ` +
                        'more than one lexical frame'
                );
            }
            activatedProviders.add(key);
            if (
                provider.visibility.kind !== 'local' ||
                provider.visibility.frameId !== frameId ||
                provider.visibility.frameKind !== frame.kind ||
                provider.origin.moduleId !== currentModuleId ||
                provider.ambientDepth !== contextDepth
            ) {
                return fail(
                    'INELIGIBLE_PROVIDER',
                    `${path}.providers[${index}]`,
                    `Provider '${displaySymbol(providerId)}' is not valid in ` +
                        'this exact lexical frame and Core depth'
                );
            }
        });
        return {
            ordinal,
            frameId,
            kind: frame.kind,
            providers: providerIds
        };
    });
};

const candidate = (
    provider: CoreLfInstanceProviderDeclaration,
    tier: CoreLfInstanceScopeCandidate['tier'],
    rank: number,
    activation: CoreLfInstanceCandidateActivation
): CoreLfInstanceScopeCandidate => ({
    providerId: { ...provider.providerId },
    tier,
    rank,
    priority: provider.priority,
    activation
});

/**
 * Build one explicit finite instance scope without attempting resolution.
 *
 * Local-frame input order is outermost-to-innermost and is semantic. Every
 * other set-like input is canonicalized independently of caller order.
 */
export function createCoreLfInstanceScopeSnapshot(
    input: CoreLfCreateInstanceScopeInput
): CoreLfInstanceScopeSnapshot {
    if (!record(input)) {
        return fail(
            'INVALID_SCOPE',
            'input',
            'Instance scope input must be an object'
        );
    }
    const scopeRevision = validateRevision(
        input.revision,
        'input.revision',
        'INVALID_SCOPE'
    );
    if (typeof input.moduleId !== 'string' || !MODULE_ID.test(input.moduleId)) {
        return fail(
            'INVALID_SCOPE',
            'input.moduleId',
            'Instance scope requires one exact current module ID'
        );
    }
    const contextDepth = validateDepth(
        input.contextDepth,
        'input.contextDepth',
        'INVALID_SCOPE'
    );
    if (!record(input.registry)) {
        return fail(
            'INVALID_REGISTRY',
            'input.registry',
            'Instance scope requires one immutable registry snapshot'
        );
    }
    const registry = createCoreLfInstanceRegistrySnapshot({
        revision: input.registry.registryRevision,
        providers: input.registry.providers
    });
    if (input.registry.revision !== registry.revision) {
        return fail(
            'INVALID_REGISTRY',
            'input.registry.revision',
            'Instance registry profile revision is invalid'
        );
    }
    const providers = providerMap(registry);

    const importsInput = input.imports ?? [];
    if (!Array.isArray(importsInput)) {
        return fail(
            'INVALID_IMPORT',
            'input.imports',
            'Imported instance interfaces must be a finite array'
        );
    }
    const imports = importsInput
        .map((entry, index) => importSnapshot(
            entry,
            `input.imports[${index}]`,
            input.moduleId,
            providers
        ))
        .sort((left, right) => compareText(left.moduleId, right.moduleId));
    for (let index = 1; index < imports.length; index++) {
        if (imports[index - 1].moduleId === imports[index].moduleId) {
            return fail(
                'DUPLICATE_IMPORT',
                `input.imports[${index}]`,
                `Module '${imports[index].moduleId}' has two instance imports`
            );
        }
    }
    const importedProvider = new Map<string, CoreLfInstanceImportSnapshot>();
    imports.forEach(importEntry => {
        importEntry.providers.forEach(providerId => {
            const key = symbolKey(providerId);
            if (importedProvider.has(key)) {
                fail(
                    'DUPLICATE_IMPORT',
                    'input.imports',
                    `Provider '${displaySymbol(providerId)}' is supplied by ` +
                        'two imported interfaces'
                );
            }
            importedProvider.set(key, importEntry);
        });
    });

    const localFrames = localFramesSnapshot(
        input.localFrames ?? [],
        input.moduleId,
        contextDepth,
        providers
    );

    const namedInput = input.openedNamedScopes ?? [];
    if (!Array.isArray(namedInput)) {
        return fail(
            'INVALID_NAMED_SCOPE',
            'input.openedNamedScopes',
            'Opened named scopes must be a finite array'
        );
    }
    const openedNamedScopes = namedInput
        .map((entry, index) => namedScope(
            entry,
            `input.openedNamedScopes[${index}]`,
            'INVALID_NAMED_SCOPE'
        ))
        .sort((left, right) => compareText(symbolKey(left), symbolKey(right)));
    for (let index = 1; index < openedNamedScopes.length; index++) {
        if (
            symbolKey(openedNamedScopes[index - 1]) ===
            symbolKey(openedNamedScopes[index])
        ) {
            return fail(
                'DUPLICATE_NAMED_SCOPE',
                `input.openedNamedScopes[${index}]`,
                `Named scope '${displaySymbol(openedNamedScopes[index])}' ` +
                    'is opened twice'
            );
        }
    }

    const candidates: CoreLfInstanceScopeCandidate[] = [];
    for (let index = localFrames.length - 1; index >= 0; index--) {
        const frame = localFrames[index];
        const rank = localFrames.length - index - 1;
        frame.providers.forEach(providerId => {
            const provider = providers.get(symbolKey(providerId))!;
            candidates.push(candidate(provider, 'local', rank, {
                kind: 'local-frame',
                frameId: frame.frameId,
                frameKind: frame.kind,
                frameOrdinal: frame.ordinal
            }));
        });
    }

    const namedRank = localFrames.length;
    openedNamedScopes.forEach(scope => {
        const eligible = registry.providers.filter(provider =>
            provider.visibility.kind === 'named' &&
            sameSymbol(provider.visibility.scope, scope) &&
            (
                provider.origin.moduleId === input.moduleId ||
                importedProvider.has(symbolKey(provider.providerId))
            )
        );
        if (eligible.length === 0) {
            return fail(
                'INVALID_NAMED_SCOPE',
                'input.openedNamedScopes',
                `Named scope '${displaySymbol(scope)}' has no provider in ` +
                    'the current module or pinned imports'
            );
        }
        eligible.forEach(provider => {
            const importEntry = importedProvider.get(
                symbolKey(provider.providerId)
            );
            candidates.push(candidate(
                provider,
                'named',
                namedRank,
                {
                    kind: 'named-scope',
                    scope: { ...scope },
                    availability: importEntry === undefined
                        ? {
                            kind: 'current-module',
                            moduleId: input.moduleId
                        }
                        : {
                            kind: 'imported-interface',
                            moduleId: importEntry.moduleId,
                            interfaceRevision:
                                importEntry.interfaceRevision,
                            interfaceSha256: importEntry.interfaceSha256
                        }
                }
            ));
        });
    });

    const ambientRank = namedRank + 1;
    registry.providers.forEach(provider => {
        if (provider.visibility.kind !== 'global') return;
        if (provider.origin.moduleId === input.moduleId) {
            candidates.push(candidate(provider, 'ambient', ambientRank, {
                kind: 'current-global',
                moduleId: input.moduleId
            }));
            return;
        }
        const importEntry = importedProvider.get(symbolKey(provider.providerId));
        if (importEntry !== undefined) {
            candidates.push(candidate(provider, 'ambient', ambientRank, {
                kind: 'imported-global',
                moduleId: importEntry.moduleId,
                interfaceRevision: importEntry.interfaceRevision,
                interfaceSha256: importEntry.interfaceSha256
            }));
        }
    });
    candidates.sort((left, right) =>
        left.rank - right.rank ||
        right.priority - left.priority ||
        compareText(symbolKey(left.providerId), symbolKey(right.providerId))
    );

    return deepFreeze({
        revision: CORE_LF_INSTANCE_SCOPE_PROFILE.scopeRevision,
        scopeRevision,
        registryRevision: registry.registryRevision,
        registryProviderIds: registry.providers.map(provider => ({
            ...provider.providerId
        })),
        moduleId: input.moduleId,
        contextDepth,
        localFrames,
        openedNamedScopes,
        imports,
        candidates
    });
}

/** Canonical portable JSON for one immutable explicit instance scope. */
export const serializeCoreLfInstanceScopeSnapshot = (
    snapshot: CoreLfInstanceScopeSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'instanceScopeSnapshot'
);
