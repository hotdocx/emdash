/**
 * Browser-safe exact premise discovery over one checked LF module scope.
 *
 * The compiled index reconstructs the selected module's exact dependency
 * closure before deriving bounded type fingerprints. Its portable snapshot
 * contains source-visible declaration metadata only. Search never proves
 * applicability, constructs a proof, performs I/O, or retains mutable global
 * state.
 */

import {
    CORE_EXPLICIT_SERIALIZATION_REVISION,
    serializeCoreExpressionAtDepth
} from './core_serialization';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfCombinedNextStep,
    coreLfCombinedWeakHead
} from './lf_conversion';
import {
    CoreLfQualifiedSymbol,
    CoreLfTransferPolicyClass,
    CoreLfTransferVisibility,
    coreLfQualifiedSymbol
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationStatus,
    CoreLfTransferDeclarationLink
} from './lf_transfer_compiler';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE,
    CoreLfCompiledDeclarationWorkspace,
    CoreLfDeclarationWorkspaceInterfaceSnapshot,
    compileCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspaceClosureSnapshot,
    createCoreLfDeclarationWorkspaceSnapshot
} from './lf_workspace';
import {
    KernelExpression,
    assertSafeIdentifier
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export const CORE_LF_PREMISE_INDEX_PROFILE = Object.freeze({
    revision: 'emdash-lf-premise-index-v1' as const,
    snapshotRevision: 'emdash-lf-premise-index-snapshot-v1' as const,
    searchRevision: 'emdash-lf-premise-search-v1' as const,
    workspaceProfileRevision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
    explicitCoreRevision: CORE_EXPLICIT_SERIALIZATION_REVISION,
    scopePolicy:
        'root-local-plus-direct-public-imports' as const,
    closurePolicy:
        'recompile-exact-transitive-closure' as const,
    normalizationPolicy:
        'combined-beta-delta-conclusion-weak-head' as const,
    maxTypeVisitLimit: 16_384,
    maxNormalizationStepLimit: 256,
    defaultSearchResultLimit: 64,
    maxSearchResultLimit: 1_024,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const,
    provesApplicability: false as const,
    usesEmbeddings: false as const
});

export type CoreLfPremiseIndexErrorCode =
    | 'INVALID_INDEX_INPUT'
    | 'UNKNOWN_ROOT_MODULE'
    | 'INVALID_COMPILED_WORKSPACE'
    | 'CLOSURE_DRIFT'
    | 'INVALID_BUDGET'
    | 'TYPE_VISIT_LIMIT_EXCEEDED'
    | 'INVALID_TYPE'
    | 'INVALID_SEARCH_QUERY';

export class CoreLfPremiseIndexError extends Error {
    constructor(
        public readonly code: CoreLfPremiseIndexErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfPremiseIndexError';
    }
}

const fail = (
    code: CoreLfPremiseIndexErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfPremiseIndexError(code, path, message, underlying);
};

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const compareSymbols = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): number => compareText(symbolKey(left), symbolKey(right));

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean => left.moduleId === right.moduleId && left.name === right.name;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) return value.map(cloneData) as T;
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(Object.entries(
            value as Record<string, unknown>
        ).map(([key, entry]) => [key, cloneData(entry)])) as T;
    }
    return value;
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

const freezeData = <T>(value: T): T => deepFreeze(cloneData(value));

const sameTextArray = (
    left: readonly string[],
    right: readonly string[]
): boolean => left.length === right.length &&
    left.every((entry, index) => entry === right[index]);

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;

const assertModuleId = (value: string, path: string): void => {
    if (typeof value === 'string' && MODULE_ID.test(value)) return;
    fail(
        'INVALID_INDEX_INPUT',
        path,
        'Premise index root must be a valid exact module ID'
    );
};

const boundedSetting = (
    value: number | undefined,
    defaultValue: number,
    maximum: number,
    path: string
): number => {
    const selected = value ?? defaultValue;
    if (
        Number.isSafeInteger(selected) &&
        selected >= 0 &&
        selected <= maximum
    ) {
        return selected;
    }
    return fail(
        'INVALID_BUDGET',
        path,
        `Budget must be a nonnegative safe integer at most ${maximum}; ` +
            `received ${String(selected)}`
    );
};

export interface CoreLfPremiseIndexOptions {
    readonly typeVisitLimit?: number;
    readonly normalizationStepLimit?: number;
}

export interface CoreLfPremiseIndexSettings {
    readonly typeVisitLimit: number;
    readonly normalizationStepLimit: number;
}

const indexSettings = (
    options: CoreLfPremiseIndexOptions
): CoreLfPremiseIndexSettings => freezeData({
    typeVisitLimit: boundedSetting(
        options.typeVisitLimit,
        CORE_LF_PREMISE_INDEX_PROFILE.maxTypeVisitLimit,
        CORE_LF_PREMISE_INDEX_PROFILE.maxTypeVisitLimit,
        'options.typeVisitLimit'
    ),
    normalizationStepLimit: boundedSetting(
        options.normalizationStepLimit,
        CORE_LF_PREMISE_INDEX_PROFILE.maxNormalizationStepLimit,
        CORE_LF_PREMISE_INDEX_PROFILE.maxNormalizationStepLimit,
        'options.normalizationStepLimit'
    )
});

export type CoreLfPremiseTypeNodeTag = KernelExpression['tag'];

export type CoreLfPremiseHead =
    | { readonly kind: 'universe' }
    | { readonly kind: 'owner'; readonly owner: CoreOwnerId }
    | { readonly kind: 'free-reference'; readonly name: string }
    | { readonly kind: 'bound'; readonly index: number }
    | { readonly kind: 'lambda' }
    | { readonly kind: 'pi' }
    | { readonly kind: 'meta'; readonly expression: string };

interface CoreLfPremiseConclusionBase {
    readonly leadingBinderCount: number;
    readonly steps: number;
    readonly conclusion: string;
}

export interface CoreLfPremiseConclusionNormalized
extends CoreLfPremiseConclusionBase {
    readonly status: 'normalized';
    readonly head: CoreLfPremiseHead;
}

export interface CoreLfPremiseConclusionStuck
extends CoreLfPremiseConclusionBase {
    readonly status: 'stuck';
    readonly reason: 'plicity-mismatch';
    readonly expectedPlicity: 'explicit' | 'implicit';
    readonly actualPlicity: 'explicit' | 'implicit';
}

export interface CoreLfPremiseConclusionStepLimit
extends CoreLfPremiseConclusionBase {
    readonly status: 'step-limit-exceeded';
    readonly next: CoreLfCombinedNextStep;
}

export type CoreLfPremiseConclusionFingerprint =
    | CoreLfPremiseConclusionNormalized
    | CoreLfPremiseConclusionStuck
    | CoreLfPremiseConclusionStepLimit;

export interface CoreLfPremiseTypeFingerprint {
    readonly type: string;
    readonly nodeCount: number;
    readonly nodeTags: readonly CoreLfPremiseTypeNodeTag[];
    readonly owners: readonly CoreOwnerId[];
    readonly freeReferences: readonly string[];
    readonly conclusion: CoreLfPremiseConclusionFingerprint;
}

const expressionChildren = (
    expression: KernelExpression
): readonly KernelExpression[] => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return [];
        case 'meta':
            return expression.spine;
        case 'application':
            return expression.arguments.map(argument => argument.value);
        case 'call':
            return [
                expression.callee,
                ...expression.arguments.map(argument => argument.value)
            ];
        case 'pi':
        case 'lambda':
            return [expression.binder.type, expression.body];
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

interface StructuralFingerprint {
    readonly nodeCount: number;
    readonly nodeTags: readonly CoreLfPremiseTypeNodeTag[];
    readonly owners: readonly CoreOwnerId[];
    readonly freeReferences: readonly string[];
}

const structuralFingerprint = (
    expression: KernelExpression,
    visitLimit: number,
    path: string
): StructuralFingerprint => {
    const pending: KernelExpression[] = [expression];
    const nodeTags = new Set<CoreLfPremiseTypeNodeTag>();
    const owners = new Set<CoreOwnerId>();
    const freeReferences = new Set<string>();
    let nodeCount = 0;

    while (pending.length > 0) {
        const current = pending.pop();
        if (current === undefined) break;
        if (nodeCount === visitLimit) {
            return fail(
                'TYPE_VISIT_LIMIT_EXCEEDED',
                path,
                `Type fingerprint exceeds its ${visitLimit}-node budget`
            );
        }
        nodeCount++;
        nodeTags.add(current.tag);
        if (current.tag === 'application') owners.add(current.owner);
        if (current.tag === 'reference') freeReferences.add(current.name);
        const children = expressionChildren(current);
        for (let index = children.length - 1; index >= 0; index--) {
            pending.push(children[index]);
        }
    }

    return freezeData({
        nodeCount,
        nodeTags: [...nodeTags].sort(compareText),
        owners: [...owners].sort(compareText),
        freeReferences: [...freeReferences].sort(compareText)
    });
};

const rigidHead = (
    expression: KernelExpression,
    ambientDepth: number
): CoreLfPremiseHead => {
    let current = expression;
    while (current.tag === 'call') current = current.callee;
    switch (current.tag) {
        case 'universe':
            return Object.freeze({ kind: 'universe' });
        case 'application':
            return Object.freeze({
                kind: 'owner',
                owner: current.owner
            });
        case 'reference':
            return Object.freeze({
                kind: 'free-reference',
                name: current.name
            });
        case 'bound':
            return Object.freeze({
                kind: 'bound',
                index: current.index
            });
        case 'lambda':
            return Object.freeze({ kind: 'lambda' });
        case 'pi':
            return Object.freeze({ kind: 'pi' });
        case 'meta':
            return Object.freeze({
                kind: 'meta',
                expression: serializeCoreExpressionAtDepth(
                    current,
                    ambientDepth
                )
            });
        default: {
            const exhaustive: never = current;
            return exhaustive;
        }
    }
};

const conclusionFingerprint = (
    environment: CoreLfDeclarationEnvironment,
    expression: KernelExpression,
    ambientDepth: number,
    stepLimit: number
): CoreLfPremiseConclusionFingerprint => {
    let current = expression;
    let depth = ambientDepth;
    let leadingBinderCount = 0;
    let steps = 0;

    while (true) {
        while (current.tag === 'pi') {
            current = current.body;
            depth++;
            leadingBinderCount++;
        }

        const result = coreLfCombinedWeakHead(
            environment,
            current,
            stepLimit - steps
        );
        steps += result.steps;
        current = result.expression;
        const conclusion = serializeCoreExpressionAtDepth(current, depth);

        if (result.status === 'step-limit-exceeded') {
            return freezeData({
                status: result.status,
                leadingBinderCount,
                steps,
                conclusion,
                next: result.next
            });
        }
        if (result.status === 'stuck') {
            return freezeData({
                status: result.status,
                leadingBinderCount,
                steps,
                conclusion,
                reason: result.reason,
                expectedPlicity: result.expectedPlicity,
                actualPlicity: result.actualPlicity
            });
        }
        if (current.tag === 'pi') continue;
        return freezeData({
            status: 'normalized',
            leadingBinderCount,
            steps,
            conclusion,
            head: rigidHead(current, depth)
        });
    }
};

const fingerprintType = (
    environment: CoreLfDeclarationEnvironment,
    expression: KernelExpression,
    ambientDepth: number,
    settings: CoreLfPremiseIndexSettings,
    path: string
): CoreLfPremiseTypeFingerprint => {
    if (
        !Number.isSafeInteger(ambientDepth) ||
        ambientDepth < 0 ||
        ambientDepth > 1_000_000
    ) {
        return fail(
            'INVALID_TYPE',
            `${path}.ambientDepth`,
            'Type ambient depth must be a nonnegative safe integer at most ' +
                '1000000'
        );
    }
    const structural = structuralFingerprint(
        expression,
        settings.typeVisitLimit,
        path
    );
    let type: string;
    try {
        type = serializeCoreExpressionAtDepth(expression, ambientDepth);
    } catch (error: unknown) {
        return fail(
            'INVALID_TYPE',
            path,
            'Premise fingerprint input is not a valid scoped Core type',
            error instanceof Error ? error : undefined
        );
    }
    let conclusion: CoreLfPremiseConclusionFingerprint;
    try {
        conclusion = conclusionFingerprint(
            environment,
            expression,
            ambientDepth,
            settings.normalizationStepLimit
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_TYPE',
            path,
            'Premise conclusion head could not be normalized safely',
            error instanceof Error ? error : undefined
        );
    }
    return freezeData({
        type,
        nodeCount: structural.nodeCount,
        nodeTags: structural.nodeTags,
        owners: structural.owners,
        freeReferences: structural.freeReferences,
        conclusion
    });
};

export type CoreLfPremiseScope =
    | {
        readonly kind: 'local';
        readonly rootModuleId: string;
        readonly providerModuleId: string;
    }
    | {
        readonly kind: 'direct-public-import';
        readonly rootModuleId: string;
        readonly providerModuleId: string;
        readonly dependencyIndex: number;
    };

export type CoreLfPremiseIndexModuleRole =
    | 'root'
    | 'direct-import'
    | 'transitive-closure';

export interface CoreLfPremiseIndexModuleSnapshot {
    readonly moduleId: string;
    readonly role: CoreLfPremiseIndexModuleRole;
    readonly closureOrder: number;
    readonly directDependencyIndex?: number;
    readonly moduleRevision: string;
    readonly fragmentId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport?: {
        readonly exporterVersion: string;
        readonly sha256: string;
    };
    readonly dependencies: readonly string[];
    readonly interfaceRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.interfaceSnapshotRevision;
}

export interface CoreLfPremiseIndexEntrySnapshot {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly sourceOrder: number;
    readonly scope: CoreLfPremiseScope;
    readonly visibility: CoreLfTransferVisibility;
    readonly policy: CoreLfTransferPolicyClass;
    readonly status: CoreLfCompiledDeclarationStatus;
    readonly link: CoreLfTransferDeclarationLink;
    readonly type: string;
    readonly fingerprint: CoreLfPremiseTypeFingerprint;
}

export interface CoreLfPremiseIndexSnapshot {
    readonly revision:
        typeof CORE_LF_PREMISE_INDEX_PROFILE.snapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_PREMISE_INDEX_PROFILE.revision;
    readonly workspaceProfileRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision;
    readonly explicitCoreRevision:
        typeof CORE_EXPLICIT_SERIALIZATION_REVISION;
    readonly workspaceRevision: string;
    readonly rootModuleId: string;
    readonly settings: CoreLfPremiseIndexSettings;
    readonly closureOrder: readonly string[];
    readonly modules: readonly CoreLfPremiseIndexModuleSnapshot[];
    readonly entries: readonly CoreLfPremiseIndexEntrySnapshot[];
}

export interface CoreLfCompiledAccessiblePremise {
    readonly entry: CoreLfPremiseIndexEntrySnapshot;
    readonly checkedType: KernelExpression;
}

/** Process-local index paired with its portable immutable snapshot. */
export class CoreLfCompiledPremiseIndex {
    readonly revision: string;
    readonly entries: readonly CoreLfCompiledAccessiblePremise[];

    constructor(
        public readonly snapshot: CoreLfPremiseIndexSnapshot,
        entries: readonly CoreLfCompiledAccessiblePremise[],
        public readonly closureCompilation:
            CoreLfCompiledDeclarationWorkspace
    ) {
        this.revision = `${snapshot.revision}+compiled-1`;
        this.entries = Object.freeze(entries.map(entry => Object.freeze({
            entry: entry.entry,
            checkedType: entry.checkedType
        })));
        Object.freeze(this);
    }

    resolve(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledAccessiblePremise | undefined {
        return this.entries.find(candidate =>
            sameSymbol(candidate.entry.symbol, symbol)
        );
    }

    fingerprintType(
        type: KernelExpression,
        ambientDepth = 0
    ): CoreLfPremiseTypeFingerprint {
        return fingerprintType(
            this.closureCompilation.environment,
            type,
            ambientDepth,
            this.snapshot.settings,
            'type'
        );
    }
}

interface RecompiledClosure {
    readonly compilation: CoreLfCompiledDeclarationWorkspace;
    readonly closureOrder: readonly string[];
}

const recompileExactClosure = (
    workspace: CoreLfCompiledDeclarationWorkspace,
    rootModuleId: string
): RecompiledClosure => {
    if (workspace.module(rootModuleId) === undefined) {
        return fail(
            'UNKNOWN_ROOT_MODULE',
            'rootModuleId',
            `Compiled workspace has no module '${rootModuleId}'`
        );
    }
    try {
        const snapshot = createCoreLfDeclarationWorkspaceSnapshot(workspace);
        const closure = createCoreLfDeclarationWorkspaceClosureSnapshot(
            snapshot,
            rootModuleId
        );
        const sourceById = new Map(workspace.plan.modules.map(source => [
            source.module.moduleId,
            source
        ] as const));
        if (sourceById.size !== workspace.plan.modules.length) {
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                'workspace.plan.modules',
                'Compiled workspace plan contains duplicate module sources'
            );
        }
        const sources = closure.order.map((moduleId, index) => {
            const source = sourceById.get(moduleId);
            if (source !== undefined) return source;
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                `closure.order[${index}]`,
                `Compiled workspace plan has no source for '${moduleId}'`
            );
        });
        const plan = createCoreLfDeclarationWorkspace({
            revision: `${workspace.plan.revision}+premise-index-closure-1`,
            modules: sources
        });
        if (!sameTextArray(plan.order, closure.order)) {
            return fail(
                'CLOSURE_DRIFT',
                'closure.order',
                'Reconstructed premise closure has a different module order'
            );
        }
        const compilation = compileCoreLfDeclarationWorkspace(plan);
        closure.order.forEach((moduleId, index) => {
            const original = workspace.module(moduleId);
            const reconstructed = compilation.module(moduleId);
            if (original === undefined || reconstructed === undefined) {
                return fail(
                    'INVALID_COMPILED_WORKSPACE',
                    `closure.order[${index}]`,
                    `Compiled workspace has no executable module '${moduleId}'`
                );
            }
            if (original.sourceText !== reconstructed.sourceText) {
                return fail(
                    'CLOSURE_DRIFT',
                    `closure.modules[${index}].source`,
                    `Reconstructed source for '${moduleId}' differs from ` +
                        'the supplied workspace'
                );
            }
            if (original.interfaceText !== reconstructed.interfaceText) {
                return fail(
                    'CLOSURE_DRIFT',
                    `closure.modules[${index}].interface`,
                    `Reconstructed interface for '${moduleId}' differs from ` +
                        'the supplied workspace'
                );
            }
        });
        return Object.freeze({
            compilation,
            closureOrder: Object.freeze([...closure.order])
        });
    } catch (error: unknown) {
        if (error instanceof CoreLfPremiseIndexError) throw error;
        return fail(
            'INVALID_COMPILED_WORKSPACE',
            'workspace',
            'Could not reconstruct the exact premise-index closure',
            error instanceof Error ? error : undefined
        );
    }
};

const moduleSnapshot = (
    index: number,
    module: CoreLfDeclarationWorkspaceInterfaceSnapshot,
    rootModuleId: string,
    directDependencies: readonly string[]
): CoreLfPremiseIndexModuleSnapshot => {
    const dependencyIndex = directDependencies.indexOf(module.moduleId);
    const role: CoreLfPremiseIndexModuleRole =
        module.moduleId === rootModuleId
            ? 'root'
            : dependencyIndex >= 0
                ? 'direct-import'
                : 'transitive-closure';
    return freezeData({
        moduleId: module.moduleId,
        role,
        closureOrder: index,
        ...(dependencyIndex < 0
            ? {}
            : { directDependencyIndex: dependencyIndex }),
        moduleRevision: module.moduleRevision,
        fragmentId: module.fragmentId,
        authorityPath: module.authorityPath,
        sourceSha256: module.sourceSha256,
        ...(module.canonicalExport === undefined
            ? {}
            : { canonicalExport: module.canonicalExport }),
        dependencies: [...module.dependencies],
        interfaceRevision: module.revision
    });
};

/** Build one exact source-visible premise index for a checked module. */
export function createCoreLfAccessiblePremiseIndex(
    workspace: CoreLfCompiledDeclarationWorkspace,
    rootModuleId: string,
    options: CoreLfPremiseIndexOptions = {}
): CoreLfCompiledPremiseIndex {
    assertModuleId(rootModuleId, 'rootModuleId');
    if (
        workspace === null ||
        typeof workspace !== 'object' ||
        !(workspace instanceof CoreLfCompiledDeclarationWorkspace)
    ) {
        return fail(
            'INVALID_INDEX_INPUT',
            'workspace',
            'Premise index requires a compiled declaration workspace'
        );
    }
    if (options === null || typeof options !== 'object') {
        return fail(
            'INVALID_INDEX_INPUT',
            'options',
            'Premise index options must be an object'
        );
    }
    const settings = indexSettings(options);
    const closure = recompileExactClosure(workspace, rootModuleId);
    const root = closure.compilation.module(rootModuleId);
    if (root === undefined) {
        return fail(
            'INVALID_COMPILED_WORKSPACE',
            'rootModuleId',
            `Reconstructed closure has no root '${rootModuleId}'`
        );
    }
    const directDependencies = root.source.module.dependencies;
    const modules = closure.compilation.modules.map((module, index) =>
        moduleSnapshot(
            index,
            module.interfaceSnapshot,
            rootModuleId,
            directDependencies
        )
    );
    const compiledEntries: CoreLfCompiledAccessiblePremise[] = [];

    closure.compilation.modules.forEach(module => {
        const moduleId = module.source.module.moduleId;
        const local = moduleId === rootModuleId;
        const dependencyIndex = directDependencies.indexOf(moduleId);
        if (!local && dependencyIndex < 0) return;
        const interfaceBySymbol = new Map(
            module.interfaceSnapshot.declarations.map(declaration => [
                symbolKey(declaration.symbol),
                declaration
            ] as const)
        );
        module.compiled.declarations.forEach(declaration => {
            const portable = interfaceBySymbol.get(
                symbolKey(declaration.symbol)
            );
            if (portable === undefined) {
                return fail(
                    'INVALID_COMPILED_WORKSPACE',
                    `modules.${moduleId}.declarations`,
                    `Declaration '${displaySymbol(declaration.symbol)}' has ` +
                        'no reconstructed interface entry'
                );
            }
            if (portable.status === 'excluded') return;
            if (!local && portable.visibility !== 'public') return;
            const scope: CoreLfPremiseScope = local
                ? Object.freeze({
                    kind: 'local',
                    rootModuleId,
                    providerModuleId: moduleId
                })
                : Object.freeze({
                    kind: 'direct-public-import',
                    rootModuleId,
                    providerModuleId: moduleId,
                    dependencyIndex
                });
            const fingerprint = fingerprintType(
                closure.compilation.environment,
                declaration.type,
                0,
                settings,
                `entries.${displaySymbol(declaration.symbol)}.type`
            );
            const entry: CoreLfPremiseIndexEntrySnapshot = freezeData({
                symbol: declaration.symbol,
                sourceOrder: declaration.order,
                scope,
                visibility: portable.visibility,
                policy: declaration.policy,
                status: declaration.status,
                link: declaration.link,
                type: fingerprint.type,
                fingerprint
            });
            compiledEntries.push(Object.freeze({
                entry,
                checkedType: declaration.type
            }));
        });
    });

    compiledEntries.sort((left, right) =>
        compareSymbols(left.entry.symbol, right.entry.symbol)
    );
    for (let index = 1; index < compiledEntries.length; index++) {
        if (sameSymbol(
            compiledEntries[index - 1].entry.symbol,
            compiledEntries[index].entry.symbol
        )) {
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                `entries[${index}]`,
                `Premise index duplicates '${displaySymbol(
                    compiledEntries[index].entry.symbol
                )}'`
            );
        }
    }

    const snapshot: CoreLfPremiseIndexSnapshot = freezeData({
        revision: CORE_LF_PREMISE_INDEX_PROFILE.snapshotRevision,
        profileRevision: CORE_LF_PREMISE_INDEX_PROFILE.revision,
        workspaceProfileRevision:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
        explicitCoreRevision: CORE_EXPLICIT_SERIALIZATION_REVISION,
        workspaceRevision: workspace.plan.revision,
        rootModuleId,
        settings,
        closureOrder: closure.closureOrder,
        modules,
        entries: compiledEntries.map(entry => entry.entry)
    });
    return new CoreLfCompiledPremiseIndex(
        snapshot,
        compiledEntries,
        closure.compilation
    );
}

export const serializeCoreLfPremiseIndexSnapshot = (
    snapshot: CoreLfPremiseIndexSnapshot
): string => `${JSON.stringify(snapshot, null, 2)}\n`;

export type CoreLfPremiseSearchQuery =
    | { readonly kind: 'all' }
    | {
        readonly kind: 'exact-id';
        readonly symbol: CoreLfQualifiedSymbol;
    }
    | {
        readonly kind: 'conclusion-head';
        readonly type: KernelExpression;
        readonly ambientDepth?: number;
    }
    | {
        readonly kind: 'contains-owner';
        readonly owner: CoreOwnerId;
    }
    | {
        readonly kind: 'contains-free-reference';
        readonly name: string;
    }
    | {
        readonly kind: 'contains-node';
        readonly tag: CoreLfPremiseTypeNodeTag;
    };

export type CoreLfPremiseSearchQuerySnapshot =
    | { readonly kind: 'all' }
    | {
        readonly kind: 'exact-id';
        readonly symbol: CoreLfQualifiedSymbol;
    }
    | {
        readonly kind: 'conclusion-head';
        readonly ambientDepth: number;
        readonly target: string;
        readonly conclusion: CoreLfPremiseConclusionFingerprint;
    }
    | {
        readonly kind: 'contains-owner';
        readonly owner: CoreOwnerId;
    }
    | {
        readonly kind: 'contains-free-reference';
        readonly name: string;
    }
    | {
        readonly kind: 'contains-node';
        readonly tag: CoreLfPremiseTypeNodeTag;
    };

export interface CoreLfPremiseSearchOptions {
    readonly limit?: number;
}

export interface CoreLfPremiseSearchResult {
    readonly revision:
        typeof CORE_LF_PREMISE_INDEX_PROFILE.searchRevision;
    readonly indexRevision: string;
    readonly rootModuleId: string;
    readonly query: CoreLfPremiseSearchQuerySnapshot;
    readonly limit: number;
    readonly totalMatches: number;
    readonly truncated: boolean;
    readonly matches: readonly CoreLfPremiseIndexEntrySnapshot[];
}

const NODE_TAGS: readonly CoreLfPremiseTypeNodeTag[] = Object.freeze([
    'application',
    'bound',
    'call',
    'lambda',
    'meta',
    'pi',
    'reference',
    'universe'
]);

const assertExactSymbol = (
    symbol: CoreLfQualifiedSymbol,
    path: string
): CoreLfQualifiedSymbol => {
    try {
        return coreLfQualifiedSymbol(symbol.moduleId, symbol.name);
    } catch (error: unknown) {
        return fail(
            'INVALID_SEARCH_QUERY',
            path,
            'Exact premise query requires a valid qualified symbol',
            error instanceof Error ? error : undefined
        );
    }
};

const assertOwner = (value: CoreOwnerId, path: string): CoreOwnerId => {
    if (Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, value)) {
        return value;
    }
    return fail(
        'INVALID_SEARCH_QUERY',
        path,
        `Unknown semantic owner '${String(value)}'`
    );
};

const assertFreeReference = (value: string, path: string): string => {
    try {
        assertSafeIdentifier(value, 'premise search free reference');
        return value;
    } catch (error: unknown) {
        return fail(
            'INVALID_SEARCH_QUERY',
            path,
            'Free-reference query requires a safe Core identifier',
            error instanceof Error ? error : undefined
        );
    }
};

const assertNodeTag = (
    value: CoreLfPremiseTypeNodeTag,
    path: string
): CoreLfPremiseTypeNodeTag => {
    if (NODE_TAGS.includes(value)) return value;
    return fail(
        'INVALID_SEARCH_QUERY',
        path,
        `Unknown Core node tag '${String(value)}'`
    );
};

const headKey = (head: CoreLfPremiseHead): string => JSON.stringify(head);

interface PreparedSearch {
    readonly snapshot: CoreLfPremiseSearchQuerySnapshot;
    readonly accepts: (entry: CoreLfPremiseIndexEntrySnapshot) => boolean;
}

const prepareSearch = (
    index: CoreLfCompiledPremiseIndex,
    query: CoreLfPremiseSearchQuery
): PreparedSearch => {
    if (query === null || typeof query !== 'object') {
        return fail(
            'INVALID_SEARCH_QUERY',
            'query',
            'Premise search query must be an object'
        );
    }
    switch (query.kind) {
        case 'all':
            return {
                snapshot: Object.freeze({ kind: query.kind }),
                accepts: () => true
            };
        case 'exact-id': {
            const symbol = assertExactSymbol(query.symbol, 'query.symbol');
            return {
                snapshot: freezeData({ kind: query.kind, symbol }),
                accepts: entry => sameSymbol(entry.symbol, symbol)
            };
        }
        case 'conclusion-head': {
            const ambientDepth = query.ambientDepth ?? 0;
            const fingerprint = index.fingerprintType(
                query.type,
                ambientDepth
            );
            const target = fingerprint.conclusion;
            const key = target.status === 'normalized'
                ? headKey(target.head)
                : undefined;
            return {
                snapshot: freezeData({
                    kind: query.kind,
                    ambientDepth,
                    target: fingerprint.type,
                    conclusion: target
                }),
                accepts: entry =>
                    key !== undefined &&
                    entry.fingerprint.conclusion.status === 'normalized' &&
                    headKey(entry.fingerprint.conclusion.head) === key
            };
        }
        case 'contains-owner': {
            const owner = assertOwner(query.owner, 'query.owner');
            return {
                snapshot: Object.freeze({ kind: query.kind, owner }),
                accepts: entry => entry.fingerprint.owners.includes(owner)
            };
        }
        case 'contains-free-reference': {
            const name = assertFreeReference(query.name, 'query.name');
            return {
                snapshot: Object.freeze({ kind: query.kind, name }),
                accepts: entry =>
                    entry.fingerprint.freeReferences.includes(name)
            };
        }
        case 'contains-node': {
            const tag = assertNodeTag(query.tag, 'query.tag');
            return {
                snapshot: Object.freeze({ kind: query.kind, tag }),
                accepts: entry => entry.fingerprint.nodeTags.includes(tag)
            };
        }
        default:
            return fail(
                'INVALID_SEARCH_QUERY',
                'query.kind',
                `Unknown premise search kind '${String(
                    (query as { readonly kind?: unknown }).kind
                )}'`
            );
    }
};

/** Search one already constructed source-visible index exactly and finitely. */
export function searchCoreLfAccessiblePremises(
    index: CoreLfCompiledPremiseIndex,
    query: CoreLfPremiseSearchQuery,
    options: CoreLfPremiseSearchOptions = {}
): CoreLfPremiseSearchResult {
    if (!(index instanceof CoreLfCompiledPremiseIndex)) {
        return fail(
            'INVALID_SEARCH_QUERY',
            'index',
            'Premise search requires a compiled premise index'
        );
    }
    if (options === null || typeof options !== 'object') {
        return fail(
            'INVALID_SEARCH_QUERY',
            'options',
            'Premise search options must be an object'
        );
    }
    const limit = boundedSetting(
        options.limit,
        CORE_LF_PREMISE_INDEX_PROFILE.defaultSearchResultLimit,
        CORE_LF_PREMISE_INDEX_PROFILE.maxSearchResultLimit,
        'options.limit'
    );
    const prepared = prepareSearch(index, query);
    const candidates = index.snapshot.entries.filter(prepared.accepts);
    return freezeData({
        revision: CORE_LF_PREMISE_INDEX_PROFILE.searchRevision,
        indexRevision: index.snapshot.revision,
        rootModuleId: index.snapshot.rootModuleId,
        query: prepared.snapshot,
        limit,
        totalMatches: candidates.length,
        truncated: candidates.length > limit,
        matches: candidates.slice(0, limit)
    });
}

export const serializeCoreLfPremiseSearchResult = (
    result: CoreLfPremiseSearchResult
): string => `${JSON.stringify(result, null, 2)}\n`;
