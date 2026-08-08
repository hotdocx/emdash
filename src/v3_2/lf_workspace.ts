/**
 * Browser-safe local declaration workspaces for AI-authored emdash modules.
 *
 * This layer owns graph planning, deterministic portable snapshots, and
 * conservative invalidation diagnostics. Mathematical checking remains in
 * the existing LF declaration compiler and its exact dependency interfaces.
 * Filesystem I/O, hashing, cache writes, runtime fragments, and proof
 * documents deliberately remain outside this first workspace profile.
 */

import {
    CORE_EXPLICIT_SERIALIZATION_REVISION,
    serializeCoreExpression
} from './core_serialization';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfModuleSpec,
    CoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclaration,
    CoreLfCompiledDeclarationModule,
    CoreLfTransferDeclarationLink,
    CoreLfTransferDeclarationLinkage,
    compileCoreLfDeclarations
} from './lf_transfer_compiler';
import {
    CoreLfCompiledModuleInterface,
    createCoreLfCompiledModuleInterface
} from './lf_transfer_visibility';

export const CORE_LF_DECLARATION_WORKSPACE_PROFILE = Object.freeze({
    revision: 'emdash-lf-declaration-workspace-v1' as const,
    sourceSnapshotRevision: 'emdash-lf-workspace-source-v1' as const,
    interfaceSnapshotRevision: 'emdash-lf-workspace-interface-v1' as const,
    workspaceSnapshotRevision: 'emdash-lf-workspace-snapshot-v1' as const,
    closureSnapshotRevision: 'emdash-lf-workspace-closure-v1' as const,
    invalidationRevision: 'emdash-lf-workspace-invalidation-v1' as const,
    explicitCoreRevision: CORE_EXPLICIT_SERIALIZATION_REVISION,
    contentProfile: 'declaration-only-single-fragment-modules' as const,
    invalidationProfile: 'conservative-dependency-closure' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    executesIncrementally: false as const
});

export type CoreLfDeclarationWorkspaceErrorCode =
    | 'INVALID_WORKSPACE'
    | 'DUPLICATE_MODULE'
    | 'MISSING_DEPENDENCY'
    | 'CYCLIC_DEPENDENCY'
    | 'FOREIGN_COMPANION'
    | 'UNSUPPORTED_MODULE_CONTENT'
    | 'UNKNOWN_MODULE'
    | 'INVALID_SNAPSHOT'
    | 'NON_PORTABLE_DATA';

export class CoreLfDeclarationWorkspaceError extends Error {
    constructor(
        public readonly code: CoreLfDeclarationWorkspaceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfDeclarationWorkspaceError';
    }
}

const fail = (
    code: CoreLfDeclarationWorkspaceErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfDeclarationWorkspaceError(code, path, message);
};

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const WORKSPACE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

type CanonicalJsonValue =
    | null
    | boolean
    | number
    | string
    | readonly CanonicalJsonValue[]
    | { readonly [key: string]: CanonicalJsonValue };

const canonicalJsonValue = (
    value: unknown,
    path: string,
    ancestors: ReadonlySet<object>
): CanonicalJsonValue => {
    if (value === null) return null;
    switch (typeof value) {
        case 'boolean':
        case 'string':
            return value;
        case 'number':
            if (Number.isFinite(value)) return value;
            return fail(
                'NON_PORTABLE_DATA',
                path,
                'Canonical workspace data requires a finite number'
            );
        case 'object':
            break;
        case 'bigint':
        case 'function':
        case 'symbol':
        case 'undefined':
            return fail(
                'NON_PORTABLE_DATA',
                path,
                `Canonical workspace data cannot contain ${typeof value}`
            );
        default:
            return fail(
                'NON_PORTABLE_DATA',
                path,
                'Canonical workspace data has an unsupported value'
            );
    }

    if (ancestors.has(value)) {
        return fail(
            'NON_PORTABLE_DATA',
            path,
            'Canonical workspace data cannot contain a cycle'
        );
    }
    const nextAncestors = new Set(ancestors);
    nextAncestors.add(value);

    if (Array.isArray(value)) {
        return value.map((entry, index) => canonicalJsonValue(
            entry,
            `${path}[${index}]`,
            nextAncestors
        ));
    }

    const prototype = Object.getPrototypeOf(value);
    if (prototype !== Object.prototype && prototype !== null) {
        return fail(
            'NON_PORTABLE_DATA',
            path,
            'Canonical workspace data must use plain records and arrays'
        );
    }
    const record = value as Record<string, unknown>;
    const result: Record<string, CanonicalJsonValue> = {};
    Object.keys(record).sort(compareText).forEach(key => {
        result[key] = canonicalJsonValue(
            record[key],
            `${path}.${key}`,
            nextAncestors
        );
    });
    return result;
};

const canonicalJson = (value: unknown, path: string): string =>
    `${JSON.stringify(canonicalJsonValue(value, path, new Set()))}\n`;

/** Browser-safe canonical JSON shared by qualified workspace profiles. */
export const serializeCoreLfWorkspaceCanonicalJson = (
    value: unknown,
    path = 'workspacePortableData'
): string => canonicalJson(value, path);

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

const symbolKey = (
    symbol: { readonly moduleId: string; readonly name: string }
): string => `${symbol.moduleId}\u0000${symbol.name}`;

export interface CoreLfDeclarationWorkspaceModule {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

export interface CoreLfDeclarationWorkspaceInput {
    readonly revision: string;
    readonly modules: readonly CoreLfDeclarationWorkspaceModule[];
}

export interface CoreLfDeclarationWorkspacePlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision;
    readonly modules: readonly CoreLfDeclarationWorkspaceModule[];
    readonly order: readonly string[];
}

const assertWorkspaceModule = (
    source: CoreLfDeclarationWorkspaceModule,
    path: string
): void => {
    const { module, policy, linkage } = source;
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        fail(
            'FOREIGN_COMPANION',
            `${path}.policy`,
            `Policy does not target '${module.moduleId}/${module.fragmentId}'`
        );
    }
    if (
        linkage.moduleRevision !== module.revision ||
        linkage.moduleId !== module.moduleId ||
        linkage.fragmentId !== module.fragmentId
    ) {
        fail(
            'FOREIGN_COMPANION',
            `${path}.linkage`,
            `Linkage does not target '${module.moduleId}/${module.fragmentId}'`
        );
    }
    if (
        module.inductives.length > 0 ||
        module.runtimeRules.length > 0 ||
        module.proofRules.length > 0
    ) {
        fail(
            'UNSUPPORTED_MODULE_CONTENT',
            `${path}.module`,
            'The first workspace profile accepts declaration-only modules'
        );
    }
};

/** Freeze one exact semantic module/policy/linkage source unit. */
export function defineCoreLfDeclarationWorkspaceModule(
    source: CoreLfDeclarationWorkspaceModule
): CoreLfDeclarationWorkspaceModule {
    assertWorkspaceModule(source, 'module');
    return Object.freeze({
        module: source.module,
        policy: source.policy,
        linkage: source.linkage
    });
}

const dependencyCycle = (
    byId: ReadonlyMap<string, CoreLfDeclarationWorkspaceModule>
): readonly string[] | undefined => {
    const state = new Map<string, 'visiting' | 'complete'>();
    const stack: string[] = [];

    const visit = (moduleId: string): readonly string[] | undefined => {
        const existing = state.get(moduleId);
        if (existing === 'complete') return undefined;
        if (existing === 'visiting') {
            const start = stack.indexOf(moduleId);
            return Object.freeze([...stack.slice(start), moduleId]);
        }
        state.set(moduleId, 'visiting');
        stack.push(moduleId);
        const source = byId.get(moduleId);
        if (source === undefined) {
            return fail(
                'MISSING_DEPENDENCY',
                'modules',
                `Workspace has no module '${moduleId}'`
            );
        }
        for (const dependency of [...source.module.dependencies]
            .sort(compareText)) {
            const cycle = visit(dependency);
            if (cycle !== undefined) return cycle;
        }
        stack.pop();
        state.set(moduleId, 'complete');
        return undefined;
    };

    for (const moduleId of [...byId.keys()].sort(compareText)) {
        const cycle = visit(moduleId);
        if (cycle !== undefined) return cycle;
    }
    return undefined;
};

const topologicalOrder = (
    byId: ReadonlyMap<string, CoreLfDeclarationWorkspaceModule>
): readonly string[] => {
    const cycle = dependencyCycle(byId);
    if (cycle !== undefined) {
        return fail(
            'CYCLIC_DEPENDENCY',
            'modules',
            `Workspace dependency cycle: ${cycle.join(' -> ')}`
        );
    }

    const inDegree = new Map<string, number>();
    const dependents = new Map<string, Set<string>>();
    byId.forEach(source => {
        inDegree.set(source.module.moduleId, source.module.dependencies.length);
        source.module.dependencies.forEach(dependency => {
            const consumers = dependents.get(dependency) ?? new Set<string>();
            consumers.add(source.module.moduleId);
            dependents.set(dependency, consumers);
        });
    });
    const ready = [...inDegree.entries()]
        .filter(([, degree]) => degree === 0)
        .map(([moduleId]) => moduleId)
        .sort(compareText);
    const order: string[] = [];
    while (ready.length > 0) {
        const moduleId = ready.shift();
        if (moduleId === undefined) break;
        order.push(moduleId);
        [...(dependents.get(moduleId) ?? [])]
            .sort(compareText)
            .forEach(consumer => {
                const degree = (inDegree.get(consumer) ?? 0) - 1;
                inDegree.set(consumer, degree);
                if (degree === 0) {
                    ready.push(consumer);
                    ready.sort(compareText);
                }
            });
    }
    if (order.length !== byId.size) {
        return fail(
            'CYCLIC_DEPENDENCY',
            'modules',
            'Workspace dependency graph cannot be ordered'
        );
    }
    return Object.freeze(order);
};

/** Validate and freeze one deterministic declaration-workspace graph. */
export function createCoreLfDeclarationWorkspace(
    input: CoreLfDeclarationWorkspaceInput
): CoreLfDeclarationWorkspacePlan {
    if (!WORKSPACE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_WORKSPACE',
            'revision',
            `Invalid workspace revision '${input.revision}'`
        );
    }
    if (input.modules.length === 0) {
        return fail(
            'INVALID_WORKSPACE',
            'modules',
            'A declaration workspace requires at least one module'
        );
    }

    const byId = new Map<string, CoreLfDeclarationWorkspaceModule>();
    input.modules.forEach((source, index) => {
        assertWorkspaceModule(source, `modules[${index}]`);
        const defined = defineCoreLfDeclarationWorkspaceModule(source);
        const moduleId = defined.module.moduleId;
        const existing = byId.get(moduleId);
        if (existing !== undefined) {
            return fail(
                'DUPLICATE_MODULE',
                `modules[${index}].module.moduleId`,
                `Workspace profile permits one fragment for module ` +
                    `'${moduleId}', but received '${existing.module.fragmentId}' ` +
                    `and '${defined.module.fragmentId}'`
            );
        }
        byId.set(moduleId, defined);
    });
    input.modules.forEach((source, index) => {
        source.module.dependencies.forEach((dependency, dependencyIndex) => {
            if (byId.has(dependency)) return;
            fail(
                'MISSING_DEPENDENCY',
                `modules[${index}].module.dependencies[${dependencyIndex}]`,
                `Module '${source.module.moduleId}' requires missing module ` +
                    `'${dependency}'`
            );
        });
    });

    const order = topologicalOrder(byId);
    const modules = Object.freeze(order.map(moduleId => {
        const source = byId.get(moduleId);
        if (source === undefined) {
            return fail(
                'INVALID_WORKSPACE',
                'modules',
                `Planned module '${moduleId}' disappeared`
            );
        }
        return Object.freeze({
            module: source.module,
            policy: source.policy,
            linkage: source.linkage
        });
    }));
    return Object.freeze({
        revision: input.revision,
        profileRevision: CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
        modules,
        order
    });
}

export interface CoreLfDeclarationWorkspaceSourceSnapshot {
    readonly revision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.sourceSnapshotRevision;
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly linkage: CoreLfTransferDeclarationLinkage;
}

export const createCoreLfDeclarationWorkspaceSourceSnapshot = (
    source: CoreLfDeclarationWorkspaceModule
): CoreLfDeclarationWorkspaceSourceSnapshot => deepFreeze({
    revision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.sourceSnapshotRevision,
    module: source.module,
    policy: source.policy,
    linkage: source.linkage
});

export const serializeCoreLfDeclarationWorkspaceSource = (
    source: CoreLfDeclarationWorkspaceSourceSnapshot
): string => canonicalJson(source, 'sourceSnapshot');

export interface CoreLfDeclarationWorkspaceInterfaceEntry {
    readonly order: number;
    readonly symbol: {
        readonly moduleId: string;
        readonly name: string;
    };
    readonly visibility: 'public' | 'protected' | 'private';
    readonly policy: CoreLfCompiledDeclaration['policy'];
    readonly status: CoreLfCompiledDeclaration['status'];
    readonly link: CoreLfTransferDeclarationLink;
    readonly type: string;
    readonly body?: string;
}

export interface CoreLfDeclarationWorkspaceInterfaceSnapshot {
    readonly revision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.interfaceSnapshotRevision;
    readonly explicitCoreRevision:
        typeof CORE_EXPLICIT_SERIALIZATION_REVISION;
    readonly moduleId: string;
    readonly moduleRevision: string;
    readonly fragmentId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport?: CoreLfModuleSpec['canonicalExport'];
    readonly dependencies: readonly string[];
    readonly declarations:
        readonly CoreLfDeclarationWorkspaceInterfaceEntry[];
}

export const createCoreLfDeclarationWorkspaceInterfaceSnapshot = (
    compiled: CoreLfCompiledDeclarationModule
): CoreLfDeclarationWorkspaceInterfaceSnapshot => {
    const sourceBySymbol = new Map(
        compiled.module.declarations.map(declaration => [
            symbolKey(declaration.symbol),
            declaration
        ] as const)
    );
    const declarations = compiled.declarations.map((declaration, index) => {
        const source = sourceBySymbol.get(symbolKey(declaration.symbol));
        if (source === undefined) {
            return fail(
                'INVALID_SNAPSHOT',
                `interface.declarations[${index}]`,
                `Compiled declaration '${declaration.symbol.moduleId}.` +
                    `${declaration.symbol.name}' has no source record`
            );
        }
        return {
            order: declaration.order,
            symbol: { ...declaration.symbol },
            visibility: source.modifiers.visibility,
            policy: declaration.policy,
            status: declaration.status,
            link: declaration.link,
            type: serializeCoreExpression(declaration.type),
            ...(declaration.body === undefined
                ? {}
                : { body: serializeCoreExpression(declaration.body) })
        };
    });
    return deepFreeze({
        revision:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.interfaceSnapshotRevision,
        explicitCoreRevision: CORE_EXPLICIT_SERIALIZATION_REVISION,
        moduleId: compiled.module.moduleId,
        moduleRevision: compiled.module.revision,
        fragmentId: compiled.module.fragmentId,
        authorityPath: compiled.module.authorityPath,
        sourceSha256: compiled.module.sourceSha256,
        ...(compiled.module.canonicalExport === undefined
            ? {}
            : { canonicalExport: compiled.module.canonicalExport }),
        dependencies: [...compiled.module.dependencies],
        declarations
    });
};

export const serializeCoreLfDeclarationWorkspaceInterface = (
    snapshot: CoreLfDeclarationWorkspaceInterfaceSnapshot
): string => canonicalJson(snapshot, 'interfaceSnapshot');

export interface CoreLfCompiledDeclarationWorkspaceModule {
    readonly source: CoreLfDeclarationWorkspaceModule;
    readonly sourceSnapshot: CoreLfDeclarationWorkspaceSourceSnapshot;
    readonly sourceText: string;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly interface: CoreLfCompiledModuleInterface;
    readonly interfaceSnapshot:
        CoreLfDeclarationWorkspaceInterfaceSnapshot;
    readonly interfaceText: string;
}

/** Immutable executable result; portable data is exposed through snapshots. */
export class CoreLfCompiledDeclarationWorkspace {
    readonly revision: string;
    readonly modules: readonly CoreLfCompiledDeclarationWorkspaceModule[];

    constructor(
        public readonly plan: CoreLfDeclarationWorkspacePlan,
        modules: readonly CoreLfCompiledDeclarationWorkspaceModule[],
        public readonly environment: CoreLfDeclarationEnvironment
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.modules = Object.freeze([...modules]);
        Object.freeze(this);
    }

    module(
        moduleId: string
    ): CoreLfCompiledDeclarationWorkspaceModule | undefined {
        return this.modules.find(entry =>
            entry.source.module.moduleId === moduleId
        );
    }
}

/** Compile a planned graph by delegating each module to the existing checker. */
export function compileCoreLfDeclarationWorkspace(
    plan: CoreLfDeclarationWorkspacePlan
): CoreLfCompiledDeclarationWorkspace {
    if (
        plan.profileRevision !==
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision
    ) {
        return fail(
            'INVALID_WORKSPACE',
            'plan.profileRevision',
            'Workspace plan targets an unsupported profile'
        );
    }
    let environment = CoreLfDeclarationEnvironment.empty();
    const compiledById = new Map<
        string,
        CoreLfCompiledDeclarationWorkspaceModule
    >();
    const modules: CoreLfCompiledDeclarationWorkspaceModule[] = [];

    plan.modules.forEach((source, index) => {
        const dependencyInterfaces = source.module.dependencies.map(
            (dependency, dependencyIndex) => {
                const compiled = compiledById.get(dependency);
                if (compiled !== undefined) return compiled.interface;
                return fail(
                    'INVALID_WORKSPACE',
                    `plan.modules[${index}].module.dependencies[` +
                        `${dependencyIndex}]`,
                    `Dependency '${dependency}' is not compiled before ` +
                        `'${source.module.moduleId}'`
                );
            }
        );
        const compiled = compileCoreLfDeclarations(
            source.module,
            source.policy,
            source.linkage,
            {
                initialEnvironment: environment,
                dependencyInterfaces
            }
        );
        environment = compiled.environment;
        const moduleInterface =
            createCoreLfCompiledModuleInterface(compiled);
        const sourceSnapshot =
            createCoreLfDeclarationWorkspaceSourceSnapshot(source);
        const interfaceSnapshot =
            createCoreLfDeclarationWorkspaceInterfaceSnapshot(compiled);
        const result = Object.freeze({
            source,
            sourceSnapshot,
            sourceText:
                serializeCoreLfDeclarationWorkspaceSource(sourceSnapshot),
            compiled,
            interface: moduleInterface,
            interfaceSnapshot,
            interfaceText:
                serializeCoreLfDeclarationWorkspaceInterface(
                    interfaceSnapshot
                )
        });
        compiledById.set(source.module.moduleId, result);
        modules.push(result);
    });

    return new CoreLfCompiledDeclarationWorkspace(
        plan,
        modules,
        environment
    );
}

export interface CoreLfDeclarationWorkspaceSnapshotModule {
    readonly moduleId: string;
    readonly dependencies: readonly string[];
    readonly source: CoreLfDeclarationWorkspaceSourceSnapshot;
    readonly interface: CoreLfDeclarationWorkspaceInterfaceSnapshot;
}

export interface CoreLfDeclarationWorkspaceSnapshot {
    readonly revision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.workspaceSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly order: readonly string[];
    readonly modules: readonly CoreLfDeclarationWorkspaceSnapshotModule[];
}

export const createCoreLfDeclarationWorkspaceSnapshot = (
    compiled: CoreLfCompiledDeclarationWorkspace
): CoreLfDeclarationWorkspaceSnapshot => deepFreeze({
    revision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.workspaceSnapshotRevision,
    profileRevision: CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
    workspaceRevision: compiled.plan.revision,
    order: [...compiled.plan.order],
    modules: compiled.modules.map(entry => ({
        moduleId: entry.source.module.moduleId,
        dependencies: [...entry.source.module.dependencies],
        source: entry.sourceSnapshot,
        interface: entry.interfaceSnapshot
    }))
});

export const serializeCoreLfDeclarationWorkspaceSnapshot = (
    snapshot: CoreLfDeclarationWorkspaceSnapshot
): string => canonicalJson(snapshot, 'workspaceSnapshot');

export interface CoreLfDeclarationWorkspaceClosureSnapshot {
    readonly revision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.closureSnapshotRevision;
    readonly profileRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly rootModuleId: string;
    readonly order: readonly string[];
    readonly modules: readonly CoreLfDeclarationWorkspaceSnapshotModule[];
}

export function createCoreLfDeclarationWorkspaceClosureSnapshot(
    snapshot: CoreLfDeclarationWorkspaceSnapshot,
    rootModuleId: string
): CoreLfDeclarationWorkspaceClosureSnapshot {
    assertSnapshot(snapshot, 'snapshot');
    const byId = new Map(
        snapshot.modules.map(module => [module.moduleId, module] as const)
    );
    if (!byId.has(rootModuleId)) {
        return fail(
            'UNKNOWN_MODULE',
            'rootModuleId',
            `Workspace snapshot has no module '${rootModuleId}'`
        );
    }
    const closure = new Set<string>();
    const visit = (moduleId: string): void => {
        if (closure.has(moduleId)) return;
        const module = byId.get(moduleId);
        if (module === undefined) {
            return fail(
                'INVALID_SNAPSHOT',
                'snapshot.modules',
                `Workspace snapshot closure requires missing module ` +
                    `'${moduleId}'`
            );
        }
        module.dependencies.forEach(visit);
        closure.add(moduleId);
    };
    visit(rootModuleId);
    const modules = snapshot.modules.filter(module =>
        closure.has(module.moduleId)
    );
    return deepFreeze({
        revision:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.closureSnapshotRevision,
        profileRevision: CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
        workspaceRevision: snapshot.workspaceRevision,
        rootModuleId,
        order: modules.map(module => module.moduleId),
        modules
    });
}

export const serializeCoreLfDeclarationWorkspaceClosure = (
    snapshot: CoreLfDeclarationWorkspaceClosureSnapshot
): string => canonicalJson(snapshot, 'closureSnapshot');

export type CoreLfDeclarationWorkspaceInvalidationState =
    | 'added'
    | 'removed'
    | 'changed'
    | 'affected'
    | 'reusable';

export interface CoreLfDeclarationWorkspaceInvalidationModule {
    readonly moduleId: string;
    readonly state: CoreLfDeclarationWorkspaceInvalidationState;
    readonly reasons: readonly string[];
    readonly interfaceChanged: boolean;
}

export interface CoreLfDeclarationWorkspaceInvalidation {
    readonly revision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.invalidationRevision;
    readonly profile:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.invalidationProfile;
    readonly previousWorkspaceRevision: string;
    readonly currentWorkspaceRevision: string;
    readonly modules:
        readonly CoreLfDeclarationWorkspaceInvalidationModule[];
    readonly addedModuleIds: readonly string[];
    readonly removedModuleIds: readonly string[];
    readonly changedModuleIds: readonly string[];
    readonly affectedModuleIds: readonly string[];
    readonly reusableModuleIds: readonly string[];
    readonly executesIncrementally: false;
}

export const serializeCoreLfDeclarationWorkspaceInvalidation = (
    invalidation: CoreLfDeclarationWorkspaceInvalidation
): string => canonicalJson(invalidation, 'workspaceInvalidation');

const assertSnapshot = (
    snapshot: CoreLfDeclarationWorkspaceSnapshot,
    path: string
): void => {
    if (
        snapshot.revision !==
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.workspaceSnapshotRevision ||
        snapshot.profileRevision !==
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision ||
        snapshot.order.length !== snapshot.modules.length ||
        snapshot.order.some((moduleId, index) =>
            snapshot.modules[index]?.moduleId !== moduleId
        ) ||
        new Set(snapshot.order).size !== snapshot.order.length
    ) {
        fail(
            'INVALID_SNAPSHOT',
            path,
            'Workspace snapshot revision or deterministic order is invalid'
        );
    }
    snapshot.modules.forEach((module, index) => {
        if (
            module.source.revision !==
                CORE_LF_DECLARATION_WORKSPACE_PROFILE
                    .sourceSnapshotRevision ||
            module.interface.revision !==
                CORE_LF_DECLARATION_WORKSPACE_PROFILE
                    .interfaceSnapshotRevision ||
            module.moduleId !== module.source.module.moduleId ||
            module.moduleId !== module.interface.moduleId ||
            canonicalJson(module.dependencies, 'snapshot.dependencies') !==
                canonicalJson(
                    module.source.module.dependencies,
                    'snapshot.source.module.dependencies'
                ) ||
            canonicalJson(module.dependencies, 'snapshot.dependencies') !==
                canonicalJson(
                    module.interface.dependencies,
                    'snapshot.interface.dependencies'
                )
        ) {
            fail(
                'INVALID_SNAPSHOT',
                `${path}.modules[${index}]`,
                'Workspace snapshot module identity or dependency data drifted'
            );
        }
    });
    try {
        const plan = createCoreLfDeclarationWorkspace({
            revision: snapshot.workspaceRevision,
            modules: snapshot.modules.map(module => ({
                module: module.source.module,
                policy: module.source.policy,
                linkage: module.source.linkage
            }))
        });
        if (
            plan.order.length !== snapshot.order.length ||
            plan.order.some((moduleId, index) =>
                snapshot.order[index] !== moduleId
            )
        ) {
            fail(
                'INVALID_SNAPSHOT',
                `${path}.order`,
                'Workspace snapshot order is not the canonical graph order'
            );
        }
    } catch (error: unknown) {
        if (
            error instanceof CoreLfDeclarationWorkspaceError &&
            error.code === 'INVALID_SNAPSHOT'
        ) {
            throw error;
        }
        fail(
            'INVALID_SNAPSHOT',
            path,
            `Workspace snapshot graph is invalid: ` +
                (error instanceof Error ? error.message : String(error))
        );
    }
};

/**
 * Compare two valid snapshots and report a conservative dependency closure.
 * This does not execute or promise an incremental build.
 */
export function compareCoreLfDeclarationWorkspaceSnapshots(
    previous: CoreLfDeclarationWorkspaceSnapshot,
    current: CoreLfDeclarationWorkspaceSnapshot
): CoreLfDeclarationWorkspaceInvalidation {
    assertSnapshot(previous, 'previous');
    assertSnapshot(current, 'current');
    const previousById = new Map(
        previous.modules.map(module => [module.moduleId, module] as const)
    );
    const currentById = new Map(
        current.modules.map(module => [module.moduleId, module] as const)
    );
    const moduleIds = [...new Set([
        ...previousById.keys(),
        ...currentById.keys()
    ])].sort(compareText);
    const added = new Set<string>();
    const removed = new Set<string>();
    const sourceChanged = new Set<string>();
    const changed = new Set<string>();
    const interfaceChanged = new Set<string>();

    moduleIds.forEach(moduleId => {
        const before = previousById.get(moduleId);
        const after = currentById.get(moduleId);
        if (before === undefined) {
            added.add(moduleId);
            interfaceChanged.add(moduleId);
            return;
        }
        if (after === undefined) {
            removed.add(moduleId);
            interfaceChanged.add(moduleId);
            return;
        }
        if (
            canonicalJson(before.source, 'previous.source') !==
                canonicalJson(after.source, 'current.source')
        ) {
            sourceChanged.add(moduleId);
            changed.add(moduleId);
        }
        if (
            canonicalJson(before.interface, 'previous.interface') !==
                canonicalJson(after.interface, 'current.interface')
        ) {
            interfaceChanged.add(moduleId);
            changed.add(moduleId);
        }
    });

    const dependents = new Map<string, Set<string>>();
    const addEdges = (
        modules: readonly CoreLfDeclarationWorkspaceSnapshotModule[]
    ): void => modules.forEach(module =>
        module.dependencies.forEach(dependency => {
            const consumers = dependents.get(dependency) ?? new Set<string>();
            consumers.add(module.moduleId);
            dependents.set(dependency, consumers);
        })
    );
    addEdges(previous.modules);
    addEdges(current.modules);

    const affected = new Set<string>([
        ...added,
        ...removed,
        ...changed
    ]);
    const pending = [...affected].sort(compareText);
    while (pending.length > 0) {
        const dependency = pending.shift();
        if (dependency === undefined) break;
        [...(dependents.get(dependency) ?? [])]
            .sort(compareText)
            .forEach(consumer => {
                if (affected.has(consumer)) return;
                affected.add(consumer);
                pending.push(consumer);
                pending.sort(compareText);
            });
    }

    const modules = moduleIds.map(moduleId => {
        let state: CoreLfDeclarationWorkspaceInvalidationState;
        let reasons: string[];
        if (added.has(moduleId)) {
            state = 'added';
            reasons = ['module-added'];
        } else if (removed.has(moduleId)) {
            state = 'removed';
            reasons = ['module-removed'];
        } else if (changed.has(moduleId)) {
            state = 'changed';
            reasons = [
                ...(sourceChanged.has(moduleId)
                    ? ['source-bundle-changed']
                    : []),
                ...(interfaceChanged.has(moduleId)
                    ? ['interface-changed']
                    : [])
            ];
        } else if (affected.has(moduleId)) {
            state = 'affected';
            const source = currentById.get(moduleId) ??
                previousById.get(moduleId);
            reasons = (source?.dependencies ?? [])
                .filter(dependency => affected.has(dependency))
                .sort(compareText)
                .map(dependency => `dependency-affected:${dependency}`);
            if (reasons.length === 0) {
                reasons = ['dependency-closure-changed'];
            }
        } else {
            state = 'reusable';
            reasons = [];
        }
        return {
            moduleId,
            state,
            reasons,
            interfaceChanged: interfaceChanged.has(moduleId)
        };
    });

    return deepFreeze({
        revision:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.invalidationRevision,
        profile:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.invalidationProfile,
        previousWorkspaceRevision: previous.workspaceRevision,
        currentWorkspaceRevision: current.workspaceRevision,
        modules,
        addedModuleIds: [...added].sort(compareText),
        removedModuleIds: [...removed].sort(compareText),
        changedModuleIds: [...changed].sort(compareText),
        affectedModuleIds: [...affected].sort(compareText),
        reusableModuleIds: moduleIds.filter(moduleId =>
            !affected.has(moduleId)
        ),
        executesIncrementally: false as const
    });
}
