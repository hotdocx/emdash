/**
 * Browser-safe immutable lock and cache-data contracts for remote LF graphs.
 *
 * This layer validates portable data and reconstructs canonical source plans.
 * It deliberately does not compute hashes, fetch content, read paths, or own
 * persistent storage. The adjacent Node materializer owns byte/hash checks.
 */

import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE,
    CoreLfFragmentModuleWorkspacePlan,
    CoreLfFragmentModuleWorkspaceSourceSnapshot,
    CoreLfFragmentModuleWorkspaceSourceSnapshotModule,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSourceSnapshot,
    serializeCoreLfFragmentModuleWorkspaceSourceSnapshot
} from './lf_fragment_module_workspace';
import {
    CoreLfSameModuleFragmentSourceSnapshot,
    createCoreLfDependencyModuleFragmentChain,
    defineCoreLfDependencyModuleDeclarationFragment,
    defineCoreLfDependencyModuleMixedFragment
} from './lf_fragment_workspace';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE = Object.freeze({
    revision: 'emdash-lf-remote-workspace-lock-v1' as const,
    cacheEntryRevision:
        'emdash-lf-remote-workspace-cache-entry-v1' as const,
    sourceArtifact:
        'canonical-fragment-module-workspace-source-snapshot' as const,
    identityProfile:
        'logical-workspace-source-bytes-source-and-compiled-digests' as const,
    mirrorProfile: 'non-authoritative-canonical-https' as const,
    cacheProfile: 'immutable-source-text-reverify-on-every-use' as const,
    computesCryptographicHashes: false as const,
    performsTransport: false as const,
    ownsPersistentStorage: false as const,
    nodeBuiltinDependency: false as const
});

export const serializeCoreLfRemoteWorkspaceLockProfile = (): string =>
    `${JSON.stringify(CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE, null, 2)}\n`;

export type CoreLfRemoteWorkspaceErrorCode =
    | 'INVALID_LOCK'
    | 'INVALID_ARTIFACT_IDENTITY'
    | 'INVALID_MIRROR'
    | 'INVALID_CACHE_ENTRY'
    | 'CACHE_IDENTITY_MISMATCH'
    | 'INVALID_SOURCE_SNAPSHOT'
    | 'NONCANONICAL_SOURCE_SNAPSHOT'
    | 'WORKSPACE_IDENTITY_MISMATCH'
    | 'SOURCE_BYTE_LENGTH_MISMATCH'
    | 'SOURCE_HASH_MISMATCH'
    | 'COMPILED_HASH_MISMATCH';

export class CoreLfRemoteWorkspaceError extends Error {
    constructor(
        public readonly code: CoreLfRemoteWorkspaceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfRemoteWorkspaceError';
    }
}

const fail = (
    code: CoreLfRemoteWorkspaceErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfRemoteWorkspaceError(code, path, message);
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

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const sameKeys = (
    value: object,
    keys: readonly string[]
): boolean => {
    const actual = Object.keys(value).sort();
    const expected = [...keys].sort();
    return JSON.stringify(actual) === JSON.stringify(expected);
};

const plainRecord = (value: unknown): value is Record<string, unknown> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        Array.isArray(value)
    ) return false;
    const prototype = Object.getPrototypeOf(value);
    return prototype === Object.prototype || prototype === null;
};

const validRevision = (value: unknown): value is string =>
    typeof value === 'string' &&
    /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u.test(value);

const validLogicalId = (value: unknown): value is string =>
    typeof value === 'string' &&
    /^[A-Za-z0-9][A-Za-z0-9._:/@+-]*$/u.test(value);

const validSha256 = (value: unknown): value is string =>
    typeof value === 'string' && /^sha256:[0-9a-f]{64}$/u.test(value);

export interface CoreLfRemoteWorkspaceArtifactIdentity {
    readonly logicalWorkspaceId: string;
    readonly workspaceRevision: string;
    readonly sourceSnapshotRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
            .sourceSnapshotRevision;
    readonly sourceProfileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly sourceUtf8Bytes: number;
    readonly sourceSha256: string;
    readonly compiledSnapshotRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
            .compiledSnapshotRevision;
    readonly compiledProfileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly compiledSha256: string;
}

export interface CoreLfRemoteWorkspaceMirror {
    readonly kind: 'https';
    readonly uri: string;
}

export interface CoreLfRemoteWorkspaceLockInput {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision;
    readonly artifact: CoreLfRemoteWorkspaceArtifactIdentity;
    readonly mirrors: readonly CoreLfRemoteWorkspaceMirror[];
}

export type CoreLfRemoteWorkspaceLock = CoreLfRemoteWorkspaceLockInput;

export interface CoreLfRemoteWorkspaceCacheEntryInput {
    readonly revision:
        typeof CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.cacheEntryRevision;
    readonly profileRevision:
        typeof CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision;
    readonly artifact: CoreLfRemoteWorkspaceArtifactIdentity;
    readonly sourceText: string;
}

export type CoreLfRemoteWorkspaceCacheEntry =
    CoreLfRemoteWorkspaceCacheEntryInput;

export interface CoreLfRemoteWorkspaceSourceReconstruction {
    readonly sourceSnapshot:
        CoreLfFragmentModuleWorkspaceSourceSnapshot;
    readonly plan: CoreLfFragmentModuleWorkspacePlan;
    readonly sourceText: string;
}

/** Validate and clone one location-free immutable artifact identity. */
export function createCoreLfRemoteWorkspaceArtifactIdentity(
    input: CoreLfRemoteWorkspaceArtifactIdentity
): CoreLfRemoteWorkspaceArtifactIdentity {
    if (
        !plainRecord(input) ||
        !sameKeys(input, [
            'logicalWorkspaceId',
            'workspaceRevision',
            'sourceSnapshotRevision',
            'sourceProfileRevision',
            'sourceUtf8Bytes',
            'sourceSha256',
            'compiledSnapshotRevision',
            'compiledProfileRevision',
            'compiledSha256'
        ])
    ) {
        return fail(
            'INVALID_ARTIFACT_IDENTITY',
            'artifact',
            'Remote artifact identity has missing or unsupported fields'
        );
    }
    if (!validLogicalId(input.logicalWorkspaceId)) {
        return fail(
            'INVALID_ARTIFACT_IDENTITY',
            'artifact.logicalWorkspaceId',
            'Remote logical workspace ID is invalid'
        );
    }
    if (!validRevision(input.workspaceRevision)) {
        return fail(
            'INVALID_ARTIFACT_IDENTITY',
            'artifact.workspaceRevision',
            'Remote workspace revision is invalid'
        );
    }
    if (
        input.sourceSnapshotRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
                .sourceSnapshotRevision ||
        input.sourceProfileRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision ||
        input.compiledSnapshotRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
                .compiledSnapshotRevision ||
        input.compiledProfileRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision
    ) {
        return fail(
            'INVALID_ARTIFACT_IDENTITY',
            'artifact.profileRevision',
            'Remote artifact targets unsupported source or compiled profiles'
        );
    }
    if (
        !Number.isSafeInteger(input.sourceUtf8Bytes) ||
        input.sourceUtf8Bytes <= 0
    ) {
        return fail(
            'INVALID_ARTIFACT_IDENTITY',
            'artifact.sourceUtf8Bytes',
            'Remote source byte length must be a positive safe integer'
        );
    }
    if (
        !validSha256(input.sourceSha256) ||
        !validSha256(input.compiledSha256)
    ) {
        return fail(
            'INVALID_ARTIFACT_IDENTITY',
            'artifact.sha256',
            'Remote source and compiled identities require exact SHA-256'
        );
    }
    return deepFreeze(cloneData(input));
}

const createMirror = (
    input: CoreLfRemoteWorkspaceMirror,
    index: number
): CoreLfRemoteWorkspaceMirror => {
    if (
        !plainRecord(input) ||
        !sameKeys(input, ['kind', 'uri']) ||
        input.kind !== 'https' ||
        typeof input.uri !== 'string'
    ) {
        return fail(
            'INVALID_MIRROR',
            `mirrors[${index}]`,
            'Remote mirror must be one exact HTTPS record'
        );
    }
    let parsed: URL;
    try {
        parsed = new URL(input.uri);
    } catch {
        return fail(
            'INVALID_MIRROR',
            `mirrors[${index}].uri`,
            'Remote mirror URI is invalid'
        );
    }
    if (
        parsed.protocol !== 'https:' ||
        parsed.username.length > 0 ||
        parsed.password.length > 0 ||
        parsed.search.length > 0 ||
        parsed.hash.length > 0 ||
        parsed.toString() !== input.uri
    ) {
        return fail(
            'INVALID_MIRROR',
            `mirrors[${index}].uri`,
            'Persisted mirrors must be canonical credential-free HTTPS ' +
                'URLs without query or fragment'
        );
    }
    return deepFreeze({ kind: 'https' as const, uri: input.uri });
};

/** Validate and freeze one lock. Mirror locations never enter identity. */
export function createCoreLfRemoteWorkspaceLock(
    input: CoreLfRemoteWorkspaceLockInput
): CoreLfRemoteWorkspaceLock {
    if (
        !plainRecord(input) ||
        !sameKeys(input, [
            'revision',
            'profileRevision',
            'artifact',
            'mirrors'
        ]) ||
        !validRevision(input.revision) ||
        input.profileRevision !==
            CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision ||
        !Array.isArray(input.mirrors)
    ) {
        return fail(
            'INVALID_LOCK',
            'lock',
            'Remote workspace lock has invalid identity or shape'
        );
    }
    const artifact = createCoreLfRemoteWorkspaceArtifactIdentity(
        input.artifact
    );
    const mirrors = input.mirrors.map(createMirror);
    if (new Set(mirrors.map(mirror => mirror.uri)).size !== mirrors.length) {
        return fail(
            'INVALID_MIRROR',
            'mirrors',
            'Remote workspace lock duplicates a mirror'
        );
    }
    return deepFreeze({
        revision: input.revision,
        profileRevision: CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision,
        artifact,
        mirrors
    });
}

export const serializeCoreLfRemoteWorkspaceArtifactIdentity = (
    identity: CoreLfRemoteWorkspaceArtifactIdentity
): string => serializeCoreLfWorkspaceCanonicalJson(
    createCoreLfRemoteWorkspaceArtifactIdentity(identity),
    'remoteWorkspaceArtifactIdentity'
);

export const serializeCoreLfRemoteWorkspaceLock = (
    lock: CoreLfRemoteWorkspaceLockInput
): string => serializeCoreLfWorkspaceCanonicalJson(
    createCoreLfRemoteWorkspaceLock(lock),
    'remoteWorkspaceLock'
);

const objectRecord = (
    value: unknown,
    path: string
): Record<string, unknown> => {
    if (
        !plainRecord(value)
    ) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Remote source snapshot requires a plain record'
        );
    }
    return value as Record<string, unknown>;
};

/** Re-run every fragment, chain, and graph constructor from portable data. */
export function reconstructCoreLfFragmentModuleWorkspaceSourceSnapshot(
    value: unknown
): CoreLfRemoteWorkspaceSourceReconstruction {
    try {
        const snapshotRecord = objectRecord(value, 'sourceSnapshot');
        const moduleValues = snapshotRecord.modules;
        if (!Array.isArray(moduleValues)) {
            return fail(
                'INVALID_SOURCE_SNAPSHOT',
                'sourceSnapshot.modules',
                'Remote source snapshot requires a module array'
            );
        }
        const modules = moduleValues.map((moduleValue, moduleIndex) => {
            const moduleRecord = objectRecord(
                moduleValue,
                `sourceSnapshot.modules[${moduleIndex}]`
            );
            const chainRecord = objectRecord(
                moduleRecord.chain,
                `sourceSnapshot.modules[${moduleIndex}].chain`
            );
            if (!Array.isArray(chainRecord.fragments)) {
                return fail(
                    'INVALID_SOURCE_SNAPSHOT',
                    `sourceSnapshot.modules[${moduleIndex}].chain.fragments`,
                    'Remote module chain requires fragment snapshots'
                );
            }
            const fragments = chainRecord.fragments.map(
                (fragmentValue, fragmentIndex) => {
                    const fragment = objectRecord(
                        fragmentValue,
                        `sourceSnapshot.modules[${moduleIndex}].chain.` +
                            `fragments[${fragmentIndex}]`
                    ) as unknown as CoreLfSameModuleFragmentSourceSnapshot;
                    const input = {
                        module: fragment.module,
                        policy: fragment.policy,
                        linkage: fragment.linkage,
                        externalProviders: fragment.externalProviders,
                        ...(fragment.runtimeProvider === undefined
                            ? {}
                            : { runtimeProvider: fragment.runtimeProvider })
                    };
                    if (fragment.kind === 'declaration') {
                        return defineCoreLfDependencyModuleDeclarationFragment(
                            input
                        );
                    }
                    if (fragment.kind === 'mixed') {
                        return defineCoreLfDependencyModuleMixedFragment(input);
                    }
                    return fail(
                        'INVALID_SOURCE_SNAPSHOT',
                        `sourceSnapshot.modules[${moduleIndex}].chain.` +
                            `fragments[${fragmentIndex}].kind`,
                        'Remote fragment snapshot has an unsupported kind'
                    );
                }
            );
            if (typeof chainRecord.workspaceRevision !== 'string') {
                return fail(
                    'INVALID_SOURCE_SNAPSHOT',
                    `sourceSnapshot.modules[${moduleIndex}].chain.` +
                        'workspaceRevision',
                    'Remote module chain requires a workspace revision'
                );
            }
            return {
                chain: createCoreLfDependencyModuleFragmentChain({
                    revision: chainRecord.workspaceRevision,
                    fragments
                }),
                dependencyProviders: moduleRecord.dependencyProviders as
                    CoreLfFragmentModuleWorkspaceSourceSnapshotModule[
                        'dependencyProviders'
                    ],
                runtimeProviders: moduleRecord.runtimeProviders as
                    CoreLfFragmentModuleWorkspaceSourceSnapshotModule[
                        'runtimeProviders'
                    ]
            };
        });
        if (typeof snapshotRecord.workspaceRevision !== 'string') {
            return fail(
                'INVALID_SOURCE_SNAPSHOT',
                'sourceSnapshot.workspaceRevision',
                'Remote graph source requires a workspace revision'
            );
        }
        const plan = createCoreLfFragmentModuleWorkspace({
            revision: snapshotRecord.workspaceRevision,
            modules
        });
        const sourceSnapshot =
            createCoreLfFragmentModuleWorkspaceSourceSnapshot(plan);
        const sourceText =
            serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
                sourceSnapshot
            );
        if (
            serializeCoreLfWorkspaceCanonicalJson(
                value,
                'suppliedFragmentModuleWorkspaceSourceSnapshot'
            ) !== sourceText
        ) {
            return fail(
                'INVALID_SOURCE_SNAPSHOT',
                'sourceSnapshot',
                'Remote graph source differs from canonical reconstruction'
            );
        }
        return deepFreeze({ sourceSnapshot, plan, sourceText });
    } catch (error) {
        if (error instanceof CoreLfRemoteWorkspaceError) throw error;
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceSnapshot',
            error instanceof Error
                ? `Remote graph source reconstruction failed: ${error.message}`
                : 'Remote graph source reconstruction failed'
        );
    }
}

/** Parse only exact canonical serializer output and reconstruct its graph. */
export function parseCoreLfFragmentModuleWorkspaceSourceText(
    sourceText: string
): CoreLfRemoteWorkspaceSourceReconstruction {
    if (typeof sourceText !== 'string' || sourceText.length === 0) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceText',
            'Remote graph source text must be nonempty'
        );
    }
    let value: unknown;
    try {
        value = JSON.parse(sourceText);
    } catch {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceText',
            'Remote graph source text is not valid JSON'
        );
    }
    const result =
        reconstructCoreLfFragmentModuleWorkspaceSourceSnapshot(value);
    if (result.sourceText !== sourceText) {
        return fail(
            'NONCANONICAL_SOURCE_SNAPSHOT',
            'sourceText',
            'Remote graph source must be exact canonical serializer output'
        );
    }
    return result;
}

/** Validate portable cache data without claiming that its digest was checked. */
export function createCoreLfRemoteWorkspaceCacheEntry(
    input: CoreLfRemoteWorkspaceCacheEntryInput
): CoreLfRemoteWorkspaceCacheEntry {
    if (
        !plainRecord(input) ||
        !sameKeys(input, [
            'revision',
            'profileRevision',
            'artifact',
            'sourceText'
        ]) ||
        input.revision !==
            CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.cacheEntryRevision ||
        input.profileRevision !==
            CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision ||
        typeof input.sourceText !== 'string'
    ) {
        return fail(
            'INVALID_CACHE_ENTRY',
            'cacheEntry',
            'Remote cache entry has invalid identity or shape'
        );
    }
    const artifact = createCoreLfRemoteWorkspaceArtifactIdentity(
        input.artifact
    );
    const reconstruction =
        parseCoreLfFragmentModuleWorkspaceSourceText(input.sourceText);
    if (
        reconstruction.plan.revision !== artifact.workspaceRevision ||
        reconstruction.sourceSnapshot.revision !==
            artifact.sourceSnapshotRevision ||
        reconstruction.sourceSnapshot.profileRevision !==
            artifact.sourceProfileRevision
    ) {
        return fail(
            'WORKSPACE_IDENTITY_MISMATCH',
            'cacheEntry.artifact',
            'Cached source graph differs from its artifact identity'
        );
    }
    return deepFreeze({
        revision:
            CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.cacheEntryRevision,
        profileRevision: CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision,
        artifact,
        sourceText: reconstruction.sourceText
    });
}

export const serializeCoreLfRemoteWorkspaceCacheEntry = (
    entry: CoreLfRemoteWorkspaceCacheEntryInput
): string => serializeCoreLfWorkspaceCanonicalJson(
    createCoreLfRemoteWorkspaceCacheEntry(entry),
    'remoteWorkspaceCacheEntry'
);
