/**
 * Node-owned mounted-file and immutable-cache adapter for remote LF graphs.
 *
 * The hosting platform owns transport, authentication, mounts, and snapshots.
 * This adapter reads two fixed project files, verifies them through the pure
 * TypeScript materializer, and installs one fully revalidated cache entry.
 */

import { createHash, randomUUID } from 'node:crypto';
import { constants } from 'node:fs';
import {
    link,
    lstat,
    mkdir,
    open,
    realpath,
    unlink
} from 'node:fs/promises';
import path from 'node:path';
import {
    CoreLfMaterializedRemoteWorkspace,
    materializeCoreLfLockedRemoteWorkspace,
    materializeCoreLfLockedRemoteWorkspaceFromCache
} from './lf_remote_workspace';
import {
    CoreLfRemoteWorkspaceArtifactIdentity,
    CoreLfRemoteWorkspaceCacheEntry,
    CoreLfRemoteWorkspaceLock,
    CoreLfRemoteWorkspaceLockInput,
    createCoreLfRemoteWorkspaceCacheEntry,
    createCoreLfRemoteWorkspaceLock,
    serializeCoreLfRemoteWorkspaceArtifactIdentity,
    serializeCoreLfRemoteWorkspaceCacheEntry,
    serializeCoreLfRemoteWorkspaceLock
} from './lf_remote_workspace_contract';

const KIB = 1024;
const MIB = 1024 * KIB;

export const CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE = Object.freeze({
    revision: 'emdash-lf-mounted-remote-workspace-store-v1' as const,
    filesystemProfile: 'node-posix-mounted-roots-v1' as const,
    backend: 'typescript-emdash-explicit-core' as const,
    lockFileName: 'emdash.workspace.lock.json' as const,
    sourceFileName: 'emdash.workspace.source.json' as const,
    cacheRelativeDirectory:
        '.emdash/cache/lf-remote-workspace-v1' as const,
    cacheKeyProfile:
        'sha256-canonical-remote-artifact-identity' as const,
    cacheFileProfile: 'artifact-<sha256-hex>.json' as const,
    installProfile:
        'fsynced-temporary-file-atomic-hard-link-no-replace' as const,
    maximumLockBytes: 256 * KIB,
    maximumSourceBytes: 64 * MIB,
    cacheMetadataAllowanceBytes: MIB,
    performsFetch: false as const,
    readsCredentials: false as const,
    readsEnvironment: false as const,
    readsCurrentWorkingDirectory: false as const,
    invokesGit: false as const,
    invokesLambdapi: false as const,
    mutatesExistingCacheEntries: false as const,
    evictsCacheEntries: false as const
});

export type CoreLfMountedRemoteWorkspaceStoreErrorCode =
    | 'INVALID_ROOTS'
    | 'UNSAFE_ROOT'
    | 'UNSAFE_FILE'
    | 'FILE_MISSING'
    | 'FILE_TOO_LARGE'
    | 'SOURCE_SIZE_MISMATCH'
    | 'INVALID_UTF8'
    | 'INVALID_LOCK_TEXT'
    | 'NONCANONICAL_LOCK_TEXT'
    | 'INVALID_CACHE_TEXT'
    | 'NONCANONICAL_CACHE_TEXT'
    | 'OFFLINE_CACHE_MISSING'
    | 'CACHE_CONFLICT'
    | 'CACHE_INSTALL_FAILED'
    | 'IO_FAILURE';

export class CoreLfMountedRemoteWorkspaceStoreError extends Error {
    public readonly cause: unknown;

    constructor(
        public readonly code:
            CoreLfMountedRemoteWorkspaceStoreErrorCode,
        public readonly path: string,
        message: string,
        cause?: unknown
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfMountedRemoteWorkspaceStoreError';
        this.cause = cause;
    }
}

export interface CoreLfMountedRemoteWorkspaceRoots {
    readonly projectRoot: string;
    readonly dataRoot: string;
}

export interface CoreLfMountedRemoteWorkspacePaths {
    readonly projectRoot: string;
    readonly dataRoot: string;
    readonly lockPath: string;
    readonly sourcePath: string;
    readonly cacheDirectory: string;
    readonly cachePath: string;
}

export type CoreLfMountedRemoteWorkspaceMode = 'source' | 'offline';
export type CoreLfMountedRemoteWorkspaceCacheDisposition =
    | 'installed'
    | 'verified-existing';

export interface CoreLfMountedRemoteWorkspaceResult {
    readonly revision:
        typeof CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.revision;
    readonly mode: CoreLfMountedRemoteWorkspaceMode;
    readonly cacheDisposition:
        CoreLfMountedRemoteWorkspaceCacheDisposition;
    readonly cacheKey: string;
    readonly paths: CoreLfMountedRemoteWorkspacePaths;
    readonly materialized: CoreLfMaterializedRemoteWorkspace;
}

interface ResolvedRoots {
    readonly projectRoot: string;
    readonly dataRoot: string;
    readonly lockPath: string;
    readonly sourcePath: string;
}

interface VerifiedCache {
    readonly text: string;
    readonly materialized: CoreLfMaterializedRemoteWorkspace;
}

const fail = (
    code: CoreLfMountedRemoteWorkspaceStoreErrorCode,
    targetPath: string,
    message: string,
    cause?: unknown
): never => {
    throw new CoreLfMountedRemoteWorkspaceStoreError(
        code,
        targetPath,
        message,
        cause
    );
};

const errnoCode = (error: unknown): string | undefined =>
    typeof error === 'object' &&
    error !== null &&
    'code' in error &&
    typeof (error as { code?: unknown }).code === 'string'
        ? (error as { code: string }).code
        : undefined;

const plainRecord = (value: unknown): value is Record<string, unknown> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        Array.isArray(value)
    ) return false;
    const prototype = Object.getPrototypeOf(value);
    return prototype === Object.prototype || prototype === null;
};

const sameKeys = (value: object, keys: readonly string[]): boolean =>
    JSON.stringify(Object.keys(value).sort()) ===
    JSON.stringify([...keys].sort());

const containsPath = (root: string, candidate: string): boolean => {
    const relative = path.relative(root, candidate);
    return relative === '' || (
        relative !== '..' &&
        !relative.startsWith(`..${path.sep}`) &&
        !path.isAbsolute(relative)
    );
};

const canonicalExistingRoot = async (
    input: string,
    label: 'projectRoot' | 'dataRoot'
): Promise<string> => {
    if (
        typeof input !== 'string' ||
        !path.isAbsolute(input) ||
        path.normalize(input) !== input
    ) {
        return fail(
            'INVALID_ROOTS',
            label,
            'Mounted workspace roots must be canonical absolute paths'
        );
    }
    let stat;
    try {
        stat = await lstat(input);
    } catch (error) {
        return fail(
            errnoCode(error) === 'ENOENT' ? 'INVALID_ROOTS' : 'IO_FAILURE',
            label,
            'Mounted workspace root is unavailable',
            error
        );
    }
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
        return fail(
            'UNSAFE_ROOT',
            label,
            'Mounted workspace root must be a real directory'
        );
    }
    let resolved: string;
    try {
        resolved = await realpath(input);
    } catch (error) {
        return fail(
            'IO_FAILURE',
            label,
            'Mounted workspace root cannot be resolved',
            error
        );
    }
    if (resolved !== input) {
        return fail(
            'UNSAFE_ROOT',
            label,
            'Mounted workspace root must not traverse symbolic-link parents'
        );
    }
    return resolved;
};

const resolveRoots = async (
    input: CoreLfMountedRemoteWorkspaceRoots
): Promise<ResolvedRoots> => {
    if (
        !plainRecord(input) ||
        !sameKeys(input, ['projectRoot', 'dataRoot']) ||
        typeof input.projectRoot !== 'string' ||
        typeof input.dataRoot !== 'string'
    ) {
        return fail(
            'INVALID_ROOTS',
            'roots',
            'Mounted workspace roots have missing or unsupported fields'
        );
    }
    const [projectRoot, dataRoot] = await Promise.all([
        canonicalExistingRoot(input.projectRoot, 'projectRoot'),
        canonicalExistingRoot(input.dataRoot, 'dataRoot')
    ]);
    if (
        containsPath(projectRoot, dataRoot) ||
        containsPath(dataRoot, projectRoot)
    ) {
        return fail(
            'INVALID_ROOTS',
            'roots',
            'Project and persistent-data roots must not overlap'
        );
    }
    return Object.freeze({
        projectRoot,
        dataRoot,
        lockPath: path.join(
            projectRoot,
            CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.lockFileName
        ),
        sourcePath: path.join(
            projectRoot,
            CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.sourceFileName
        )
    });
};

const decodeUtf8 = (bytes: Buffer, targetPath: string): string => {
    const text = bytes.toString('utf8');
    if (!Buffer.from(text, 'utf8').equals(bytes)) {
        return fail(
            'INVALID_UTF8',
            targetPath,
            'Mounted workspace file is not exact UTF-8'
        );
    }
    return text;
};

const readBoundedRegularFile = async (
    targetPath: string,
    maximumBytes: number,
    missingCode: CoreLfMountedRemoteWorkspaceStoreErrorCode
): Promise<Buffer> => {
    let handle;
    try {
        handle = await open(
            targetPath,
            constants.O_RDONLY |
                constants.O_NOFOLLOW |
                constants.O_NONBLOCK
        );
    } catch (error) {
        const code = errnoCode(error);
        if (code === 'ENOENT') {
            return fail(
                missingCode,
                targetPath,
                'Mounted workspace file is missing',
                error
            );
        }
        if (code === 'ELOOP') {
            return fail(
                'UNSAFE_FILE',
                targetPath,
                'Mounted workspace files must not be symbolic links',
                error
            );
        }
        return fail(
            'IO_FAILURE',
            targetPath,
            'Mounted workspace file cannot be opened',
            error
        );
    }
    try {
        const stat = await handle.stat();
        if (!stat.isFile()) {
            return fail(
                'UNSAFE_FILE',
                targetPath,
                'Mounted workspace path must be a regular file'
            );
        }
        if (stat.size > maximumBytes) {
            return fail(
                'FILE_TOO_LARGE',
                targetPath,
                `Mounted workspace file exceeds ${maximumBytes} bytes`
            );
        }
        const bytes = await handle.readFile();
        if (bytes.byteLength > maximumBytes) {
            return fail(
                'FILE_TOO_LARGE',
                targetPath,
                `Mounted workspace file exceeds ${maximumBytes} bytes`
            );
        }
        return bytes;
    } catch (error) {
        if (error instanceof CoreLfMountedRemoteWorkspaceStoreError) {
            throw error;
        }
        return fail(
            'IO_FAILURE',
            targetPath,
            'Mounted workspace file cannot be read',
            error
        );
    } finally {
        await handle.close().catch(() => undefined);
    }
};

const parseCanonicalLock = (
    text: string,
    targetPath: string
): CoreLfRemoteWorkspaceLock => {
    let value: unknown;
    try {
        value = JSON.parse(text);
    } catch (error) {
        return fail(
            'INVALID_LOCK_TEXT',
            targetPath,
            'Mounted workspace lock is not valid JSON',
            error
        );
    }
    const lock = createCoreLfRemoteWorkspaceLock(
        value as CoreLfRemoteWorkspaceLockInput
    );
    if (serializeCoreLfRemoteWorkspaceLock(lock) !== text) {
        return fail(
            'NONCANONICAL_LOCK_TEXT',
            targetPath,
            'Mounted workspace lock must be exact canonical serializer output'
        );
    }
    return lock;
};

const parseCanonicalCacheEntry = (
    text: string,
    targetPath: string
): CoreLfRemoteWorkspaceCacheEntry => {
    let value: unknown;
    try {
        value = JSON.parse(text);
    } catch (error) {
        return fail(
            'INVALID_CACHE_TEXT',
            targetPath,
            'Mounted workspace cache entry is not valid JSON',
            error
        );
    }
    const cache = createCoreLfRemoteWorkspaceCacheEntry(
        value as CoreLfRemoteWorkspaceCacheEntry
    );
    if (serializeCoreLfRemoteWorkspaceCacheEntry(cache) !== text) {
        return fail(
            'NONCANONICAL_CACHE_TEXT',
            targetPath,
            'Mounted workspace cache must be exact canonical serializer output'
        );
    }
    return cache;
};

const sha256Hex = (text: string): string =>
    createHash('sha256').update(text, 'utf8').digest('hex');

/** Derive the store key solely from exact canonical artifact identity. */
export function createCoreLfMountedRemoteWorkspaceCacheKey(
    artifact: CoreLfRemoteWorkspaceArtifactIdentity
): string {
    return sha256Hex(
        serializeCoreLfRemoteWorkspaceArtifactIdentity(artifact)
    );
}

const cacheMaximumBytes = (
    lock: CoreLfRemoteWorkspaceLock
): number =>
    (2 * lock.artifact.sourceUtf8Bytes) +
    CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE
        .cacheMetadataAllowanceBytes;

const inspectFixedDirectory = async (
    targetPath: string,
    missingCode: CoreLfMountedRemoteWorkspaceStoreErrorCode
): Promise<string> => {
    let stat;
    try {
        stat = await lstat(targetPath);
    } catch (error) {
        return fail(
            errnoCode(error) === 'ENOENT' ? missingCode : 'IO_FAILURE',
            targetPath,
            'Cache directory is unavailable',
            error
        );
    }
    if (stat.isSymbolicLink() || !stat.isDirectory()) {
        return fail(
            'UNSAFE_FILE',
            targetPath,
            'Cache path component must be a real directory'
        );
    }
    const resolved = await realpath(targetPath).catch(error => fail(
        'IO_FAILURE',
        targetPath,
        'Cache directory cannot be resolved',
        error
    ));
    if (resolved !== targetPath) {
        return fail(
            'UNSAFE_FILE',
            targetPath,
            'Cache directory must not traverse symbolic-link parents'
        );
    }
    return resolved;
};

const ensureFixedDirectory = async (
    parent: string,
    name: string
): Promise<string> => {
    const target = path.join(parent, name);
    try {
        await mkdir(target, { mode: 0o700 });
    } catch (error) {
        if (errnoCode(error) !== 'EEXIST') {
            return fail(
                'IO_FAILURE',
                target,
                'Cache directory cannot be created',
                error
            );
        }
    }
    return inspectFixedDirectory(target, 'IO_FAILURE');
};

const resolveCacheDirectory = async (
    dataRoot: string,
    create: boolean
): Promise<string> => {
    const components = CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE
        .cacheRelativeDirectory.split('/');
    let current = dataRoot;
    for (const component of components) {
        const target = path.join(current, component);
        current = create
            ? await ensureFixedDirectory(current, component)
            : await inspectFixedDirectory(
                target,
                'OFFLINE_CACHE_MISSING'
            );
    }
    if (!containsPath(dataRoot, current)) {
        return fail(
            'UNSAFE_FILE',
            current,
            'Derived cache directory escaped the persistent-data root'
        );
    }
    return current;
};

const readLock = async (
    roots: ResolvedRoots
): Promise<CoreLfRemoteWorkspaceLock> => {
    const bytes = await readBoundedRegularFile(
        roots.lockPath,
        CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.maximumLockBytes,
        'FILE_MISSING'
    );
    return parseCanonicalLock(decodeUtf8(bytes, roots.lockPath), roots.lockPath);
};

const readVerifiedCache = async (
    lock: CoreLfRemoteWorkspaceLock,
    cachePath: string
): Promise<VerifiedCache> => {
    const bytes = await readBoundedRegularFile(
        cachePath,
        cacheMaximumBytes(lock),
        'OFFLINE_CACHE_MISSING'
    );
    const text = decodeUtf8(bytes, cachePath);
    const entry = parseCanonicalCacheEntry(text, cachePath);
    const materialized = materializeCoreLfLockedRemoteWorkspaceFromCache(
        lock,
        entry
    );
    return Object.freeze({ text, materialized });
};

const syncDirectoryWhereSupported = async (
    directory: string
): Promise<void> => {
    let handle;
    try {
        handle = await open(directory, constants.O_RDONLY);
        await handle.sync();
    } catch (error) {
        if (!['EINVAL', 'ENOTSUP', 'EBADF', 'EISDIR'].includes(
            errnoCode(error) ?? ''
        )) {
            return fail(
                'CACHE_INSTALL_FAILED',
                directory,
                'Cache directory could not be synchronized',
                error
            );
        }
    } finally {
        await handle?.close().catch(() => undefined);
    }
};

const installOrVerifyCache = async (
    lock: CoreLfRemoteWorkspaceLock,
    cacheDirectory: string,
    cachePath: string,
    expectedText: string
): Promise<CoreLfMountedRemoteWorkspaceCacheDisposition> => {
    try {
        const existing = await readVerifiedCache(lock, cachePath);
        if (existing.text !== expectedText) {
            return fail(
                'CACHE_CONFLICT',
                cachePath,
                'Existing immutable cache bytes differ from verified source'
            );
        }
        return 'verified-existing';
    } catch (error) {
        if (
            !(error instanceof CoreLfMountedRemoteWorkspaceStoreError) ||
            error.code !== 'OFFLINE_CACHE_MISSING'
        ) {
            return fail(
                'CACHE_CONFLICT',
                cachePath,
                'Existing immutable cache entry failed full verification',
                error
            );
        }
    }

    const temporaryPath = path.join(
        cacheDirectory,
        `.artifact-${process.pid}-${randomUUID()}.tmp`
    );
    let handle;
    try {
        handle = await open(
            temporaryPath,
            constants.O_WRONLY |
                constants.O_CREAT |
                constants.O_EXCL |
                constants.O_NOFOLLOW,
            0o600
        );
        await handle.writeFile(expectedText, 'utf8');
        await handle.sync();
        await handle.close();
        handle = undefined;

        try {
            await link(temporaryPath, cachePath);
        } catch (error) {
            if (errnoCode(error) !== 'EEXIST') {
                return fail(
                    'CACHE_INSTALL_FAILED',
                    cachePath,
                    'Immutable cache entry could not be installed atomically',
                    error
                );
            }
            const existing = await readVerifiedCache(lock, cachePath).catch(
                verifyError => fail(
                    'CACHE_CONFLICT',
                    cachePath,
                    'Concurrent cache entry failed full verification',
                    verifyError
                )
            );
            if (existing.text !== expectedText) {
                return fail(
                    'CACHE_CONFLICT',
                    cachePath,
                    'Concurrent immutable cache bytes differ from source'
                );
            }
            return 'verified-existing';
        }
        await syncDirectoryWhereSupported(cacheDirectory);
        return 'installed';
    } catch (error) {
        if (error instanceof CoreLfMountedRemoteWorkspaceStoreError) {
            throw error;
        }
        return fail(
            'CACHE_INSTALL_FAILED',
            cachePath,
            'Immutable cache entry installation failed',
            error
        );
    } finally {
        await handle?.close().catch(() => undefined);
        await unlink(temporaryPath).catch(() => undefined);
    }
};

const makePaths = (
    roots: ResolvedRoots,
    cacheDirectory: string,
    cachePath: string
): CoreLfMountedRemoteWorkspacePaths => Object.freeze({
    projectRoot: roots.projectRoot,
    dataRoot: roots.dataRoot,
    lockPath: roots.lockPath,
    sourcePath: roots.sourcePath,
    cacheDirectory,
    cachePath
});

const makeResult = (
    mode: CoreLfMountedRemoteWorkspaceMode,
    cacheDisposition: CoreLfMountedRemoteWorkspaceCacheDisposition,
    cacheKey: string,
    paths: CoreLfMountedRemoteWorkspacePaths,
    materialized: CoreLfMaterializedRemoteWorkspace
): CoreLfMountedRemoteWorkspaceResult => Object.freeze({
    revision: CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.revision,
    mode,
    cacheDisposition,
    cacheKey,
    paths,
    materialized
});

/** Verify mounted project source and install/reuse its immutable cache. */
export async function materializeCoreLfMountedRemoteWorkspace(
    input: CoreLfMountedRemoteWorkspaceRoots
): Promise<CoreLfMountedRemoteWorkspaceResult> {
    const roots = await resolveRoots(input);
    const lock = await readLock(roots);
    if (
        lock.artifact.sourceUtf8Bytes >
            CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.maximumSourceBytes
    ) {
        return fail(
            'FILE_TOO_LARGE',
            roots.sourcePath,
            'Locked source exceeds the mounted-workspace profile bound'
        );
    }
    const sourceBytes = await readBoundedRegularFile(
        roots.sourcePath,
        CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.maximumSourceBytes,
        'FILE_MISSING'
    );
    if (sourceBytes.byteLength !== lock.artifact.sourceUtf8Bytes) {
        return fail(
            'SOURCE_SIZE_MISMATCH',
            roots.sourcePath,
            'Mounted source byte length differs from its lock'
        );
    }
    const sourceText = decodeUtf8(sourceBytes, roots.sourcePath);
    const materialized = materializeCoreLfLockedRemoteWorkspace(
        lock,
        sourceText
    );
    const cacheText = serializeCoreLfRemoteWorkspaceCacheEntry(
        materialized.cacheEntry
    );
    const cacheKey = createCoreLfMountedRemoteWorkspaceCacheKey(
        lock.artifact
    );
    const cacheDirectory = await resolveCacheDirectory(
        roots.dataRoot,
        true
    );
    const cachePath = path.join(
        cacheDirectory,
        `artifact-${cacheKey}.json`
    );
    const cacheDisposition = await installOrVerifyCache(
        lock,
        cacheDirectory,
        cachePath,
        cacheText
    );
    return makeResult(
        'source',
        cacheDisposition,
        cacheKey,
        makePaths(roots, cacheDirectory, cachePath),
        materialized
    );
}

/** Reverify a derived immutable cache entry without reading project source. */
export async function materializeCoreLfMountedRemoteWorkspaceOffline(
    input: CoreLfMountedRemoteWorkspaceRoots
): Promise<CoreLfMountedRemoteWorkspaceResult> {
    const roots = await resolveRoots(input);
    const lock = await readLock(roots);
    if (
        lock.artifact.sourceUtf8Bytes >
            CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.maximumSourceBytes
    ) {
        return fail(
            'FILE_TOO_LARGE',
            roots.sourcePath,
            'Locked source exceeds the mounted-workspace profile bound'
        );
    }
    const cacheKey = createCoreLfMountedRemoteWorkspaceCacheKey(
        lock.artifact
    );
    const cacheDirectory = await resolveCacheDirectory(
        roots.dataRoot,
        false
    );
    const cachePath = path.join(
        cacheDirectory,
        `artifact-${cacheKey}.json`
    );
    const verified = await readVerifiedCache(lock, cachePath);
    return makeResult(
        'offline',
        'verified-existing',
        cacheKey,
        makePaths(roots, cacheDirectory, cachePath),
        verified.materialized
    );
}
