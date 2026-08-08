/**
 * Node-owned integrity materializer for locked remote LF graph snapshots.
 *
 * The caller supplies text. This module computes hashes and reconstructs the
 * graph, but performs no fetch, path read/write, cache mutation, credential
 * lookup, subprocess, or Lambdapi execution.
 */

import { createHash } from 'node:crypto';
import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE,
    CoreLfCompiledFragmentModuleWorkspace,
    CoreLfFragmentModuleWorkspaceSnapshot,
    compileCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSnapshot,
    serializeCoreLfFragmentModuleWorkspaceSnapshot
} from './lf_fragment_module_workspace';
import {
    CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE,
    CoreLfRemoteWorkspaceCacheEntry,
    CoreLfRemoteWorkspaceCacheEntryInput,
    CoreLfRemoteWorkspaceError,
    CoreLfRemoteWorkspaceErrorCode,
    CoreLfRemoteWorkspaceLock,
    CoreLfRemoteWorkspaceLockInput,
    CoreLfRemoteWorkspaceSourceReconstruction,
    createCoreLfRemoteWorkspaceCacheEntry,
    createCoreLfRemoteWorkspaceLock,
    parseCoreLfFragmentModuleWorkspaceSourceText,
    serializeCoreLfRemoteWorkspaceArtifactIdentity
} from './lf_remote_workspace_contract';

export interface CoreLfMaterializedRemoteWorkspace {
    readonly revision: 'emdash-lf-materialized-remote-workspace-v1';
    readonly lock: CoreLfRemoteWorkspaceLock;
    readonly source:
        CoreLfRemoteWorkspaceSourceReconstruction;
    readonly compiled: CoreLfCompiledFragmentModuleWorkspace;
    readonly compiledSnapshot:
        CoreLfFragmentModuleWorkspaceSnapshot;
    readonly compiledText: string;
    readonly cacheEntry: CoreLfRemoteWorkspaceCacheEntry;
}

const fail = (
    code: CoreLfRemoteWorkspaceErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfRemoteWorkspaceError(code, path, message);
};

const sha256 = (source: string): string =>
    'sha256:' + createHash('sha256').update(source).digest('hex');

/** Verify supplied canonical source and its deterministic compiled snapshot. */
export function materializeCoreLfLockedRemoteWorkspace(
    lockInput: CoreLfRemoteWorkspaceLockInput,
    sourceText: string
): CoreLfMaterializedRemoteWorkspace {
    const lock = createCoreLfRemoteWorkspaceLock(lockInput);
    if (typeof sourceText !== 'string' || sourceText.length === 0) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceText',
            'Remote source text must be a nonempty string'
        );
    }
    const sourceUtf8Bytes = Buffer.byteLength(sourceText, 'utf8');
    if (sourceUtf8Bytes !== lock.artifact.sourceUtf8Bytes) {
        return fail(
            'SOURCE_BYTE_LENGTH_MISMATCH',
            'sourceText',
            `Remote source has ${sourceUtf8Bytes} UTF-8 bytes; lock ` +
                `requires ${lock.artifact.sourceUtf8Bytes}`
        );
    }
    if (sha256(sourceText) !== lock.artifact.sourceSha256) {
        return fail(
            'SOURCE_HASH_MISMATCH',
            'sourceText',
            'Remote source content differs from its locked SHA-256'
        );
    }
    const source = parseCoreLfFragmentModuleWorkspaceSourceText(sourceText);
    if (
        source.plan.revision !== lock.artifact.workspaceRevision ||
        source.sourceSnapshot.revision !==
            lock.artifact.sourceSnapshotRevision ||
        source.sourceSnapshot.profileRevision !==
            lock.artifact.sourceProfileRevision
    ) {
        return fail(
            'WORKSPACE_IDENTITY_MISMATCH',
            'lock.artifact',
            'Locked source profile or workspace revision differs from content'
        );
    }
    const compiled = compileCoreLfFragmentModuleWorkspace(source.plan);
    const compiledSnapshot =
        createCoreLfFragmentModuleWorkspaceSnapshot(compiled);
    if (
        compiledSnapshot.revision !==
            lock.artifact.compiledSnapshotRevision ||
        compiledSnapshot.profileRevision !==
            lock.artifact.compiledProfileRevision ||
        compiledSnapshot.revision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE
                .compiledSnapshotRevision
    ) {
        return fail(
            'WORKSPACE_IDENTITY_MISMATCH',
            'compiledSnapshot',
            'Compiled workspace targets a foreign snapshot profile'
        );
    }
    const compiledText = serializeCoreLfFragmentModuleWorkspaceSnapshot(
        compiledSnapshot
    );
    if (sha256(compiledText) !== lock.artifact.compiledSha256) {
        return fail(
            'COMPILED_HASH_MISMATCH',
            'compiledSnapshot',
            'Locally compiled snapshot differs from its locked SHA-256'
        );
    }
    const cacheEntry = createCoreLfRemoteWorkspaceCacheEntry({
        revision:
            CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.cacheEntryRevision,
        profileRevision: CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision,
        artifact: lock.artifact,
        sourceText: source.sourceText
    });
    return Object.freeze({
        revision: 'emdash-lf-materialized-remote-workspace-v1' as const,
        lock,
        source,
        compiled,
        compiledSnapshot,
        compiledText,
        cacheEntry
    });
}

/** Reverify immutable portable cache data and rebuild without transport. */
export function materializeCoreLfLockedRemoteWorkspaceFromCache(
    lockInput: CoreLfRemoteWorkspaceLockInput,
    cacheInput: CoreLfRemoteWorkspaceCacheEntryInput
): CoreLfMaterializedRemoteWorkspace {
    const lock = createCoreLfRemoteWorkspaceLock(lockInput);
    const cache = createCoreLfRemoteWorkspaceCacheEntry(cacheInput);
    if (
        serializeCoreLfRemoteWorkspaceArtifactIdentity(lock.artifact) !==
        serializeCoreLfRemoteWorkspaceArtifactIdentity(cache.artifact)
    ) {
        return fail(
            'CACHE_IDENTITY_MISMATCH',
            'cacheEntry.artifact',
            'Offline cache entry targets a different remote artifact'
        );
    }
    return materializeCoreLfLockedRemoteWorkspace(lock, cache.sourceText);
}
