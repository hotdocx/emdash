/** Focused AI-REMOTE-1A/1B1 lock, reconstruction, and mounted-store tests. */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import {
    mkdir,
    mkdtemp,
    readFile,
    readdir,
    rm,
    stat,
    symlink,
    unlink,
    writeFile
} from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE,
    CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE,
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfRemoteWorkspaceArtifactIdentity,
    CoreLfRemoteWorkspaceError,
    CoreLfRemoteWorkspaceErrorCode,
    CoreLfRemoteWorkspaceLockInput,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    compileCoreLfFragmentModuleWorkspace,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfDependencyModuleFragmentChain,
    createCoreLfFragmentModuleIdentity,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSnapshot,
    createCoreLfFragmentModuleWorkspaceSourceSnapshot,
    createCoreLfModuleSpec,
    createCoreLfRemoteWorkspaceLock,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    defineCoreLfDependencyModuleDeclarationFragment,
    materializeCoreLfLockedRemoteWorkspace,
    materializeCoreLfLockedRemoteWorkspaceFromCache,
    serializeCoreLfFragmentModuleWorkspaceSnapshot,
    serializeCoreLfFragmentModuleWorkspaceSourceSnapshot,
    serializeCoreLfRemoteWorkspaceArtifactIdentity,
    serializeCoreLfRemoteWorkspaceCacheEntry,
    serializeCoreLfRemoteWorkspaceLock,
    serializeCoreLfWorkspaceCanonicalJson
} from '../src/v3_2';
import {
    CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE,
    CoreLfMountedRemoteWorkspaceRoots,
    CoreLfMountedRemoteWorkspaceStoreError,
    CoreLfMountedRemoteWorkspaceStoreErrorCode,
    createCoreLfMountedRemoteWorkspaceCacheKey,
    materializeCoreLfMountedRemoteWorkspace,
    materializeCoreLfMountedRemoteWorkspaceOffline
} from '../src/v3_2/lf_remote_workspace_store';

const providerId = 'fixture.remote_provider';
const consumerId = 'fixture.remote_consumer';
const providerAuthority = 'tests/fixtures/remote_provider.lp';
const consumerAuthority = 'tests/fixtures/remote_consumer.lp';
const defaultProviderSourceSha = `sha256:${'a'.repeat(64)}`;
const consumerSourceSha = `sha256:${'b'.repeat(64)}`;
const carrier = coreLfQualifiedSymbol(providerId, 'Carrier');
const token = coreLfQualifiedSymbol(consumerId, 'token');

const sha256 = (value: string): string =>
    `sha256:${createHash('sha256').update(value).digest('hex')}`;

const source = (authorityPath: string, sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const modifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const global = (
    symbol: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({ tag: 'global', symbol });

const declaration = (
    order: number,
    symbol: CoreLfQualifiedSymbol,
    type: CoreLfTransferExpression,
    authorityPath: string
) => ({
    order,
    symbol,
    type,
    body: coreLfTransferAbsentBody(),
    modifiers,
    provenance: source(authorityPath, `symbol ${symbol.name};`)
});

const policyFor = (
    module: CoreLfModuleSpec,
    revision: string
): CoreLfTransferPolicyOverlay => createCoreLfTransferPolicyOverlay(module, {
    revision,
    moduleRevision: module.revision,
    entries: module.declarations.map((entry, order) => ({
        order,
        target: {
            kind: 'declaration' as const,
            symbol: entry.symbol
        },
        policy: 'opaque-signature' as const,
        evidence: 'remote workspace integrity fixture'
    }))
});

const linkageFor = (
    module: CoreLfModuleSpec,
    revision: string,
    symbols: readonly CoreLfQualifiedSymbol[]
) => createCoreLfTransferDeclarationLinkage(module, {
    revision,
    moduleRevision: module.revision,
    entries: symbols.map((symbol, order) => ({
        order,
        symbol,
        kind: 'free-declaration' as const,
        coreName: `${symbol.moduleId.replace(/\./gu, '_')}_${symbol.name}`,
        backendName: symbol.name
    }))
});

interface RemoteFixtureOptions {
    readonly providerSourceSha?: string;
}

const graphFixture = (options: RemoteFixtureOptions = {}) => {
    const providerModule = createCoreLfModuleSpec({
        revision: 'remote-provider-module-1',
        moduleId: providerId,
        fragmentId: 'provider-declarations',
        authorityPath: providerAuthority,
        sourceSha256:
            options.providerSourceSha ?? defaultProviderSourceSha,
        dependencies: [],
        externalSymbols: [],
        declarations: [declaration(
            0,
            carrier,
            { tag: 'type' },
            providerAuthority
        )],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const provider = defineCoreLfDependencyModuleDeclarationFragment({
        module: providerModule,
        policy: policyFor(providerModule, 'remote-provider-policy-1'),
        linkage: linkageFor(
            providerModule,
            'remote-provider-linkage-1',
            [carrier]
        )
    });
    const providerChain = createCoreLfDependencyModuleFragmentChain({
        revision: 'remote-provider-chain-1',
        fragments: [provider]
    });

    const consumerModule = createCoreLfModuleSpec({
        revision: 'remote-consumer-module-1',
        moduleId: consumerId,
        fragmentId: 'consumer-declarations',
        authorityPath: consumerAuthority,
        sourceSha256: consumerSourceSha,
        dependencies: [providerId],
        externalSymbols: [{
            symbol: carrier,
            availability: 'dependency-module'
        }],
        declarations: [declaration(
            0,
            token,
            global(carrier),
            consumerAuthority
        )],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const consumer = defineCoreLfDependencyModuleDeclarationFragment({
        module: consumerModule,
        policy: policyFor(consumerModule, 'remote-consumer-policy-1'),
        linkage: linkageFor(
            consumerModule,
            'remote-consumer-linkage-1',
            [carrier, token]
        )
    });
    const consumerChain = createCoreLfDependencyModuleFragmentChain({
        revision: 'remote-consumer-chain-1',
        fragments: [consumer]
    });
    const plan = createCoreLfFragmentModuleWorkspace({
        revision: 'remote-workspace-fixture-1',
        modules: [{
            chain: consumerChain,
            dependencyProviders: [
                createCoreLfFragmentModuleIdentity(providerChain)
            ]
        }, { chain: providerChain }]
    });
    const sourceSnapshot =
        createCoreLfFragmentModuleWorkspaceSourceSnapshot(plan);
    const sourceText =
        serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(sourceSnapshot);
    const compiled = compileCoreLfFragmentModuleWorkspace(plan);
    const compiledSnapshot =
        createCoreLfFragmentModuleWorkspaceSnapshot(compiled);
    const compiledText =
        serializeCoreLfFragmentModuleWorkspaceSnapshot(compiledSnapshot);
    return {
        plan,
        sourceSnapshot,
        sourceText,
        compiledSnapshot,
        compiledText
    };
};

const artifactFor = (
    fixture: ReturnType<typeof graphFixture>,
    overrides: Partial<CoreLfRemoteWorkspaceArtifactIdentity> = {}
): CoreLfRemoteWorkspaceArtifactIdentity => ({
    logicalWorkspaceId: 'emdash://fixture/remote-workspace',
    workspaceRevision: fixture.plan.revision,
    sourceSnapshotRevision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.sourceSnapshotRevision,
    sourceProfileRevision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
    sourceUtf8Bytes: Buffer.byteLength(fixture.sourceText, 'utf8'),
    sourceSha256: sha256(fixture.sourceText),
    compiledSnapshotRevision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.compiledSnapshotRevision,
    compiledProfileRevision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
    compiledSha256: sha256(fixture.compiledText),
    ...overrides
});

const lockFor = (
    fixture: ReturnType<typeof graphFixture>,
    mirrors: CoreLfRemoteWorkspaceLockInput['mirrors'] = [{
        kind: 'https',
        uri: 'https://cdn.example.test/emdash/remote-workspace.json'
    }],
    artifactOverrides: Partial<CoreLfRemoteWorkspaceArtifactIdentity> = {}
): CoreLfRemoteWorkspaceLockInput => ({
    revision: 'remote-workspace-lock-1',
    profileRevision: CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision,
    artifact: artifactFor(fixture, artifactOverrides),
    mirrors
});

const expectRemoteError = (
    action: () => unknown,
    code: CoreLfRemoteWorkspaceErrorCode
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfRemoteWorkspaceError &&
            error.code === code &&
            error.path.length > 0
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

interface MountedFixture {
    readonly root: string;
    readonly roots: CoreLfMountedRemoteWorkspaceRoots;
    readonly fixture: ReturnType<typeof graphFixture>;
    readonly lock: CoreLfRemoteWorkspaceLockInput;
    readonly lockPath: string;
    readonly sourcePath: string;
}

const createMountedFixture = async (): Promise<MountedFixture> => {
    const root = await mkdtemp(path.join(
        tmpdir(),
        'emdash-remote-workspace-store-'
    ));
    const projectRoot = path.join(root, 'project');
    const dataRoot = path.join(root, 'data');
    await Promise.all([
        mkdir(projectRoot, { mode: 0o700 }),
        mkdir(dataRoot, { mode: 0o700 })
    ]);
    const fixture = graphFixture();
    const lock = lockFor(fixture);
    const lockPath = path.join(
        projectRoot,
        CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.lockFileName
    );
    const sourcePath = path.join(
        projectRoot,
        CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.sourceFileName
    );
    await Promise.all([
        writeFile(lockPath, serializeCoreLfRemoteWorkspaceLock(lock)),
        writeFile(sourcePath, fixture.sourceText)
    ]);
    return {
        root,
        roots: { projectRoot, dataRoot },
        fixture,
        lock,
        lockPath,
        sourcePath
    };
};

const withMountedFixture = async <T>(
    action: (mounted: MountedFixture) => Promise<T>
): Promise<T> => {
    const mounted = await createMountedFixture();
    try {
        return await action(mounted);
    } finally {
        await rm(mounted.root, { recursive: true, force: true });
    }
};

const expectStoreError = async (
    action: () => Promise<unknown>,
    code: CoreLfMountedRemoteWorkspaceStoreErrorCode
): Promise<CoreLfMountedRemoteWorkspaceStoreError> => {
    let observed: unknown;
    await assert.rejects(action, error => {
        observed = error;
        return error instanceof CoreLfMountedRemoteWorkspaceStoreError &&
            error.code === code &&
            error.path.length > 0;
    });
    return observed as CoreLfMountedRemoteWorkspaceStoreError;
};

describe('AI-REMOTE-1A immutable lock and offline reconstruction', () => {
    it('materializes exact source and compiled snapshots into portable cache', () => {
        const fixture = graphFixture();
        const lock = lockFor(fixture);
        const materialized = materializeCoreLfLockedRemoteWorkspace(
            lock,
            fixture.sourceText
        );

        assert.equal(materialized.source.sourceText, fixture.sourceText);
        assert.equal(materialized.compiledText, fixture.compiledText);
        assert.deepEqual(
            materialized.source.sourceSnapshot,
            fixture.sourceSnapshot
        );
        assert.deepEqual(
            materialized.compiledSnapshot,
            fixture.compiledSnapshot
        );
        assert.equal(
            materialized.compiled.module(consumerId)?.compiled
                .declarations.declaration(token) !== undefined,
            true
        );
        assert.equal(
            materialized.cacheEntry.sourceText,
            fixture.sourceText
        );
        assert.equal(
            serializeCoreLfRemoteWorkspaceCacheEntry(
                materialized.cacheEntry
            ).endsWith('\n'),
            true
        );
        assertDeepFrozen(materialized.lock);
        assertDeepFrozen(materialized.cacheEntry);
        assert.equal(Object.isFrozen(materialized), true);
    });

    it('rebuilds offline after mirror changes because locations are not identity', () => {
        const fixture = graphFixture();
        const first = materializeCoreLfLockedRemoteWorkspace(
            lockFor(fixture),
            fixture.sourceText
        );
        const relocated = lockFor(fixture, [{
            kind: 'https',
            uri: 'https://mirror.example.test/research/graph.json'
        }]);
        const offline = materializeCoreLfLockedRemoteWorkspaceFromCache(
            relocated,
            first.cacheEntry
        );

        assert.equal(offline.source.sourceText, fixture.sourceText);
        assert.equal(offline.compiledText, fixture.compiledText);
        assert.deepEqual(offline.lock.mirrors, relocated.mirrors);
        assert.equal(
            serializeCoreLfRemoteWorkspaceArtifactIdentity(
                first.lock.artifact
            ),
            serializeCoreLfRemoteWorkspaceArtifactIdentity(
                offline.lock.artifact
            )
        );
        assert.notEqual(
            serializeCoreLfRemoteWorkspaceLock(first.lock),
            serializeCoreLfRemoteWorkspaceLock(offline.lock)
        );
    });

    it('rejects byte-length and same-length source drift before reconstruction', () => {
        const fixture = graphFixture();
        const lock = lockFor(fixture);
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(
                lock,
                fixture.sourceText + ' '
            ),
            'SOURCE_BYTE_LENGTH_MISMATCH'
        );
        const sameLengthDrift = fixture.sourceText.replace(
            'remote-provider-module-1',
            'remote-provider-module-2'
        );
        assert.equal(
            Buffer.byteLength(sameLengthDrift, 'utf8'),
            lock.artifact.sourceUtf8Bytes
        );
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(
                lock,
                sameLengthDrift
            ),
            'SOURCE_HASH_MISMATCH'
        );
    });

    it('rejects noncanonical or fabricated JSON even under recomputed hashes', () => {
        const fixture = graphFixture();
        const pretty = `${JSON.stringify(
            JSON.parse(fixture.sourceText),
            null,
            2
        )}\n`;
        const prettyLock = lockFor(fixture, [], {
            sourceUtf8Bytes: Buffer.byteLength(pretty, 'utf8'),
            sourceSha256: sha256(pretty)
        });
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(prettyLock, pretty),
            'NONCANONICAL_SOURCE_SNAPSHOT'
        );

        const fabricatedValue = JSON.parse(fixture.sourceText) as
            Record<string, unknown>;
        fabricatedValue.unreviewedCompilerCallback = 'accept-all';
        const fabricated = serializeCoreLfWorkspaceCanonicalJson(
            fabricatedValue
        );
        const fabricatedLock = lockFor(fixture, [], {
            sourceUtf8Bytes: Buffer.byteLength(fabricated, 'utf8'),
            sourceSha256: sha256(fabricated)
        });
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(
                fabricatedLock,
                fabricated
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );
    });

    it('checks workspace/profile pins and deterministic compiled identity', () => {
        const fixture = graphFixture();
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(
                lockFor(fixture, [], {
                    workspaceRevision: 'remote-workspace-fixture-2'
                }),
                fixture.sourceText
            ),
            'WORKSPACE_IDENTITY_MISMATCH'
        );
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock({
                ...lockFor(fixture),
                artifact: {
                    ...artifactFor(fixture),
                    sourceProfileRevision: 'foreign-source-profile'
                }
            } as unknown as CoreLfRemoteWorkspaceLockInput),
            'INVALID_ARTIFACT_IDENTITY'
        );
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(
                lockFor(fixture, [], {
                    compiledSha256: `sha256:${'f'.repeat(64)}`
                }),
                fixture.sourceText
            ),
            'COMPILED_HASH_MISMATCH'
        );
    });

    it('revalidates poisoned cache identity and content on every offline use', () => {
        const fixture = graphFixture();
        const lock = lockFor(fixture);
        const materialized = materializeCoreLfLockedRemoteWorkspace(
            lock,
            fixture.sourceText
        );
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspaceFromCache(
                lock,
                {
                    ...materialized.cacheEntry,
                    artifact: {
                        ...materialized.cacheEntry.artifact,
                        compiledSha256: `sha256:${'e'.repeat(64)}`
                    }
                }
            ),
            'CACHE_IDENTITY_MISMATCH'
        );

        const alternate = graphFixture({
            providerSourceSha: `sha256:${'c'.repeat(64)}`
        });
        assert.equal(alternate.plan.revision, fixture.plan.revision);
        assert.equal(
            Buffer.byteLength(alternate.sourceText, 'utf8'),
            Buffer.byteLength(fixture.sourceText, 'utf8')
        );
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspaceFromCache(
                lock,
                {
                    ...materialized.cacheEntry,
                    sourceText: alternate.sourceText
                }
            ),
            'SOURCE_HASH_MISMATCH'
        );
    });

    it('accepts zero mirrors but rejects duplicate or unsafe persisted URLs', () => {
        const fixture = graphFixture();
        assert.deepEqual(
            createCoreLfRemoteWorkspaceLock(lockFor(fixture, [])).mirrors,
            []
        );
        const invalidUris = [
            'http://example.test/graph.json',
            'https://user@example.test/graph.json',
            'https://example.test/graph.json?token=secret',
            'https://example.test/graph.json#fragment',
            'https://example.test/a/../graph.json'
        ];
        invalidUris.forEach(uri => expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock(lockFor(fixture, [{
                kind: 'https',
                uri
            }])),
            'INVALID_MIRROR'
        ));
        const mirror = {
            kind: 'https' as const,
            uri: 'https://example.test/graph.json'
        };
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock(
                lockFor(fixture, [mirror, mirror])
            ),
            'INVALID_MIRROR'
        );
    });

    it('rejects coercible primitive fields, class records, and extra state', () => {
        const fixture = graphFixture();
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock({
                ...lockFor(fixture),
                revision: 7
            } as unknown as CoreLfRemoteWorkspaceLockInput),
            'INVALID_LOCK'
        );
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock({
                ...lockFor(fixture),
                artifact: {
                    ...artifactFor(fixture),
                    logicalWorkspaceId: 7
                }
            } as unknown as CoreLfRemoteWorkspaceLockInput),
            'INVALID_ARTIFACT_IDENTITY'
        );
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock({
                ...lockFor(fixture),
                mirrors: [{ kind: 'https', uri: 7 }]
            } as unknown as CoreLfRemoteWorkspaceLockInput),
            'INVALID_MIRROR'
        );
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock({
                ...lockFor(fixture),
                ambientWorkingDirectory: '/tmp/unreviewed'
            } as unknown as CoreLfRemoteWorkspaceLockInput),
            'INVALID_LOCK'
        );
        class LockRecord {
            readonly revision = 'remote-workspace-lock-1';
            readonly profileRevision =
                CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE.revision;
            readonly artifact = artifactFor(fixture);
            readonly mirrors = [];
        }
        expectRemoteError(
            () => createCoreLfRemoteWorkspaceLock(
                new LockRecord() as CoreLfRemoteWorkspaceLockInput
            ),
            'INVALID_LOCK'
        );
        expectRemoteError(
            () => materializeCoreLfLockedRemoteWorkspace(
                lockFor(fixture),
                7 as unknown as string
            ),
            'INVALID_SOURCE_SNAPSHOT'
        );
    });

    it('publishes an explicit portable boundary with no ambient state claims', () => {
        const fixture = graphFixture();
        const lock = createCoreLfRemoteWorkspaceLock(lockFor(fixture));
        const text = serializeCoreLfRemoteWorkspaceLock(lock);

        assert.deepEqual(CORE_LF_REMOTE_WORKSPACE_LOCK_PROFILE, {
            revision: 'emdash-lf-remote-workspace-lock-v1',
            cacheEntryRevision:
                'emdash-lf-remote-workspace-cache-entry-v1',
            sourceArtifact:
                'canonical-fragment-module-workspace-source-snapshot',
            identityProfile:
                'logical-workspace-source-bytes-source-and-compiled-digests',
            mirrorProfile: 'non-authoritative-canonical-https',
            cacheProfile: 'immutable-source-text-reverify-on-every-use',
            computesCryptographicHashes: false,
            performsTransport: false,
            ownsPersistentStorage: false,
            nodeBuiltinDependency: false
        });
        assert.equal(text.endsWith('\n'), true);
        assert.deepEqual(JSON.parse(text), lock);
        assert.doesNotMatch(text, /credential|authorization|cookie|\/home\//iu);
        assert.equal('path' in lock, false);
        assert.equal('cacheKey' in lock, false);
        assert.equal('environment' in lock, false);
        assertDeepFrozen(lock);
    });
});

describe('AI-REMOTE-1B1 TypeScript mounted workspace store', () => {
    it('installs canonical cache and rebuilds offline without project source', async () => {
        await withMountedFixture(async mounted => {
            const online = await materializeCoreLfMountedRemoteWorkspace(
                mounted.roots
            );
            assert.equal(online.mode, 'source');
            assert.equal(online.cacheDisposition, 'installed');
            assert.equal(
                online.cacheKey,
                createCoreLfMountedRemoteWorkspaceCacheKey(
                    mounted.lock.artifact
                )
            );
            assert.equal(
                online.paths.cachePath.startsWith(
                    `${mounted.roots.dataRoot}${path.sep}`
                ),
                true
            );
            assert.equal(
                await readFile(online.paths.cachePath, 'utf8'),
                serializeCoreLfRemoteWorkspaceCacheEntry(
                    online.materialized.cacheEntry
                )
            );

            await unlink(mounted.sourcePath);
            await writeFile(
                mounted.lockPath,
                serializeCoreLfRemoteWorkspaceLock({
                    ...mounted.lock,
                    mirrors: [{
                        kind: 'https',
                        uri: 'https://mirror.example.test/graph.json'
                    }]
                })
            );
            const offline =
                await materializeCoreLfMountedRemoteWorkspaceOffline(
                    mounted.roots
                );
            assert.equal(offline.mode, 'offline');
            assert.equal(offline.cacheDisposition, 'verified-existing');
            assert.equal(offline.cacheKey, online.cacheKey);
            assert.equal(
                offline.materialized.compiledText,
                online.materialized.compiledText
            );
            assert.equal(
                offline.materialized.source.sourceText,
                mounted.fixture.sourceText
            );
            assert.equal(Object.isFrozen(offline), true);
            assert.equal(Object.isFrozen(offline.paths), true);
        });
    });

    it('reuses exact bytes and never overwrites a poisoned cache entry', async () => {
        await withMountedFixture(async mounted => {
            const first = await materializeCoreLfMountedRemoteWorkspace(
                mounted.roots
            );
            const before = await stat(first.paths.cachePath);
            const second = await materializeCoreLfMountedRemoteWorkspace(
                mounted.roots
            );
            const after = await stat(first.paths.cachePath);
            assert.equal(second.cacheDisposition, 'verified-existing');
            assert.equal(after.ino, before.ino);
            assert.equal(after.mtimeMs, before.mtimeMs);

            const poisoned = '{"poisoned":true}\n';
            await writeFile(first.paths.cachePath, poisoned);
            const error = await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace(mounted.roots),
                'CACHE_CONFLICT'
            );
            assert.ok(error.cause);
            assert.equal(
                await readFile(first.paths.cachePath, 'utf8'),
                poisoned
            );
        });
    });

    it('converges concurrent identical population without temporary debris', async () => {
        await withMountedFixture(async mounted => {
            const results = await Promise.all([
                materializeCoreLfMountedRemoteWorkspace(mounted.roots),
                materializeCoreLfMountedRemoteWorkspace(mounted.roots)
            ]);
            assert.deepEqual(
                results.map(result => result.cacheDisposition).sort(),
                ['installed', 'verified-existing']
            );
            assert.equal(results[0].cacheKey, results[1].cacheKey);
            assert.equal(
                results[0].materialized.compiledText,
                results[1].materialized.compiledText
            );
            assert.deepEqual(
                await readdir(results[0].paths.cacheDirectory),
                [`artifact-${results[0].cacheKey}.json`]
            );
        });
    });

    it('rejects noncanonical lock text and fixed-file symbolic links', async () => {
        await withMountedFixture(async mounted => {
            const prettyLock = `${JSON.stringify(
                JSON.parse(serializeCoreLfRemoteWorkspaceLock(mounted.lock)),
                null,
                4
            )}\n`;
            await writeFile(mounted.lockPath, prettyLock);
            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace(mounted.roots),
                'NONCANONICAL_LOCK_TEXT'
            );

            await writeFile(
                mounted.lockPath,
                serializeCoreLfRemoteWorkspaceLock(mounted.lock)
            );
            await writeFile(
                mounted.sourcePath,
                `${mounted.fixture.sourceText}\n`
            );
            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace(mounted.roots),
                'SOURCE_SIZE_MISMATCH'
            );

            const linkedSource = path.join(mounted.root, 'linked-source.json');
            await writeFile(linkedSource, mounted.fixture.sourceText);
            await unlink(mounted.sourcePath);
            await symlink(linkedSource, mounted.sourcePath);
            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace(mounted.roots),
                'UNSAFE_FILE'
            );
        });
    });

    it('rejects cache-entry symbolic links without modifying their targets', async () => {
        await withMountedFixture(async mounted => {
            const first = await materializeCoreLfMountedRemoteWorkspace(
                mounted.roots
            );
            const externalCache = path.join(
                mounted.root,
                'external-cache.json'
            );
            const externalText = await readFile(
                first.paths.cachePath,
                'utf8'
            );
            await writeFile(externalCache, externalText);
            await unlink(first.paths.cachePath);
            await symlink(externalCache, first.paths.cachePath);

            const error = await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace(mounted.roots),
                'CACHE_CONFLICT'
            );
            assert.ok(
                error.cause instanceof
                    CoreLfMountedRemoteWorkspaceStoreError
            );
            assert.equal(
                (error.cause as CoreLfMountedRemoteWorkspaceStoreError).code,
                'UNSAFE_FILE'
            );
            assert.equal(await readFile(externalCache, 'utf8'), externalText);
        });
    });

    it('keeps offline checks read-only and roots explicit and disjoint', async () => {
        await withMountedFixture(async mounted => {
            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspaceOffline(
                    mounted.roots
                ),
                'OFFLINE_CACHE_MISSING'
            );
            assert.deepEqual(await readdir(mounted.roots.dataRoot), []);

            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace({
                    projectRoot: '.',
                    dataRoot: mounted.roots.dataRoot
                }),
                'INVALID_ROOTS'
            );
            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace({
                    projectRoot: mounted.roots.projectRoot,
                    dataRoot: mounted.roots.projectRoot
                }),
                'INVALID_ROOTS'
            );
            await expectStoreError(
                () => materializeCoreLfMountedRemoteWorkspace({
                    ...mounted.roots,
                    credential: 'must-not-be-accepted'
                } as unknown as CoreLfMountedRemoteWorkspaceRoots),
                'INVALID_ROOTS'
            );

            assert.deepEqual(
                CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE,
                {
                    revision:
                        'emdash-lf-mounted-remote-workspace-store-v1',
                    filesystemProfile: 'node-posix-mounted-roots-v1',
                    backend: 'typescript-emdash-explicit-core',
                    lockFileName: 'emdash.workspace.lock.json',
                    sourceFileName: 'emdash.workspace.source.json',
                    cacheRelativeDirectory:
                        '.emdash/cache/lf-remote-workspace-v1',
                    cacheKeyProfile:
                        'sha256-canonical-remote-artifact-identity',
                    cacheFileProfile: 'artifact-<sha256-hex>.json',
                    installProfile:
                        'fsynced-temporary-file-atomic-hard-link-no-replace',
                    maximumLockBytes: 256 * 1024,
                    maximumSourceBytes: 64 * 1024 * 1024,
                    cacheMetadataAllowanceBytes: 1024 * 1024,
                    performsFetch: false,
                    readsCredentials: false,
                    readsEnvironment: false,
                    readsCurrentWorkingDirectory: false,
                    invokesGit: false,
                    invokesLambdapi: false,
                    mutatesExistingCacheEntries: false,
                    evictsCacheEntries: false
                }
            );
        });
    });
});
