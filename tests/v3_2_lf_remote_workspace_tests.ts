/** Focused AI-REMOTE-1A immutable lock and offline reconstruction tests. */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
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
