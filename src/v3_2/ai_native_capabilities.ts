/**
 * Source-visible capability contract for the qualified AI-native foundation.
 *
 * This is descriptive immutable data. It neither checks a proof nor imports
 * an implementation profile, so an agent can inspect it without acquiring a
 * checker session, filesystem authority, or an accidental runtime closure.
 */

export const CORE_AI_NATIVE_CAPABILITIES_PROFILE = Object.freeze({
    revision: 'emdash-ai-native-capabilities-v1' as const,
    recordRevision: 'emdash-ai-native-capability-record-v1' as const,
    status: 'qualified-local-foundation' as const,
    backend: 'typescript-emdash-explicit-core' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const,
    performsSemanticChecks: false as const,
    computesCryptographicHashes: false as const,
    invokesLambdapi: false as const
});

export interface CoreAiNativeImplementedProfile {
    readonly id: string;
    readonly revision: string;
    readonly scope: string;
}

export interface CoreAiNativeCommandCapability {
    readonly id: string;
    readonly syntax: string;
    readonly scope: string;
    readonly performsSemanticChecks: boolean;
}

export interface CoreAiNativeDeferredCapability {
    readonly id: string;
    readonly state:
        'consumer-gated' | 'platform-gated' | 'research-gated';
    readonly prerequisite: string;
}

export interface CoreAiNativeCapabilityRecord {
    readonly revision:
        typeof CORE_AI_NATIVE_CAPABILITIES_PROFILE.recordRevision;
    readonly status: typeof CORE_AI_NATIVE_CAPABILITIES_PROFILE.status;
    readonly backend: typeof CORE_AI_NATIVE_CAPABILITIES_PROFILE.backend;
    readonly trust: {
        readonly semanticResult: 'checked-backend-neutral-explicit-core';
        readonly arbitraryTypeScriptTrusted: false;
        readonly cachedArtifactsAreProofAuthority: false;
        readonly productionLambdapiDependency: false;
        readonly lambdapiRole: 'optional-development-conformance';
    };
    readonly implementedProfiles:
        readonly CoreAiNativeImplementedProfile[];
    readonly commands: readonly CoreAiNativeCommandCapability[];
    readonly deferred: readonly CoreAiNativeDeferredCapability[];
}

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

/** Exact implemented profiles; this list is intentionally not aspirational. */
export const CORE_AI_NATIVE_CAPABILITIES: CoreAiNativeCapabilityRecord =
    deepFreeze({
        revision:
            CORE_AI_NATIVE_CAPABILITIES_PROFILE.recordRevision,
        status: CORE_AI_NATIVE_CAPABILITIES_PROFILE.status,
        backend: CORE_AI_NATIVE_CAPABILITIES_PROFILE.backend,
        trust: {
            semanticResult: 'checked-backend-neutral-explicit-core',
            arbitraryTypeScriptTrusted: false,
            cachedArtifactsAreProofAuthority: false,
            productionLambdapiDependency: false,
            lambdapiRole: 'optional-development-conformance'
        },
        implementedProfiles: [
            {
                id: 'proof-document',
                revision: 'emdash-v3.2-ai-proof-1',
                scope: 'fresh checked artifacts and stable named goals'
            },
            {
                id: 'declaration-workspace',
                revision: 'emdash-lf-declaration-workspace-v1',
                scope: 'deterministic declaration graphs and invalidation'
            },
            {
                id: 'workspace-proof',
                revision: 'emdash-lf-workspace-proof-v1',
                scope: 'fresh proof checking in one exact module closure'
            },
            {
                id: 'same-module-fragment-workspace',
                revision: 'emdash-lf-same-module-fragment-workspace-v1',
                scope: 'explicit declaration/runtime/proof source lineage'
            },
            {
                id: 'fragment-module-workspace',
                revision: 'emdash-lf-fragment-module-workspace-v1',
                scope: 'exact declaration/runtime/proof fragment graphs'
            },
            {
                id: 'mounted-workspace-store',
                revision: 'emdash-lf-mounted-remote-workspace-store-v1',
                scope: 'locked fixed files and immutable offline cache reuse'
            },
            {
                id: 'dictionary-synthesis',
                revision: 'emdash-lf-dictionary-synthesis-v1',
                scope: 'finite explicit global candidate selection'
            },
            {
                id: 'dictionary-authoring',
                revision: 'emdash-lf-dictionary-authoring-v1',
                scope: 'one direct leading implicit global argument'
            },
            {
                id: 'instance-provider-scope',
                revision: 'emdash-lf-instance-scope-v1',
                scope:
                    'checked providers and immutable local, named, ' +
                    'imported, and global precedence'
            },
            {
                id: 'recursive-instance-synthesis',
                revision: 'emdash-lf-instance-synthesis-v2',
                scope:
                    'bounded ground-goal search with role-scheduled ' +
                    'premises, shared tables, strict ambiguity, and ' +
                    'explicit checked evidence'
            },
            {
                id: 'role-aware-instance-synthesis',
                revision: 'emdash-lf-instance-role-synthesis-v1',
                scope:
                    'bounded output-parameter inference over exact checked ' +
                    'ground instance synthesis'
            },
            {
                id: 'class-call-elaboration',
                revision: 'emdash-lf-class-call-elaboration-v2',
                scope:
                    'saturated dependent calls with ordinary implicit ' +
                    'and output inference plus checked instance insertion'
            },
            {
                id: 'research-document-binding',
                revision: 'emdash-research-document-binding-v1',
                scope: 'stable diagram/declaration/proof block identities'
            },
            {
                id: 'research-browser-recheck',
                revision: 'emdash-ai-research-overview-browser-v1',
                scope: 'release-pinned checked/open client replay'
            }
        ],
        commands: [
            {
                id: 'capabilities',
                syntax:
                    './scripts/emdash capabilities ' +
                    '[--format jsonl|text]',
                scope: 'this static capability record only',
                performsSemanticChecks: false
            },
            {
                id: 'proof-check',
                syntax:
                    './scripts/emdash check [declaration] ' +
                    '[--format jsonl|text]',
                scope: 'fixed ai_native.local proof demo declarations',
                performsSemanticChecks: true
            },
            {
                id: 'proof-goals',
                syntax:
                    './scripts/emdash goals [declaration] ' +
                    '[--format jsonl|text]',
                scope: 'fixed ai_native.local proof demo declarations',
                performsSemanticChecks: true
            },
            {
                id: 'workspace-check',
                syntax:
                    './scripts/emdash workspace check --project-root PATH ' +
                    '--data-root PATH [--offline] [--format jsonl|text]',
                scope:
                    'canonical emdash.workspace.lock.json and ' +
                    'emdash.workspace.source.json under explicit roots',
                performsSemanticChecks: true
            }
        ],
        deferred: [
            {
                id: 'general-source-acquisition',
                state: 'consumer-gated',
                prerequisite:
                    'a real general module/theorem facade and restricted ' +
                    'TypeScript acquisition consumer'
            },
            {
                id: 'general-development-cli',
                state: 'consumer-gated',
                prerequisite:
                    'arbitrary module/declaration targeting plus measured ' +
                    'build, graph, and snapshot consumers'
            },
            {
                id: 'persisted-or-inline-paper-artifacts',
                state: 'consumer-gated',
                prerequisite:
                    'an owning artifact or inline print-placement consumer'
            },
            {
                id: 'network-acquisition',
                state: 'consumer-gated',
                prerequisite:
                    'a stable authenticated or public transport consumer'
            },
            {
                id: 'hosted-workspace-delivery',
                state: 'platform-gated',
                prerequisite:
                    'a distributable runtime, compatible Node/template ' +
                    'contract, and generic platform source capability'
            },
            {
                id: 'whole-library-transfer-and-global-metatheory',
                state: 'research-gated',
                prerequisite:
                    'separate scale evidence and explicit mathematical review'
            }
        ]
    });

export const serializeCoreAiNativeCapabilities = (): string =>
    `${JSON.stringify(CORE_AI_NATIVE_CAPABILITIES)}\n`;
