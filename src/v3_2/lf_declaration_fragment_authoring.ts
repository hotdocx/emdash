/**
 * Direct-TypeScript authoring facade for declaration-only LF fragments.
 *
 * Each local declaration carries its explicit trust review and symbol
 * linkage. This owner derives only repetitive orders and companion revisions,
 * then lowers through the existing module, policy, linkage, and fragment
 * factories. It adds no declaration, checking, or runtime semantics.
 */

import {
    CoreLfCanonicalExportEvidence,
    CoreLfQualifiedSymbol,
    CoreLfTransferBody,
    CoreLfTransferExpression,
    CoreLfTransferModifiers,
    CoreLfTransferProvenance,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfSameModuleDeclarationFragmentSource,
    CoreLfWorkspaceFragmentIdentity,
    defineCoreLfDependencyModuleDeclarationFragment
} from './lf_fragment_workspace';
import {
    CoreOwnerId
} from './schema';

export const CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE = Object.freeze({
    revision: 'emdash-lf-declaration-fragment-authoring-v1' as const,
    lowering: 'exact-dependency-module-declaration-fragment' as const,
    sourceOrderPolicy: 'explicit-first-then-consecutive' as const,
    companionRevisionPolicy:
        'module-revision-plus-policy-or-linkage-suffix' as const,
    trustPolicy: 'explicit-policy-class-and-review-evidence' as const,
    linkagePolicy: 'explicit-core-owner-or-free-declaration' as const,
    generatesDeclarations: false as const,
    infersTrust: false as const,
    generatesRuntimeRules: false as const,
    generatesProofRules: false as const,
    acceptsRuntimeInput: false as const,
    acceptsCompilerCallbacks: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export const serializeCoreLfDeclarationFragmentAuthoringProfile = (): string =>
    `${JSON.stringify(
        CORE_LF_DECLARATION_FRAGMENT_AUTHORING_PROFILE,
        null,
        2
    )}\n`;

export type CoreLfDeclarationFragmentAuthoringPolicy =
    | 'opaque-signature'
    | 'checked-transparent-definition'
    | 'theorem-body'
    | 'conformance-only'
    | 'excluded';

export type CoreLfDeclarationFragmentAuthoringLink =
    | {
        readonly kind: 'core-owner';
        readonly owner: CoreOwnerId;
    }
    | {
        readonly kind: 'free-declaration';
        readonly coreName: string;
        readonly backendName: string;
    };

export interface CoreLfDeclarationFragmentAuthoringTrust {
    readonly policy: CoreLfDeclarationFragmentAuthoringPolicy;
    readonly evidence: string;
}

export interface CoreLfDeclarationFragmentAuthoringDeclaration {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly type: CoreLfTransferExpression;
    readonly body: CoreLfTransferBody;
    readonly modifiers: CoreLfTransferModifiers;
    readonly provenance: CoreLfTransferProvenance;
    readonly trust: CoreLfDeclarationFragmentAuthoringTrust;
    readonly linkage: CoreLfDeclarationFragmentAuthoringLink;
}

interface CoreLfDeclarationFragmentAuthoringExternalBase {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly linkage: CoreLfDeclarationFragmentAuthoringLink;
}

export type CoreLfDeclarationFragmentAuthoringExternal =
    | CoreLfDeclarationFragmentAuthoringExternalBase & {
        readonly availability: 'earlier-fragment';
        readonly provider: CoreLfWorkspaceFragmentIdentity;
    }
    | CoreLfDeclarationFragmentAuthoringExternalBase & {
        readonly availability: 'dependency-module' | 'existing-core';
        readonly provider?: never;
    };

export interface CoreLfDeclarationFragmentAuthoringInput {
    readonly moduleRevision: string;
    readonly moduleId: string;
    readonly fragmentId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport?: CoreLfCanonicalExportEvidence;
    readonly dependencies: readonly string[];
    readonly firstSourceOrder: number;
    readonly externals: readonly CoreLfDeclarationFragmentAuthoringExternal[];
    readonly declarations:
        readonly CoreLfDeclarationFragmentAuthoringDeclaration[];
    readonly runtimeProvider?: CoreLfWorkspaceFragmentIdentity;
}

const policyRevision = (moduleRevision: string): string =>
    `${moduleRevision}.policy`;

const linkageRevision = (moduleRevision: string): string =>
    `${moduleRevision}.linkage`;

/**
 * Lower one compact declaration list to the unchanged dependency-fragment
 * source. All semantic validation remains in the existing owners.
 */
export function createCoreLfAuthoredDependencyModuleDeclarationFragment(
    input: CoreLfDeclarationFragmentAuthoringInput
): CoreLfSameModuleDeclarationFragmentSource {
    const module = createCoreLfModuleSpec({
        revision: input.moduleRevision,
        moduleId: input.moduleId,
        fragmentId: input.fragmentId,
        authorityPath: input.authorityPath,
        sourceSha256: input.sourceSha256,
        ...(input.canonicalExport === undefined
            ? {}
            : { canonicalExport: input.canonicalExport }),
        dependencies: input.dependencies,
        externalSymbols: input.externals.map(external => ({
            symbol: external.symbol,
            availability: external.availability
        })),
        declarations: input.declarations.map((declaration, index) => ({
            order: input.firstSourceOrder + index,
            symbol: declaration.symbol,
            type: declaration.type,
            body: declaration.body,
            modifiers: declaration.modifiers,
            provenance: declaration.provenance
        })),
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: policyRevision(input.moduleRevision),
        moduleRevision: input.moduleRevision,
        entries: input.declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: declaration.trust.policy,
            evidence: declaration.trust.evidence
        }))
    });
    const links = [
        ...input.externals.map(external => ({
            symbol: external.symbol,
            linkage: external.linkage
        })),
        ...input.declarations.map(declaration => ({
            symbol: declaration.symbol,
            linkage: declaration.linkage
        }))
    ];
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: linkageRevision(input.moduleRevision),
        moduleRevision: input.moduleRevision,
        entries: links.map((entry, order) => ({
            order,
            symbol: entry.symbol,
            ...entry.linkage
        }))
    });
    return defineCoreLfDependencyModuleDeclarationFragment({
        module,
        policy,
        linkage,
        externalProviders: input.externals.flatMap(external =>
            external.availability === 'earlier-fragment'
                ? [{
                    symbol: external.symbol,
                    provider: external.provider
                }]
                : []
        ),
        ...(input.runtimeProvider === undefined
            ? {}
            : { runtimeProvider: input.runtimeProvider })
    });
}
