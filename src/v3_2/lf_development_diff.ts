/**
 * Browser-safe semantic maintenance reports for two proof-development
 * revisions.
 *
 * Both canonical sources are reconstructed and both declaration workspaces
 * are checked. Proof source is inspected structurally but is deliberately not
 * executed: a broken current proof is one of the primary consumers of this
 * report. The result is conservative invalidation evidence, never a repair or
 * a proof-validity judgment.
 */

import {
    CoreOwnerId,
    KernelExpression
} from './kernel';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    CoreProofPlan
} from './proof_plan';
import {
    CoreLfWorkspaceProofDocumentInput
} from './lf_workspace_proof';
import {
    CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
    CoreLfProofDevelopmentSourceSnapshot,
    reconstructCoreLfProofDevelopmentSourceSnapshot
} from './lf_proof_development_source';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE,
    CoreLfCompiledDeclarationWorkspace,
    CoreLfDeclarationWorkspaceInterfaceEntry,
    CoreLfDeclarationWorkspaceInvalidation,
    CoreLfDeclarationWorkspaceInvalidationState,
    CoreLfDeclarationWorkspaceSnapshot,
    compareCoreLfDeclarationWorkspaceSnapshots,
    compileCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspaceClosureSnapshot,
    createCoreLfDeclarationWorkspaceSnapshot,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreLfCompiledDeclaration,
    CoreLfTransferDeclarationLink
} from './lf_transfer_compiler';
import {
    CoreLfQualifiedSymbol
} from './lf_transfer';

export const CORE_LF_DEVELOPMENT_DIFF_PROFILE = Object.freeze({
    revision: 'emdash-lf-development-diff-v1' as const,
    reportRevision: 'emdash-lf-development-diff-report-v1' as const,
    sourceProfileRevision:
        CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision,
    workspaceProfileRevision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
    dependencyPolicy:
        'exact-revision-linkage-structural-core-uses' as const,
    proofImpactPolicy:
        'unchanged-source-reusable-closure-and-dependencies' as const,
    repairPolicy: 'repair-not-proposed' as const,
    defaultExpressionVisitLimit: 100_000,
    maxExpressionVisitLimit: 1_000_000,
    compilesProofs: false as const,
    executesIncrementally: false as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const
});

export type CoreLfDevelopmentDiffErrorCode =
    | 'INVALID_EXPRESSION_VISIT_LIMIT'
    | 'INVALID_PREVIOUS_SOURCE'
    | 'INVALID_CURRENT_SOURCE'
    | 'PREVIOUS_DECLARATION_COMPILATION_FAILED'
    | 'CURRENT_DECLARATION_COMPILATION_FAILED'
    | 'EXPRESSION_VISIT_LIMIT_EXCEEDED'
    | 'CYCLIC_EXPRESSION'
    | 'CYCLIC_PROOF_PLAN'
    | 'DECLARATION_IDENTITY_DRIFT'
    | 'REFERENCE_RESOLUTION_DRIFT'
    | 'UNKNOWN_PROOF_MODULE';

export class CoreLfDevelopmentDiffError extends Error {
    constructor(
        public readonly code: CoreLfDevelopmentDiffErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfDevelopmentDiffError';
    }
}

const fail = (
    code: CoreLfDevelopmentDiffErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreLfDevelopmentDiffError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const errorText = (error: unknown): string => error instanceof Error
    ? error.message
    : String(error);

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const compareSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): number => compareText(left.moduleId, right.moduleId) ||
    compareText(left.name, right.name);

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const proofKey = (
    proof: { readonly moduleId: string; readonly declarationId: string }
): string => `${proof.moduleId}\u0000${proof.declarationId}`;

const canonical = (value: unknown, path: string): string =>
    serializeCoreLfWorkspaceCanonicalJson(value, path);

const sameCanonical = (
    left: unknown,
    right: unknown,
    path: string
): boolean => canonical(left, `${path}.previous`) ===
    canonical(right, `${path}.current`);

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

const cloneSymbol = (
    symbol: CoreLfQualifiedSymbol
): CoreLfQualifiedSymbol => ({
    moduleId: symbol.moduleId,
    name: symbol.name
});

export interface CoreLfDevelopmentDiffOptions {
    /** Shared hard ceiling across both revisions and all expression roots. */
    readonly expressionVisitLimit?: number;
}

export type CoreLfDevelopmentReferenceResolutionStatus =
    | 'resolved'
    | 'unresolved'
    | 'ambiguous';

interface CoreLfDevelopmentReferenceResolutionBase {
    readonly status: CoreLfDevelopmentReferenceResolutionStatus;
    readonly candidates: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfDevelopmentFreeReferenceResolution
extends CoreLfDevelopmentReferenceResolutionBase {
    readonly kind: 'free-reference';
    readonly name: string;
}

export interface CoreLfDevelopmentOwnerResolution
extends CoreLfDevelopmentReferenceResolutionBase {
    readonly kind: 'semantic-owner';
    readonly owner: CoreOwnerId;
}

export type CoreLfDevelopmentReferenceResolution =
    | CoreLfDevelopmentFreeReferenceResolution
    | CoreLfDevelopmentOwnerResolution;

export interface CoreLfDevelopmentDependencyEvidence {
    readonly nodeCount: number;
    readonly freeReferences: readonly string[];
    readonly semanticOwners: readonly CoreOwnerId[];
    readonly resolutions:
        readonly CoreLfDevelopmentReferenceResolution[];
    readonly declarationDependencies:
        readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfDevelopmentDeclarationRevision {
    readonly entry: CoreLfDeclarationWorkspaceInterfaceEntry;
    readonly expressionNodeCounts: {
        readonly type: number;
        readonly body: number;
    };
    readonly dependencies: CoreLfDevelopmentDependencyEvidence;
}

export type CoreLfDevelopmentDeclarationChangedField =
    | 'order'
    | 'visibility'
    | 'policy'
    | 'status'
    | 'link'
    | 'type'
    | 'body';

export type CoreLfDevelopmentDeclarationDiffState =
    | 'added'
    | 'removed'
    | 'changed'
    | 'reusable';

export interface CoreLfDevelopmentDeclarationDiff {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly state: CoreLfDevelopmentDeclarationDiffState;
    readonly changedFields:
        readonly CoreLfDevelopmentDeclarationChangedField[];
    readonly previous?: CoreLfDevelopmentDeclarationRevision;
    readonly current?: CoreLfDevelopmentDeclarationRevision;
}

export interface CoreLfDevelopmentDeclarationDependencyEdge {
    /** Declaration containing the structural use. */
    readonly dependent: CoreLfQualifiedSymbol;
    /** Exact declaration reached through revision-local linkage. */
    readonly dependency: CoreLfQualifiedSymbol;
}

export interface CoreLfDevelopmentDeclarationDependencyGraph {
    readonly declarations: readonly CoreLfQualifiedSymbol[];
    readonly edges: readonly CoreLfDevelopmentDeclarationDependencyEdge[];
}

export interface CoreLfDevelopmentDeclarationImpact {
    readonly source: CoreLfQualifiedSymbol;
    readonly sourceState: Exclude<
        CoreLfDevelopmentDeclarationDiffState,
        'reusable'
    >;
    readonly directDependents: readonly CoreLfQualifiedSymbol[];
    /** Proper transitive dependents at distance two or greater. */
    readonly transitiveDependents: readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfDevelopmentProofSource {
    readonly typeCanonicalJson: string;
    readonly planCanonicalJson: string;
    readonly provenanceCanonicalJson: string;
    readonly fingerprintCanonicalJson: string;
}

export interface CoreLfDevelopmentProofRevision {
    readonly source: CoreLfDevelopmentProofSource;
    readonly closureModuleIds: readonly string[];
    readonly expressionNodeCounts: {
        readonly type: number;
        readonly plan: number;
    };
    readonly dependencies: CoreLfDevelopmentDependencyEvidence;
}

export type CoreLfDevelopmentProofChangedField =
    | 'type'
    | 'plan'
    | 'provenance'
    | 'fingerprint';

export type CoreLfDevelopmentProofDiffState =
    | 'added'
    | 'removed'
    | 'source-changed'
    | 'recheck-required'
    | 'reusable';

export type CoreLfDevelopmentProofImpactReason =
    | { readonly kind: 'proof-added' }
    | { readonly kind: 'proof-removed' }
    | {
        readonly kind: 'proof-source-changed';
        readonly fields: readonly CoreLfDevelopmentProofChangedField[];
    }
    | {
        readonly kind: 'module-not-reusable';
        readonly moduleId: string;
        readonly state: CoreLfDeclarationWorkspaceInvalidationState;
    }
    | {
        readonly kind: 'declaration-impacted';
        readonly declaration: CoreLfQualifiedSymbol;
        readonly declarationState: 'changed' | 'removed';
        readonly relationship: 'direct' | 'transitive';
        readonly directDependency: CoreLfQualifiedSymbol;
    }
    | {
        readonly kind: 'reference-not-uniquely-resolved';
        readonly side: 'previous' | 'current';
        readonly reference:
            CoreLfDevelopmentReferenceResolution;
    };

export interface CoreLfDevelopmentProofDiff {
    readonly proof: {
        readonly moduleId: string;
        readonly declarationId: string;
    };
    readonly state: CoreLfDevelopmentProofDiffState;
    readonly changedFields: readonly CoreLfDevelopmentProofChangedField[];
    readonly reasons: readonly CoreLfDevelopmentProofImpactReason[];
    readonly previous?: CoreLfDevelopmentProofRevision;
    readonly current?: CoreLfDevelopmentProofRevision;
}

export interface CoreLfDevelopmentSemanticDiffReport {
    readonly revision:
        typeof CORE_LF_DEVELOPMENT_DIFF_PROFILE.reportRevision;
    readonly profileRevision:
        typeof CORE_LF_DEVELOPMENT_DIFF_PROFILE.revision;
    readonly sourceProfileRevision:
        typeof CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision;
    readonly workspaceProfileRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision;
    readonly dependencyPolicy:
        typeof CORE_LF_DEVELOPMENT_DIFF_PROFILE.dependencyPolicy;
    readonly proofImpactPolicy:
        typeof CORE_LF_DEVELOPMENT_DIFF_PROFILE.proofImpactPolicy;
    readonly repairPolicy:
        typeof CORE_LF_DEVELOPMENT_DIFF_PROFILE.repairPolicy;
    readonly previous: {
        readonly developmentRevision: string;
        readonly workspaceRevision: string;
        readonly moduleOrder: readonly string[];
    };
    readonly current: {
        readonly developmentRevision: string;
        readonly workspaceRevision: string;
        readonly moduleOrder: readonly string[];
    };
    readonly visitBudget: {
        readonly expressionVisitLimit: number;
        readonly expressionNodesVisited: number;
    };
    readonly moduleInvalidation: CoreLfDeclarationWorkspaceInvalidation;
    readonly declarations: readonly CoreLfDevelopmentDeclarationDiff[];
    readonly declarationDependencies: {
        readonly previous: CoreLfDevelopmentDeclarationDependencyGraph;
        readonly current: CoreLfDevelopmentDeclarationDependencyGraph;
        readonly union: CoreLfDevelopmentDeclarationDependencyGraph;
    };
    readonly declarationImpacts:
        readonly CoreLfDevelopmentDeclarationImpact[];
    readonly proofs: readonly CoreLfDevelopmentProofDiff[];
    readonly counts: {
        readonly previousModules: number;
        readonly currentModules: number;
        readonly previousDeclarations: number;
        readonly currentDeclarations: number;
        readonly addedDeclarations: number;
        readonly removedDeclarations: number;
        readonly changedDeclarations: number;
        readonly reusableDeclarations: number;
        readonly previousDependencyEdges: number;
        readonly currentDependencyEdges: number;
        readonly unionDependencyEdges: number;
        readonly previousProofs: number;
        readonly currentProofs: number;
        readonly addedProofs: number;
        readonly removedProofs: number;
        readonly sourceChangedProofs: number;
        readonly recheckRequiredProofs: number;
        readonly reusableProofs: number;
    };
    readonly compilesProofs: false;
    readonly executesIncrementally: false;
}

interface VisitCounter {
    readonly limit: number;
    visited: number;
}

interface RawStructuralScan {
    readonly nodeCount: number;
    readonly freeReferences: readonly string[];
    readonly semanticOwners: readonly CoreOwnerId[];
}

interface ExpressionRoot {
    readonly expression: KernelExpression;
    readonly path: string;
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

interface VisitFrame {
    readonly node: KernelExpression;
    readonly path: string;
    readonly leaving: boolean;
}

const scanExpressionRoots = (
    roots: readonly ExpressionRoot[],
    counter: VisitCounter
): RawStructuralScan => {
    const freeReferences = new Set<string>();
    const semanticOwners = new Set<CoreOwnerId>();
    let nodeCount = 0;

    roots.forEach(root => {
        const active = new Set<KernelExpression>();
        const pending: VisitFrame[] = [{
            node: root.expression,
            path: root.path,
            leaving: false
        }];
        while (pending.length > 0) {
            const frame = pending.pop();
            if (frame === undefined) break;
            if (frame.leaving) {
                active.delete(frame.node);
                continue;
            }
            if (active.has(frame.node)) {
                fail(
                    'CYCLIC_EXPRESSION',
                    frame.path,
                    'Semantic diff input contains a cyclic Core expression'
                );
            }
            if (counter.visited === counter.limit) {
                fail(
                    'EXPRESSION_VISIT_LIMIT_EXCEEDED',
                    frame.path,
                    `Semantic diff exceeds its shared ` +
                        `${counter.limit}-node expression budget`
                );
            }
            counter.visited++;
            nodeCount++;
            active.add(frame.node);
            if (frame.node.tag === 'reference') {
                freeReferences.add(frame.node.name);
            } else if (frame.node.tag === 'application') {
                semanticOwners.add(frame.node.owner);
            }
            pending.push({ ...frame, leaving: true });
            const children = expressionChildren(frame.node);
            for (let index = children.length - 1; index >= 0; index--) {
                pending.push({
                    node: children[index],
                    path: `${frame.path}.child[${index}]`,
                    leaving: false
                });
            }
        }
    });

    return {
        nodeCount,
        freeReferences: [...freeReferences].sort(compareText),
        semanticOwners: [...semanticOwners].sort(compareText)
    };
};

const mergeScans = (
    scans: readonly RawStructuralScan[]
): RawStructuralScan => ({
    nodeCount: scans.reduce((count, scan) => count + scan.nodeCount, 0),
    freeReferences: [...new Set(scans.flatMap(scan =>
        scan.freeReferences
    ))].sort(compareText),
    semanticOwners: [...new Set(scans.flatMap(scan =>
        scan.semanticOwners
    ))].sort(compareText)
});

const proofPlanExpressionRoots = (
    plan: CoreProofPlan,
    path: string
): readonly ExpressionRoot[] => {
    const roots: ExpressionRoot[] = [];
    const active = new Set<CoreProofPlan>();
    const visit = (
        node: CoreProofPlan,
        nodePath: string,
        depth: number
    ): void => {
        if (active.has(node)) {
            fail(
                'CYCLIC_PROOF_PLAN',
                nodePath,
                'Semantic diff input contains a cyclic proof plan'
            );
        }
        active.add(node);
        switch (node.tag) {
            case 'exact':
                roots.push({
                    expression: node.solution,
                    path: `${nodePath}.solution@${depth}`
                });
                break;
            case 'intro':
                visit(node.body, `${nodePath}.body`, depth + 1);
                break;
            case 'apply':
                roots.push({
                    expression: node.callee,
                    path: `${nodePath}.callee@${depth}`
                });
                node.premises.forEach((premise, index) =>
                    visit(
                        premise,
                        `${nodePath}.premises[${index}]`,
                        depth
                    )
                );
                break;
            case 'have':
                roots.push({
                    expression: node.binding.type,
                    path: `${nodePath}.binding.type@${depth}`
                });
                visit(node.proof, `${nodePath}.proof`, depth);
                visit(node.body, `${nodePath}.body`, depth + 1);
                break;
            case 'hole':
                if (node.expectation?.target !== undefined) {
                    roots.push({
                        expression: node.expectation.target,
                        path: `${nodePath}.expectation.target@${depth}`
                    });
                }
                break;
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }
        active.delete(node);
    };
    visit(plan, path, 0);
    return roots;
};

interface LinkIndex {
    readonly free: ReadonlyMap<string, readonly CoreLfQualifiedSymbol[]>;
    readonly owners: ReadonlyMap<string, readonly CoreLfQualifiedSymbol[]>;
}

const addLinkCandidate = (
    map: Map<string, CoreLfQualifiedSymbol[]>,
    key: string,
    symbol: CoreLfQualifiedSymbol
): void => {
    const candidates = map.get(key) ?? [];
    if (!candidates.some(candidate => symbolKey(candidate) === symbolKey(symbol))) {
        candidates.push(cloneSymbol(symbol));
        candidates.sort(compareSymbol);
    }
    map.set(key, candidates);
};

const createLinkIndex = (
    declarations: readonly CoreLfCompiledDeclaration[]
): LinkIndex => {
    const free = new Map<string, CoreLfQualifiedSymbol[]>();
    const owners = new Map<string, CoreLfQualifiedSymbol[]>();
    declarations.forEach(declaration => {
        const link: CoreLfTransferDeclarationLink = declaration.link;
        if (link.kind === 'free-declaration') {
            addLinkCandidate(free, link.coreName, declaration.symbol);
        } else {
            addLinkCandidate(owners, link.owner, declaration.symbol);
        }
    });
    return { free, owners };
};

const resolutionStatus = (
    candidates: readonly CoreLfQualifiedSymbol[]
): CoreLfDevelopmentReferenceResolutionStatus => candidates.length === 0
    ? 'unresolved'
    : candidates.length === 1
        ? 'resolved'
        : 'ambiguous';

const assertResolution = (
    resolution: CoreLfDevelopmentReferenceResolution,
    path: string
): void => {
    const expected = resolutionStatus(resolution.candidates);
    if (
        resolution.status !== expected ||
        new Set(resolution.candidates.map(symbolKey)).size !==
            resolution.candidates.length
    ) {
        fail(
            'REFERENCE_RESOLUTION_DRIFT',
            path,
            'Reference resolution status or exact candidates drifted'
        );
    }
};

const resolveScan = (
    scan: RawStructuralScan,
    links: LinkIndex,
    path: string
): CoreLfDevelopmentDependencyEvidence => {
    const resolutions: CoreLfDevelopmentReferenceResolution[] = [
        ...scan.freeReferences.map(name => {
            const candidates = [...(links.free.get(name) ?? [])]
                .sort(compareSymbol);
            return {
                kind: 'free-reference' as const,
                name,
                status: resolutionStatus(candidates),
                candidates
            };
        }),
        ...scan.semanticOwners.map(owner => {
            const candidates = [...(links.owners.get(owner) ?? [])]
                .sort(compareSymbol);
            return {
                kind: 'semantic-owner' as const,
                owner,
                status: resolutionStatus(candidates),
                candidates
            };
        })
    ];
    resolutions.forEach((resolution, index) =>
        assertResolution(resolution, `${path}.resolutions[${index}]`)
    );
    const dependencies = new Map<string, CoreLfQualifiedSymbol>();
    resolutions.forEach(resolution => {
        if (resolution.status !== 'resolved') return;
        const candidate = resolution.candidates[0];
        dependencies.set(symbolKey(candidate), cloneSymbol(candidate));
    });
    return {
        nodeCount: scan.nodeCount,
        freeReferences: scan.freeReferences,
        semanticOwners: scan.semanticOwners,
        resolutions,
        declarationDependencies: [...dependencies.values()].sort(compareSymbol)
    };
};

interface InternalDeclarationRevision {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly entry: CoreLfDeclarationWorkspaceInterfaceEntry;
    readonly compiled: CoreLfCompiledDeclaration;
    readonly typeScan: RawStructuralScan;
    readonly bodyScan: RawStructuralScan;
    readonly scan: RawStructuralScan;
    dependencies?: CoreLfDevelopmentDependencyEvidence;
}

interface CompiledRevision {
    readonly workspace: CoreLfCompiledDeclarationWorkspace;
    readonly snapshot: CoreLfDeclarationWorkspaceSnapshot;
    readonly declarations:
        ReadonlyMap<string, InternalDeclarationRevision>;
    readonly links: LinkIndex;
}

const verifyDeclarationInterface = (
    declaration: CoreLfCompiledDeclaration,
    entry: CoreLfDeclarationWorkspaceInterfaceEntry,
    path: string
): void => {
    if (
        symbolKey(declaration.symbol) !== symbolKey(entry.symbol) ||
        declaration.order !== entry.order ||
        !sameCanonical(declaration.link, entry.link, `${path}.link`) ||
        serializeCoreExpression(declaration.type) !== entry.type ||
        (declaration.body === undefined
            ? entry.body !== undefined
            : serializeCoreExpression(declaration.body) !== entry.body)
    ) {
        fail(
            'DECLARATION_IDENTITY_DRIFT',
            path,
            'Checked declaration and portable interface entry drifted'
        );
    }
};

const prepareCompiledRevision = (
    workspace: CoreLfCompiledDeclarationWorkspace,
    counter: VisitCounter,
    path: string
): CompiledRevision => {
    const snapshot = createCoreLfDeclarationWorkspaceSnapshot(workspace);
    const declarations = new Map<string, InternalDeclarationRevision>();
    const compiledDeclarations = workspace.modules.flatMap(module =>
        module.compiled.declarations
    );
    const links = createLinkIndex(compiledDeclarations);

    workspace.modules.forEach((module, moduleIndex) => {
        const compiledByKey = new Map(module.compiled.declarations.map(
            declaration => [symbolKey(declaration.symbol), declaration]
        ));
        if (
            compiledByKey.size !== module.compiled.declarations.length ||
            module.interfaceSnapshot.declarations.length !==
                module.compiled.declarations.length
        ) {
            fail(
                'DECLARATION_IDENTITY_DRIFT',
                `${path}.modules[${moduleIndex}]`,
                'Checked declarations are not in one-to-one interface correspondence'
            );
        }
        module.interfaceSnapshot.declarations.forEach((entry, entryIndex) => {
            const key = symbolKey(entry.symbol);
            const compiled = compiledByKey.get(key);
            if (compiled === undefined || declarations.has(key)) {
                fail(
                    'DECLARATION_IDENTITY_DRIFT',
                    `${path}.modules[${moduleIndex}].declarations[` +
                        `${entryIndex}]`,
                    'Declaration identity is absent or duplicated'
                );
            }
            verifyDeclarationInterface(
                compiled,
                entry,
                `${path}.modules[${moduleIndex}].declarations[` +
                    `${entryIndex}]`
            );
            const typeScan = scanExpressionRoots([{
                expression: compiled.type,
                path: `${path}.${key}.type`
            }], counter);
            const bodyScan = compiled.body === undefined
                ? { nodeCount: 0, freeReferences: [], semanticOwners: [] }
                : scanExpressionRoots([{
                    expression: compiled.body,
                    path: `${path}.${key}.body`
                }], counter);
            declarations.set(key, {
                symbol: cloneSymbol(entry.symbol),
                entry,
                compiled,
                typeScan,
                bodyScan,
                scan: mergeScans([typeScan, bodyScan])
            });
        });
    });

    declarations.forEach((declaration, key) => {
        declaration.dependencies = resolveScan(
            declaration.scan,
            links,
            `${path}.declarations.${key}`
        );
    });
    return { workspace, snapshot, declarations, links };
};

const publicDeclarationRevision = (
    declaration: InternalDeclarationRevision
): CoreLfDevelopmentDeclarationRevision => {
    if (declaration.dependencies === undefined) {
        return fail(
            'DECLARATION_IDENTITY_DRIFT',
            `declarations.${symbolKey(declaration.symbol)}`,
            'Declaration dependency evidence was not resolved'
        );
    }
    return {
        entry: declaration.entry,
        expressionNodeCounts: {
            type: declaration.typeScan.nodeCount,
            body: declaration.bodyScan.nodeCount
        },
        dependencies: declaration.dependencies
    };
};

const declarationChangedFields = (
    previous: CoreLfDeclarationWorkspaceInterfaceEntry,
    current: CoreLfDeclarationWorkspaceInterfaceEntry
): readonly CoreLfDevelopmentDeclarationChangedField[] => {
    const changed: CoreLfDevelopmentDeclarationChangedField[] = [];
    if (previous.order !== current.order) changed.push('order');
    if (previous.visibility !== current.visibility) changed.push('visibility');
    if (previous.policy !== current.policy) changed.push('policy');
    if (previous.status !== current.status) changed.push('status');
    if (!sameCanonical(previous.link, current.link, 'declaration.link')) {
        changed.push('link');
    }
    if (previous.type !== current.type) changed.push('type');
    if (previous.body !== current.body) changed.push('body');
    return changed;
};

const diffDeclarations = (
    previous: CompiledRevision,
    current: CompiledRevision
): readonly CoreLfDevelopmentDeclarationDiff[] => {
    const keys = [...new Set([
        ...previous.declarations.keys(),
        ...current.declarations.keys()
    ])].sort(compareText);
    return keys.map(key => {
        const before = previous.declarations.get(key);
        const after = current.declarations.get(key);
        const symbol = cloneSymbol((before ?? after)?.symbol ?? fail(
            'DECLARATION_IDENTITY_DRIFT',
            `declarations.${key}`,
            'Declaration union contains no revision entry'
        ));
        if (before === undefined) {
            return {
                symbol,
                state: 'added' as const,
                changedFields: [],
                current: publicDeclarationRevision(after as InternalDeclarationRevision)
            };
        }
        if (after === undefined) {
            return {
                symbol,
                state: 'removed' as const,
                changedFields: [],
                previous: publicDeclarationRevision(before)
            };
        }
        const changedFields = declarationChangedFields(
            before.entry,
            after.entry
        );
        return {
            symbol,
            state: changedFields.length === 0
                ? 'reusable' as const
                : 'changed' as const,
            changedFields,
            previous: publicDeclarationRevision(before),
            current: publicDeclarationRevision(after)
        };
    });
};

const compareEdge = (
    left: CoreLfDevelopmentDeclarationDependencyEdge,
    right: CoreLfDevelopmentDeclarationDependencyEdge
): number => compareSymbol(left.dependent, right.dependent) ||
    compareSymbol(left.dependency, right.dependency);

const edgeKey = (
    edge: CoreLfDevelopmentDeclarationDependencyEdge
): string => `${symbolKey(edge.dependent)}\u0001${symbolKey(edge.dependency)}`;

const dependencyGraph = (
    declarations: ReadonlyMap<string, InternalDeclarationRevision>
): CoreLfDevelopmentDeclarationDependencyGraph => {
    const edges: CoreLfDevelopmentDeclarationDependencyEdge[] = [];
    declarations.forEach(declaration => {
        declaration.dependencies?.declarationDependencies.forEach(
            dependency => edges.push({
                dependent: cloneSymbol(declaration.symbol),
                dependency: cloneSymbol(dependency)
            })
        );
    });
    return {
        declarations: [...declarations.values()]
            .map(declaration => cloneSymbol(declaration.symbol))
            .sort(compareSymbol),
        edges: edges.sort(compareEdge)
    };
};

const unionDependencyGraph = (
    previous: CoreLfDevelopmentDeclarationDependencyGraph,
    current: CoreLfDevelopmentDeclarationDependencyGraph
): CoreLfDevelopmentDeclarationDependencyGraph => {
    const declarationByKey = new Map<string, CoreLfQualifiedSymbol>();
    [...previous.declarations, ...current.declarations].forEach(symbol =>
        declarationByKey.set(symbolKey(symbol), cloneSymbol(symbol))
    );
    const edgeByKey = new Map<
        string,
        CoreLfDevelopmentDeclarationDependencyEdge
    >();
    [...previous.edges, ...current.edges].forEach(edge =>
        edgeByKey.set(edgeKey(edge), {
            dependent: cloneSymbol(edge.dependent),
            dependency: cloneSymbol(edge.dependency)
        })
    );
    return {
        declarations: [...declarationByKey.values()].sort(compareSymbol),
        edges: [...edgeByKey.values()].sort(compareEdge)
    };
};

const declarationImpacts = (
    declarations: readonly CoreLfDevelopmentDeclarationDiff[],
    graph: CoreLfDevelopmentDeclarationDependencyGraph
): readonly CoreLfDevelopmentDeclarationImpact[] => {
    const symbolByKey = new Map(graph.declarations.map(symbol =>
        [symbolKey(symbol), symbol] as const
    ));
    const dependents = new Map<string, Set<string>>();
    graph.edges.forEach(edge => {
        const key = symbolKey(edge.dependency);
        const current = dependents.get(key) ?? new Set<string>();
        current.add(symbolKey(edge.dependent));
        dependents.set(key, current);
    });
    return declarations
        .filter(declaration => declaration.state !== 'reusable')
        .map(declaration => {
            const sourceKey = symbolKey(declaration.symbol);
            const distances = new Map<string, number>();
            const pending = [...(dependents.get(sourceKey) ?? [])]
                .sort(compareText)
                .map(key => ({ key, distance: 1 }));
            while (pending.length > 0) {
                const next = pending.shift();
                if (next === undefined) break;
                if (next.key === sourceKey) continue;
                const known = distances.get(next.key);
                if (known !== undefined && known <= next.distance) continue;
                distances.set(next.key, next.distance);
                [...(dependents.get(next.key) ?? [])]
                    .sort(compareText)
                    .forEach(key => pending.push({
                        key,
                        distance: next.distance + 1
                    }));
            }
            const symbolsAt = (predicate: (distance: number) => boolean) =>
                [...distances.entries()]
                    .filter(([, distance]) => predicate(distance))
                    .map(([key]) => symbolByKey.get(key) ?? fail(
                        'DECLARATION_IDENTITY_DRIFT',
                        `declarationImpacts.${key}`,
                        'Dependency graph refers to an absent declaration'
                    ))
                    .map(cloneSymbol)
                    .sort(compareSymbol);
            return {
                source: cloneSymbol(declaration.symbol),
                sourceState: declaration.state as Exclude<
                    CoreLfDevelopmentDeclarationDiffState,
                    'reusable'
                >,
                directDependents: symbolsAt(distance => distance === 1),
                transitiveDependents: symbolsAt(distance => distance >= 2)
            };
        });
};

interface InternalProofRevision {
    readonly proof: CoreLfWorkspaceProofDocumentInput;
    readonly source: CoreLfDevelopmentProofSource;
    readonly closureModuleIds: readonly string[];
    readonly typeScan: RawStructuralScan;
    readonly planScan: RawStructuralScan;
    readonly dependencies: CoreLfDevelopmentDependencyEvidence;
}

const prepareProofRevisions = (
    proofs: readonly CoreLfWorkspaceProofDocumentInput[],
    workspace: CoreLfDeclarationWorkspaceSnapshot,
    links: LinkIndex,
    counter: VisitCounter,
    path: string
): ReadonlyMap<string, InternalProofRevision> => {
    const records = new Map<string, InternalProofRevision>();
    proofs.forEach((proof, index) => {
        let closure;
        try {
            closure = createCoreLfDeclarationWorkspaceClosureSnapshot(
                workspace,
                proof.moduleId
            );
        } catch (error: unknown) {
            fail(
                'UNKNOWN_PROOF_MODULE',
                `${path}[${index}].moduleId`,
                `Proof root '${proof.moduleId}' is absent from its revision`,
                error
            );
        }
        const key = proofKey(proof);
        if (records.has(key)) {
            fail(
                'DECLARATION_IDENTITY_DRIFT',
                `${path}[${index}]`,
                'Canonical proof identity is duplicated'
            );
        }
        const typeScan = scanExpressionRoots([{
            expression: proof.type,
            path: `${path}[${index}].type`
        }], counter);
        const planScan = scanExpressionRoots(
            proofPlanExpressionRoots(
                proof.plan,
                `${path}[${index}].plan`
            ),
            counter
        );
        const scan = mergeScans([typeScan, planScan]);
        records.set(key, {
            proof,
            source: {
                typeCanonicalJson: canonical(
                    proof.type,
                    `${path}[${index}].type`
                ),
                planCanonicalJson: canonical(
                    proof.plan,
                    `${path}[${index}].plan`
                ),
                provenanceCanonicalJson: canonical(
                    proof.provenance,
                    `${path}[${index}].provenance`
                ),
                fingerprintCanonicalJson: canonical(
                    proof.fingerprint,
                    `${path}[${index}].fingerprint`
                )
            },
            closureModuleIds: [...closure.order],
            typeScan,
            planScan,
            dependencies: resolveScan(scan, links, `${path}[${index}]`)
        });
    });
    return records;
};

const publicProofRevision = (
    proof: InternalProofRevision
): CoreLfDevelopmentProofRevision => ({
    source: proof.source,
    closureModuleIds: proof.closureModuleIds,
    expressionNodeCounts: {
        type: proof.typeScan.nodeCount,
        plan: proof.planScan.nodeCount
    },
    dependencies: proof.dependencies
});

const proofChangedFields = (
    previous: CoreLfDevelopmentProofSource,
    current: CoreLfDevelopmentProofSource
): readonly CoreLfDevelopmentProofChangedField[] => {
    const changed: CoreLfDevelopmentProofChangedField[] = [];
    if (previous.typeCanonicalJson !== current.typeCanonicalJson) {
        changed.push('type');
    }
    if (previous.planCanonicalJson !== current.planCanonicalJson) {
        changed.push('plan');
    }
    if (previous.provenanceCanonicalJson !== current.provenanceCanonicalJson) {
        changed.push('provenance');
    }
    if (previous.fingerprintCanonicalJson !== current.fingerprintCanonicalJson) {
        changed.push('fingerprint');
    }
    return changed;
};

const resolutionSortKey = (
    resolution: CoreLfDevelopmentReferenceResolution
): string => resolution.kind === 'free-reference'
    ? `0:${resolution.name}`
    : `1:${resolution.owner}`;

const moduleReasons = (
    previous: InternalProofRevision,
    current: InternalProofRevision,
    invalidation: CoreLfDeclarationWorkspaceInvalidation
): readonly CoreLfDevelopmentProofImpactReason[] => {
    const byId = new Map(invalidation.modules.map(module =>
        [module.moduleId, module] as const
    ));
    return [...new Set([
        ...previous.closureModuleIds,
        ...current.closureModuleIds
    ])].sort(compareText).flatMap(moduleId => {
        const module = byId.get(moduleId);
        if (module === undefined) {
            fail(
                'DECLARATION_IDENTITY_DRIFT',
                `proof.moduleClosure.${moduleId}`,
                'Proof closure module is absent from workspace invalidation'
            );
        }
        return module.state === 'reusable'
            ? []
            : [{
                kind: 'module-not-reusable' as const,
                moduleId,
                state: module.state
            }];
    });
};

const resolutionReasons = (
    side: 'previous' | 'current',
    proof: InternalProofRevision
): readonly CoreLfDevelopmentProofImpactReason[] => proof.dependencies
    .resolutions
    .filter(resolution => resolution.status !== 'resolved')
    .sort((left, right) => compareText(
        resolutionSortKey(left),
        resolutionSortKey(right)
    ))
    .map(reference => ({
        kind: 'reference-not-uniquely-resolved' as const,
        side,
        reference
    }));

const declarationImpactReasons = (
    previous: InternalProofRevision,
    current: InternalProofRevision,
    declarations: readonly CoreLfDevelopmentDeclarationDiff[],
    graph: CoreLfDevelopmentDeclarationDependencyGraph
): readonly CoreLfDevelopmentProofImpactReason[] => {
    const changed = new Map(
        declarations
            .filter(declaration =>
                declaration.state === 'changed' ||
                declaration.state === 'removed'
            )
            .map(declaration => [
                symbolKey(declaration.symbol),
                declaration
            ] as const)
    );
    if (changed.size === 0) return [];
    const dependencies = new Map<string, Set<string>>();
    graph.edges.forEach(edge => {
        const key = symbolKey(edge.dependent);
        const currentDependencies = dependencies.get(key) ?? new Set<string>();
        currentDependencies.add(symbolKey(edge.dependency));
        dependencies.set(key, currentDependencies);
    });
    const direct = new Map<string, CoreLfQualifiedSymbol>();
    [
        ...previous.dependencies.declarationDependencies,
        ...current.dependencies.declarationDependencies
    ].forEach(symbol => direct.set(symbolKey(symbol), symbol));
    const reasons: CoreLfDevelopmentProofImpactReason[] = [];
    [...direct.values()].sort(compareSymbol).forEach(directDependency => {
        const start = symbolKey(directDependency);
        const distances = new Map<string, number>([[start, 0]]);
        const pending = [start];
        while (pending.length > 0) {
            const dependent = pending.shift();
            if (dependent === undefined) break;
            const distance = distances.get(dependent) ?? 0;
            [...(dependencies.get(dependent) ?? [])]
                .sort(compareText)
                .forEach(dependency => {
                    if (distances.has(dependency)) return;
                    distances.set(dependency, distance + 1);
                    pending.push(dependency);
                });
        }
        [...distances.entries()]
            .filter(([key]) => changed.has(key))
            .sort(([left], [right]) => compareText(left, right))
            .forEach(([key, distance]) => {
                const declaration = changed.get(key);
                if (declaration === undefined) return;
                reasons.push({
                    kind: 'declaration-impacted',
                    declaration: cloneSymbol(declaration.symbol),
                    declarationState: declaration.state as
                        'changed' | 'removed',
                    relationship: distance === 0
                        ? 'direct'
                        : 'transitive',
                    directDependency: cloneSymbol(directDependency)
                });
            });
    });
    return reasons;
};

const diffProofs = (
    previous: ReadonlyMap<string, InternalProofRevision>,
    current: ReadonlyMap<string, InternalProofRevision>,
    declarations: readonly CoreLfDevelopmentDeclarationDiff[],
    graph: CoreLfDevelopmentDeclarationDependencyGraph,
    invalidation: CoreLfDeclarationWorkspaceInvalidation
): readonly CoreLfDevelopmentProofDiff[] => {
    const keys = [...new Set([
        ...previous.keys(),
        ...current.keys()
    ])].sort(compareText);
    return keys.map(key => {
        const before = previous.get(key);
        const after = current.get(key);
        const input = before?.proof ?? after?.proof ?? fail(
            'DECLARATION_IDENTITY_DRIFT',
            `proofs.${key}`,
            'Proof union contains no revision entry'
        );
        const proof = {
            moduleId: input.moduleId,
            declarationId: input.declarationId
        };
        if (before === undefined) {
            return {
                proof,
                state: 'added' as const,
                changedFields: [],
                reasons: [{ kind: 'proof-added' as const }],
                current: publicProofRevision(after as InternalProofRevision)
            };
        }
        if (after === undefined) {
            return {
                proof,
                state: 'removed' as const,
                changedFields: [],
                reasons: [{ kind: 'proof-removed' as const }],
                previous: publicProofRevision(before)
            };
        }
        const changedFields = proofChangedFields(before.source, after.source);
        if (changedFields.length > 0) {
            return {
                proof,
                state: 'source-changed' as const,
                changedFields,
                reasons: [{
                    kind: 'proof-source-changed' as const,
                    fields: changedFields
                }],
                previous: publicProofRevision(before),
                current: publicProofRevision(after)
            };
        }
        const reasons = [
            ...moduleReasons(before, after, invalidation),
            ...declarationImpactReasons(
                before,
                after,
                declarations,
                graph
            ),
            ...resolutionReasons('previous', before),
            ...resolutionReasons('current', after)
        ];
        return {
            proof,
            state: reasons.length === 0
                ? 'reusable' as const
                : 'recheck-required' as const,
            changedFields,
            reasons,
            previous: publicProofRevision(before),
            current: publicProofRevision(after)
        };
    });
};

const compileSourceRevision = (
    source: CoreLfProofDevelopmentSourceSnapshot,
    side: 'previous' | 'current'
) => {
    let reconstruction;
    try {
        reconstruction = reconstructCoreLfProofDevelopmentSourceSnapshot(
            source
        );
    } catch (error: unknown) {
        fail(
            side === 'previous'
                ? 'INVALID_PREVIOUS_SOURCE'
                : 'INVALID_CURRENT_SOURCE',
            side,
            `Cannot reconstruct ${side} canonical proof-development source: ` +
                errorText(error),
            error
        );
    }
    let workspace;
    try {
        workspace = compileCoreLfDeclarationWorkspace(
            reconstruction.plan.workspace
        );
    } catch (error: unknown) {
        fail(
            side === 'previous'
                ? 'PREVIOUS_DECLARATION_COMPILATION_FAILED'
                : 'CURRENT_DECLARATION_COMPILATION_FAILED',
            `${side}.workspace`,
            `Cannot compile ${side} declaration workspace: ${errorText(error)}`,
            error
        );
    }
    return { reconstruction, workspace };
};

const countState = <T extends { readonly state: string }>(
    entries: readonly T[],
    state: T['state']
): number => entries.filter(entry => entry.state === state).length;

/**
 * Compare two canonical development sources without compiling either proof.
 */
export function compareCoreLfProofDevelopmentSources(
    previousSource: CoreLfProofDevelopmentSourceSnapshot,
    currentSource: CoreLfProofDevelopmentSourceSnapshot,
    options: CoreLfDevelopmentDiffOptions = {}
): CoreLfDevelopmentSemanticDiffReport {
    const expressionVisitLimit = options.expressionVisitLimit ??
        CORE_LF_DEVELOPMENT_DIFF_PROFILE.defaultExpressionVisitLimit;
    if (
        !Number.isSafeInteger(expressionVisitLimit) ||
        expressionVisitLimit <= 0 ||
        expressionVisitLimit >
            CORE_LF_DEVELOPMENT_DIFF_PROFILE.maxExpressionVisitLimit
    ) {
        fail(
            'INVALID_EXPRESSION_VISIT_LIMIT',
            'options.expressionVisitLimit',
            'Expression visit limit must be a positive safe integer no ' +
                `greater than ` +
                CORE_LF_DEVELOPMENT_DIFF_PROFILE.maxExpressionVisitLimit
        );
    }

    const previousCompiled = compileSourceRevision(
        previousSource,
        'previous'
    );
    const currentCompiled = compileSourceRevision(
        currentSource,
        'current'
    );
    const counter: VisitCounter = {
        limit: expressionVisitLimit,
        visited: 0
    };
    const previous = prepareCompiledRevision(
        previousCompiled.workspace,
        counter,
        'previous.workspace'
    );
    const current = prepareCompiledRevision(
        currentCompiled.workspace,
        counter,
        'current.workspace'
    );
    const moduleInvalidation =
        compareCoreLfDeclarationWorkspaceSnapshots(
            previous.snapshot,
            current.snapshot
        );
    const declarations = diffDeclarations(previous, current);
    const previousGraph = dependencyGraph(previous.declarations);
    const currentGraph = dependencyGraph(current.declarations);
    const unionGraph = unionDependencyGraph(previousGraph, currentGraph);
    const impacts = declarationImpacts(declarations, unionGraph);
    const previousProofs = prepareProofRevisions(
        previousCompiled.reconstruction.snapshot.proofs,
        previous.snapshot,
        previous.links,
        counter,
        'previous.proofs'
    );
    const currentProofs = prepareProofRevisions(
        currentCompiled.reconstruction.snapshot.proofs,
        current.snapshot,
        current.links,
        counter,
        'current.proofs'
    );
    const proofs = diffProofs(
        previousProofs,
        currentProofs,
        declarations,
        unionGraph,
        moduleInvalidation
    );

    return deepFreeze({
        revision: CORE_LF_DEVELOPMENT_DIFF_PROFILE.reportRevision,
        profileRevision: CORE_LF_DEVELOPMENT_DIFF_PROFILE.revision,
        sourceProfileRevision:
            CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision,
        workspaceProfileRevision:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
        dependencyPolicy:
            CORE_LF_DEVELOPMENT_DIFF_PROFILE.dependencyPolicy,
        proofImpactPolicy:
            CORE_LF_DEVELOPMENT_DIFF_PROFILE.proofImpactPolicy,
        repairPolicy: CORE_LF_DEVELOPMENT_DIFF_PROFILE.repairPolicy,
        previous: {
            developmentRevision:
                previousCompiled.reconstruction.plan.revision,
            workspaceRevision:
                previousCompiled.reconstruction.plan.workspace.revision,
            moduleOrder: [...previous.snapshot.order]
        },
        current: {
            developmentRevision:
                currentCompiled.reconstruction.plan.revision,
            workspaceRevision:
                currentCompiled.reconstruction.plan.workspace.revision,
            moduleOrder: [...current.snapshot.order]
        },
        visitBudget: {
            expressionVisitLimit,
            expressionNodesVisited: counter.visited
        },
        moduleInvalidation,
        declarations,
        declarationDependencies: {
            previous: previousGraph,
            current: currentGraph,
            union: unionGraph
        },
        declarationImpacts: impacts,
        proofs,
        counts: {
            previousModules: previous.snapshot.modules.length,
            currentModules: current.snapshot.modules.length,
            previousDeclarations: previous.declarations.size,
            currentDeclarations: current.declarations.size,
            addedDeclarations: countState(declarations, 'added'),
            removedDeclarations: countState(declarations, 'removed'),
            changedDeclarations: countState(declarations, 'changed'),
            reusableDeclarations: countState(declarations, 'reusable'),
            previousDependencyEdges: previousGraph.edges.length,
            currentDependencyEdges: currentGraph.edges.length,
            unionDependencyEdges: unionGraph.edges.length,
            previousProofs: previousProofs.size,
            currentProofs: currentProofs.size,
            addedProofs: countState(proofs, 'added'),
            removedProofs: countState(proofs, 'removed'),
            sourceChangedProofs: countState(proofs, 'source-changed'),
            recheckRequiredProofs: countState(proofs, 'recheck-required'),
            reusableProofs: countState(proofs, 'reusable')
        },
        compilesProofs: false as const,
        executesIncrementally: false as const
    });
}

/** Canonical, exact-byte semantic-diff report representation. */
export const serializeCoreLfDevelopmentSemanticDiff = (
    report: CoreLfDevelopmentSemanticDiffReport
): string => serializeCoreLfWorkspaceCanonicalJson(
    report,
    'developmentSemanticDiff'
);
