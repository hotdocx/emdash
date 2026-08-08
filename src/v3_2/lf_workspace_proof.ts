/**
 * Fresh proof attachment to one exact checked LF declaration closure.
 *
 * The accumulated workspace environment can contain unrelated modules that
 * happened to compile earlier. This layer therefore reconstructs and checks
 * exactly the selected module's dependency closure before delegating proof
 * execution to the existing AI proof-document compiler.
 *
 * Hash computation, filesystem access, remote loading, runtime fragments,
 * and cache writes remain explicit outer or later boundaries.
 */

import {
    KernelExpression,
    Provenance
} from './kernel';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE,
    CoreLfCompiledDeclarationWorkspace,
    CoreLfDeclarationWorkspaceClosureSnapshot,
    compileCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspaceClosureSnapshot,
    createCoreLfDeclarationWorkspaceSnapshot,
    serializeCoreLfDeclarationWorkspaceClosure
} from './lf_workspace';
import {
    CORE_PROOF_DOCUMENT_PROFILE,
    CoreProofArtifact,
    CoreProofArtifactFingerprint,
    CoreProofDocumentCompilation,
    compileCoreProofDocument,
    validateCoreProofArtifactFingerprint
} from './proof_document';
import {
    CoreProofPlan
} from './proof_plan';

export const CORE_LF_WORKSPACE_PROOF_PROFILE = Object.freeze({
    revision: 'emdash-lf-workspace-proof-v1' as const,
    compilerRevision: 'emdash-lf-workspace-proof-compiler-v1' as const,
    artifactRevision: 'emdash-lf-workspace-proof-artifact-v1' as const,
    workspaceProfileRevision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
    proofProfileRevision: CORE_PROOF_DOCUMENT_PROFILE.revision,
    checker: CORE_PROOF_DOCUMENT_PROFILE.checker,
    closurePolicy: 'recompile-exact-transitive-closure' as const,
    fingerprintPolicy: 'exact-closure-module-set' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    executesIncrementally: false as const,
    supportsRuntimeFragments: false as const
});

export const serializeCoreLfWorkspaceProofProfile = (): string =>
    `${JSON.stringify(CORE_LF_WORKSPACE_PROOF_PROFILE, null, 2)}\n`;

export type CoreLfWorkspaceProofErrorCode =
    | 'INVALID_COMPILED_WORKSPACE'
    | 'CLOSURE_DRIFT'
    | 'FINGERPRINT_CLOSURE_MISMATCH';

export class CoreLfWorkspaceProofError extends Error {
    constructor(
        public readonly code: CoreLfWorkspaceProofErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfWorkspaceProofError';
    }
}

const fail = (
    code: CoreLfWorkspaceProofErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfWorkspaceProofError(code, path, message);
};

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const sameTextArray = (
    left: readonly string[],
    right: readonly string[]
): boolean => left.length === right.length &&
    left.every((entry, index) => entry === right[index]);

export interface CoreLfWorkspaceProofDocumentInput {
    /** Existing declaration-workspace module that owns this proof. */
    readonly moduleId: string;
    readonly declarationId: string;
    readonly type: KernelExpression;
    readonly plan: CoreProofPlan;
    readonly provenance: Provenance;
    /**
     * Caller-supplied stamps whose module IDs must cover the exact closure.
     * This browser-safe layer validates but does not compute the hashes.
     */
    readonly fingerprint: CoreProofArtifactFingerprint;
}

export interface CoreLfWorkspaceProofArtifact {
    readonly revision:
        typeof CORE_LF_WORKSPACE_PROOF_PROFILE.artifactRevision;
    readonly compilerRevision:
        typeof CORE_LF_WORKSPACE_PROOF_PROFILE.compilerRevision;
    readonly workspaceRevision: string;
    readonly rootModuleId: string;
    readonly closure: CoreLfDeclarationWorkspaceClosureSnapshot;
    readonly closureText: string;
    readonly proofArtifact: CoreProofArtifact;
}

export interface CoreLfWorkspaceProofCompilation {
    /** Portable, deterministic result. */
    readonly artifact: CoreLfWorkspaceProofArtifact;
    /** Process-local closure reconstruction; never part of the artifact. */
    readonly closureCompilation: CoreLfCompiledDeclarationWorkspace;
    /** Process-local checked term authority when the proof is complete. */
    readonly proofCompilation: CoreProofDocumentCompilation;
}

interface RecompiledClosure {
    readonly snapshot: CoreLfDeclarationWorkspaceClosureSnapshot;
    readonly text: string;
    readonly compilation: CoreLfCompiledDeclarationWorkspace;
}

const recompileExactClosure = (
    workspace: CoreLfCompiledDeclarationWorkspace,
    rootModuleId: string
): RecompiledClosure => {
    const workspaceSnapshot =
        createCoreLfDeclarationWorkspaceSnapshot(workspace);
    const closure = createCoreLfDeclarationWorkspaceClosureSnapshot(
        workspaceSnapshot,
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
        revision: `${workspace.plan.revision}+proof-closure-1`,
        modules: sources
    });
    if (!sameTextArray(plan.order, closure.order)) {
        return fail(
            'CLOSURE_DRIFT',
            'closure.order',
            'Reconstructed closure has a different canonical module order'
        );
    }
    const compilation = compileCoreLfDeclarationWorkspace(plan);

    closure.order.forEach((moduleId, index) => {
        const original = workspace.module(moduleId);
        const reconstructed = compilation.module(moduleId);
        if (original === undefined || reconstructed === undefined) {
            fail(
                'INVALID_COMPILED_WORKSPACE',
                `closure.order[${index}]`,
                `Compiled workspace has no executable module '${moduleId}'`
            );
        }
        if (original.sourceText !== reconstructed.sourceText) {
            fail(
                'CLOSURE_DRIFT',
                `closure.modules[${index}].source`,
                `Reconstructed source for '${moduleId}' differs from the ` +
                    'compiled workspace'
            );
        }
        if (original.interfaceText !== reconstructed.interfaceText) {
            fail(
                'CLOSURE_DRIFT',
                `closure.modules[${index}].interface`,
                `Reconstructed interface for '${moduleId}' differs from the ` +
                    'compiled workspace'
            );
        }
    });

    return Object.freeze({
        snapshot: closure,
        text: serializeCoreLfDeclarationWorkspaceClosure(closure),
        compilation
    });
};

const validateFingerprintClosure = (
    fingerprint: CoreProofArtifactFingerprint,
    closure: CoreLfDeclarationWorkspaceClosureSnapshot
): CoreProofArtifactFingerprint => {
    const canonical = validateCoreProofArtifactFingerprint(fingerprint);
    const expected = [...closure.order].sort(compareText);
    const actual = canonical.dependencies.map(entry => entry.moduleId);
    if (!sameTextArray(actual, expected)) {
        return fail(
            'FINGERPRINT_CLOSURE_MISMATCH',
            'fingerprint.dependencies',
            `Proof fingerprint modules [${actual.join(', ')}] do not equal ` +
                `the exact closure [${expected.join(', ')}]`
        );
    }
    return canonical;
};

/**
 * Reconstruct an exact module closure and compile one fresh proof within it.
 */
export function compileCoreLfWorkspaceProofDocument(
    workspace: CoreLfCompiledDeclarationWorkspace,
    input: CoreLfWorkspaceProofDocumentInput
): CoreLfWorkspaceProofCompilation {
    const closure = recompileExactClosure(workspace, input.moduleId);
    const fingerprint = validateFingerprintClosure(
        input.fingerprint,
        closure.snapshot
    );
    const root = closure.compilation.module(input.moduleId);
    if (root === undefined) {
        return fail(
            'INVALID_COMPILED_WORKSPACE',
            'moduleId',
            `Reconstructed closure has no root module '${input.moduleId}'`
        );
    }
    const proofCompilation = compileCoreProofDocument({
        moduleId: input.moduleId,
        declarationId: input.declarationId,
        environment: root.compiled.environment.coreEnvironment,
        type: input.type,
        plan: input.plan,
        provenance: input.provenance,
        fingerprint
    });
    const artifact: CoreLfWorkspaceProofArtifact = Object.freeze({
        revision: CORE_LF_WORKSPACE_PROOF_PROFILE.artifactRevision,
        compilerRevision: CORE_LF_WORKSPACE_PROOF_PROFILE.compilerRevision,
        workspaceRevision: workspace.plan.revision,
        rootModuleId: input.moduleId,
        closure: closure.snapshot,
        closureText: closure.text,
        proofArtifact: proofCompilation.artifact
    });
    return Object.freeze({
        artifact,
        closureCompilation: closure.compilation,
        proofCompilation
    });
}

export const serializeCoreLfWorkspaceProofArtifact = (
    artifact: CoreLfWorkspaceProofArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;
