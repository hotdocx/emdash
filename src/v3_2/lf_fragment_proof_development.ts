/**
 * Browser-safe catalogs for multi-proof mixed-fragment developments.
 *
 * The catalog owns ordering, identity, aggregate status, and portable
 * projection only. Every proof is freshly replayed by the exact runtime-
 * closure proof owner; no theorem becomes an implicit premise of another.
 */

import {
    CoreProofPlanGoalSnapshot
} from './proof_plan';
import {
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE,
    CoreLfCompiledFragmentModuleWorkspace,
    CoreLfFragmentModuleWorkspacePlan,
    CoreLfFragmentModuleWorkspaceSourceSnapshot,
    compileCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSourceSnapshot
} from './lf_fragment_module_workspace';
import {
    CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE,
    CoreLfFragmentWorkspaceProofArtifact,
    CoreLfFragmentWorkspaceProofCompilation,
    CoreLfFragmentWorkspaceProofDocumentInput,
    compileCoreLfFragmentWorkspaceProofDocument
} from './lf_fragment_workspace_proof';

export const CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE = Object.freeze({
    revision: 'emdash-lf-fragment-proof-development-v1' as const,
    artifactRevision:
        'emdash-lf-fragment-proof-development-artifact-v1' as const,
    workspaceProfileRevision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
    workspaceProofProfileRevision:
        CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision,
    proofOrder: 'module-id-then-declaration-id' as const,
    theoremDependencyPolicy: 'independent-proof-leaves' as const,
    compilationPolicy:
        'compile-fragment-workspace-once-replay-each-exact-runtime-closure' as
            const,
    supportsRuntimeFragments: true as const,
    acceptsRuntimeInput: false as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const
});

export const serializeCoreLfFragmentProofDevelopmentProfile = (): string =>
    `${JSON.stringify(CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE, null, 2)}\n`;

export type CoreLfFragmentProofDevelopmentErrorCode =
    | 'INVALID_DEVELOPMENT'
    | 'INVALID_PROOF_ID'
    | 'DUPLICATE_PROOF'
    | 'UNKNOWN_PROOF_MODULE';

export class CoreLfFragmentProofDevelopmentError extends Error {
    constructor(
        public readonly code: CoreLfFragmentProofDevelopmentErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfFragmentProofDevelopmentError';
    }
}

const fail = (
    code: CoreLfFragmentProofDevelopmentErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfFragmentProofDevelopmentError(code, path, message);
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

const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SAFE_PROOF_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const compareProof = (
    left: CoreLfFragmentWorkspaceProofDocumentInput,
    right: CoreLfFragmentWorkspaceProofDocumentInput
): number => compareText(left.moduleId, right.moduleId) ||
    compareText(left.declarationId, right.declarationId);

const proofKey = (
    moduleId: string,
    declarationId: string
): string => `${moduleId}\u0000${declarationId}`;

const assertProofId = (value: string, path: string): void => {
    if (SAFE_PROOF_ID.test(value)) return;
    fail(
        'INVALID_PROOF_ID',
        path,
        `Proof identity '${value}' is not stable and portable`
    );
};

export interface CoreLfFragmentProofDevelopmentInput {
    readonly revision: string;
    readonly workspace: CoreLfFragmentModuleWorkspacePlan;
    readonly proofs:
        readonly CoreLfFragmentWorkspaceProofDocumentInput[];
}

export interface CoreLfFragmentProofDevelopmentPlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly workspaceProfileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly workspaceProofProfileRevision:
        typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision;
    readonly workspace: CoreLfFragmentModuleWorkspacePlan;
    readonly proofs:
        readonly CoreLfFragmentWorkspaceProofDocumentInput[];
}

/** Validate and canonically order one inert runtime-proof development. */
export function createCoreLfFragmentProofDevelopment(
    input: CoreLfFragmentProofDevelopmentInput
): CoreLfFragmentProofDevelopmentPlan {
    if (!SAFE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_DEVELOPMENT',
            'revision',
            `Invalid fragment proof-development revision '${input.revision}'`
        );
    }
    if (
        input.workspace.profileRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision
    ) {
        return fail(
            'INVALID_DEVELOPMENT',
            'workspace.profileRevision',
            'Fragment proof development targets an unsupported workspace'
        );
    }
    if (input.proofs.length === 0) {
        return fail(
            'INVALID_DEVELOPMENT',
            'proofs',
            'A fragment proof development requires at least one proof'
        );
    }

    const workspace = createCoreLfFragmentModuleWorkspace({
        revision: input.workspace.revision,
        modules: input.workspace.modules
    });
    const moduleIds = new Set(workspace.modules.map(module =>
        module.identity.moduleId
    ));
    const seen = new Set<string>();
    const proofs = Object.freeze([...input.proofs]
        .sort(compareProof)
        .map((proof, index) => {
            assertProofId(proof.moduleId, `proofs[${index}].moduleId`);
            assertProofId(
                proof.declarationId,
                `proofs[${index}].declarationId`
            );
            if (!moduleIds.has(proof.moduleId)) {
                return fail(
                    'UNKNOWN_PROOF_MODULE',
                    `proofs[${index}].moduleId`,
                    `Proof '${proof.declarationId}' names absent module ` +
                        `'${proof.moduleId}'`
                );
            }
            const key = proofKey(proof.moduleId, proof.declarationId);
            if (seen.has(key)) {
                return fail(
                    'DUPLICATE_PROOF',
                    `proofs[${index}]`,
                    `Duplicate proof '${proof.moduleId}.` +
                        `${proof.declarationId}'`
                );
            }
            seen.add(key);
            return Object.freeze({ ...proof });
        }));

    return Object.freeze({
        revision: input.revision,
        profileRevision:
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision,
        workspaceProfileRevision:
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
        workspaceProofProfileRevision:
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision,
        workspace,
        proofs
    });
}

export interface CoreLfFragmentProofDevelopmentArtifact {
    readonly revision:
        typeof CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.artifactRevision;
    readonly profileRevision:
        typeof CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly developmentRevision: string;
    readonly status: 'complete' | 'incomplete';
    readonly openGoalCount: number;
    readonly workspace: CoreLfFragmentModuleWorkspaceSourceSnapshot;
    readonly proofs: readonly CoreLfFragmentWorkspaceProofArtifact[];
}

export interface CoreLfFragmentProofDevelopmentGoal {
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goal: CoreProofPlanGoalSnapshot;
}

/** Process-local checked result; `artifact` is its portable projection. */
export class CoreLfCompiledFragmentProofDevelopment {
    readonly revision: string;
    readonly proofs:
        readonly CoreLfFragmentWorkspaceProofCompilation[];
    readonly goals: readonly CoreLfFragmentProofDevelopmentGoal[];

    constructor(
        public readonly plan: CoreLfFragmentProofDevelopmentPlan,
        public readonly workspace: CoreLfCompiledFragmentModuleWorkspace,
        proofs: readonly CoreLfFragmentWorkspaceProofCompilation[],
        public readonly artifact: CoreLfFragmentProofDevelopmentArtifact
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.proofs = Object.freeze([...proofs]);
        this.goals = Object.freeze(this.proofs.flatMap(compilation =>
            compilation.artifact.state.goals.map(goal => Object.freeze({
                moduleId: compilation.artifact.moduleId,
                declarationId: compilation.artifact.declarationId,
                goal
            }))
        ));
        Object.freeze(this);
    }

    proof(
        moduleId: string,
        declarationId: string
    ): CoreLfFragmentWorkspaceProofCompilation | undefined {
        return this.proofs.find(compilation =>
            compilation.artifact.moduleId === moduleId &&
            compilation.artifact.declarationId === declarationId
        );
    }
}

/** Compile the workspace once and freshly replay every independent proof. */
export function compileCoreLfFragmentProofDevelopment(
    plan: CoreLfFragmentProofDevelopmentPlan
): CoreLfCompiledFragmentProofDevelopment {
    if (
        plan.profileRevision !==
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision ||
        plan.workspaceProfileRevision !==
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision ||
        plan.workspaceProofProfileRevision !==
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision
    ) {
        return fail(
            'INVALID_DEVELOPMENT',
            'profileRevision',
            'Fragment proof-development plan targets an unsupported profile'
        );
    }
    const canonical = createCoreLfFragmentProofDevelopment({
        revision: plan.revision,
        workspace: plan.workspace,
        proofs: plan.proofs
    });
    const workspace = compileCoreLfFragmentModuleWorkspace(
        canonical.workspace
    );
    const proofs = Object.freeze(canonical.proofs.map(proof =>
        compileCoreLfFragmentWorkspaceProofDocument(workspace, proof)
    ));
    const proofArtifacts = Object.freeze(proofs.map(proof =>
        proof.artifact
    ));
    const openGoalCount = proofArtifacts.reduce(
        (count, proof) => count + proof.state.goals.length,
        0
    );
    const artifact: CoreLfFragmentProofDevelopmentArtifact = deepFreeze({
        revision:
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.artifactRevision,
        profileRevision:
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision,
        developmentRevision: canonical.revision,
        status: openGoalCount === 0 ? 'complete' : 'incomplete',
        openGoalCount,
        workspace: createCoreLfFragmentModuleWorkspaceSourceSnapshot(
            workspace.plan
        ),
        proofs: proofArtifacts
    });
    return new CoreLfCompiledFragmentProofDevelopment(
        canonical,
        workspace,
        proofs,
        artifact
    );
}

/** Deterministic, diff-friendly portable development artifact. */
export const serializeCoreLfFragmentProofDevelopmentArtifact = (
    artifact: CoreLfFragmentProofDevelopmentArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;
