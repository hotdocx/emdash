/**
 * Browser-safe catalogs for multi-module, multi-proof emdash developments.
 *
 * The catalog composes the existing declaration-workspace and exact-closure
 * proof-document owners. It adds no checker rule, proof-plan node, file or
 * hash authority, theorem-to-theorem import, or backend dependency.
 */

import {
    CoreProofPlanGoalSnapshot
} from './proof_plan';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE,
    CoreLfCompiledDeclarationWorkspace,
    CoreLfDeclarationWorkspacePlan,
    CoreLfDeclarationWorkspaceSnapshot,
    compileCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspaceSnapshot
} from './lf_workspace';
import {
    CORE_LF_WORKSPACE_PROOF_PROFILE,
    CoreLfWorkspaceProofArtifact,
    CoreLfWorkspaceProofCompilation,
    CoreLfWorkspaceProofDocumentInput,
    compileCoreLfWorkspaceProofDocument
} from './lf_workspace_proof';

export const CORE_LF_PROOF_DEVELOPMENT_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-development-v1' as const,
    artifactRevision:
        'emdash-lf-proof-development-artifact-v1' as const,
    workspaceProfileRevision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
    workspaceProofProfileRevision:
        CORE_LF_WORKSPACE_PROOF_PROFILE.revision,
    proofOrder: 'module-id-then-declaration-id' as const,
    theoremDependencyPolicy: 'independent-proof-leaves' as const,
    compilationPolicy:
        'compile-workspace-once-recheck-each-exact-closure' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const
});

export type CoreLfProofDevelopmentErrorCode =
    | 'INVALID_DEVELOPMENT'
    | 'INVALID_PROOF_ID'
    | 'DUPLICATE_PROOF'
    | 'UNKNOWN_PROOF_MODULE';

export class CoreLfProofDevelopmentError extends Error {
    constructor(
        public readonly code: CoreLfProofDevelopmentErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfProofDevelopmentError';
    }
}

const fail = (
    code: CoreLfProofDevelopmentErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfProofDevelopmentError(code, path, message);
};

const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SAFE_PROOF_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const compareProof = (
    left: CoreLfWorkspaceProofDocumentInput,
    right: CoreLfWorkspaceProofDocumentInput
): number => compareText(left.moduleId, right.moduleId) ||
    compareText(left.declarationId, right.declarationId);

const proofKey = (
    moduleId: string,
    declarationId: string
): string => `${moduleId}\u0000${declarationId}`;

export interface CoreLfProofDevelopmentInput {
    readonly revision: string;
    readonly workspace: CoreLfDeclarationWorkspacePlan;
    readonly proofs: readonly CoreLfWorkspaceProofDocumentInput[];
}

export interface CoreLfProofDevelopmentPlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly workspaceProfileRevision:
        typeof CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision;
    readonly workspaceProofProfileRevision:
        typeof CORE_LF_WORKSPACE_PROOF_PROFILE.revision;
    readonly workspace: CoreLfDeclarationWorkspacePlan;
    readonly proofs: readonly CoreLfWorkspaceProofDocumentInput[];
}

const assertProofId = (
    value: string,
    path: string
): void => {
    if (SAFE_PROOF_ID.test(value)) return;
    fail(
        'INVALID_PROOF_ID',
        path,
        `Proof identity '${value}' is not stable and portable`
    );
};

/** Validate and canonically order one inert proof-development plan. */
export function createCoreLfProofDevelopment(
    input: CoreLfProofDevelopmentInput
): CoreLfProofDevelopmentPlan {
    if (!SAFE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_DEVELOPMENT',
            'revision',
            `Invalid proof-development revision '${input.revision}'`
        );
    }
    if (
        input.workspace.profileRevision !==
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision
    ) {
        return fail(
            'INVALID_DEVELOPMENT',
            'workspace.profileRevision',
            'Proof development targets an unsupported workspace profile'
        );
    }
    if (input.proofs.length === 0) {
        return fail(
            'INVALID_DEVELOPMENT',
            'proofs',
            'A proof development requires at least one proof document'
        );
    }

    const moduleIds = new Set(input.workspace.modules.map(source =>
        source.module.moduleId
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
        profileRevision: CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision,
        workspaceProfileRevision:
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
        workspaceProofProfileRevision:
            CORE_LF_WORKSPACE_PROOF_PROFILE.revision,
        workspace: input.workspace,
        proofs
    });
}

export interface CoreLfProofDevelopmentArtifact {
    readonly revision:
        typeof CORE_LF_PROOF_DEVELOPMENT_PROFILE.artifactRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly developmentRevision: string;
    readonly status: 'complete' | 'incomplete';
    readonly openGoalCount: number;
    readonly workspace: CoreLfDeclarationWorkspaceSnapshot;
    readonly proofs: readonly CoreLfWorkspaceProofArtifact[];
}

export interface CoreLfProofDevelopmentGoal {
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goal: CoreProofPlanGoalSnapshot;
}

/** Process-local checked result; `artifact` is its portable projection. */
export class CoreLfCompiledProofDevelopment {
    readonly revision: string;
    readonly proofs: readonly CoreLfWorkspaceProofCompilation[];
    readonly goals: readonly CoreLfProofDevelopmentGoal[];

    constructor(
        public readonly plan: CoreLfProofDevelopmentPlan,
        public readonly workspace: CoreLfCompiledDeclarationWorkspace,
        proofs: readonly CoreLfWorkspaceProofCompilation[],
        public readonly artifact: CoreLfProofDevelopmentArtifact
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.proofs = Object.freeze([...proofs]);
        this.goals = Object.freeze(this.proofs.flatMap(compilation =>
            compilation.artifact.proofArtifact.state.goals.map(goal =>
                Object.freeze({
                    moduleId:
                        compilation.artifact.proofArtifact.moduleId,
                    declarationId:
                        compilation.artifact.proofArtifact.declarationId,
                    goal
                })
            )
        ));
        Object.freeze(this);
    }

    proof(
        moduleId: string,
        declarationId: string
    ): CoreLfWorkspaceProofCompilation | undefined {
        return this.proofs.find(compilation => {
            const proof = compilation.artifact.proofArtifact;
            return proof.moduleId === moduleId &&
                proof.declarationId === declarationId;
        });
    }
}

/** Compile every independent theorem against its exact checked closure. */
export function compileCoreLfProofDevelopment(
    plan: CoreLfProofDevelopmentPlan
): CoreLfCompiledProofDevelopment {
    if (
        plan.profileRevision !==
            CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision ||
        plan.workspaceProfileRevision !==
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision ||
        plan.workspaceProofProfileRevision !==
            CORE_LF_WORKSPACE_PROOF_PROFILE.revision
    ) {
        return fail(
            'INVALID_DEVELOPMENT',
            'profileRevision',
            'Proof-development plan targets an unsupported profile'
        );
    }
    const canonical = createCoreLfProofDevelopment({
        revision: plan.revision,
        workspace: plan.workspace,
        proofs: plan.proofs
    });
    const workspace = compileCoreLfDeclarationWorkspace(
        canonical.workspace
    );
    const proofs = Object.freeze(canonical.proofs.map(proof =>
        compileCoreLfWorkspaceProofDocument(workspace, proof)
    ));
    const proofArtifacts = Object.freeze(proofs.map(proof =>
        proof.artifact
    ));
    const openGoalCount = proofArtifacts.reduce(
        (count, proof) => count +
            proof.proofArtifact.state.goals.length,
        0
    );
    const artifact: CoreLfProofDevelopmentArtifact = Object.freeze({
        revision: CORE_LF_PROOF_DEVELOPMENT_PROFILE.artifactRevision,
        profileRevision: CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision,
        developmentRevision: canonical.revision,
        status: openGoalCount === 0 ? 'complete' : 'incomplete',
        openGoalCount,
        workspace: createCoreLfDeclarationWorkspaceSnapshot(workspace),
        proofs: proofArtifacts
    });
    return new CoreLfCompiledProofDevelopment(
        canonical,
        workspace,
        proofs,
        artifact
    );
}

/** Deterministic, diff-friendly portable development artifact. */
export const serializeCoreLfProofDevelopmentArtifact = (
    artifact: CoreLfProofDevelopmentArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;
