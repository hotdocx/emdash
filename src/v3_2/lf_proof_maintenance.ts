/**
 * Browser-safe selected-proof diagnostics and open-hole repair proposals.
 *
 * This layer composes exact two-revision impact, fresh exact-closure proof
 * replay, accessible-premise indexing, and the bounded obvious-proof provider.
 * It never resumes a failed process-local cursor and never persists patched
 * source without an outer fingerprint/revision owner.
 */

import {
    CoreCheckerError
} from './checker';
import {
    CoreContextError
} from './context';
import {
    CoreLfConversionError
} from './lf_conversion';
import {
    CORE_LF_DEVELOPMENT_DIFF_PROFILE,
    CoreLfDevelopmentDiffOptions,
    CoreLfDevelopmentProofDiff,
    CoreLfDevelopmentSemanticDiffReport,
    compareCoreLfProofDevelopmentSources,
    serializeCoreLfDevelopmentSemanticDiff
} from './lf_development_diff';
import {
    CoreLfPremiseIndexOptions,
    CoreLfPremiseIndexSettings,
    CORE_LF_PREMISE_INDEX_PROFILE,
    createCoreLfAccessiblePremiseIndex
} from './lf_premise_index';
import {
    CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE,
    CoreLfProofDevelopmentSourceSnapshot,
    reconstructCoreLfProofDevelopmentSourceSnapshot,
    serializeCoreLfProofDevelopmentSourceSnapshot
} from './lf_proof_development_source';
import {
    compileCoreLfDeclarationWorkspace,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreLfWorkspaceProofArtifact,
    CoreLfWorkspaceProofCompilation,
    CoreLfWorkspaceProofDocumentInput,
    CoreLfWorkspaceProofError,
    compileCoreLfWorkspaceProofDocument
} from './lf_workspace_proof';
import {
    Provenance
} from './kernel';
import {
    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
    CoreObviousProofBudgetOptions,
    CoreObviousProofCandidateReplay,
    CoreObviousProofProposalReport,
    proposeCoreObviousProofPlanPatches,
    replayCoreObviousProofCandidate
} from './proof_obvious';
import {
    CoreProofRefinementError
} from './proof';
import {
    CoreProofArtifactError
} from './proof_document';
import {
    CoreProofGoalCouplingGraph
} from './proof_goal_graph';
import {
    CoreProofPlan,
    CoreProofPlanError,
    CoreProofPlanExecution,
    CoreProofPlanProvenanceSnapshot,
    CoreProofPlanStateSnapshot
} from './proof_plan';
import {
    CORE_PROOF_PLAN_PATCH_PROFILE,
    CoreProofPlanPatch
} from './proof_plan_patch';
import {
    CoreSessionError
} from './session';

export const CORE_LF_PROOF_MAINTENANCE_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-maintenance-v1' as const,
    inspectionRevision: 'emdash-lf-proof-maintenance-inspection-v1' as const,
    proposalRevision: 'emdash-lf-proof-repair-proposal-v1' as const,
    preconditionRevision:
        'emdash-lf-proof-repair-precondition-v1' as const,
    replayRevision: 'emdash-lf-proof-repair-replay-v1' as const,
    semanticDiffProfileRevision:
        CORE_LF_DEVELOPMENT_DIFF_PROFILE.revision,
    sourceProfileRevision:
        CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision,
    providerRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
    patchRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
    selectionPolicy: 'exact-one-stable-proof-identity' as const,
    repairPolicy: 'freshly-replayed-named-hole-only' as const,
    diagnosticPolicy: 'stable-structured-fields-no-message' as const,
    materializesUpdatedSource: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const,
    retainsSessionState: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export interface CoreLfProofMaintenanceIdentity {
    readonly moduleId: string;
    readonly declarationId: string;
}

export interface CoreLfProofMaintenanceInspectionInput {
    readonly previousSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly currentSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly proof: CoreLfProofMaintenanceIdentity;
    readonly diffOptions?: CoreLfDevelopmentDiffOptions;
}

export type CoreLfProofMaintenanceErrorCode =
    | 'INVALID_INPUT'
    | 'UNKNOWN_PROOF'
    | 'UNSUPPORTED_REPLAY_ERROR'
    | 'PROOF_NOT_REPAIRABLE'
    | 'GOAL_NOT_OPEN'
    | 'PROVIDER_FAILED'
    | 'INVALID_PROPOSAL'
    | 'INVALID_CANDIDATE_INDEX'
    | 'STALE_PROPOSAL'
    | 'CANDIDATE_REPLAY_FAILED';

export class CoreLfProofMaintenanceError extends Error {
    constructor(
        public readonly code: CoreLfProofMaintenanceErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfProofMaintenanceError';
    }
}

const fail = (
    code: CoreLfProofMaintenanceErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreLfProofMaintenanceError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_GOAL_ID = /^[A-Za-z][A-Za-z0-9._-]*$/u;

const assertIdentity = (
    proof: CoreLfProofMaintenanceIdentity,
    path: string
): void => {
    if (
        proof === null ||
        typeof proof !== 'object' ||
        typeof proof.moduleId !== 'string' ||
        !SAFE_ID.test(proof.moduleId) ||
        typeof proof.declarationId !== 'string' ||
        !SAFE_ID.test(proof.declarationId)
    ) {
        fail(
            'INVALID_INPUT',
            path,
            'Proof selection requires one stable module/declaration identity'
        );
    }
};

const assertGoalId = (goalId: string, path: string): void => {
    if (typeof goalId === 'string' && SAFE_GOAL_ID.test(goalId)) return;
    fail(
        'INVALID_INPUT',
        path,
        'Proof repair requires one stable current source goal ID'
    );
};

const sameProof = (
    left: CoreLfProofMaintenanceIdentity,
    right: CoreLfProofMaintenanceIdentity
): boolean => left.moduleId === right.moduleId &&
    left.declarationId === right.declarationId;

const cloneIdentity = (
    proof: CoreLfProofMaintenanceIdentity
): CoreLfProofMaintenanceIdentity => ({
    moduleId: proof.moduleId,
    declarationId: proof.declarationId
});

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

/** Strip only absent optional data fields from reviewed portable owner output. */
const freezePortable = <T>(value: T, path: string): T => {
    let text: string | undefined;
    try {
        text = JSON.stringify(value);
    } catch (error: unknown) {
        return fail(
            'INVALID_INPUT',
            path,
            'Portable proof-maintenance data cannot be serialized',
            error
        );
    }
    if (text === undefined) {
        return fail(
            'INVALID_INPUT',
            path,
            'Portable proof-maintenance data cannot be undefined'
        );
    }
    const projected = JSON.parse(text) as T;
    serializeCoreLfWorkspaceCanonicalJson(projected, path);
    return deepFreeze(projected);
};

const canonical = (value: unknown, path: string): string =>
    serializeCoreLfWorkspaceCanonicalJson(value, path);

const snapshotProvenance = (
    source: Provenance
): CoreProofPlanProvenanceSnapshot => ({
    origin: source.origin,
    detail: source.detail,
    ...(source.span === undefined
        ? {}
        : {
            span: {
                file: source.span.file,
                start: { ...source.span.start },
                end: { ...source.span.end }
            }
        })
});

interface CoreLfProofReplayDiagnosticBase {
    readonly code: string;
}

export interface CoreLfProofReplayPathDiagnostic
extends CoreLfProofReplayDiagnosticBase {
    readonly family: 'workspace-proof' | 'proof-artifact';
    readonly path: string;
}

export interface CoreLfProofReplayPlanDiagnostic
extends CoreLfProofReplayDiagnosticBase {
    readonly family: 'proof-plan';
    readonly nodeId: string;
    readonly provenance: CoreProofPlanProvenanceSnapshot;
}

export interface CoreLfProofReplayProvenanceDiagnostic
extends CoreLfProofReplayDiagnosticBase {
    readonly family:
        | 'proof-refinement'
        | 'checker'
        | 'context'
        | 'session';
    readonly provenance: CoreProofPlanProvenanceSnapshot;
}

export interface CoreLfProofReplayConversionDiagnostic
extends CoreLfProofReplayDiagnosticBase {
    readonly family: 'lf-conversion';
}

export type CoreLfProofReplayDiagnostic =
    | CoreLfProofReplayPathDiagnostic
    | CoreLfProofReplayPlanDiagnostic
    | CoreLfProofReplayProvenanceDiagnostic
    | CoreLfProofReplayConversionDiagnostic;

const replayDiagnostic = (
    error: unknown
): CoreLfProofReplayDiagnostic | undefined => {
    if (error instanceof CoreLfWorkspaceProofError) {
        return {
            family: 'workspace-proof',
            code: error.code,
            path: error.path
        };
    }
    if (error instanceof CoreProofArtifactError) {
        return {
            family: 'proof-artifact',
            code: error.code,
            path: error.path
        };
    }
    if (error instanceof CoreProofPlanError) {
        return {
            family: 'proof-plan',
            code: error.code,
            nodeId: error.nodeId,
            provenance: snapshotProvenance(error.provenance)
        };
    }
    if (error instanceof CoreProofRefinementError) {
        return {
            family: 'proof-refinement',
            code: error.code,
            provenance: snapshotProvenance(error.provenance)
        };
    }
    if (error instanceof CoreCheckerError) {
        return {
            family: 'checker',
            code: error.code,
            provenance: snapshotProvenance(error.provenance)
        };
    }
    if (error instanceof CoreContextError) {
        return {
            family: 'context',
            code: error.code,
            provenance: snapshotProvenance(error.provenance)
        };
    }
    if (error instanceof CoreSessionError) {
        return {
            family: 'session',
            code: error.code,
            provenance: snapshotProvenance(error.provenance)
        };
    }
    if (error instanceof CoreLfConversionError) {
        return {
            family: 'lf-conversion',
            code: error.code
        };
    }
    return undefined;
};

interface CoreLfProofMaintenanceInspectionBase {
    readonly revision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.inspectionRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.revision;
    readonly proof: CoreLfProofMaintenanceIdentity;
    readonly impact: CoreLfDevelopmentProofDiff;
    readonly semanticDiff: CoreLfDevelopmentSemanticDiffReport;
    readonly compilesCompleteDevelopment: false;
}

export interface CoreLfProofMaintenanceAbsentInspection
extends CoreLfProofMaintenanceInspectionBase {
    readonly outcome: 'absent-current';
}

export interface CoreLfProofMaintenanceCheckedInspection
extends CoreLfProofMaintenanceInspectionBase {
    readonly outcome: 'checked-complete' | 'checked-incomplete';
    readonly artifact: CoreLfWorkspaceProofArtifact;
    readonly goalGraph: CoreProofGoalCouplingGraph;
}

export interface CoreLfProofMaintenanceRejectedInspection
extends CoreLfProofMaintenanceInspectionBase {
    readonly outcome: 'rejected';
    readonly diagnostic: CoreLfProofReplayDiagnostic;
}

export type CoreLfProofMaintenanceInspection =
    | CoreLfProofMaintenanceAbsentInspection
    | CoreLfProofMaintenanceCheckedInspection
    | CoreLfProofMaintenanceRejectedInspection;

interface PreparedMaintenance {
    readonly inspection: CoreLfProofMaintenanceInspection;
    readonly currentProof?: CoreLfWorkspaceProofDocumentInput;
    readonly currentWorkspace: ReturnType<
        typeof compileCoreLfDeclarationWorkspace
    >;
    readonly proofCompilation?: CoreLfWorkspaceProofCompilation;
}

const selectedImpact = (
    semanticDiff: CoreLfDevelopmentSemanticDiffReport,
    proof: CoreLfProofMaintenanceIdentity
): CoreLfDevelopmentProofDiff => semanticDiff.proofs.find(candidate =>
    sameProof(candidate.proof, proof)
) ?? fail(
    'UNKNOWN_PROOF',
    'proof',
    `Neither revision contains proof '${proof.moduleId}.` +
        `${proof.declarationId}'`
);

const inspectionBase = (
    proof: CoreLfProofMaintenanceIdentity,
    impact: CoreLfDevelopmentProofDiff,
    semanticDiff: CoreLfDevelopmentSemanticDiffReport
): CoreLfProofMaintenanceInspectionBase => ({
    revision: CORE_LF_PROOF_MAINTENANCE_PROFILE.inspectionRevision,
    profileRevision: CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
    proof: cloneIdentity(proof),
    impact,
    semanticDiff,
    compilesCompleteDevelopment: false as const
});

const prepareMaintenance = (
    input: CoreLfProofMaintenanceInspectionInput
): PreparedMaintenance => {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_INPUT',
            'input',
            'Proof maintenance input must be a data record'
        );
    }
    assertIdentity(input.proof, 'proof');
    const semanticDiff = compareCoreLfProofDevelopmentSources(
        input.previousSource,
        input.currentSource,
        input.diffOptions
    );
    const impact = selectedImpact(semanticDiff, input.proof);
    const current = reconstructCoreLfProofDevelopmentSourceSnapshot(
        input.currentSource
    );
    const currentWorkspace = compileCoreLfDeclarationWorkspace(
        current.plan.workspace
    );
    const currentProof = current.plan.proofs.find(proof =>
        sameProof(proof, input.proof)
    );
    const base = inspectionBase(input.proof, impact, semanticDiff);
    if (currentProof === undefined) {
        return {
            inspection: freezePortable({
                ...base,
                outcome: 'absent-current' as const
            }, 'proofMaintenanceInspection'),
            currentWorkspace
        };
    }

    let proofCompilation: CoreLfWorkspaceProofCompilation;
    try {
        proofCompilation = compileCoreLfWorkspaceProofDocument(
            currentWorkspace,
            currentProof
        );
    } catch (error: unknown) {
        const diagnostic = replayDiagnostic(error);
        if (diagnostic === undefined) {
            return fail(
                'UNSUPPORTED_REPLAY_ERROR',
                'currentProof',
                'Selected proof replay raised an unclassified error',
                error
            );
        }
        return {
            inspection: freezePortable({
                ...base,
                outcome: 'rejected' as const,
                diagnostic
            }, 'proofMaintenanceInspection'),
            currentProof,
            currentWorkspace
        };
    }
    const state = proofCompilation.artifact.proofArtifact.state;
    return {
        inspection: freezePortable({
            ...base,
            outcome: state.status === 'complete'
                ? 'checked-complete' as const
                : 'checked-incomplete' as const,
            artifact: proofCompilation.artifact,
            goalGraph: proofCompilation.proofCompilation.goalGraph
        }, 'proofMaintenanceInspection'),
        currentProof,
        currentWorkspace,
        proofCompilation
    };
};

/** Inspect one exact current proof without compiling its siblings. */
export function inspectCoreLfProofMaintenance(
    input: CoreLfProofMaintenanceInspectionInput
): CoreLfProofMaintenanceInspection {
    return prepareMaintenance(input).inspection;
}

/** Canonical selected-proof diagnosis and impact representation. */
export const serializeCoreLfProofMaintenanceInspection = (
    inspection: CoreLfProofMaintenanceInspection
): string => serializeCoreLfWorkspaceCanonicalJson(
    inspection,
    'proofMaintenanceInspection'
);

export interface CoreLfProofRepairProviderOptions {
    readonly allowedProfiles?: readonly string[];
    readonly seed?: string;
    readonly budget?: CoreObviousProofBudgetOptions;
}

export interface CoreLfProofRepairProposalInput
extends CoreLfProofMaintenanceInspectionInput {
    readonly goalId: string;
    readonly premiseIndexOptions?: CoreLfPremiseIndexOptions;
    readonly providerOptions?: CoreLfProofRepairProviderOptions;
}

export interface CoreLfProofRepairPrecondition {
    readonly revision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.preconditionRevision;
    readonly proof: CoreLfProofMaintenanceIdentity;
    readonly goalId: string;
    readonly previousSourceText: string;
    readonly currentSourceText: string;
    readonly semanticDiffText: string;
    readonly inspectionText: string;
}

export interface CoreLfProofRepairProposalSettings {
    readonly expressionVisitLimit: number;
    readonly premiseIndex: CoreLfPremiseIndexSettings;
}

export interface CoreLfProofRepairProposal {
    readonly revision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.proposalRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.revision;
    readonly providerRevision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision;
    readonly patchRevision:
        typeof CORE_PROOF_PLAN_PATCH_PROFILE.revision;
    readonly precondition: CoreLfProofRepairPrecondition;
    readonly settings: CoreLfProofRepairProposalSettings;
    readonly provider: CoreObviousProofProposalReport;
    readonly materializesUpdatedSource: false;
}

const repairPrecondition = (
    input: CoreLfProofMaintenanceInspectionInput,
    inspection: CoreLfProofMaintenanceInspection,
    goalId: string
): CoreLfProofRepairPrecondition => freezePortable({
    revision: CORE_LF_PROOF_MAINTENANCE_PROFILE.preconditionRevision,
    proof: cloneIdentity(input.proof),
    goalId,
    previousSourceText: serializeCoreLfProofDevelopmentSourceSnapshot(
        input.previousSource
    ),
    currentSourceText: serializeCoreLfProofDevelopmentSourceSnapshot(
        input.currentSource
    ),
    semanticDiffText: serializeCoreLfDevelopmentSemanticDiff(
        inspection.semanticDiff
    ),
    inspectionText: serializeCoreLfProofMaintenanceInspection(inspection)
}, 'proofRepairPrecondition');

const assertRepairable = (
    prepared: PreparedMaintenance,
    goalId: string
): {
    readonly proof: CoreLfWorkspaceProofDocumentInput;
    readonly state: CoreProofPlanStateSnapshot;
} => {
    if (
        prepared.inspection.outcome !== 'checked-incomplete' ||
        prepared.currentProof === undefined ||
        prepared.proofCompilation === undefined
    ) {
        return fail(
            'PROOF_NOT_REPAIRABLE',
            'proof',
            `Selected proof outcome '${prepared.inspection.outcome}' does ` +
                'not expose a freshly replayed named hole'
        );
    }
    const state = prepared.proofCompilation.artifact.proofArtifact.state;
    if (!state.goals.some(goal => goal.id === goalId)) {
        return fail(
            'GOAL_NOT_OPEN',
            'goalId',
            `Selected source goal '${goalId}' is not open after fresh replay`
        );
    }
    return { proof: prepared.currentProof, state };
};

const providerProposal = (
    prepared: PreparedMaintenance,
    proof: CoreLfWorkspaceProofDocumentInput,
    goalId: string,
    premiseIndexOptions: CoreLfPremiseIndexOptions,
    providerOptions: CoreLfProofRepairProviderOptions
) => {
    try {
        const index = createCoreLfAccessiblePremiseIndex(
            prepared.currentWorkspace,
            proof.moduleId,
            premiseIndexOptions
        );
        const provider = proposeCoreObviousProofPlanPatches({
            index,
            type: proof.type,
            plan: proof.plan,
            goalId,
            ...(providerOptions.allowedProfiles === undefined
                ? {}
                : { allowedProfiles: providerOptions.allowedProfiles }),
            ...(providerOptions.seed === undefined
                ? {}
                : { seed: providerOptions.seed }),
            ...(providerOptions.budget === undefined
                ? {}
                : { budget: providerOptions.budget })
        });
        return { index, provider };
    } catch (error: unknown) {
        return fail(
            'PROVIDER_FAILED',
            'provider',
            'Obvious-proof provider could not propose current repairs',
            error
        );
    }
};

/** Propose bounded checked patches for one freshly replayed named hole. */
export function proposeCoreLfProofRepairs(
    input: CoreLfProofRepairProposalInput
): CoreLfProofRepairProposal {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_INPUT',
            'input',
            'Proof repair proposal input must be a data record'
        );
    }
    assertGoalId(input.goalId, 'goalId');
    const prepared = prepareMaintenance(input);
    const repairable = assertRepairable(prepared, input.goalId);
    const proposal = providerProposal(
        prepared,
        repairable.proof,
        input.goalId,
        input.premiseIndexOptions ?? {},
        input.providerOptions ?? {}
    );
    return freezePortable({
        revision: CORE_LF_PROOF_MAINTENANCE_PROFILE.proposalRevision,
        profileRevision: CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
        providerRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
        patchRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
        precondition: repairPrecondition(
            input,
            prepared.inspection,
            input.goalId
        ),
        settings: {
            expressionVisitLimit:
                prepared.inspection.semanticDiff.visitBudget
                    .expressionVisitLimit,
            premiseIndex: proposal.index.snapshot.settings
        },
        provider: proposal.provider,
        materializesUpdatedSource: false as const
    }, 'proofRepairProposal');
}

/** Canonical proposal, including exact source/replay/provider preconditions. */
export const serializeCoreLfProofRepairProposal = (
    proposal: CoreLfProofRepairProposal
): string => serializeCoreLfWorkspaceCanonicalJson(
    proposal,
    'proofRepairProposal'
);

export interface CoreLfProofRepairCandidateReplayInput {
    readonly previousSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly currentSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly proposal: CoreLfProofRepairProposal;
    readonly candidateIndex: number;
}

export interface CoreLfProofRepairCandidateReplaySnapshot {
    readonly revision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.replayRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_MAINTENANCE_PROFILE.revision;
    readonly providerRevision:
        typeof CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision;
    readonly patchRevision:
        typeof CORE_PROOF_PLAN_PATCH_PROFILE.revision;
    readonly proof: CoreLfProofMaintenanceIdentity;
    readonly goalId: string;
    readonly candidateIndex: number;
    readonly patch: CoreProofPlanPatch;
    readonly result: CoreProofPlanStateSnapshot;
    readonly meaning: 'candidate-replayed';
    readonly materializesUpdatedSource: false;
}

export interface CoreLfProofRepairCandidateReplayResult {
    readonly snapshot: CoreLfProofRepairCandidateReplaySnapshot;
    readonly patch: CoreProofPlanPatch;
    readonly plan: CoreProofPlan;
    readonly execution: CoreProofPlanExecution;
}

const assertProposalShape = (
    proposal: CoreLfProofRepairProposal
): void => {
    if (
        proposal === null ||
        typeof proposal !== 'object' ||
        proposal.revision !==
            CORE_LF_PROOF_MAINTENANCE_PROFILE.proposalRevision ||
        proposal.profileRevision !==
            CORE_LF_PROOF_MAINTENANCE_PROFILE.revision ||
        proposal.providerRevision !==
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision ||
        proposal.patchRevision !== CORE_PROOF_PLAN_PATCH_PROFILE.revision ||
        proposal.precondition?.revision !==
            CORE_LF_PROOF_MAINTENANCE_PROFILE.preconditionRevision ||
        typeof proposal.precondition.previousSourceText !== 'string' ||
        typeof proposal.precondition.currentSourceText !== 'string' ||
        typeof proposal.precondition.semanticDiffText !== 'string' ||
        typeof proposal.precondition.inspectionText !== 'string' ||
        proposal.settings === null ||
        typeof proposal.settings !== 'object' ||
        !Number.isSafeInteger(proposal.settings.expressionVisitLimit) ||
        proposal.settings.expressionVisitLimit < 1 ||
        proposal.settings.expressionVisitLimit >
            CORE_LF_DEVELOPMENT_DIFF_PROFILE.maxExpressionVisitLimit ||
        proposal.settings.premiseIndex === null ||
        typeof proposal.settings.premiseIndex !== 'object' ||
        !Number.isSafeInteger(
            proposal.settings.premiseIndex.typeVisitLimit
        ) ||
        proposal.settings.premiseIndex.typeVisitLimit < 0 ||
        proposal.settings.premiseIndex.typeVisitLimit >
            CORE_LF_PREMISE_INDEX_PROFILE.maxTypeVisitLimit ||
        !Number.isSafeInteger(
            proposal.settings.premiseIndex.normalizationStepLimit
        ) ||
        proposal.settings.premiseIndex.normalizationStepLimit < 0 ||
        proposal.settings.premiseIndex.normalizationStepLimit >
            CORE_LF_PREMISE_INDEX_PROFILE.maxNormalizationStepLimit ||
        proposal.provider?.revision !==
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.reportRevision ||
        !Array.isArray(proposal.provider.candidates) ||
        proposal.materializesUpdatedSource !== false
    ) {
        fail(
            'INVALID_PROPOSAL',
            'proposal',
            'Proof repair proposal does not use the current frozen profiles'
        );
    }
    assertIdentity(proposal.precondition.proof, 'proposal.precondition.proof');
    assertGoalId(
        proposal.precondition.goalId,
        'proposal.precondition.goalId'
    );
    try {
        canonical(proposal, 'proposal');
    } catch (error: unknown) {
        fail(
            'INVALID_PROPOSAL',
            'proposal',
            'Proof repair proposal must be portable canonical data',
            error
        );
    }
};

const samePrecondition = (
    previous: CoreLfProofRepairPrecondition,
    current: CoreLfProofRepairPrecondition
): boolean => {
    try {
        return canonical(previous, 'proposal.precondition.recorded') ===
            canonical(current, 'proposal.precondition.current');
    } catch (error: unknown) {
        return fail(
            'INVALID_PROPOSAL',
            'proposal.precondition',
            'Recorded maintenance precondition is not canonical data',
            error
        );
    }
};

const replayProviderProposal = (
    prepared: PreparedMaintenance,
    proof: CoreLfWorkspaceProofDocumentInput,
    proposal: CoreLfProofRepairProposal
) => providerProposal(
    prepared,
    proof,
    proposal.precondition.goalId,
    proposal.settings.premiseIndex,
    {
        allowedProfiles: proposal.provider.allowedProfiles,
        seed: proposal.provider.seed,
        budget: proposal.provider.budget
    }
);

/** Recompute all freshness data and replay one recorded candidate. */
export function replayCoreLfProofRepairCandidate(
    input: CoreLfProofRepairCandidateReplayInput
): CoreLfProofRepairCandidateReplayResult {
    if (input === null || typeof input !== 'object') {
        return fail(
            'INVALID_INPUT',
            'input',
            'Proof repair candidate replay requires a data record'
        );
    }
    assertProposalShape(input.proposal);
    if (
        !Number.isSafeInteger(input.candidateIndex) ||
        input.candidateIndex < 0 ||
        input.candidateIndex >= input.proposal.provider.candidates.length
    ) {
        return fail(
            'INVALID_CANDIDATE_INDEX',
            'candidateIndex',
            'Candidate index must select one recorded provider candidate'
        );
    }
    const maintenanceInput: CoreLfProofMaintenanceInspectionInput = {
        previousSource: input.previousSource,
        currentSource: input.currentSource,
        proof: input.proposal.precondition.proof,
        diffOptions: {
            expressionVisitLimit:
                input.proposal.settings.expressionVisitLimit
        }
    };
    const prepared = prepareMaintenance(maintenanceInput);
    const currentPrecondition = repairPrecondition(
        maintenanceInput,
        prepared.inspection,
        input.proposal.precondition.goalId
    );
    if (!samePrecondition(input.proposal.precondition, currentPrecondition)) {
        return fail(
            'STALE_PROPOSAL',
            'proposal.precondition',
            'Current development, impact, replay, identity, or goal changed'
        );
    }
    const repairable = assertRepairable(
        prepared,
        input.proposal.precondition.goalId
    );
    const currentProvider = replayProviderProposal(
        prepared,
        repairable.proof,
        input.proposal
    );
    const currentProposal = freezePortable({
        revision: CORE_LF_PROOF_MAINTENANCE_PROFILE.proposalRevision,
        profileRevision: CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
        providerRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
        patchRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
        precondition: currentPrecondition,
        settings: {
            expressionVisitLimit:
                input.proposal.settings.expressionVisitLimit,
            premiseIndex: currentProvider.index.snapshot.settings
        },
        provider: currentProvider.provider,
        materializesUpdatedSource: false as const
    }, 'currentProofRepairProposal');
    if (
        serializeCoreLfProofRepairProposal(currentProposal) !==
            serializeCoreLfProofRepairProposal(input.proposal)
    ) {
        return fail(
            'STALE_PROPOSAL',
            'proposal',
            'Recorded proposal differs from fresh deterministic reconstruction'
        );
    }
    const candidate = currentProvider.provider.candidates[
        input.candidateIndex
    ];
    let replay: CoreObviousProofCandidateReplay;
    try {
        replay = replayCoreObviousProofCandidate({
            index: currentProvider.index,
            type: repairable.proof.type,
            plan: repairable.proof.plan,
            goalId: input.proposal.precondition.goalId,
            candidate
        });
    } catch (error: unknown) {
        return fail(
            'CANDIDATE_REPLAY_FAILED',
            'proposal.provider.candidates',
            'Recorded proof repair candidate failed fresh replay',
            error
        );
    }
    const snapshot = freezePortable({
        revision: CORE_LF_PROOF_MAINTENANCE_PROFILE.replayRevision,
        profileRevision: CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
        providerRevision: CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
        patchRevision: CORE_PROOF_PLAN_PATCH_PROFILE.revision,
        proof: cloneIdentity(input.proposal.precondition.proof),
        goalId: input.proposal.precondition.goalId,
        candidateIndex: input.candidateIndex,
        patch: candidate.patch,
        result: replay.execution.snapshot,
        meaning: 'candidate-replayed' as const,
        materializesUpdatedSource: false as const
    }, 'proofRepairReplay');
    return Object.freeze({
        snapshot,
        patch: candidate.patch,
        plan: replay.plan,
        execution: replay.execution
    });
}

/** Canonical portable projection of a successful candidate replay. */
export const serializeCoreLfProofRepairCandidateReplay = (
    replay: CoreLfProofRepairCandidateReplaySnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    replay,
    'proofRepairReplay'
);
