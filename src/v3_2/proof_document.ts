/**
 * Fresh checked proof documents and versioned AI-facing artifacts.
 *
 * This module is browser-safe. Fingerprint computation and filesystem I/O
 * belong to outer adapters; this boundary validates immutable fingerprint
 * data, owns the fresh checker session/root, and returns derived artifacts.
 */

import {
    CoreDeclarationEnvironment
} from './context';
import {
    CoreChecker
} from './checker';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    KernelExpression,
    Provenance,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CoreProofPlan,
    CoreProofPlanExecution,
    CoreProofPlanGoalSnapshot,
    CoreProofPlanStateSnapshot,
    CoreProofPlanTraceStep,
    executeCoreProofPlan
} from './proof_plan';
import {
    CoreProofRefiner
} from './proof';
import {
    CoreProofGoalCouplingGraph
} from './proof_goal_graph';
import {
    CoreElaborationSession
} from './session';

export const CORE_PROOF_DOCUMENT_PROFILE = Object.freeze({
    revision: 'emdash-v3.2-ai-proof-2' as const,
    compilerRevision: 'emdash-proof-document-compiler-v2' as const,
    explicitCoreRevision: 'EMDASH-CORE-SEXP-1' as const,
    proofStateRevision: 'emdash-proof-state-v2' as const,
    artifactRevision: 'emdash-proof-artifact-v2' as const,
    jsonlRevision: 'emdash-proof-jsonl-v2' as const,
    checker: 'CoreChecker' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const
});

export const serializeCoreProofDocumentProfile = (): string =>
    `${JSON.stringify(CORE_PROOF_DOCUMENT_PROFILE, null, 2)}\n`;

export interface CoreProofArtifactDependencyFingerprintInput {
    readonly moduleId: string;
    readonly interfaceSha256: string;
}

export interface CoreProofArtifactFingerprintInput {
    readonly source: {
        readonly id: string;
        readonly sha256: string;
    };
    readonly profileSha256: string;
    readonly dependencies?:
        readonly CoreProofArtifactDependencyFingerprintInput[];
}

export interface CoreProofArtifactDependencyFingerprint {
    readonly moduleId: string;
    readonly interfaceSha256: string;
}

export interface CoreProofArtifactFingerprint {
    readonly revision: 'emdash-proof-inputs-v1';
    readonly compilerRevision:
        typeof CORE_PROOF_DOCUMENT_PROFILE.compilerRevision;
    readonly source: {
        readonly id: string;
        readonly sha256: string;
    };
    readonly profile: {
        readonly id: typeof CORE_PROOF_DOCUMENT_PROFILE.revision;
        readonly sha256: string;
    };
    readonly dependencies:
        readonly CoreProofArtifactDependencyFingerprint[];
}

export type CoreProofArtifactErrorCode =
    | 'INVALID_ID'
    | 'INVALID_FINGERPRINT'
    | 'DUPLICATE_DEPENDENCY'
    | 'INVALID_ARTIFACT'
    | 'STALE_ARTIFACT';

export class CoreProofArtifactError extends Error {
    constructor(
        public readonly code: CoreProofArtifactErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreProofArtifactError';
    }
}

const SAFE_DOCUMENT_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SHA256 = /^sha256:[0-9a-f]{64}$/u;

const assertDocumentId = (value: string, path: string): void => {
    if (SAFE_DOCUMENT_ID.test(value)) return;
    throw new CoreProofArtifactError(
        'INVALID_ID',
        path,
        `AI proof document ID '${value}' is not stable and portable`
    );
};

const assertSourceId = (value: string): void => {
    if (
        value.length > 0 &&
        !/[\u0000-\u001f\u007f]/u.test(value)
    ) {
        return;
    }
    throw new CoreProofArtifactError(
        'INVALID_ID',
        'fingerprint.source.id',
        'AI proof source identity must be nonempty and contain no controls'
    );
};

const assertSha256 = (value: string, path: string): void => {
    if (SHA256.test(value)) return;
    throw new CoreProofArtifactError(
        'INVALID_FINGERPRINT',
        path,
        `Expected 'sha256:' followed by 64 lowercase hexadecimal digits`
    );
};

/** Build a canonical, dependency-order-independent input fingerprint. */
export function createCoreProofArtifactFingerprint(
    input: CoreProofArtifactFingerprintInput
): CoreProofArtifactFingerprint {
    assertSourceId(input.source.id);
    assertSha256(input.source.sha256, 'fingerprint.source.sha256');
    assertSha256(input.profileSha256, 'fingerprint.profile.sha256');

    const dependencies = [...(input.dependencies ?? [])]
        .sort((left, right) => {
            if (left.moduleId < right.moduleId) return -1;
            if (left.moduleId > right.moduleId) return 1;
            return 0;
        });
    const seen = new Set<string>();
    const frozenDependencies = Object.freeze(dependencies.map(
        (dependency, index) => {
            assertDocumentId(
                dependency.moduleId,
                `fingerprint.dependencies[${index}].moduleId`
            );
            assertSha256(
                dependency.interfaceSha256,
                `fingerprint.dependencies[${index}].interfaceSha256`
            );
            if (seen.has(dependency.moduleId)) {
                throw new CoreProofArtifactError(
                    'DUPLICATE_DEPENDENCY',
                    `fingerprint.dependencies[${index}].moduleId`,
                    `Duplicate AI proof dependency ` +
                    `'${dependency.moduleId}'`
                );
            }
            seen.add(dependency.moduleId);
            return Object.freeze({ ...dependency });
        }
    ));

    return Object.freeze({
        revision: 'emdash-proof-inputs-v1',
        compilerRevision:
            CORE_PROOF_DOCUMENT_PROFILE.compilerRevision,
        source: Object.freeze({ ...input.source }),
        profile: Object.freeze({
            id: CORE_PROOF_DOCUMENT_PROFILE.revision,
            sha256: input.profileSha256
        }),
        dependencies: frozenDependencies
    });
}

/** Revalidate a possibly deserialized fingerprint and canonicalize ordering. */
export function validateCoreProofArtifactFingerprint(
    fingerprint: CoreProofArtifactFingerprint
): CoreProofArtifactFingerprint {
    if (fingerprint.revision !== 'emdash-proof-inputs-v1') {
        throw new CoreProofArtifactError(
            'INVALID_FINGERPRINT',
            'fingerprint.revision',
            `Unsupported AI proof fingerprint revision ` +
            `'${String(fingerprint.revision)}'`
        );
    }
    if (
        fingerprint.compilerRevision !==
        CORE_PROOF_DOCUMENT_PROFILE.compilerRevision
    ) {
        throw new CoreProofArtifactError(
            'INVALID_FINGERPRINT',
            'fingerprint.compilerRevision',
            `Unsupported AI proof compiler revision ` +
            `'${String(fingerprint.compilerRevision)}'`
        );
    }
    if (fingerprint.profile.id !== CORE_PROOF_DOCUMENT_PROFILE.revision) {
        throw new CoreProofArtifactError(
            'INVALID_FINGERPRINT',
            'fingerprint.profile.id',
            `Unsupported AI proof profile '${String(fingerprint.profile.id)}'`
        );
    }
    return createCoreProofArtifactFingerprint({
        source: fingerprint.source,
        profileSha256: fingerprint.profile.sha256,
        dependencies: fingerprint.dependencies
    });
}

export interface CoreProofArtifact {
    readonly revision: typeof CORE_PROOF_DOCUMENT_PROFILE.artifactRevision;
    readonly moduleId: string;
    readonly declarationId: string;
    readonly fingerprint: CoreProofArtifactFingerprint;
    readonly state: CoreProofPlanStateSnapshot;
    /** Present only when the proof is complete and rechecked. */
    readonly checkedCore?: string;
}

export interface CoreProofDocumentInput {
    readonly moduleId: string;
    readonly declarationId: string;
    readonly environment: CoreDeclarationEnvironment;
    readonly type: KernelExpression;
    readonly plan: CoreProofPlan;
    readonly provenance: Provenance;
    readonly fingerprint: CoreProofArtifactFingerprint;
}

export interface CoreProofDocumentCompilation {
    readonly artifact: CoreProofArtifact;
    /** Portable graph derived during the same fresh replay, not artifact data. */
    readonly goalGraph: CoreProofGoalCouplingGraph;
    /** Checked explicit Core authority, present only for a complete proof. */
    readonly checkedTerm?: KernelExpression;
}

const checkedTargetProvenance = (
    input: CoreProofDocumentInput
): Provenance => provenance(
    'derived',
    `well-formed target for ${input.moduleId}.${input.declarationId}`,
    input.provenance.span
);

/**
 * Compile one theorem in a fresh session whose root never enters source data.
 */
export function compileCoreProofDocument(
    input: CoreProofDocumentInput
): CoreProofDocumentCompilation {
    assertDocumentId(input.moduleId, 'moduleId');
    assertDocumentId(input.declarationId, 'declarationId');
    const fingerprint = validateCoreProofArtifactFingerprint(
        input.fingerprint
    );

    const session = new CoreElaborationSession(input.environment);
    const checker = new CoreChecker(session);
    checker.validateEnvironment();

    const targetProvenance = checkedTargetProvenance(input);
    const checkedTarget = checker.check(
        session.rootContext,
        input.type,
        kernelUniverse(targetProvenance)
    ).term;
    const root = session.freshMeta(
        session.rootContext,
        checkedTarget,
        input.provenance
    );
    const execution: CoreProofPlanExecution = executeCoreProofPlan(
        new CoreProofRefiner(checker, root),
        root.identity,
        input.plan
    );

    let checkedTerm: KernelExpression | undefined;
    let checkedCore: string | undefined;
    if (execution.state.status === 'complete') {
        checkedTerm = checker.check(
            session.rootContext,
            execution.term,
            checkedTarget
        ).term;
        checkedCore = serializeCoreExpression(checkedTerm);
    }

    const artifact: CoreProofArtifact = Object.freeze({
        revision: CORE_PROOF_DOCUMENT_PROFILE.artifactRevision,
        moduleId: input.moduleId,
        declarationId: input.declarationId,
        fingerprint,
        state: execution.snapshot,
        checkedCore
    });
    return Object.freeze({
        artifact,
        goalGraph: execution.goalGraph,
        checkedTerm
    });
}

const fingerprintSerialization = (
    fingerprint: CoreProofArtifactFingerprint
): string => JSON.stringify(fingerprint);

/** Reject a cached artifact whose complete input stamp is no longer current. */
export function assertCoreProofArtifactCurrent(
    artifact: CoreProofArtifact,
    current: CoreProofArtifactFingerprint
): void {
    if (artifact.revision !== CORE_PROOF_DOCUMENT_PROFILE.artifactRevision) {
        throw new CoreProofArtifactError(
            'STALE_ARTIFACT',
            `${artifact.moduleId}.${artifact.declarationId}.revision`,
            `AI proof artifact revision '${String(artifact.revision)}' is ` +
            'not current'
        );
    }
    if (
        artifact.state.revision !==
        CORE_PROOF_DOCUMENT_PROFILE.proofStateRevision
    ) {
        throw new CoreProofArtifactError(
            'STALE_ARTIFACT',
            `${artifact.moduleId}.${artifact.declarationId}.state.revision`,
            `AI proof state revision ` +
            `'${String(artifact.state.revision)}' is not current`
        );
    }
    if (
        artifact.state.status === 'complete' &&
        artifact.checkedCore === undefined
    ) {
        throw new CoreProofArtifactError(
            'INVALID_ARTIFACT',
            `${artifact.moduleId}.${artifact.declarationId}.checkedCore`,
            'A complete AI proof artifact must contain rechecked explicit Core'
        );
    }
    if (
        artifact.state.status === 'incomplete' &&
        artifact.checkedCore !== undefined
    ) {
        throw new CoreProofArtifactError(
            'INVALID_ARTIFACT',
            `${artifact.moduleId}.${artifact.declarationId}.checkedCore`,
            'An incomplete AI proof artifact cannot claim checked explicit Core'
        );
    }

    const storedFingerprint = validateCoreProofArtifactFingerprint(
        artifact.fingerprint
    );
    const currentFingerprint = validateCoreProofArtifactFingerprint(current);
    if (
        fingerprintSerialization(storedFingerprint) !==
        fingerprintSerialization(artifact.fingerprint)
    ) {
        throw new CoreProofArtifactError(
            'INVALID_ARTIFACT',
            `${artifact.moduleId}.${artifact.declarationId}.fingerprint`,
            'AI proof artifact fingerprint is not in canonical order'
        );
    }
    if (
        fingerprintSerialization(storedFingerprint) ===
        fingerprintSerialization(currentFingerprint)
    ) {
        return;
    }
    throw new CoreProofArtifactError(
        'STALE_ARTIFACT',
        `${artifact.moduleId}.${artifact.declarationId}.fingerprint`,
        'AI proof artifact inputs differ from the current source, profile, ' +
        'compiler, or dependency interfaces'
    );
}

export interface CoreProofJsonlProofRecord {
    readonly revision: typeof CORE_PROOF_DOCUMENT_PROFILE.jsonlRevision;
    readonly kind: 'proof';
    readonly artifactRevision:
        typeof CORE_PROOF_DOCUMENT_PROFILE.artifactRevision;
    readonly moduleId: string;
    readonly declarationId: string;
    readonly status: CoreProofPlanStateSnapshot['status'];
    readonly fingerprint: CoreProofArtifactFingerprint;
    readonly term: string;
    readonly checkedCore?: string;
    readonly trace: readonly CoreProofPlanTraceStep[];
}

export interface CoreProofJsonlGoalRecord {
    readonly revision: typeof CORE_PROOF_DOCUMENT_PROFILE.jsonlRevision;
    readonly kind: 'goal';
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goal: CoreProofPlanGoalSnapshot;
}

export type CoreProofJsonlRecord =
    | CoreProofJsonlProofRecord
    | CoreProofJsonlGoalRecord;

export function coreProofArtifactJsonlRecords(
    artifact: CoreProofArtifact
): readonly CoreProofJsonlRecord[] {
    const proof: CoreProofJsonlProofRecord = Object.freeze({
        revision: CORE_PROOF_DOCUMENT_PROFILE.jsonlRevision,
        kind: 'proof',
        artifactRevision: artifact.revision,
        moduleId: artifact.moduleId,
        declarationId: artifact.declarationId,
        status: artifact.state.status,
        fingerprint: artifact.fingerprint,
        term: artifact.state.term,
        checkedCore: artifact.checkedCore,
        trace: artifact.state.trace
    });
    return Object.freeze([
        proof,
        ...artifact.state.goals.map(goal => Object.freeze({
            revision: CORE_PROOF_DOCUMENT_PROFILE.jsonlRevision,
            kind: 'goal' as const,
            moduleId: artifact.moduleId,
            declarationId: artifact.declarationId,
            goal
        }))
    ]);
}

export const serializeCoreProofArtifactJsonl = (
    artifact: CoreProofArtifact
): string => coreProofArtifactJsonlRecords(artifact)
    .map(record => JSON.stringify(record))
    .join('\n') + '\n';

export const serializeCoreProofArtifact = (
    artifact: CoreProofArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;

const formatContext = (
    goal: CoreProofPlanGoalSnapshot
): readonly string[] => goal.context.map(binding =>
    `  ${binding.name} [#${binding.index}; ` +
    `${binding.plicity}/${binding.variation}] : ${binding.type}`
);

export function formatCoreProofArtifact(
    artifact: CoreProofArtifact
): string {
    const identity = `${artifact.moduleId}.${artifact.declarationId}`;
    if (artifact.state.status === 'complete') {
        return `${identity}: complete\n` +
            `  checked Core: ${artifact.checkedCore}`;
    }

    const goals = artifact.state.goals.flatMap(goal => [
        `Goal ${goal.id} [depth ${goal.contextDepth}]`,
        ...formatContext(goal),
        `  |- ${goal.target}`
    ]);
    return `${identity}: incomplete ` +
        `(${artifact.state.goals.length} open ` +
        `${artifact.state.goals.length === 1 ? 'goal' : 'goals'})\n` +
        goals.join('\n');
}
