/**
 * Browser-safe semantic bindings between research-document blocks and proofs.
 *
 * This layer receives source and artifact digests as data. It neither reads
 * nor hashes bytes. Proof status is derived only from an ordinary current
 * proof artifact; a supplied artifact digest is never proof authority.
 */

import {
    CORE_PROOF_DOCUMENT_PROFILE,
    CoreProofArtifact,
    CoreProofArtifactFingerprint,
    assertCoreProofArtifactCurrent,
    validateCoreProofArtifactFingerprint
} from './proof_document';
import {
    CoreProofPlanGoalSnapshot,
    CoreProofPlanProvenanceSnapshot,
    CoreProofPlanSourceSpanSnapshot
} from './proof_plan';

export const CORE_RESEARCH_DOCUMENT_PROFILE = Object.freeze({
    revision: 'emdash-research-document-binding-v1' as const,
    snapshotRevision:
        'emdash-research-document-binding-snapshot-v1' as const,
    proofArtifactRevision:
        CORE_PROOF_DOCUMENT_PROFILE.artifactRevision,
    digestPolicy: 'caller-supplied-sha256' as const,
    proofFreshnessPolicy:
        'exact-declaration-and-current-fingerprint' as const,
    blockOrderPolicy: 'declared-document-order' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    parsesMarkdown: false as const,
    rendersHtml: false as const
});

export type CoreResearchDocumentErrorCode =
    | 'INVALID_DOCUMENT'
    | 'INVALID_BLOCK'
    | 'DUPLICATE_BLOCK'
    | 'INVALID_DECLARATION'
    | 'DUPLICATE_DECLARATION'
    | 'INVALID_DIGEST'
    | 'PROOF_IDENTITY_MISMATCH';

export class CoreResearchDocumentError extends Error {
    constructor(
        public readonly code: CoreResearchDocumentErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreResearchDocumentError';
    }
}

const fail = (
    code: CoreResearchDocumentErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreResearchDocumentError(code, path, message);
};

const PORTABLE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const PORTABLE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;
const SHA256 = /^sha256:[0-9a-f]{64}$/u;

const assertPortableId = (
    value: string,
    path: string,
    code: CoreResearchDocumentErrorCode
): void => {
    if (PORTABLE_ID.test(value)) return;
    fail(code, path, `Invalid stable research identity '${value}'`);
};

const assertSourceId = (value: string, path: string): void => {
    if (value.length > 0 && !/[\u0000-\u001f\u007f]/u.test(value)) return;
    fail(
        'INVALID_DOCUMENT',
        path,
        'Research source identity must be nonempty and contain no controls'
    );
};

const assertSha256 = (value: string, path: string): void => {
    if (SHA256.test(value)) return;
    fail(
        'INVALID_DIGEST',
        path,
        "Expected 'sha256:' followed by 64 lowercase hexadecimal digits"
    );
};

export interface CoreResearchContentReference {
    readonly id: string;
    readonly sha256: string;
}

export interface CoreResearchDeclarationReference {
    readonly moduleId: string;
    readonly declarationId: string;
}

export interface CoreResearchDiagramBlockInput {
    readonly kind: 'diagram';
    readonly blockId: string;
    readonly format: 'arrowgram';
    /** Exact diagram bytes are located and hashed by a later outer adapter. */
    readonly source: CoreResearchContentReference;
    readonly declarations: readonly CoreResearchDeclarationReference[];
}

export interface CoreResearchProofBlockInput {
    readonly kind: 'proof';
    readonly blockId: string;
    readonly declaration: CoreResearchDeclarationReference;
    /** Stable external identity and caller-supplied digest of artifact bytes. */
    readonly artifactSource: CoreResearchContentReference;
    readonly artifact: CoreProofArtifact;
    readonly currentFingerprint: CoreProofArtifactFingerprint;
}

export type CoreResearchDocumentBlockInput =
    | CoreResearchDiagramBlockInput
    | CoreResearchProofBlockInput;

export interface CoreResearchDocumentInput {
    readonly documentId: string;
    readonly documentRevision: string;
    readonly source: CoreResearchContentReference;
    /** Canonical document order; duplicate stable block IDs are rejected. */
    readonly blocks: readonly CoreResearchDocumentBlockInput[];
}

export interface CoreResearchDiagramBlockSnapshot {
    readonly kind: 'diagram';
    readonly blockId: string;
    readonly format: 'arrowgram';
    readonly source: CoreResearchContentReference;
    readonly declarations: readonly CoreResearchDeclarationReference[];
}

export interface CoreResearchProofBlockSnapshot {
    readonly kind: 'proof';
    readonly blockId: string;
    readonly declaration: CoreResearchDeclarationReference;
    readonly artifactSource: CoreResearchContentReference;
    readonly artifactFingerprint: CoreProofArtifactFingerprint;
    readonly status: CoreProofArtifact['state']['status'];
    /** Present only for a current complete artifact. */
    readonly checkedCore?: string;
    /** Empty for a complete artifact; stable named goals when incomplete. */
    readonly goals: readonly CoreProofPlanGoalSnapshot[];
}

export type CoreResearchDocumentBlockSnapshot =
    | CoreResearchDiagramBlockSnapshot
    | CoreResearchProofBlockSnapshot;

export interface CoreResearchDocumentSnapshot {
    readonly revision:
        typeof CORE_RESEARCH_DOCUMENT_PROFILE.snapshotRevision;
    readonly profileRevision:
        typeof CORE_RESEARCH_DOCUMENT_PROFILE.revision;
    readonly documentId: string;
    readonly documentRevision: string;
    readonly source: CoreResearchContentReference;
    readonly digestVerification: 'not-performed';
    readonly blocks: readonly CoreResearchDocumentBlockSnapshot[];
}

const contentReference = (
    value: CoreResearchContentReference,
    path: string
): CoreResearchContentReference => {
    assertSourceId(value.id, `${path}.id`);
    assertSha256(value.sha256, `${path}.sha256`);
    return Object.freeze({ id: value.id, sha256: value.sha256 });
};

const declarationReference = (
    value: CoreResearchDeclarationReference,
    path: string
): CoreResearchDeclarationReference => {
    assertPortableId(value.moduleId, `${path}.moduleId`, 'INVALID_DECLARATION');
    assertPortableId(
        value.declarationId,
        `${path}.declarationId`,
        'INVALID_DECLARATION'
    );
    return Object.freeze({
        moduleId: value.moduleId,
        declarationId: value.declarationId
    });
};

const declarationIdentity = (
    value: CoreResearchDeclarationReference
): string => `${value.moduleId}.${value.declarationId}`;

const compareDeclarations = (
    left: CoreResearchDeclarationReference,
    right: CoreResearchDeclarationReference
): number => {
    if (left.moduleId < right.moduleId) return -1;
    if (left.moduleId > right.moduleId) return 1;
    if (left.declarationId < right.declarationId) return -1;
    if (left.declarationId > right.declarationId) return 1;
    return 0;
};

const sameDeclaration = (
    left: CoreResearchDeclarationReference,
    right: CoreResearchDeclarationReference
): boolean => left.moduleId === right.moduleId &&
    left.declarationId === right.declarationId;

const diagramDeclarations = (
    values: readonly CoreResearchDeclarationReference[],
    path: string
): readonly CoreResearchDeclarationReference[] => {
    if (values.length === 0) {
        return fail(
            'INVALID_BLOCK',
            path,
            'A research diagram must name at least one semantic declaration'
        );
    }
    const declarations = values.map((value, index) =>
        declarationReference(value, `${path}[${index}]`)
    ).sort(compareDeclarations);
    declarations.forEach((value, index) => {
        if (
            index > 0 &&
            sameDeclaration(declarations[index - 1], value)
        ) {
            fail(
                'DUPLICATE_DECLARATION',
                `${path}[${index}]`,
                `Duplicate diagram declaration '${declarationIdentity(value)}'`
            );
        }
    });
    return Object.freeze(declarations);
};

const cloneSpan = (
    value: CoreProofPlanSourceSpanSnapshot
): CoreProofPlanSourceSpanSnapshot => Object.freeze({
    file: value.file,
    start: Object.freeze({ ...value.start }),
    end: Object.freeze({ ...value.end })
});

const cloneProvenance = (
    value: CoreProofPlanProvenanceSnapshot
): CoreProofPlanProvenanceSnapshot => Object.freeze({
    origin: value.origin,
    detail: value.detail,
    ...(value.span === undefined ? {} : { span: cloneSpan(value.span) })
});

const cloneGoal = (
    value: CoreProofPlanGoalSnapshot
): CoreProofPlanGoalSnapshot => Object.freeze({
    id: value.id,
    contextDepth: value.contextDepth,
    context: Object.freeze(value.context.map(binding => Object.freeze({
        ...binding
    }))),
    target: value.target,
    occurrenceCount: value.occurrenceCount,
    declarationProvenance: cloneProvenance(value.declarationProvenance),
    firstOccurrenceProvenance: cloneProvenance(
        value.firstOccurrenceProvenance
    )
});

const diagramBlock = (
    input: CoreResearchDiagramBlockInput,
    path: string
): CoreResearchDiagramBlockSnapshot => {
    if (input.format !== 'arrowgram') {
        return fail(
            'INVALID_BLOCK',
            `${path}.format`,
            `Unsupported research diagram format '${String(input.format)}'`
        );
    }
    return Object.freeze({
        kind: 'diagram',
        blockId: input.blockId,
        format: input.format,
        source: contentReference(input.source, `${path}.source`),
        declarations: diagramDeclarations(
            input.declarations,
            `${path}.declarations`
        )
    });
};

const proofBlock = (
    input: CoreResearchProofBlockInput,
    path: string
): CoreResearchProofBlockSnapshot => {
    const declaration = declarationReference(
        input.declaration,
        `${path}.declaration`
    );
    const actualDeclaration = {
        moduleId: input.artifact.moduleId,
        declarationId: input.artifact.declarationId
    };
    if (!sameDeclaration(declaration, actualDeclaration)) {
        return fail(
            'PROOF_IDENTITY_MISMATCH',
            `${path}.declaration`,
            `Proof block expects '${declarationIdentity(declaration)}', ` +
                `but artifact is '${declarationIdentity(actualDeclaration)}'`
        );
    }

    assertCoreProofArtifactCurrent(
        input.artifact,
        input.currentFingerprint
    );
    const currentFingerprint = validateCoreProofArtifactFingerprint(
        input.currentFingerprint
    );
    const status = input.artifact.state.status;
    if (status !== 'complete' && status !== 'incomplete') {
        return fail(
            'INVALID_BLOCK',
            `${path}.artifact.state.status`,
            `Unsupported proof status '${String(status)}'`
        );
    }
    if (
        (status === 'complete' && input.artifact.state.goals.length !== 0) ||
        (status === 'incomplete' && input.artifact.state.goals.length === 0)
    ) {
        return fail(
            'INVALID_BLOCK',
            `${path}.artifact.state.goals`,
            'Complete proof artifacts must have no goals and incomplete ' +
                'artifacts must retain at least one named goal'
        );
    }
    const goals = Object.freeze(input.artifact.state.goals.map(cloneGoal));
    return Object.freeze({
        kind: 'proof',
        blockId: input.blockId,
        declaration,
        artifactSource: contentReference(
            input.artifactSource,
            `${path}.artifactSource`
        ),
        artifactFingerprint: currentFingerprint,
        status,
        ...(status === 'complete'
            ? { checkedCore: input.artifact.checkedCore }
            : {}),
        goals
    });
};

/**
 * Bind stable document blocks to semantic declarations and current proofs.
 *
 * Block order is document order. Diagram declaration references are sorted by
 * identity because their input order carries no semantics.
 */
export function createCoreResearchDocumentSnapshot(
    input: CoreResearchDocumentInput
): CoreResearchDocumentSnapshot {
    assertPortableId(input.documentId, 'documentId', 'INVALID_DOCUMENT');
    if (!PORTABLE_REVISION.test(input.documentRevision)) {
        return fail(
            'INVALID_DOCUMENT',
            'documentRevision',
            `Invalid research document revision '${input.documentRevision}'`
        );
    }
    const source = contentReference(input.source, 'source');
    if (input.blocks.length === 0) {
        return fail(
            'INVALID_DOCUMENT',
            'blocks',
            'A research document binding must contain at least one block'
        );
    }
    const blockIds = new Set<string>();
    const blocks = input.blocks.map((block, index) => {
        const path = `blocks[${index}]`;
        assertPortableId(block.blockId, `${path}.blockId`, 'INVALID_BLOCK');
        if (blockIds.has(block.blockId)) {
            return fail(
                'DUPLICATE_BLOCK',
                `${path}.blockId`,
                `Duplicate research block '${block.blockId}'`
            );
        }
        blockIds.add(block.blockId);
        switch (block.kind) {
            case 'diagram':
                return diagramBlock(block, path);
            case 'proof':
                return proofBlock(block, path);
            default: {
                const exhaustive: never = block;
                return fail(
                    'INVALID_BLOCK',
                    `${path}.kind`,
                    `Unsupported research block kind '${String(exhaustive)}'`
                );
            }
        }
    });

    return Object.freeze({
        revision: CORE_RESEARCH_DOCUMENT_PROFILE.snapshotRevision,
        profileRevision: CORE_RESEARCH_DOCUMENT_PROFILE.revision,
        documentId: input.documentId,
        documentRevision: input.documentRevision,
        source,
        digestVerification: 'not-performed',
        blocks: Object.freeze(blocks)
    });
}

export const serializeCoreResearchDocumentSnapshot = (
    snapshot: CoreResearchDocumentSnapshot
): string => `${JSON.stringify(snapshot, null, 2)}\n`;
