/**
 * Node-owned exact-file materializer for the first research workspace.
 *
 * It reads three fixed repository files, selects every inline Arrowgram by a
 * unique content digest, freshly compiles two fixed proof declarations, and
 * delegates semantic projection to the browser-safe research-document layer.
 * It performs no writes, path discovery, rendering, or publication.
 */

import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { TextDecoder } from 'node:util';
import {
    CORE_AI_RESEARCH_OVERVIEW_PLAN,
    CORE_AI_RESEARCH_OVERVIEW_PROFILE,
    CoreAiResearchOverviewDiagramBlockPlan,
    CoreAiResearchOverviewProofBlockPlan
} from './ai_research_overview';
import {
    CORE_AI_PROOF_DEMO_MODULE_ID,
    compileCoreAiProofDemo,
    createCoreAiProofDemoFingerprint
} from './ai_proof_demo';
import {
    CoreProofArtifact,
    serializeCoreProofArtifact,
    serializeCoreProofDocumentProfile
} from './proof_document';
import {
    CoreResearchContentReference,
    CoreResearchDocumentBlockInput,
    CoreResearchDocumentSnapshot,
    createCoreResearchDocumentSnapshot
} from './research_document';

const KIB = 1024;
const MIB = 1024 * KIB;

export const CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE = Object.freeze({
    revision: 'emdash-ai-research-overview-files-v3' as const,
    snapshotRevision:
        'emdash-ai-research-overview-files-snapshot-v3' as const,
    backend: 'typescript-emdash-explicit-core' as const,
    encoding: 'utf-8' as const,
    managementProfileRevision:
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.revision,
    maximumManagementSourceBytes: 2 * MIB,
    maximumDocumentSourceBytes: 4 * MIB,
    maximumProofSourceBytes: 2 * MIB,
    managementSourceSha256:
        'sha256:c115215083f35f2e1b75cd80d05276ed' +
        '2fd351a1273a977cc5106d7c13ecb93d',
    proofSourceSha256:
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.proofSourceSha256,
    readsFixedFiles: true as const,
    performsWrites: false as const,
    discoversPaths: false as const,
    parsesTypeScript: false as const,
    rendersDocuments: false as const,
    invokesGit: false as const,
    invokesLambdapi: false as const,
    performsNetworkAccess: false as const
});

export type CoreAiResearchOverviewFilesErrorCode =
    | 'FILE_READ_FAILED'
    | 'INVALID_FILE_BYTES'
    | 'FILE_TOO_LARGE'
    | 'INVALID_UTF8'
    | 'SOURCE_PIN_MISMATCH'
    | 'MISSING_DIAGRAM'
    | 'AMBIGUOUS_DIAGRAM'
    | 'UNBOUND_DIAGRAM'
    | 'ARTIFACT_PIN_MISMATCH'
    | 'UNSUPPORTED_PROOF';

export class CoreAiResearchOverviewFilesError extends Error {
    public readonly cause: unknown;

    constructor(
        public readonly code: CoreAiResearchOverviewFilesErrorCode,
        public readonly target: string,
        message: string,
        cause?: unknown
    ) {
        super(`${message} (${target})`);
        this.name = 'CoreAiResearchOverviewFilesError';
        this.cause = cause;
    }
}

const fail = (
    code: CoreAiResearchOverviewFilesErrorCode,
    target: string,
    message: string,
    cause?: unknown
): never => {
    throw new CoreAiResearchOverviewFilesError(
        code,
        target,
        message,
        cause
    );
};

export interface CoreAiResearchOverviewFilesIo {
    readonly readBytes?: (absolutePath: string) => Uint8Array;
}

export interface CoreAiResearchOverviewProofArtifactSnapshot {
    readonly blockId: string;
    readonly source: CoreResearchContentReference;
    readonly artifact: CoreProofArtifact;
}

export interface CoreAiResearchOverviewFilesSnapshot {
    readonly revision:
        typeof CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.snapshotRevision;
    readonly backend:
        typeof CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.backend;
    readonly planRevision:
        typeof CORE_AI_RESEARCH_OVERVIEW_PROFILE.revision;
    readonly digestVerification: 'performed-exact-utf8';
    readonly managementSource: CoreResearchContentReference;
    readonly documentSource: CoreResearchContentReference;
    readonly proofSource: CoreResearchContentReference;
    readonly proofProfile: CoreResearchContentReference;
    readonly binding: CoreResearchDocumentSnapshot;
    readonly proofArtifacts:
        readonly CoreAiResearchOverviewProofArtifactSnapshot[];
}

interface ExactTextFile {
    readonly source: CoreResearchContentReference;
    readonly text: string;
}

interface DiagramCandidate {
    readonly index: number;
    readonly sha256: string;
}

const defaultReadBytes = (absolutePath: string): Uint8Array =>
    readFileSync(absolutePath);

const sha256 = (bytes: Uint8Array): string =>
    'sha256:' + createHash('sha256').update(bytes).digest('hex');

const textBytes = (value: string): Uint8Array => Buffer.from(value, 'utf8');

const decodeUtf8 = (bytes: Uint8Array, target: string): string => {
    try {
        return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    } catch (error) {
        return fail(
            'INVALID_UTF8',
            target,
            'Research workspace source is not exact UTF-8',
            error
        );
    }
};

const readExactTextFile = (
    repositoryRoot: string,
    relativePath: string,
    maximumBytes: number,
    readBytes: (absolutePath: string) => Uint8Array
): ExactTextFile => {
    const absolutePath = path.join(repositoryRoot, relativePath);
    let supplied: Uint8Array;
    try {
        supplied = readBytes(absolutePath);
    } catch (error) {
        return fail(
            'FILE_READ_FAILED',
            relativePath,
            'Fixed research workspace file cannot be read',
            error
        );
    }
    if (!(supplied instanceof Uint8Array)) {
        return fail(
            'INVALID_FILE_BYTES',
            relativePath,
            'Research workspace reader must return a byte array'
        );
    }
    const bytes = Uint8Array.from(supplied);
    if (bytes.byteLength > maximumBytes) {
        return fail(
            'FILE_TOO_LARGE',
            relativePath,
            `Research workspace file exceeds ${maximumBytes} bytes`
        );
    }
    return Object.freeze({
        source: Object.freeze({
            id: relativePath,
            sha256: sha256(bytes)
        }),
        text: decodeUtf8(bytes, relativePath)
    });
};

const assertSourcePin = (
    source: CoreResearchContentReference,
    expectedSha256: string
): void => {
    if (source.sha256 === expectedSha256) return;
    fail(
        'SOURCE_PIN_MISMATCH',
        source.id,
        `Fixed research source has digest ${source.sha256}, expected ` +
            expectedSha256
    );
};

const extractArrowgrams = (source: string): readonly DiagramCandidate[] => {
    const expression =
        /<div class="arrowgram"[^>]*>([\s\S]*?)<\/div>/gu;
    return Object.freeze([...source.matchAll(expression)].map(
        (match, index) => {
            const text = match[1].trim();
            return Object.freeze({
                index,
                sha256: sha256(textBytes(text))
            });
        }
    ));
};

const diagramPlans = ():
readonly CoreAiResearchOverviewDiagramBlockPlan[] =>
    CORE_AI_RESEARCH_OVERVIEW_PLAN.blocks.filter(
        (block): block is CoreAiResearchOverviewDiagramBlockPlan =>
            block.kind === 'diagram'
    );

const selectedDiagrams = (
    source: string
): ReadonlyMap<string, DiagramCandidate> => {
    const candidates = extractArrowgrams(source);
    const plans = diagramPlans();
    if (candidates.length !== plans.length) {
        return fail(
            'UNBOUND_DIAGRAM',
            CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath,
            `Article contains ${candidates.length} Arrowgram bodies, but ` +
                `typed management binds ${plans.length}`
        );
    }
    const selected = new Map<string, DiagramCandidate>();
    const selectedIndexes = new Set<number>();
    plans.forEach(plan => {
        const matches = candidates.filter(candidate =>
            candidate.sha256 === plan.sourceSha256
        );
        if (matches.length === 0) {
            fail(
                'MISSING_DIAGRAM',
                plan.blockId,
                `No Arrowgram body has managed digest ${plan.sourceSha256}`
            );
        }
        if (matches.length !== 1) {
            fail(
                'AMBIGUOUS_DIAGRAM',
                plan.blockId,
                `${matches.length} Arrowgram bodies have managed digest ` +
                    plan.sourceSha256
            );
        }
        selected.set(plan.blockId, matches[0]);
        selectedIndexes.add(matches[0].index);
    });
    if (selectedIndexes.size !== candidates.length) {
        return fail(
            'UNBOUND_DIAGRAM',
            CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath,
            'At least one article Arrowgram is not uniquely managed'
        );
    }
    return selected;
};

const artifactSource = (
    blockId: string,
    artifact: CoreProofArtifact
): CoreAiResearchOverviewProofArtifactSnapshot => {
    const source = Object.freeze({
        id: `emdash-artifact:${artifact.moduleId}/` +
            artifact.declarationId,
        sha256: sha256(textBytes(serializeCoreProofArtifact(artifact)))
    });
    return Object.freeze({ blockId, source, artifact });
};

const proofBlock = (
    plan: CoreAiResearchOverviewProofBlockPlan,
    proofSourceSha256: string,
    proofProfileSha256: string
): {
    readonly input: CoreResearchDocumentBlockInput;
    readonly artifact: CoreAiResearchOverviewProofArtifactSnapshot;
} => {
    if (plan.declaration.moduleId !== CORE_AI_PROOF_DEMO_MODULE_ID) {
        return fail(
            'UNSUPPORTED_PROOF',
            plan.blockId,
            `Fixed research materializer does not own proof module ` +
                `'${plan.declaration.moduleId}'`
        );
    }
    const fingerprint = createCoreAiProofDemoFingerprint(
        proofSourceSha256,
        proofProfileSha256
    );
    const artifact = compileCoreAiProofDemo(
        plan.declaration.declarationId,
        fingerprint
    ).artifact;
    const snapshot = artifactSource(plan.blockId, artifact);
    if (snapshot.source.sha256 !== plan.artifactSha256) {
        return fail(
            'ARTIFACT_PIN_MISMATCH',
            plan.blockId,
            `Canonical proof artifact has digest ${snapshot.source.sha256}, ` +
                `expected ${plan.artifactSha256}`
        );
    }
    return Object.freeze({
        input: Object.freeze({
            kind: 'proof' as const,
            blockId: plan.blockId,
            declaration: plan.declaration,
            artifactSource: snapshot.source,
            artifact,
            currentFingerprint: fingerprint
        }),
        artifact: snapshot
    });
};

/** Read and verify the one fixed local research-document workspace. */
export function materializeCoreAiResearchOverviewFiles(
    io: CoreAiResearchOverviewFilesIo = {}
): CoreAiResearchOverviewFilesSnapshot {
    const repositoryRoot = path.resolve(__dirname, '../..');
    const readBytes = io.readBytes ?? defaultReadBytes;
    const management = readExactTextFile(
        repositoryRoot,
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.managementSourcePath,
        CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE
            .maximumManagementSourceBytes,
        readBytes
    );
    const document = readExactTextFile(
        repositoryRoot,
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath,
        CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.maximumDocumentSourceBytes,
        readBytes
    );
    const proofSource = readExactTextFile(
        repositoryRoot,
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.proofSourcePath,
        CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.maximumProofSourceBytes,
        readBytes
    );
    assertSourcePin(
        management.source,
        CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.managementSourceSha256
    );
    assertSourcePin(
        proofSource.source,
        CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.proofSourceSha256
    );
    const proofProfileText = serializeCoreProofDocumentProfile();
    const proofProfile = Object.freeze({
        id: 'emdash-proof-document-profile.json',
        sha256: sha256(textBytes(proofProfileText))
    });
    assertSourcePin(
        proofProfile,
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.proofProfileSha256
    );
    const diagrams = selectedDiagrams(document.text);
    assertSourcePin(
        document.source,
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourceSha256
    );
    const proofArtifacts:
        CoreAiResearchOverviewProofArtifactSnapshot[] = [];
    const blocks = CORE_AI_RESEARCH_OVERVIEW_PLAN.blocks.map(block => {
        if (block.kind === 'diagram') {
            const selected = diagrams.get(block.blockId);
            if (selected === undefined) {
                return fail(
                    'MISSING_DIAGRAM',
                    block.blockId,
                    'Managed Arrowgram selection disappeared'
                );
            }
            return Object.freeze({
                kind: 'diagram' as const,
                blockId: block.blockId,
                format: block.format,
                source: Object.freeze({
                    id: `${document.source.id}#${block.blockId}`,
                    sha256: selected.sha256
                }),
                declarations: block.declarations
            });
        }
        const compiled = proofBlock(
            block,
            proofSource.source.sha256,
            proofProfile.sha256
        );
        proofArtifacts.push(compiled.artifact);
        return compiled.input;
    });
    const binding = createCoreResearchDocumentSnapshot({
        documentId: CORE_AI_RESEARCH_OVERVIEW_PLAN.documentId,
        documentRevision:
            CORE_AI_RESEARCH_OVERVIEW_PLAN.documentRevision,
        source: document.source,
        blocks
    });

    return Object.freeze({
        revision:
            CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.snapshotRevision,
        backend: CORE_AI_RESEARCH_OVERVIEW_FILES_PROFILE.backend,
        planRevision: CORE_AI_RESEARCH_OVERVIEW_PLAN.revision,
        digestVerification: 'performed-exact-utf8',
        managementSource: management.source,
        documentSource: document.source,
        proofSource: proofSource.source,
        proofProfile,
        binding,
        proofArtifacts: Object.freeze(proofArtifacts)
    });
}

export const serializeCoreAiResearchOverviewFilesSnapshot = (
    snapshot: CoreAiResearchOverviewFilesSnapshot
): string => `${JSON.stringify(snapshot, null, 2)}\n`;
