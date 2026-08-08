/**
 * Typed management sidecar for the first paper/diagram/proof workspace.
 *
 * An agent can inspect this source to see every stable block identity and the
 * exact declarations to which it is attached. File reading, hashing, and
 * proof compilation belong to the adjacent Node-owned materializer.
 */

import {
    CORE_AI_PROOF_DEMO_MODULE_ID,
    CORE_AI_PROOF_DEMO_SOURCE_PATH,
    CoreAiProofDemoDeclarationId
} from './ai_proof_demo';
import {
    CoreResearchDeclarationReference
} from './research_document';

export const CORE_AI_RESEARCH_OVERVIEW_PROFILE = Object.freeze({
    revision: 'emdash-ai-research-overview-v1' as const,
    documentId: 'emdash-v3-2-overview' as const,
    documentRevision: '0.2.0-dev' as const,
    managementSourcePath:
        'src/v3_2/ai_research_overview.ts' as const,
    documentSourcePath:
        'emdash2/print/public/emdash-v3-2-overview.md' as const,
    proofSourcePath: CORE_AI_PROOF_DEMO_SOURCE_PATH,
    documentSourceSha256:
        'sha256:06ba39df979f58aa91a1bc8b9ff09f90' +
        '3fc966d6cfbb79f1d310c62e24cb6183',
    proofSourceSha256:
        'sha256:1465956c04dc3e413034cbe697ead1618' +
        'c9898b33132919533f6967ecd8af2dd',
    proofProfileSha256:
        'sha256:07cfc3cae978d2add44148582502a16b4' +
        'e5b55e61814ada6b57ba4394223646c',
    diagramSelectorRevision:
        'trimmed-arrowgram-body-sha256-v1' as const,
    proofModuleId: CORE_AI_PROOF_DEMO_MODULE_ID,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    parsesMarkdown: false as const,
    retainsCallbacks: false as const
});

export interface CoreAiResearchOverviewDiagramBlockPlan {
    readonly kind: 'diagram';
    readonly blockId: string;
    readonly format: 'arrowgram';
    /** SHA-256 of the trimmed exact UTF-8 Arrowgram body. */
    readonly sourceSha256: string;
    readonly declarations: readonly CoreResearchDeclarationReference[];
}

export interface CoreAiResearchOverviewProofBlockPlan {
    readonly kind: 'proof';
    readonly blockId: string;
    readonly declaration: {
        readonly moduleId: typeof CORE_AI_PROOF_DEMO_MODULE_ID;
        readonly declarationId: CoreAiProofDemoDeclarationId;
    };
    /** SHA-256 of canonical standalone proof-artifact JSON bytes. */
    readonly artifactSha256: string;
}

export type CoreAiResearchOverviewBlockPlan =
    | CoreAiResearchOverviewDiagramBlockPlan
    | CoreAiResearchOverviewProofBlockPlan;

export interface CoreAiResearchOverviewPlan {
    readonly revision: typeof CORE_AI_RESEARCH_OVERVIEW_PROFILE.revision;
    readonly documentId:
        typeof CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentId;
    readonly documentRevision:
        typeof CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentRevision;
    readonly documentSourceId:
        typeof CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath;
    readonly blocks: readonly CoreAiResearchOverviewBlockPlan[];
}

const declaration = (
    declarationId: string
): CoreResearchDeclarationReference => Object.freeze({
    moduleId: 'emdash.emdash3_2',
    declarationId
});

const diagram = (
    blockId: string,
    sourceSha256: string,
    declarationIds: readonly string[]
): CoreAiResearchOverviewDiagramBlockPlan => Object.freeze({
    kind: 'diagram',
    blockId,
    format: 'arrowgram',
    sourceSha256,
    declarations: Object.freeze(declarationIds.map(declaration))
});

const proof = (
    blockId: string,
    declarationId: CoreAiProofDemoDeclarationId,
    artifactSha256: string
): CoreAiResearchOverviewProofBlockPlan => Object.freeze({
    kind: 'proof',
    blockId,
    declaration: Object.freeze({
        moduleId: CORE_AI_PROOF_DEMO_MODULE_ID,
        declarationId
    }),
    artifactSha256
});

/**
 * Canonical document order: two Section 4 diagrams, then two Section 7 proof
 * supplements. Proof status is intentionally absent and must be derived.
 */
export const CORE_AI_RESEARCH_OVERVIEW_PLAN:
    CoreAiResearchOverviewPlan = Object.freeze({
    revision: CORE_AI_RESEARCH_OVERVIEW_PROFILE.revision,
    documentId: CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentId,
    documentRevision: CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentRevision,
    documentSourceId:
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourcePath,
    blocks: Object.freeze([
        diagram(
            'section-4.pathout-canonical-arrow',
            'sha256:b016711b4db44a81918cc52a57a3bcc3' +
                '40f2430a6a8a885c588f93bf8e791d4a',
            ['pathout_refl_arrow', 'sigma_transport_arrow']
        ),
        diagram(
            'section-4.pathout-motive-transport',
            'sha256:14f16531b434076cc64f29cd2dd3bc3' +
                'a25f20b705b81f6c8eef5172b1ebed496',
            ['PathInd_transfd', 'path_ind_sec', 'pathout_refl_arrow']
        ),
        proof(
            'section-7.proof.complete-identity',
            'complete_identity',
            'sha256:477ac1e6bbbf912fb0e9a38d8260c5bd' +
                '6fd35779599cbd71257340000215be2c'
        ),
        proof(
            'section-7.proof.open-identity',
            'open_identity',
            'sha256:83b39e97ea0a5e24f86bc29e4ecb890e' +
                'a4f2828cb2d57e2c6b4a1ece0bbae373'
        )
    ])
});
