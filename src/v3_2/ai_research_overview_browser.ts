/** Browser-safe replay and presentation for the research-workspace sidecar. */

import {
    CORE_AI_RESEARCH_OVERVIEW_PLAN,
    CORE_AI_RESEARCH_OVERVIEW_PROFILE
} from './ai_research_overview';
import {
    compileCoreAiProofDemo,
    createCoreAiProofDemoFingerprint
} from './ai_proof_demo';
import {
    CoreResearchDocumentBlockInput,
    CoreResearchDocumentSnapshot,
    createCoreResearchDocumentSnapshot
} from './research_document';

export const CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE = Object.freeze({
    revision: 'emdash-ai-research-overview-browser-v1' as const,
    execution: 'explicit-client-side-recheck' as const,
    inputAuthority: 'typed-release-pins' as const,
    releaseParity: 'required-against-node-files-v1' as const,
    digestVerification: 'not-performed-in-browser' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const,
    retainsCheckerOrSession: false as const
});

export interface CoreAiResearchOverviewBrowserSnapshot {
    readonly revision:
        typeof CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.revision;
    readonly execution:
        typeof CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.execution;
    readonly digestVerification:
        typeof CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.digestVerification;
    readonly binding: CoreResearchDocumentSnapshot;
}

const artifactId = (moduleId: string, declarationId: string): string =>
    `emdash-artifact:${moduleId}/${declarationId}`;

/** Freshly replay the two managed proofs from source-visible release pins. */
export function runCoreAiResearchOverviewBrowser():
    CoreAiResearchOverviewBrowserSnapshot {
    const fingerprint = createCoreAiProofDemoFingerprint(
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.proofSourceSha256,
        CORE_AI_RESEARCH_OVERVIEW_PROFILE.proofProfileSha256
    );
    const blocks: readonly CoreResearchDocumentBlockInput[] =
        CORE_AI_RESEARCH_OVERVIEW_PLAN.blocks.map(block => {
            if (block.kind === 'diagram') {
                return Object.freeze({
                    kind: 'diagram' as const,
                    blockId: block.blockId,
                    format: block.format,
                    source: Object.freeze({
                        id: `${CORE_AI_RESEARCH_OVERVIEW_PROFILE
                            .documentSourcePath}#${block.blockId}`,
                        sha256: block.sourceSha256
                    }),
                    declarations: block.declarations
                });
            }
            const artifact = compileCoreAiProofDemo(
                block.declaration.declarationId,
                fingerprint
            ).artifact;
            return Object.freeze({
                kind: 'proof' as const,
                blockId: block.blockId,
                declaration: block.declaration,
                artifactSource: Object.freeze({
                    id: artifactId(
                        block.declaration.moduleId,
                        block.declaration.declarationId
                    ),
                    sha256: block.artifactSha256
                }),
                artifact,
                currentFingerprint: fingerprint
            });
        });
    const binding = createCoreResearchDocumentSnapshot({
        documentId: CORE_AI_RESEARCH_OVERVIEW_PLAN.documentId,
        documentRevision:
            CORE_AI_RESEARCH_OVERVIEW_PLAN.documentRevision,
        source: {
            id: CORE_AI_RESEARCH_OVERVIEW_PLAN.documentSourceId,
            sha256:
                CORE_AI_RESEARCH_OVERVIEW_PROFILE.documentSourceSha256
        },
        blocks
    });
    return Object.freeze({
        revision: CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.revision,
        execution: CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.execution,
        digestVerification:
            CORE_AI_RESEARCH_OVERVIEW_BROWSER_PROFILE.digestVerification,
        binding
    });
}

/** Compact reviewer prose derived only from the replayed binding. */
export function formatCoreAiResearchOverviewBrowser(
    snapshot: CoreAiResearchOverviewBrowserSnapshot
): string {
    const lines = [
        `${snapshot.binding.documentId}@` +
            `${snapshot.binding.documentRevision}: client-side recheck`,
        'Release inputs: typed and pinned; browser digest verification: ' +
            'not performed',
        ''
    ];
    snapshot.binding.blocks.forEach(block => {
        if (block.kind === 'diagram') {
            lines.push(
                `DIAGRAM ${block.blockId} — ` +
                `${block.declarations.length} linked declarations`
            );
            return;
        }
        const identity =
            `${block.declaration.moduleId}.${block.declaration.declarationId}`;
        if (block.status === 'complete') {
            lines.push(`CHECKED ${block.blockId} — ${identity}`);
            return;
        }
        lines.push(`OPEN ${block.blockId} — ${identity}`);
        block.goals.forEach(goal => {
            lines.push(`  Goal ${goal.id}`);
            goal.context.forEach(binding => {
                lines.push(`    ${binding.name} : ${binding.type}`);
            });
            lines.push(`    |- ${goal.target}`);
        });
    });
    lines.push(
        '',
        'Release gate: byte parity with the Node-verified workspace is ' +
            'checked outside the browser.'
    );
    return lines.join('\n');
}
