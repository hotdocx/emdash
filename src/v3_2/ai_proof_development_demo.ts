/** Direct-TypeScript multi-proof source for command and authoring examples. */

import {
    binderMode,
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelPi,
    provenance,
    sourceSpan
} from './kernel';
import {
    coreProofPlanExact,
    coreProofPlanHole,
    coreProofPlanIntro
} from './proof_plan';
import {
    createCoreProofArtifactFingerprint
} from './proof_document';
import {
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    createCoreLfDeclarationWorkspace
} from './lf_workspace';
import {
    CoreLfWorkspaceProofDocumentInput
} from './lf_workspace_proof';
import {
    CoreLfProofDevelopmentPlan,
    createCoreLfProofDevelopment
} from './lf_proof_development';
import {
    createCoreLfProofDevelopmentSourceSnapshot,
    serializeCoreLfProofDevelopmentSourceSnapshot
} from './lf_proof_development_source';

export const CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE = Object.freeze({
    revision: 'emdash-ai-proof-development-demo-v1' as const,
    moduleId: 'ai_native.development' as const,
    managementSourcePath:
        'src/v3_2/ai_proof_development_demo.ts' as const,
    authorityPath:
        'examples/ai_native_development.emdash.ts' as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

const moduleId = CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE.moduleId;
const authorityPath = CORE_AI_PROOF_DEVELOPMENT_DEMO_PROFILE.authorityPath;
const typeSymbol = coreLfQualifiedSymbol(moduleId, 'A');
const coreTypeName = 'ai_native_development_A';
const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;

const proofProvenance = (line: number, detail: string) => provenance(
    'surface',
    detail,
    sourceSpan(authorityPath, line, 1, line, 2)
);

const createWorkspace = () => {
    const module = createCoreLfModuleSpec({
        revision: 'ai-native-development-module-1',
        moduleId,
        fragmentId: 'declarations',
        authorityPath,
        sourceSha256: hash('a'),
        dependencies: [],
        externalSymbols: [],
        declarations: [{
            order: 0,
            symbol: typeSymbol,
            type: { tag: 'type' },
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque'
            },
            provenance: {
                authorityPath,
                sourceFragment: 'symbol A : TYPE;'
            }
        }],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'ai-native-development-policy-1',
        moduleRevision: module.revision,
        entries: [{
            order: 0,
            target: { kind: 'declaration', symbol: typeSymbol },
            policy: 'opaque-signature',
            evidence: 'direct TypeScript proof-development demo'
        }]
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'ai-native-development-linkage-1',
        moduleRevision: module.revision,
        entries: [{
            order: 0,
            symbol: typeSymbol,
            kind: 'free-declaration',
            coreName: coreTypeName,
            backendName: 'A'
        }]
    });
    return createCoreLfDeclarationWorkspace({
        revision: 'ai-native-development-workspace-1',
        modules: [{ module, policy, linkage }]
    });
};

const proofType = () => kernelPi(
    kernelBinder(
        'value',
        kernelFree(
            coreTypeName,
            proofProvenance(20, 'demo identity domain')
        ),
        binderMode('explicit', 'functorial'),
        proofProvenance(20, 'demo identity binder')
    ),
    kernelFree(
        coreTypeName,
        proofProvenance(20, 'demo identity codomain')
    ),
    proofProvenance(20, 'demo identity type')
);

const fingerprint = (declarationId: string) =>
    createCoreProofArtifactFingerprint({
        source: {
            id: `${authorityPath}#${declarationId}`,
            sha256: hash(declarationId === 'complete_identity' ? 'b' : 'c')
        },
        profileSha256: hash('d'),
        dependencies: [{
            moduleId,
            interfaceSha256: hash('e')
        }]
    });

const proof = (
    declarationId: 'complete_identity' | 'open_identity'
): CoreLfWorkspaceProofDocumentInput => {
    const open = declarationId === 'open_identity';
    return {
        moduleId,
        declarationId,
        type: proofType(),
        plan: coreProofPlanIntro(
            open
                ? coreProofPlanHole('body', {
                    provenance: proofProvenance(32, 'named demo hole'),
                    expectation: {
                        contextDepth: 1,
                        target: kernelFree(
                            coreTypeName,
                            proofProvenance(32, 'expected demo target')
                        )
                    }
                })
                : coreProofPlanExact(kernelBound(
                    0,
                    proofProvenance(28, 'introduced demo value')
                )),
            {
                name: 'value',
                provenance: proofProvenance(
                    open ? 31 : 27,
                    'demo identity introduction'
                )
            }
        ),
        provenance: proofProvenance(
            open ? 30 : 26,
            `${declarationId} theorem root`
        ),
        fingerprint: fingerprint(declarationId)
    };
};

/** Build fresh inert source data; no process or filesystem state is retained. */
export const createCoreAiProofDevelopmentDemo = (
): CoreLfProofDevelopmentPlan => createCoreLfProofDevelopment({
    revision: 'ai-native-proof-development-demo-1',
    workspace: createWorkspace(),
    proofs: [proof('open_identity'), proof('complete_identity')]
});

/** Materialize the direct TypeScript builders to exact canonical data. */
export const createCoreAiProofDevelopmentDemoSourceText = (): string =>
    serializeCoreLfProofDevelopmentSourceSnapshot(
        createCoreLfProofDevelopmentSourceSnapshot(
            createCoreAiProofDevelopmentDemo()
        )
    );
