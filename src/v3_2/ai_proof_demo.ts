/**
 * One direct-TypeScript local module for the first AI-native proof commands.
 *
 * It intentionally contains one complete and one incomplete theorem. The
 * module itself performs no filesystem access, hashing, process I/O, parsing,
 * or backend invocation.
 */

import {
    CoreBindingInput,
    CoreDeclarationEnvironment
} from './context';
import {
    BinderMode,
    KernelExpression,
    binderMode,
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelPi,
    kernelUniverse,
    provenance,
    sourceSpan
} from './kernel';
import {
    CoreProofPlan,
    coreProofPlanExact,
    coreProofPlanHole,
    coreProofPlanIntro
} from './proof_plan';
import {
    CoreProofArtifactFingerprint,
    CoreProofDocumentCompilation,
    compileCoreProofDocument,
    createCoreProofArtifactFingerprint
} from './proof_document';

export const CORE_AI_PROOF_DEMO_SOURCE_PATH =
    'src/v3_2/ai_proof_demo.ts' as const;
export const CORE_AI_PROOF_DEMO_MODULE_ID =
    'ai_native.local' as const;
export const CORE_AI_PROOF_DEMO_DECLARATION_IDS = Object.freeze([
    'complete_identity',
    'open_identity'
] as const);

export type CoreAiProofDemoDeclarationId =
    typeof CORE_AI_PROOF_DEMO_DECLARATION_IDS[number];

const at = (line: number) => sourceSpan(
    CORE_AI_PROOF_DEMO_SOURCE_PATH,
    line,
    1,
    line,
    2
);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitNatural = binderMode('explicit', 'natural');
const explicitFunctorial = binderMode('explicit', 'functorial');

const declaration = (
    name: string,
    type: KernelExpression,
    mode: BinderMode,
    line: number
): CoreBindingInput => ({
    name,
    type,
    mode,
    provenance: because(line, `AI proof demo declaration ${name}`)
});

const createEnvironment = (): CoreDeclarationEnvironment =>
    CoreDeclarationEnvironment.empty().extend(declaration(
        'AIProofA',
        kernelUniverse(because(48, 'AI proof demo universe')),
        explicitFunctorial,
        48
    ));

const environment = createEnvironment();

const typeA = (line: number): KernelExpression => kernelFree(
    'AIProofA',
    because(line, 'AI proof demo use of A')
);

const identityType = (
    declarationId: CoreAiProofDemoDeclarationId,
    line: number
): KernelExpression => kernelPi(
    kernelBinder(
        'value',
        typeA(line),
        explicitNatural,
        because(line, `${declarationId} binder`)
    ),
    typeA(line),
    because(line, `${declarationId} type`)
);

const completeIdentityPlan = (): CoreProofPlan => coreProofPlanIntro(
    coreProofPlanExact(kernelBound(
        0,
        because(72, 'complete identity introduced value')
    )),
    {
        name: 'value',
        provenance: because(70, 'complete identity intro')
    }
);

const openIdentityPlan = (): CoreProofPlan => coreProofPlanIntro(
    coreProofPlanHole('body', {
        provenance: because(82, 'open identity body hole'),
        expectation: {
            contextDepth: 1,
            target: typeA(82)
        }
    }),
    {
        name: 'value',
        provenance: because(80, 'open identity intro')
    }
);

export const createCoreAiProofDemoFingerprint = (
    sourceSha256: string,
    profileSha256: string
): CoreProofArtifactFingerprint => createCoreProofArtifactFingerprint({
    source: {
        id: CORE_AI_PROOF_DEMO_SOURCE_PATH,
        sha256: sourceSha256
    },
    profileSha256,
    dependencies: []
});

const isDeclarationId = (
    value: string
): value is CoreAiProofDemoDeclarationId =>
    CORE_AI_PROOF_DEMO_DECLARATION_IDS.some(candidate => candidate === value);

export function compileCoreAiProofDemo(
    declarationId: string,
    fingerprint: CoreProofArtifactFingerprint
): CoreProofDocumentCompilation {
    if (!isDeclarationId(declarationId)) {
        throw new Error(
            `Unknown AI proof demo declaration '${declarationId}'; expected ` +
            CORE_AI_PROOF_DEMO_DECLARATION_IDS.join(' or ')
        );
    }

    const complete = declarationId === 'complete_identity';
    const line = complete ? 70 : 80;
    return compileCoreProofDocument({
        moduleId: CORE_AI_PROOF_DEMO_MODULE_ID,
        declarationId,
        environment,
        type: identityType(declarationId, line),
        plan: complete
            ? completeIdentityPlan()
            : openIdentityPlan(),
        provenance: because(line, `${declarationId} theorem root`),
        fingerprint
    });
}
