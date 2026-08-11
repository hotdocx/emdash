/**
 * Browser-safe representative LF proof-patch corpus for AGENT-EVAL-12B1.
 *
 * Every reference attempt is generated through the named existing owner and
 * accepted (or deliberately abstained) by the unchanged 12A evaluator. This
 * module is an internal fixed corpus: it has no model, filesystem, network,
 * clock, process, persistence, or public package dependency.
 */

import {
    CoreLfQualifiedSymbol,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferPolicyEntry,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfTransferDeclarationLinkage,
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfDeclarationWorkspacePlan,
    compileCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspace,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreLfProofDevelopmentSourceSnapshot,
    createCoreLfProofDevelopmentSourceSnapshot
} from './lf_proof_development_source';
import {
    createCoreLfProofDevelopment
} from './lf_proof_development';
import {
    CoreLfWorkspaceProofDocumentInput,
    compileCoreLfWorkspaceProofDocument
} from './lf_workspace_proof';
import {
    KernelExpression,
    binderMode,
    kernelApplication,
    kernelBound,
    kernelCall,
    kernelFree,
    provenance,
    sourceSpan
} from './kernel';
import {
    CORE_PROOF_PLAN_MACRO_PROFILE,
    CORE_PROOF_PLAN_PROFILE,
    CoreProofPlan,
    coreProofPlanConstructor,
    coreProofPlanExact,
    coreProofPlanHave,
    coreProofPlanHole
} from './proof_plan';
import {
    createCoreProofArtifactFingerprint
} from './proof_document';
import {
    CORE_PROOF_REFINE_TEMPLATE_PROFILE,
    coreProofPlanRefine,
    coreProofTemplateBinding,
    coreProofTemplateCall,
    coreProofTemplateCore,
    coreProofTemplatePlaceholder
} from './proof_template';
import {
    applyCoreProofPlanPatch,
    createCoreProofPlanHoleReplacement
} from './proof_plan_patch';
import {
    createCoreLfAccessiblePremiseIndex
} from './lf_premise_index';
import {
    CORE_OBVIOUS_PROOF_PROVIDER_PROFILE,
    proposeCoreObviousProofPlanPatches,
    serializeCoreObviousProofProposalReport
} from './proof_obvious';
import {
    CORE_LF_PROOF_MAINTENANCE_PROFILE,
    proposeCoreLfProofRepairs,
    replayCoreLfProofRepairCandidate,
    serializeCoreLfProofRepairCandidateReplay,
    serializeCoreLfProofRepairProposal
} from './lf_proof_maintenance';
import {
    CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE,
    CoreLfProofAgentBenchmarkAttempt,
    CoreLfProofAgentBenchmarkCase,
    CoreLfProofAgentBenchmarkOutcome,
    CoreLfProofAgentBenchmarkReport,
    createCoreLfProofAgentBenchmarkAttempt,
    createCoreLfProofAgentBenchmarkCase,
    createCoreLfProofAgentBenchmarkRun,
    createCoreLfProofAgentBenchmarkSuite,
    evaluateCoreLfProofAgentBenchmarkRun
} from './lf_proof_agent_benchmark';
import {
    CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE,
    parseCoreLfProofAgentBenchmarkReportText
} from './lf_proof_agent_interchange';
import {
    CoreLfStructureDeclarationExpansion,
    CoreLfStructureMacroScope
} from './lf_structure_macro';
import {
    CoreLfClassMethodIdentity,
    CoreLfClassSchema,
    coreLfClassParameterTerm,
    declareCoreLfClassSchema
} from './lf_class_schema';
import {
    CoreLfClassInheritanceLayout,
    planCoreLfClassInheritance
} from './lf_class_inheritance';
import {
    CORE_LF_CLASS_INHERITANCE_LOWERING_PROFILE,
    CoreLfClassInheritanceLoweringExpansion,
    lowerCoreLfClassInheritance
} from './lf_class_inheritance_lowering';
import {
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import {
    CoreLfInstanceProviderDeclaration,
    createCoreLfInstanceRegistrySnapshot,
    createCoreLfInstanceScopeSnapshot,
    declareCoreLfGlobalInstanceProvider,
    declareCoreLfSuperclassInstanceProvider
} from './lf_instance_scope';
import {
    CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
    serializeCoreLfInstanceSynthesisReport,
    synthesizeCoreLfInstance
} from './lf_instance_synthesis';
import {
    createCoreLfChecker
} from './lf_checker';
import {
    CORE_LF_CLASS_CALL_ELABORATION_PROFILE,
    elaborateCoreLfSaturatedClassCall,
    serializeCoreLfClassCallElaborationReport
} from './lf_class_call_elaboration';
import {
    CORE_PROOF_SIMPLIFIER_PROFILE,
    coreProofSimplifierAdapter,
    coreProofSimplifierRule,
    simplifyCoreProofPlan
} from './proof_simplifier';

export const CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-agent-public-corpus-v1' as const,
    benchmarkProfileRevision:
        CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
    interchangeProfileRevision:
        CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.revision,
    suiteRevision: 'emdash-public-proof-agent-suite-v1' as const,
    referenceRunRevision: 'emdash-public-proof-agent-reference-run-v1' as const,
    trackOrder: Object.freeze([
        'explicit-proof-construction',
        'source-proof-management',
        'bounded-automation',
        'structures-classes-instances',
        'maintenance-revision',
        'lean4-manual-translation'
    ] as const),
    caseOrder: 'track-then-case-id' as const,
    selectedTrackCount: 6,
    selectedCaseCount: 10,
    minimumTrackCount: 6,
    minimumCaseCount: 8,
    referenceEvidenceClass:
        'owner-generated-baseline-freshly-scored-not-proof-authority' as const,
    leanSourceCheckpoint:
        'f29e9e488ea8242c875806e4b0564820c2d553b2' as const,
    leanSourcePath: 'tests/elab/diamond1.lean' as const,
    leanSourceSha256:
        'ca443749e65db8cb1e399446e1a9221cea0a944eda197852d2191dd767cdd3b6' as const,
    leanLicense: 'Apache-2.0' as const,
    manualLeanTranslationOnly: true as const,
    parserParityClaimed: false as const,
    changesBenchmarkSemantics: false as const,
    publicBarrelExported: false as const,
    nodeRunnerIncluded: false as const,
    invokesModel: false as const,
    invokesLambdapi: false as const,
    performsIo: false as const,
    accessesNetwork: false as const,
    acquiresTime: false as const,
    computesCryptographicHashes: false as const,
    persistsSource: false as const,
    retainsSessionState: false as const,
    nodeBuiltinDependency: false as const
});

export type CoreLfProofAgentPublicCorpusTrack =
    typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.trackOrder[number];

export type CoreLfProofAgentPublicCorpusOrigin =
    | 'emdash-native'
    | 'lean4-manual-translation';

export type CoreLfProofAgentPublicCorpusOwnerEvidenceKind =
    | 'proof-plan-construction'
    | 'proof-template-and-goal-coupling'
    | 'bounded-obvious-proof'
    | 'proof-simplifier'
    | 'instance-synthesis'
    | 'instance-ambiguity'
    | 'proof-maintenance'
    | 'class-call-elaboration';

export interface CoreLfProofAgentPublicCorpusOwnerEvidence {
    readonly kind: CoreLfProofAgentPublicCorpusOwnerEvidenceKind;
    readonly ownerRevision: string;
    readonly facts: readonly string[];
    readonly reportText: string | null;
    readonly evidenceClass: 'owner-output-not-curator-label';
}

export interface CoreLfProofAgentPublicCorpusEntry {
    readonly id: string;
    readonly track: CoreLfProofAgentPublicCorpusTrack;
    readonly origin: CoreLfProofAgentPublicCorpusOrigin;
    readonly sourceOwner: string;
    readonly referenceOwner: string;
    readonly features: readonly string[];
    readonly caseId: string;
    readonly expectedReferenceOutcome: CoreLfProofAgentBenchmarkOutcome;
    readonly actualReferenceOutcome: CoreLfProofAgentBenchmarkOutcome;
    readonly ownerEvidence: CoreLfProofAgentPublicCorpusOwnerEvidence;
    readonly referenceAttemptIsProofAuthority: false;
}

export interface CoreLfProofAgentPublicCorpusTrackSummary {
    readonly id: CoreLfProofAgentPublicCorpusTrack;
    readonly minimumCases: number;
    readonly selectedCases: number;
}

export interface CoreLfProofAgentPublicCorpus {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.revision;
    readonly benchmarkProfileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision;
    readonly interchangeProfileRevision:
        typeof CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.revision;
    readonly tracks: readonly CoreLfProofAgentPublicCorpusTrackSummary[];
    readonly entries: readonly CoreLfProofAgentPublicCorpusEntry[];
    readonly referenceReport: CoreLfProofAgentBenchmarkReport;
    readonly leanAttribution: {
        readonly repository: 'leanprover/lean4';
        readonly checkpoint:
            typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE
                .leanSourceCheckpoint;
        readonly sourcePath:
            typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.leanSourcePath;
        readonly sourceSha256:
            typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.leanSourceSha256;
        readonly license:
            typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.leanLicense;
        readonly correspondence:
            'Foo/FooComm/FooAssoc/FooAC-diamond-to-explicit-class-evidence';
        readonly manualTranslationOnly: true;
        readonly parserParityClaimed: false;
    };
    readonly meaning:
        'representative-reference-baselines-freshly-scored-not-agent-results';
    readonly naturalLanguageReasoningRequired: false;
    readonly hiddenProviderStateRetained: false;
    readonly referenceAttemptsAreProofAuthority: false;
    readonly curationLabelsAreKernelClaims: false;
}

export type CoreLfProofAgentPublicCorpusErrorCode =
    | 'CORPUS_OWNER_FAILED'
    | 'CORPUS_OUTCOME_MISMATCH'
    | 'INVALID_CORPUS_TEXT'
    | 'UNSUPPORTED_CORPUS_REVISION'
    | 'INVALID_CORPUS_ARTIFACT'
    | 'STALE_CORPUS_ARTIFACT'
    | 'NONCANONICAL_CORPUS_TEXT';

export class CoreLfProofAgentPublicCorpusError extends Error {
    constructor(
        public readonly code: CoreLfProofAgentPublicCorpusErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfProofAgentPublicCorpusError';
    }
}

const fail = (
    code: CoreLfProofAgentPublicCorpusErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new CoreLfProofAgentPublicCorpusError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
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

const freezePortable = <T>(value: T, path: string): T => {
    let text: string | undefined;
    try {
        text = JSON.stringify(value);
    } catch (error: unknown) {
        return fail(
            'CORPUS_OWNER_FAILED',
            path,
            'Corpus owner data could not be serialized',
            error
        );
    }
    if (text === undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            path,
            'Corpus owner data cannot be undefined'
        );
    }
    const projected = JSON.parse(text) as T;
    serializeCoreLfWorkspaceCanonicalJson(projected, path);
    return deepFreeze(projected);
};

const portableCanonicalText = (value: unknown, path: string): string => {
    let text: string | undefined;
    try {
        text = JSON.stringify(value);
    } catch (error: unknown) {
        return fail(
            'CORPUS_OWNER_FAILED',
            path,
            'Owner evidence could not be projected to portable data',
            error
        );
    }
    if (text === undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            path,
            'Owner evidence cannot be undefined'
        );
    }
    return serializeCoreLfWorkspaceCanonicalJson(JSON.parse(text), path);
};

const hash = (digit: string): string => `sha256:${digit.repeat(64)}`;
const explicitFunctorial = binderMode('explicit', 'functorial');

const commonModuleId = 'emdash.public_corpus.native';
const commonAuthorityPath =
    'src/v3_2/fixtures/public_proof_agent_native.emdash.ts';
const commonSymbols = {
    P: coreLfQualifiedSymbol(commonModuleId, 'P'),
    Q: coreLfQualifiedSymbol(commonModuleId, 'Q'),
    p: coreLfQualifiedSymbol(commonModuleId, 'p'),
    q: coreLfQualifiedSymbol(commonModuleId, 'q'),
    pToQ: coreLfQualifiedSymbol(commonModuleId, 'p_to_q'),
    family: coreLfQualifiedSymbol(commonModuleId, 'Family'),
    familyWitness: coreLfQualifiedSymbol(commonModuleId, 'family_witness'),
    dependentConstructor: coreLfQualifiedSymbol(commonModuleId, 'dependent_q')
} as const;
const commonCoreNames = {
    P: 'public_corpus_P',
    Q: 'public_corpus_Q',
    p: 'public_corpus_p',
    q: 'public_corpus_q',
    pToQ: 'public_corpus_p_to_q',
    family: 'public_corpus_family',
    familyWitness: 'public_corpus_family_witness',
    dependentConstructor: 'public_corpus_dependent_q'
} as const;

const transferGlobal = (symbol: CoreLfQualifiedSymbol) => ({
    tag: 'global' as const,
    symbol
});
const transferBound = (index: number) => ({
    tag: 'bound' as const,
    index
});
const transferCall = (
    callee: CoreLfTransferExpression,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => ({
    tag: 'call',
    callee,
    arguments: arguments_
});
const transferPi = (
    hint: string,
    type: CoreLfTransferExpression,
    body: CoreLfTransferExpression,
    plicity: 'explicit' | 'implicit' = 'explicit'
): CoreLfTransferExpression => ({
    tag: 'pi',
    binder: {
        hint,
        mode: { plicity, variation: 'functorial' },
        type
    },
    body
});

const sourceProvenance = (
    authorityPath: string,
    sourceFragment: string
) => ({ authorityPath, sourceFragment });

const opaqueModifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const commonWorkspace = (): CoreLfDeclarationWorkspacePlan => {
    const g = transferGlobal;
    const declarations: readonly CoreLfTransferDeclaration[] = [{
        order: 0,
        symbol: commonSymbols.P,
        type: { tag: 'type' },
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(commonAuthorityPath, 'symbol P : TYPE;')
    }, {
        order: 1,
        symbol: commonSymbols.Q,
        type: { tag: 'type' },
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(commonAuthorityPath, 'symbol Q : TYPE;')
    }, {
        order: 2,
        symbol: commonSymbols.p,
        type: g(commonSymbols.P),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(commonAuthorityPath, 'symbol p : P;')
    }, {
        order: 3,
        symbol: commonSymbols.q,
        type: g(commonSymbols.Q),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(commonAuthorityPath, 'symbol q : Q;')
    }, {
        order: 4,
        symbol: commonSymbols.pToQ,
        type: transferPi('premise', g(commonSymbols.P), g(commonSymbols.Q)),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            commonAuthorityPath,
            'symbol p_to_q (premise : P) : Q;'
        )
    }, {
        order: 5,
        symbol: commonSymbols.family,
        type: transferPi(
            'index',
            g(commonSymbols.P),
            { tag: 'type' }
        ),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            commonAuthorityPath,
            'symbol Family (index : P) : TYPE;'
        )
    }, {
        order: 6,
        symbol: commonSymbols.familyWitness,
        type: transferPi(
            'index',
            g(commonSymbols.P),
            transferCall(g(commonSymbols.family), [{
                plicity: 'explicit',
                value: transferBound(0)
            }])
        ),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            commonAuthorityPath,
            'symbol family_witness (index : P) : Family(index);'
        )
    }, {
        order: 7,
        symbol: commonSymbols.dependentConstructor,
        type: transferPi(
            'index',
            g(commonSymbols.P),
            transferPi(
                'witness',
                transferCall(g(commonSymbols.family), [{
                    plicity: 'explicit',
                    value: transferBound(0)
                }]),
                g(commonSymbols.Q)
            )
        ),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            commonAuthorityPath,
            'symbol dependent_q (index : P) ' +
                '(witness : Family(index)) : Q;'
        )
    }];
    const module = createCoreLfModuleSpec({
        revision: 'public-proof-agent-native-module-v1',
        moduleId: commonModuleId,
        fragmentId: 'native-declarations',
        authorityPath: commonAuthorityPath,
        sourceSha256: hash('1'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'public-proof-agent-native-policy-v1',
        moduleRevision: module.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: { kind: 'declaration', symbol: declaration.symbol },
            policy: 'opaque-signature',
            evidence: 'AGENT-EVAL-12B1 checked native fixture declaration'
        }))
    });
    const names = new Map<CoreLfQualifiedSymbol, string>([
        [commonSymbols.P, commonCoreNames.P],
        [commonSymbols.Q, commonCoreNames.Q],
        [commonSymbols.p, commonCoreNames.p],
        [commonSymbols.q, commonCoreNames.q],
        [commonSymbols.pToQ, commonCoreNames.pToQ],
        [commonSymbols.family, commonCoreNames.family],
        [commonSymbols.familyWitness, commonCoreNames.familyWitness],
        [
            commonSymbols.dependentConstructor,
            commonCoreNames.dependentConstructor
        ]
    ]);
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'public-proof-agent-native-linkage-v1',
        moduleRevision: module.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            symbol: declaration.symbol,
            kind: 'free-declaration',
            coreName: names.get(declaration.symbol)!,
            backendName: declaration.symbol.name
        }))
    });
    return createCoreLfDeclarationWorkspace({
        revision: 'public-proof-agent-native-workspace-v1',
        modules: [{ module, policy, linkage }]
    });
};

const proofProvenance = (
    authorityPath: string,
    line: number,
    detail: string
) => provenance(
    'surface',
    detail,
    sourceSpan(authorityPath, line, 1, line, 2)
);

interface BuiltBenchmarkCase {
    readonly benchmarkCase: CoreLfProofAgentBenchmarkCase;
    readonly previousSource: CoreLfProofDevelopmentSourceSnapshot;
    readonly currentSource: CoreLfProofDevelopmentSourceSnapshot;
}

const buildBenchmarkCase = (input: {
    readonly id: string;
    readonly ordinal: number;
    readonly workspace: CoreLfDeclarationWorkspacePlan;
    readonly moduleId: string;
    readonly type: KernelExpression;
    readonly previousPlan: CoreProofPlan;
    readonly relevantPremises: readonly CoreLfQualifiedSymbol[];
}): BuiltBenchmarkCase => {
    const declarationId = `proof_${input.ordinal}`;
    const goalId = `goal_${input.ordinal}`;
    const authorityPath =
        `src/v3_2/fixtures/public_agent_case_${input.ordinal}.emdash.ts`;
    const document = (
        version: 'previous' | 'current'
    ): CoreLfWorkspaceProofDocumentInput => ({
        moduleId: input.moduleId,
        declarationId,
        type: input.type,
        plan: version === 'previous'
            ? input.previousPlan
            : coreProofPlanHole(goalId, {
                provenance: proofProvenance(
                    authorityPath,
                    20,
                    `${input.id} selected source hole`
                ),
                expectation: { contextDepth: 0, target: input.type }
            }),
        provenance: proofProvenance(
            authorityPath,
            19,
            `${input.id} proof declaration`
        ),
        fingerprint: createCoreProofArtifactFingerprint({
            source: {
                id: authorityPath,
                sha256: hash(version === 'previous' ? '2' : '3')
            },
            profileSha256: hash('4'),
            dependencies: [{
                moduleId: input.moduleId,
                interfaceSha256: hash('5')
            }]
        })
    });
    const snapshot = (
        version: 'previous' | 'current'
    ): CoreLfProofDevelopmentSourceSnapshot =>
        createCoreLfProofDevelopmentSourceSnapshot(
            createCoreLfProofDevelopment({
                revision:
                    `public-agent-case-${input.ordinal}-${version}-v1`,
                workspace: input.workspace,
                proofs: [document(version)]
            })
        );
    const previousSource = snapshot('previous');
    const currentSource = snapshot('current');
    return {
        benchmarkCase: createCoreLfProofAgentBenchmarkCase({
            id: input.id,
            previousSource,
            currentSource,
            proof: { moduleId: input.moduleId, declarationId },
            goalId,
            relevantPremises: input.relevantPremises
        }),
        previousSource,
        currentSource
    };
};

interface BuiltCorpusEntry {
    readonly id: string;
    readonly track: CoreLfProofAgentPublicCorpusTrack;
    readonly origin: CoreLfProofAgentPublicCorpusOrigin;
    readonly sourceOwner: string;
    readonly referenceOwner: string;
    readonly features: readonly string[];
    readonly expectedReferenceOutcome: CoreLfProofAgentBenchmarkOutcome;
    readonly benchmarkCase: CoreLfProofAgentBenchmarkCase;
    readonly attempt: CoreLfProofAgentBenchmarkAttempt;
    readonly ownerEvidence: CoreLfProofAgentPublicCorpusOwnerEvidence;
}

const evidence = (
    kind: CoreLfProofAgentPublicCorpusOwnerEvidenceKind,
    ownerRevision: string,
    facts: readonly string[],
    reportText: string | null = null
): CoreLfProofAgentPublicCorpusOwnerEvidence => freezePortable({
    kind,
    ownerRevision,
    facts,
    reportText,
    evidenceClass: 'owner-output-not-curator-label' as const
}, `ownerEvidence.${kind}`);

const patchAttempt = (
    benchmarkCase: CoreLfProofAgentBenchmarkCase,
    replacement: CoreProofPlan,
    retrievedPremises: readonly CoreLfQualifiedSymbol[] = []
): CoreLfProofAgentBenchmarkAttempt =>
    createCoreLfProofAgentBenchmarkAttempt({
        benchmarkCase,
        retrievedPremises,
        decision: {
            kind: 'patch',
            patch: createCoreProofPlanHoleReplacement(
                benchmarkCase.goalId,
                replacement
            )
        }
    });

const nativeEntryBase = (
    input: Omit<BuiltCorpusEntry, 'origin'>
): BuiltCorpusEntry => ({ ...input, origin: 'emdash-native' });

const buildNativeEntries = (): readonly BuiltCorpusEntry[] => {
    const workspace = commonWorkspace();
    const compiled = compileCoreLfDeclarationWorkspace(workspace);
    const nativePath = commonAuthorityPath;
    const P = kernelFree(
        commonCoreNames.P,
        proofProvenance(nativePath, 100, 'native P')
    );
    const Q = kernelFree(
        commonCoreNames.Q,
        proofProvenance(nativePath, 101, 'native Q')
    );
    const p = () => kernelFree(
        commonCoreNames.p,
        proofProvenance(nativePath, 102, 'native p')
    );
    const q = () => kernelFree(
        commonCoreNames.q,
        proofProvenance(nativePath, 103, 'native q')
    );
    const pToQ = () => kernelFree(
        commonCoreNames.pToQ,
        proofProvenance(nativePath, 104, 'native p_to_q')
    );

    const exactPlan = coreProofPlanExact(p());
    const exactCase = buildBenchmarkCase({
        id: 'native.exact.local-premise',
        ordinal: 1,
        workspace,
        moduleId: commonModuleId,
        type: P,
        previousPlan: exactPlan,
        relevantPremises: [commonSymbols.p]
    });
    const exactEntry = nativeEntryBase({
        id: exactCase.benchmarkCase.id,
        track: 'explicit-proof-construction',
        sourceOwner: 'lf-proof-development-source',
        referenceOwner: 'coreProofPlanExact',
        features: ['named-hole', 'exact-premise', 'fresh-replay'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: exactCase.benchmarkCase,
        attempt: patchAttempt(
            exactCase.benchmarkCase,
            coreProofPlanExact(p()),
            [commonSymbols.p]
        ),
        ownerEvidence: evidence(
            'proof-plan-construction',
            CORE_PROOF_PLAN_PROFILE.revision,
            ['coreProofPlanExact generated the replacement plan']
        )
    });

    const applyPlan = coreProofPlanConstructor(
        pToQ(),
        [coreProofPlanExact(p())]
    );
    const applyCase = buildBenchmarkCase({
        id: 'native.apply.explicit-premise',
        ordinal: 2,
        workspace,
        moduleId: commonModuleId,
        type: Q,
        previousPlan: coreProofPlanExact(q()),
        relevantPremises: [commonSymbols.pToQ, commonSymbols.p]
    });
    const applyEntry = nativeEntryBase({
        id: applyCase.benchmarkCase.id,
        track: 'explicit-proof-construction',
        sourceOwner: 'lf-proof-development-source',
        referenceOwner: 'coreProofPlanConstructor-as-apply',
        features: ['named-hole', 'one-step-apply', 'relevant-premise-rank'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: applyCase.benchmarkCase,
        attempt: patchAttempt(
            applyCase.benchmarkCase,
            applyPlan,
            [commonSymbols.pToQ, commonSymbols.p]
        ),
        ownerEvidence: evidence(
            'proof-plan-construction',
            CORE_PROOF_PLAN_MACRO_PROFILE.revision,
            [
                'coreProofPlanConstructor lowered to an ordinary apply plan',
                'the explicit premise remained an ordinary exact subplan'
            ]
        )
    });

    const havePlan = coreProofPlanHave(
        {
            name: 'fact',
            type: P,
            mode: explicitFunctorial,
            provenance: proofProvenance(nativePath, 110, 'have binder')
        },
        coreProofPlanExact(p()),
        coreProofPlanExact(kernelBound(
            0,
            proofProvenance(nativePath, 111, 'have-bound fact')
        ))
    );
    const haveCase = buildBenchmarkCase({
        id: 'native.have.checked-fact',
        ordinal: 3,
        workspace,
        moduleId: commonModuleId,
        type: P,
        previousPlan: exactPlan,
        relevantPremises: [commonSymbols.p]
    });
    const haveEntry = nativeEntryBase({
        id: haveCase.benchmarkCase.id,
        track: 'source-proof-management',
        sourceOwner: 'proof-plan',
        referenceOwner: 'coreProofPlanHave',
        features: ['contextual-have', 'retained-source-obligation'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: haveCase.benchmarkCase,
        attempt: patchAttempt(haveCase.benchmarkCase, havePlan),
        ownerEvidence: evidence(
            'proof-plan-construction',
            CORE_PROOF_PLAN_PROFILE.revision,
            [
                'coreProofPlanHave generated an ordinary contextual plan',
                'the body consumes the checked local fact by De Bruijn index'
            ]
        )
    });

    const indexBinder = {
        name: 'index',
        type: P,
        mode: explicitFunctorial,
        provenance: proofProvenance(nativePath, 121, 'refine index binder')
    };
    const refineTemplate = coreProofTemplateCall(
        coreProofTemplateCore(kernelFree(
            commonCoreNames.pToQ,
            proofProvenance(nativePath, 123, 'p_to_q refine callee')
        )),
        [{
            plicity: 'explicit',
            value: coreProofTemplatePlaceholder(
                'index',
                proofProvenance(nativePath, 123, 'index placeholder')
            )
        }],
        proofProvenance(nativePath, 123, 'typed refine template')
    );
    const refinePlan = coreProofPlanRefine(refineTemplate, [
        coreProofTemplateBinding(indexBinder, coreProofPlanExact(p()))
    ]);
    const openCoupledPlan = coreProofPlanConstructor(
        kernelFree(
            commonCoreNames.dependentConstructor,
            proofProvenance(nativePath, 124, 'dependent coupling callee')
        ),
        [coreProofPlanHole(
            'refine_index',
            {
                provenance: proofProvenance(
                    nativePath,
                    125,
                    'refine index source hole'
                )
            }
        ), coreProofPlanHole(
            'refine_witness',
            {
                provenance: proofProvenance(
                    nativePath,
                    126,
                    'refine witness source hole'
                )
            }
        )]
    );
    const coupling = compileCoreLfWorkspaceProofDocument(compiled, {
        moduleId: commonModuleId,
        declarationId: 'refine_coupling_evidence',
        type: Q,
        plan: openCoupledPlan,
        provenance: proofProvenance(nativePath, 127, 'coupling evidence'),
        fingerprint: createCoreProofArtifactFingerprint({
            source: { id: commonAuthorityPath, sha256: hash('6') },
            profileSha256: hash('7'),
            dependencies: [{
                moduleId: commonModuleId,
                interfaceSha256: hash('8')
            }]
        })
    });
    const refineCase = buildBenchmarkCase({
        id: 'native.refine.coupled-goals',
        ordinal: 4,
        workspace,
        moduleId: commonModuleId,
        type: Q,
        previousPlan: coreProofPlanExact(q()),
        relevantPremises: [
            commonSymbols.dependentConstructor,
            commonSymbols.familyWitness,
            commonSymbols.p
        ]
    });
    const refineEntry = nativeEntryBase({
        id: refineCase.benchmarkCase.id,
        track: 'source-proof-management',
        sourceOwner: 'proof-template-and-goal-coupling',
        referenceOwner: 'coreProofPlanRefine',
        features: ['typed-placeholder', 'direct-goal-coupling'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: refineCase.benchmarkCase,
        attempt: patchAttempt(refineCase.benchmarkCase, refinePlan),
        ownerEvidence: evidence(
            'proof-template-and-goal-coupling',
            CORE_PROOF_REFINE_TEMPLATE_PROFILE.revision,
            [
                'coreProofPlanRefine lowered two typed placeholders to base plans',
                `open owner replay exposed ${coupling.proofCompilation.goalGraph.edges.length} direct coupling edge`
            ],
            portableCanonicalText({
                state: coupling.artifact.proofArtifact.state,
                goalGraph: coupling.proofCompilation.goalGraph
            }, 'refineOwnerEvidence')
        )
    });

    const obviousCase = buildBenchmarkCase({
        id: 'native.automation.obvious-apply',
        ordinal: 5,
        workspace,
        moduleId: commonModuleId,
        type: Q,
        previousPlan: coreProofPlanExact(q()),
        relevantPremises: [commonSymbols.pToQ, commonSymbols.p]
    });
    const rootPlan = coreProofPlanHole(obviousCase.benchmarkCase.goalId, {
        provenance: proofProvenance(nativePath, 130, 'obvious root hole')
    });
    const index = createCoreLfAccessiblePremiseIndex(
        compiled,
        commonModuleId
    );
    const rootProposal = proposeCoreObviousProofPlanPatches({
        index,
        type: Q,
        plan: rootPlan,
        goalId: obviousCase.benchmarkCase.goalId,
        seed: 'public-corpus-obvious-root-v1'
    });
    const applyCandidate = rootProposal.candidates.find(candidate =>
        candidate.operation === 'apply' &&
        candidate.premise.symbol.name === commonSymbols.pToQ.name
    );
    if (applyCandidate === undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.automation.obvious-apply.root',
            'Obvious-proof owner did not generate the selected apply patch'
        );
    }
    const partialPlan = applyCoreProofPlanPatch(
        rootPlan,
        applyCandidate.patch
    );
    const generatedGoalId = applyCandidate.generatedGoalIds[0];
    if (generatedGoalId === undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.automation.obvious-apply.generatedGoal',
            'Selected apply candidate did not expose its explicit premise'
        );
    }
    const completionProposal = proposeCoreObviousProofPlanPatches({
        index,
        type: Q,
        plan: partialPlan,
        goalId: generatedGoalId,
        seed: 'public-corpus-obvious-completion-v1'
    });
    const exactCandidate = completionProposal.candidates.find(candidate =>
        candidate.operation === 'exact' &&
        candidate.premise.symbol.name === commonSymbols.p.name
    );
    if (exactCandidate === undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.automation.obvious-apply.completion',
            'Obvious-proof owner did not close the generated premise'
        );
    }
    const completedObviousPlan = applyCoreProofPlanPatch(
        partialPlan,
        exactCandidate.patch
    );
    const obviousEntry = nativeEntryBase({
        id: obviousCase.benchmarkCase.id,
        track: 'bounded-automation',
        sourceOwner: 'proof-obvious',
        referenceOwner: 'proposeCoreObviousProofPlanPatches',
        features: ['exact-premise-index', 'bounded-candidates', 'checked-replay'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: obviousCase.benchmarkCase,
        attempt: patchAttempt(
            obviousCase.benchmarkCase,
            completedObviousPlan,
            [commonSymbols.pToQ, commonSymbols.p]
        ),
        ownerEvidence: evidence(
            'bounded-obvious-proof',
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
            [
                'the provider generated the root one-step apply patch',
                'the provider generated the exact patch for its named premise',
                'the two inert owner patches compose to the reference replacement'
            ],
            serializeCoreLfWorkspaceCanonicalJson({
                root: JSON.parse(
                    serializeCoreObviousProofProposalReport(rootProposal)
                ),
                completion: JSON.parse(
                    serializeCoreObviousProofProposalReport(
                        completionProposal
                    )
                )
            }, 'obviousOwnerEvidence')
        )
    });

    const maintenanceCase = buildBenchmarkCase({
        id: 'native.maintenance.changed-source',
        ordinal: 9,
        workspace,
        moduleId: commonModuleId,
        type: P,
        previousPlan: coreProofPlanExact(p()),
        relevantPremises: [commonSymbols.p]
    });
    const proposal = proposeCoreLfProofRepairs({
        previousSource: maintenanceCase.previousSource,
        currentSource: maintenanceCase.currentSource,
        proof: maintenanceCase.benchmarkCase.proof,
        goalId: maintenanceCase.benchmarkCase.goalId,
        providerOptions: { seed: 'public-corpus-maintenance-v1' }
    });
    const candidateIndex = proposal.provider.candidates.findIndex(candidate =>
        candidate.operation === 'exact' &&
        candidate.premise.symbol.name === commonSymbols.p.name
    );
    if (candidateIndex < 0) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.maintenance.changed-source.candidate',
            'Maintenance owner did not generate the prior exact repair'
        );
    }
    const maintenanceReplay = replayCoreLfProofRepairCandidate({
        previousSource: maintenanceCase.previousSource,
        currentSource: maintenanceCase.currentSource,
        proposal,
        candidateIndex
    });
    const maintenanceEntry = nativeEntryBase({
        id: maintenanceCase.benchmarkCase.id,
        track: 'maintenance-revision',
        sourceOwner: 'lf-proof-maintenance',
        referenceOwner: 'accepted-maintenance-candidate-patch',
        features: ['previous-current-source', 'impact', 'stale-safe-replay'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: maintenanceCase.benchmarkCase,
        attempt: createCoreLfProofAgentBenchmarkAttempt({
            benchmarkCase: maintenanceCase.benchmarkCase,
            retrievedPremises: [commonSymbols.p],
            decision: { kind: 'patch', patch: maintenanceReplay.patch }
        }),
        ownerEvidence: evidence(
            'proof-maintenance',
            CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
            [
                'the source changed from a checked exact proof to a named hole',
                'the candidate was regenerated and replayed against exact current preconditions'
            ],
            serializeCoreLfWorkspaceCanonicalJson({
                proposal: JSON.parse(serializeCoreLfProofRepairProposal(
                    proposal
                )),
                replay: JSON.parse(
                    serializeCoreLfProofRepairCandidateReplay(
                        maintenanceReplay.snapshot
                    )
                )
            }, 'maintenanceOwnerEvidence')
        )
    });

    return Object.freeze([
        exactEntry,
        applyEntry,
        haveEntry,
        refineEntry,
        obviousEntry,
        maintenanceEntry
    ]);
};

interface CorpusClassEntry {
    readonly expansion: CoreLfStructureDeclarationExpansion;
    readonly schema: CoreLfClassSchema;
    readonly layout: CoreLfClassInheritanceLayout;
}

interface CorpusClassFixture {
    readonly moduleId: string;
    readonly module: ReturnType<typeof createCoreLfModuleSpec>;
    readonly workspace: CoreLfDeclarationWorkspacePlan;
    readonly compiled: ReturnType<typeof compileCoreLfMixedPhases>;
    readonly runtimeProgram:
        NonNullable<ReturnType<typeof compileCoreLfMixedPhases>['latestRuntime']>['runtime'];
    readonly classes: {
        readonly A: CorpusClassEntry;
        readonly B: CorpusClassEntry;
        readonly C: CorpusClassEntry;
        readonly D: CorpusClassEntry;
    };
    readonly lowerings: readonly CoreLfClassInheritanceLoweringExpansion[];
    readonly instanceSymbols: {
        readonly a1: CoreLfQualifiedSymbol;
        readonly a2: CoreLfQualifiedSymbol;
        readonly d: CoreLfQualifiedSymbol;
    };
    readonly parameterValue: CoreLfQualifiedSymbol;
    readonly leanUse: CoreLfQualifiedSymbol;
    readonly coreName: (symbol: CoreLfQualifiedSymbol) => string;
}

const classSymbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const buildClassFixture = (): CorpusClassFixture => {
    const moduleId = 'emdash.public_corpus.classes';
    const authorityPath =
        'src/v3_2/fixtures/public_proof_agent_classes.emdash.ts';
    const symbol = (name: string): CoreLfQualifiedSymbol =>
        coreLfQualifiedSymbol(moduleId, name);
    const code = symbol('Code');
    const parameterValue = symbol('typeA');
    const codeDeclaration: CoreLfTransferDeclaration = {
        order: 0,
        symbol: code,
        type: { tag: 'type' },
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            authorityPath,
            'constant symbol Code : TYPE;'
        )
    };
    const parameterValueDeclaration: CoreLfTransferDeclaration = {
        order: 1,
        symbol: parameterValue,
        type: transferGlobal(code),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            authorityPath,
            'constant symbol typeA : Code;'
        )
    };
    const scope = new CoreLfStructureMacroScope(moduleId, [{
        symbol: code,
        type: { tag: 'type' },
        availability: 'earlier-fragment',
        order: 0
    }]);
    const resolvedCode = scope.resolve(code);
    let order = 2;
    const expand = (
        name: string,
        fields: readonly string[]
    ): CoreLfStructureDeclarationExpansion => {
        const prefix = name.replace(/Class$/u, '').toLowerCase();
        const expansion = scope.declareStructure({
            order,
            carrierName: name,
            constructorName: `Mk${name}`,
            fields(builder) {
                builder.parameter({
                    binderName: 'X',
                    modes: {
                        carrier: {
                            plicity: 'implicit',
                            variation: 'functorial'
                        },
                        constructor: {
                            plicity: 'implicit',
                            variation: 'functorial'
                        },
                        projection: {
                            plicity: 'implicit',
                            variation: 'functorial'
                        }
                    },
                    type: builder.global(resolvedCode)
                });
                fields.forEach(field => builder.field({
                    binderName: field,
                    projectionName: `${prefix}_${field}`,
                    mode: explicitFunctorial,
                    type: builder.global(resolvedCode)
                }));
            },
            provenance: sourceProvenance(
                authorityPath,
                `class ${name}`
            )
        });
        order = expansion.nextOrder;
        return expansion;
    };
    const schema = (
        expansion: CoreLfStructureDeclarationExpansion,
        parents: readonly CoreLfClassSchema[] = []
    ): CoreLfClassSchema => {
        const parameter = coreLfClassParameterTerm(
            expansion,
            expansion.handle.parameters[0]
        );
        return declareCoreLfClassSchema({
            expansion,
            parameterRoles: [{
                parameter: expansion.handle.parameters[0],
                role: 'input'
            }],
            directParents: parents.map(parent => ({
                parent,
                arguments: [{
                    parameter: parent.structure.parameters[0],
                    value: parameter
                }]
            }))
        });
    };
    const method = (entry: CoreLfClassSchema, name: string) => {
        const found = entry.declaredMethods.find(candidate =>
            candidate.projection.binderName === name
        );
        if (found === undefined) {
            return fail(
                'CORPUS_OWNER_FAILED',
                `classes.${entry.classId.name}.${name}`,
                'Class fixture lost a declared method'
            );
        }
        return found;
    };
    const slot = (layout: CoreLfClassInheritanceLayout, name: string) => {
        const found = layout.slots.find(candidate =>
            candidate.physicalField.binderName === name
        );
        if (found === undefined) {
            return fail(
                'CORPUS_OWNER_FAILED',
                `classes.${layout.classId.name}.${name}`,
                'Class fixture lost an inheritance slot'
            );
        }
        return found;
    };
    const binding = (
        entry: CoreLfClassSchema,
        name: string,
        inherited: readonly CoreLfClassMethodIdentity[]
    ) => ({ field: method(entry, name).projection, inherited });

    const aExpansion = expand('AClass', ['a']);
    const aSchema = schema(aExpansion);
    const A: CorpusClassEntry = {
        expansion: aExpansion,
        schema: aSchema,
        layout: planCoreLfClassInheritance({
            schema: aSchema,
            directParentLayouts: []
        })
    };
    const bExpansion = expand('BClass', ['a', 'b']);
    const bSchema = schema(bExpansion, [A.schema]);
    const B: CorpusClassEntry = {
        expansion: bExpansion,
        schema: bSchema,
        layout: planCoreLfClassInheritance({
            schema: bSchema,
            directParentLayouts: [A.layout],
            fieldBindings: [binding(
                bSchema,
                'a',
                [slot(A.layout, 'a').canonicalIdentity]
            )]
        })
    };
    const cExpansion = expand('CClass', ['a', 'c']);
    const cSchema = schema(cExpansion, [A.schema]);
    const C: CorpusClassEntry = {
        expansion: cExpansion,
        schema: cSchema,
        layout: planCoreLfClassInheritance({
            schema: cSchema,
            directParentLayouts: [A.layout],
            fieldBindings: [binding(
                cSchema,
                'a',
                [slot(A.layout, 'a').canonicalIdentity]
            )]
        })
    };
    const dExpansion = expand('DClass', ['a', 'b', 'c', 'd']);
    const dSchema = schema(dExpansion, [B.schema, C.schema]);
    const D: CorpusClassEntry = {
        expansion: dExpansion,
        schema: dSchema,
        layout: planCoreLfClassInheritance({
            schema: dSchema,
            directParentLayouts: [B.layout, C.layout],
            fieldBindings: [
                binding(
                    dSchema,
                    'a',
                    [slot(A.layout, 'a').canonicalIdentity]
                ),
                binding(
                    dSchema,
                    'b',
                    [slot(B.layout, 'b').canonicalIdentity]
                ),
                binding(
                    dSchema,
                    'c',
                    [slot(C.layout, 'c').canonicalIdentity]
                )
            ]
        })
    };
    const classes = { A, B, C, D };
    const lower = (
        child: CorpusClassEntry,
        parents: readonly {
            readonly entry: CorpusClassEntry;
            readonly name: string;
        }[]
    ): CoreLfClassInheritanceLoweringExpansion => {
        const lowering = lowerCoreLfClassInheritance({
            layout: child.layout,
            order,
            directParents: parents.map(parent => ({
                layout: parent.entry.layout,
                conversionName: parent.name
            })),
            provenance: sourceProvenance(
                authorityPath,
                `direct parent conversions for ${child.schema.classId.name}`
            )
        });
        order = lowering.nextOrder;
        return lowering;
    };
    const lowerings = [
        lower(A, []),
        lower(B, [{ entry: A, name: 'b_to_a' }]),
        lower(C, [{ entry: A, name: 'c_to_a' }]),
        lower(D, [
            { entry: B, name: 'd_to_b' },
            { entry: C, name: 'd_to_c' }
        ])
    ];
    const instanceSymbols = {
        a1: symbol('a_instance_one'),
        a2: symbol('a_instance_two'),
        d: symbol('d_instance')
    };
    const leanUse = symbol('lean_diamond_use');
    const classType = (entry: CorpusClassEntry): CoreLfTransferExpression =>
        transferCall(transferGlobal(entry.schema.structure.carrier), [{
            plicity: 'implicit',
            value: transferGlobal(parameterValue)
        }]);
    const extraDeclarations: readonly CoreLfTransferDeclaration[] = [{
        order: order++,
        symbol: instanceSymbols.a1,
        type: classType(A),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(authorityPath, 'instance a1 : AClass')
    }, {
        order: order++,
        symbol: instanceSymbols.a2,
        type: classType(A),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(authorityPath, 'instance a2 : AClass')
    }, {
        order: order++,
        symbol: instanceSymbols.d,
        type: classType(D),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(authorityPath, 'instance d : DClass')
    }, {
        order: order++,
        symbol: leanUse,
        type: transferPi(
            'instance',
            classType(A),
            classType(A),
            'implicit'
        ),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: sourceProvenance(
            authorityPath,
            'symbol lean_diamond_use [instance : AClass] : AClass'
        )
    }];
    const structures = [A, B, C, D];
    const declarations = [
        codeDeclaration,
        parameterValueDeclaration,
        ...structures.flatMap(entry => entry.expansion.declarations),
        ...lowerings.flatMap(entry => entry.declarations),
        ...extraDeclarations
    ];
    const runtimeRules = structures.flatMap(entry =>
        entry.expansion.runtimeRules
    );
    const module = createCoreLfModuleSpec({
        revision: 'public-proof-agent-class-module-v1',
        moduleId,
        fragmentId: 'class-diamond',
        authorityPath,
        sourceSha256: hash('8'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules,
        proofRules: []
    });
    const policyInputs: {
        readonly sourceOrder: number;
        readonly entry: Omit<CoreLfTransferPolicyEntry, 'order'>;
    }[] = [
        ...declarations.map(declaration => ({
            sourceOrder: declaration.order,
            entry: {
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: declaration.body.kind === 'explicit-term'
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
                evidence: 'AGENT-EVAL-12B1 checked class fixture declaration'
            }
        })),
        ...runtimeRules.map(rule => ({
            sourceOrder: rule.order,
            entry: {
                target: { kind: 'runtime-rule' as const, id: rule.id },
                policy: 'runtime-rewrite' as const,
                evidence: 'generated structure projection beta rule'
            }
        }))
    ].sort((left, right) => left.sourceOrder - right.sourceOrder);
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'public-proof-agent-class-policy-v1',
        moduleRevision: module.revision,
        entries: policyInputs.map(({ entry }, policyOrder) => ({
            order: policyOrder,
            ...entry
        }))
    });
    const mixedPlan = planCoreLfMixedPhases(module, policy);
    const names = new Map(declarations.map(declaration => [
        classSymbolKey(declaration.symbol),
        `public_class_${declaration.symbol.name}`
    ] as const));
    const coreName = (selected: CoreLfQualifiedSymbol): string => {
        const found = names.get(classSymbolKey(selected));
        if (found !== undefined) return found;
        return fail(
            'CORPUS_OWNER_FAILED',
            `classes.coreName.${selected.name}`,
            'Class fixture symbol has no compiled Core name'
        );
    };
    const linkageEntries = [...declarations]
        .sort((left, right) => left.order - right.order)
        .map((declaration, linkageOrder) => ({
            order: linkageOrder,
            symbol: declaration.symbol,
            kind: 'free-declaration' as const,
            coreName: coreName(declaration.symbol),
            backendName: declaration.symbol.name
        }));
    const mixedLinkage = createCoreLfMixedDeclarationLinkage(mixedPlan, {
        revision: 'public-proof-agent-class-mixed-linkage-v1',
        moduleRevision: module.revision,
        entries: linkageEntries
    });
    const compiled = compileCoreLfMixedPhases(mixedPlan, mixedLinkage);
    if (compiled.latestRuntime === undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'classes.runtime',
            'Class fixture did not compile its generated projection runtime'
        );
    }

    const sourceModule = createCoreLfModuleSpec({
        revision: 'public-proof-agent-class-source-module-v1',
        moduleId,
        fragmentId: 'class-diamond-source',
        authorityPath,
        sourceSha256: hash('9'),
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const sourcePolicy = createCoreLfTransferPolicyOverlay(sourceModule, {
        revision: 'public-proof-agent-class-source-policy-v1',
        moduleRevision: sourceModule.revision,
        entries: [...declarations]
            .sort((left, right) => left.order - right.order)
            .map((declaration, policyOrder) => ({
                order: policyOrder,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: declaration.body.kind === 'explicit-term'
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
                evidence: 'AGENT-EVAL-12B1 declaration-only replay surface'
            }))
    });
    const sourceLinkage = createCoreLfTransferDeclarationLinkage(
        sourceModule,
        {
            revision: 'public-proof-agent-class-source-linkage-v1',
            moduleRevision: sourceModule.revision,
            entries: linkageEntries
        }
    );
    const workspace = createCoreLfDeclarationWorkspace({
        revision: 'public-proof-agent-class-workspace-v1',
        modules: [{
            module: sourceModule,
            policy: sourcePolicy,
            linkage: sourceLinkage
        }]
    });
    compileCoreLfDeclarationWorkspace(workspace);
    return {
        moduleId,
        module,
        workspace,
        compiled,
        runtimeProgram: compiled.latestRuntime.runtime,
        classes,
        lowerings,
        instanceSymbols,
        parameterValue,
        leanUse,
        coreName
    };
};

const classEntryById = (
    fixture: CorpusClassFixture,
    classId: CoreLfQualifiedSymbol
): CorpusClassEntry => {
    const found = Object.values(fixture.classes).find(entry =>
        classSymbolKey(entry.schema.classId) === classSymbolKey(classId)
    );
    if (found !== undefined) return found;
    return fail(
        'CORPUS_OWNER_FAILED',
        `classes.layout.${classId.name}`,
        'Superclass conversion refers to an unknown class layout'
    );
};

const declareClassSuperclassProviders = (
    fixture: CorpusClassFixture
): readonly CoreLfInstanceProviderDeclaration[] =>
    fixture.lowerings.flatMap(lowering =>
        lowering.directParentConversions.map(conversion =>
            declareCoreLfSuperclassInstanceProvider({
                declarations: fixture.compiled.declarations,
                module: fixture.module,
                conversion,
                childClass: lowering.layout,
                parentClass: classEntryById(
                    fixture,
                    conversion.parent.classId
                ).layout
            })
        )
    );

const classSynthesisArtifacts = (
    fixture: CorpusClassFixture,
    providers: readonly CoreLfInstanceProviderDeclaration[]
) => {
    const registry = createCoreLfInstanceRegistrySnapshot({
        revision: 'public-proof-agent-class-registry-v1',
        providers
    });
    const scope = createCoreLfInstanceScopeSnapshot({
        revision: 'public-proof-agent-class-scope-v1',
        registry,
        moduleId: fixture.moduleId,
        contextDepth: 0
    });
    return { registry, scope };
};

const buildClassEntries = (): readonly BuiltCorpusEntry[] => {
    const fixture = buildClassFixture();
    const witness = proofProvenance(
        fixture.module.authorityPath,
        200,
        'public corpus class synthesis'
    );
    const target = kernelCall(
        kernelFree(
            fixture.coreName(fixture.classes.A.schema.classId),
            witness
        ),
        [{
            plicity: 'implicit',
            value: kernelFree(fixture.coreName(fixture.parameterValue), witness)
        }],
        witness
    );
    const prior = coreProofPlanExact(kernelFree(
        fixture.coreName(fixture.instanceSymbols.a1),
        witness
    ));
    const context = createCoreLfChecker(
        fixture.compiled.declarations.environment,
        undefined,
        fixture.runtimeProgram
    ).rootContext;
    const dProvider = declareCoreLfGlobalInstanceProvider({
        declarations: fixture.compiled.declarations,
        module: fixture.module,
        provider: fixture.instanceSymbols.d,
        resultClass: fixture.classes.D.layout
    });
    const superclasses = declareClassSuperclassProviders(fixture);
    const sharedArtifacts = classSynthesisArtifacts(
        fixture,
        [dProvider, ...superclasses]
    );
    const shared = synthesizeCoreLfInstance({
        declarations: fixture.compiled.declarations,
        context,
        runtimeProgram: fixture.runtimeProgram,
        targetClass: fixture.classes.A.layout,
        target,
        ...sharedArtifacts
    });
    if (shared.status !== 'solved') {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.class.shared-diamond.synthesis',
            `Shared-diamond synthesis returned '${shared.status}'`
        );
    }
    const tableHits = shared.report.goals.flatMap(goal =>
        goal.candidates.flatMap(candidate => candidate.premises)
    ).filter(premise => premise.disposition === 'table-hit').length;
    const rootGoal = shared.report.goals.find(goal =>
        goal.goalId === shared.report.rootGoalId
    );
    const equivalentProviders = rootGoal?.equivalentProviders?.length ?? 0;
    const ancestorOccurrences = fixture.classes.D.layout.resolutionOrder.filter(
        entry => classSymbolKey(entry.classId) ===
            classSymbolKey(fixture.classes.A.schema.classId)
    ).length;
    if (tableHits === 0 || equivalentProviders < 2 || ancestorOccurrences !== 1) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.class.shared-diamond.evidence',
            'Shared-diamond owner lost table reuse, equivalent paths, or ' +
                'canonical ancestor sharing'
        );
    }
    const sharedCase = buildBenchmarkCase({
        id: 'native.class.shared-diamond',
        ordinal: 7,
        workspace: fixture.workspace,
        moduleId: fixture.moduleId,
        type: target,
        previousPlan: prior,
        relevantPremises: [
            fixture.instanceSymbols.d,
            ...fixture.lowerings.flatMap(lowering =>
                lowering.directParentConversions.map(conversion =>
                    conversion.symbol
                )
            )
        ]
    });
    const sharedEntry = nativeEntryBase({
        id: sharedCase.benchmarkCase.id,
        track: 'structures-classes-instances',
        sourceOwner: 'class-inheritance-lowering-and-instance-synthesis',
        referenceOwner: 'synthesizeCoreLfInstance',
        features: ['structure-parameters', 'ancestor-sharing', 'table-hit'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: sharedCase.benchmarkCase,
        attempt: patchAttempt(
            sharedCase.benchmarkCase,
            coreProofPlanExact(shared.term),
            [fixture.instanceSymbols.d]
        ),
        ownerEvidence: evidence(
            'instance-synthesis',
            CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
            [
                `canonical ancestor occurrence count: ${ancestorOccurrences}`,
                `recursive synthesis table-hit count: ${tableHits}`,
                `definitionally equivalent root providers: ${equivalentProviders}`,
                `selected checked provider: ${shared.selected.name}`
            ],
            serializeCoreLfInstanceSynthesisReport(shared.report)
        )
    });

    const a1Provider = declareCoreLfGlobalInstanceProvider({
        declarations: fixture.compiled.declarations,
        module: fixture.module,
        provider: fixture.instanceSymbols.a1,
        resultClass: fixture.classes.A.layout,
        priority: 1000
    });
    const a2Provider = declareCoreLfGlobalInstanceProvider({
        declarations: fixture.compiled.declarations,
        module: fixture.module,
        provider: fixture.instanceSymbols.a2,
        resultClass: fixture.classes.A.layout,
        priority: 1000
    });
    const ambiguityArtifacts = classSynthesisArtifacts(
        fixture,
        [a1Provider, a2Provider]
    );
    const ambiguous = synthesizeCoreLfInstance({
        declarations: fixture.compiled.declarations,
        context,
        runtimeProgram: fixture.runtimeProgram,
        targetClass: fixture.classes.A.layout,
        target,
        ...ambiguityArtifacts
    });
    if (ambiguous.status !== 'ambiguous') {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.class.ambiguity-abstention.synthesis',
            `Equal-priority synthesis returned '${ambiguous.status}'`
        );
    }
    const ambiguousRoot = ambiguous.report.goals.find(goal =>
        goal.goalId === ambiguous.report.rootGoalId
    );
    const competing = ambiguousRoot?.candidates.filter(candidate =>
        candidate.outcome === 'ambiguous-success' ||
        candidate.outcome === 'success'
    ).map(candidate => candidate.providerId.name) ?? [];
    if (competing.length < 2 || ambiguousRoot?.selectedProvider !== undefined) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.class.ambiguity-abstention.evidence',
            'Ambiguity evidence selected a hidden winner or lost a competitor'
        );
    }
    const ambiguityCase = buildBenchmarkCase({
        id: 'native.class.ambiguity-abstention',
        ordinal: 8,
        workspace: fixture.workspace,
        moduleId: fixture.moduleId,
        type: target,
        previousPlan: prior,
        relevantPremises: [
            fixture.instanceSymbols.a1,
            fixture.instanceSymbols.a2
        ]
    });
    const ambiguityEntry = nativeEntryBase({
        id: ambiguityCase.benchmarkCase.id,
        track: 'structures-classes-instances',
        sourceOwner: 'instance-synthesis',
        referenceOwner: 'explicit-abstention',
        features: ['equal-priority-ambiguity', 'no-hidden-winner'],
        expectedReferenceOutcome: 'abstained',
        benchmarkCase: ambiguityCase.benchmarkCase,
        attempt: createCoreLfProofAgentBenchmarkAttempt({
            benchmarkCase: ambiguityCase.benchmarkCase,
            retrievedPremises: [
                fixture.instanceSymbols.a1,
                fixture.instanceSymbols.a2
            ],
            decision: { kind: 'abstain' }
        }),
        ownerEvidence: evidence(
            'instance-ambiguity',
            CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
            [
                `equal-priority competing providers: ${competing.join(',')}`,
                'synthesis status is ambiguous',
                'no selected provider and no arbitrary reference patch'
            ],
            serializeCoreLfInstanceSynthesisReport(ambiguous.report)
        )
    });

    const classCall = elaborateCoreLfSaturatedClassCall({
        declarations: fixture.compiled.declarations,
        context,
        runtimeProgram: fixture.runtimeProgram,
        callee: kernelFree(fixture.coreName(fixture.leanUse), witness),
        arguments: [],
        instanceBinders: [{
            binderOrdinal: 0,
            requestId: 'lean.diamond.instance',
            classLayout: fixture.classes.A.layout
        }],
        expectedType: target,
        ...sharedArtifacts,
        provenance: witness
    });
    if (classCall.status !== 'elaborated') {
        return fail(
            'CORPUS_OWNER_FAILED',
            'lean4.diamond1.explicit-translation.elaboration',
            `Class-call elaboration returned '${classCall.status}'`
        );
    }
    const synthesizedBinders = classCall.report.binders.filter(binder =>
        binder.disposition === 'synthesized'
    ).length;
    if (synthesizedBinders !== 1) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'lean4.diamond1.explicit-translation.binders',
            'Manual Lean correspondence lost its synthesized class binder'
        );
    }
    const leanCase = buildBenchmarkCase({
        id: 'lean4.diamond1.explicit-translation',
        ordinal: 10,
        workspace: fixture.workspace,
        moduleId: fixture.moduleId,
        type: target,
        previousPlan: prior,
        relevantPremises: [fixture.leanUse, fixture.instanceSymbols.d]
    });
    const leanEntry: BuiltCorpusEntry = {
        id: leanCase.benchmarkCase.id,
        track: 'lean4-manual-translation',
        origin: 'lean4-manual-translation',
        sourceOwner: 'tests/elab/diamond1.lean@f29e9e4',
        referenceOwner: 'elaborateCoreLfSaturatedClassCall',
        features: [
            'binder-and-class-style-source',
            'multiple-inheritance',
            'shared-ancestor',
            'explicit-dictionary-erasure'
        ],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: leanCase.benchmarkCase,
        attempt: patchAttempt(
            leanCase.benchmarkCase,
            coreProofPlanExact(classCall.term),
            [fixture.leanUse, fixture.instanceSymbols.d]
        ),
        ownerEvidence: evidence(
            'class-call-elaboration',
            CORE_LF_CLASS_CALL_ELABORATION_PROFILE.revision,
            [
                'manual Apache-2.0 Lean diamond correspondence, not parsing',
                `synthesized class binders: ${synthesizedBinders}`,
                'the elaborated explicit dictionary call is independently checked'
            ],
            serializeCoreLfClassCallElaborationReport(classCall.report)
        )
    };

    return Object.freeze([sharedEntry, ambiguityEntry, leanEntry]);
};

const buildSimplifierEntry = (): BuiltCorpusEntry => {
    const moduleId = 'emdash.public_corpus.simplifier';
    const authorityPath =
        'src/v3_2/fixtures/public_proof_agent_simplifier.emdash.ts';
    const symbol = (name: string): CoreLfQualifiedSymbol =>
        coreLfQualifiedSymbol(moduleId, name);
    const symbols = {
        grpd: symbol('Grpd'),
        decode: symbol('El'),
        equality: symbol('SimpEq'),
        transport: symbol('SimpIndEq'),
        wrap: symbol('simp_wrap'),
        A: symbol('SimpA'),
        zero: symbol('simp_zero'),
        predicate: symbol('SimpP'),
        rule: symbol('simp_wrap_rule'),
        base: symbol('simp_base')
    } as const;
    const g = transferGlobal;
    const tDecode = (
        classifier: CoreLfTransferExpression
    ): CoreLfTransferExpression => transferCall(g(symbols.decode), [{
        plicity: 'explicit',
        value: classifier
    }]);
    const explicit = (value: CoreLfTransferExpression) => ({
        plicity: 'explicit' as const,
        value
    });
    const implicit = (value: CoreLfTransferExpression) => ({
        plicity: 'implicit' as const,
        value
    });
    const equalityType = transferPi(
        'A',
        g(symbols.grpd),
        transferPi(
            'left',
            tDecode(transferBound(0)),
            transferPi(
                'right',
                tDecode(transferBound(1)),
                g(symbols.grpd)
            )
        ),
        'implicit'
    );
    const equalityAtXY = tDecode(transferCall(g(symbols.equality), [
        implicit(transferBound(2)),
        explicit(transferBound(1)),
        explicit(transferBound(0))
    ]));
    const motiveType = transferPi(
        'value',
        tDecode(transferBound(3)),
        g(symbols.grpd)
    );
    const motiveAtY = tDecode(transferCall(
        transferBound(0),
        [explicit(transferBound(2))]
    ));
    const motiveAtX = tDecode(transferCall(
        transferBound(1),
        [explicit(transferBound(4))]
    ));
    const transportType = transferPi(
        'A',
        g(symbols.grpd),
        transferPi(
            'x',
            tDecode(transferBound(0)),
            transferPi(
                'y',
                tDecode(transferBound(1)),
                transferPi(
                    'path',
                    equalityAtXY,
                    transferPi(
                        'motive',
                        motiveType,
                        transferPi(
                            'base',
                            motiveAtY,
                            motiveAtX
                        )
                    )
                ),
                'implicit'
            ),
            'implicit'
        ),
        'implicit'
    );
    const wrapType = transferPi(
        'B',
        g(symbols.grpd),
        transferPi(
            'value',
            tDecode(transferBound(0)),
            tDecode(transferBound(1))
        ),
        'implicit'
    );
    const predicateType = transferPi(
        'value',
        tDecode(g(symbols.A)),
        g(symbols.grpd)
    );
    const wrapAt = (
        classifier: CoreLfTransferExpression,
        value: CoreLfTransferExpression
    ): CoreLfTransferExpression => transferCall(g(symbols.wrap), [
        implicit(classifier),
        explicit(value)
    ]);
    const equalityAt = (
        classifier: CoreLfTransferExpression,
        left: CoreLfTransferExpression,
        right: CoreLfTransferExpression
    ): CoreLfTransferExpression => tDecode(transferCall(
        g(symbols.equality),
        [implicit(classifier), explicit(left), explicit(right)]
    ));
    const ruleType = transferPi(
        'B',
        g(symbols.grpd),
        transferPi(
            'value',
            tDecode(transferBound(0)),
            equalityAt(
                transferBound(1),
                wrapAt(transferBound(1), transferBound(0)),
                transferBound(0)
            )
        ),
        'implicit'
    );
    const baseType = tDecode(transferCall(g(symbols.predicate), [
        explicit(g(symbols.zero))
    ]));
    const declarationInputs: readonly {
        readonly symbol: CoreLfQualifiedSymbol;
        readonly type: CoreLfTransferExpression;
        readonly source: string;
    }[] = [{
        symbol: symbols.equality,
        type: equalityType,
        source: 'symbol SimpEq : equality classifier;'
    }, {
        symbol: symbols.transport,
        type: transportType,
        source: 'symbol SimpIndEq : backward equality transport;'
    }, {
        symbol: symbols.wrap,
        type: wrapType,
        source: 'symbol simp_wrap : polymorphic endomap;'
    }, {
        symbol: symbols.A,
        type: g(symbols.grpd),
        source: 'symbol SimpA : Grpd;'
    }, {
        symbol: symbols.zero,
        type: tDecode(g(symbols.A)),
        source: 'symbol simp_zero : El(SimpA);'
    }, {
        symbol: symbols.predicate,
        type: predicateType,
        source: 'symbol SimpP (value : El(SimpA)) : Grpd;'
    }, {
        symbol: symbols.rule,
        type: ruleType,
        source: 'symbol simp_wrap_rule : simp_wrap value = value;'
    }, {
        symbol: symbols.base,
        type: baseType,
        source: 'symbol simp_base : El(SimpP(simp_zero));'
    }];
    const declarations: readonly CoreLfTransferDeclaration[] =
        declarationInputs.map((input, order) => ({
            order,
            symbol: input.symbol,
            type: input.type,
            body: coreLfTransferAbsentBody(),
            modifiers: opaqueModifiers,
            provenance: sourceProvenance(authorityPath, input.source)
        }));
    const module = createCoreLfModuleSpec({
        revision: 'public-proof-agent-simplifier-module-v1',
        moduleId,
        fragmentId: 'simplifier',
        authorityPath,
        sourceSha256: hash('a'),
        dependencies: [],
        externalSymbols: [{
            symbol: symbols.grpd,
            availability: 'existing-core'
        }, {
            symbol: symbols.decode,
            availability: 'existing-core'
        }],
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'public-proof-agent-simplifier-policy-v1',
        moduleRevision: module.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: { kind: 'declaration', symbol: declaration.symbol },
            policy: 'opaque-signature',
            evidence: 'AGENT-EVAL-12B1 checked simplifier fixture declaration'
        }))
    });
    const coreNames = new Map([
        [symbols.equality.name, 'public_simp_eq'],
        [symbols.transport.name, 'public_simp_transport'],
        [symbols.wrap.name, 'public_simp_wrap'],
        [symbols.A.name, 'public_simp_A'],
        [symbols.zero.name, 'public_simp_zero'],
        [symbols.predicate.name, 'public_simp_P'],
        [symbols.rule.name, 'public_simp_wrap_rule'],
        [symbols.base.name, 'public_simp_base']
    ]);
    const linkage: CoreLfTransferDeclarationLinkage =
        createCoreLfTransferDeclarationLinkage(module, {
            revision: 'public-proof-agent-simplifier-linkage-v1',
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                symbol: symbols.grpd,
                kind: 'core-owner',
                owner: 'groupoid-universe'
            }, {
                order: 1,
                symbol: symbols.decode,
                kind: 'core-owner',
                owner: 'decode'
            }, ...declarations.map((declaration, index) => ({
                order: index + 2,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName: coreNames.get(declaration.symbol.name)!,
                backendName: declaration.symbol.name
            }))]
        });
    const workspace = createCoreLfDeclarationWorkspace({
        revision: 'public-proof-agent-simplifier-workspace-v1',
        modules: [{ module, policy, linkage }]
    });
    const compiled = compileCoreLfDeclarationWorkspace(workspace);

    const kBecause = (line: number, detail: string) =>
        proofProvenance(authorityPath, line, detail);
    const kGrpd = (line: number): KernelExpression => kernelApplication(
        'groupoid-universe',
        [],
        kBecause(line, 'simplifier groupoid universe')
    );
    const kDecode = (
        classifier: KernelExpression,
        line: number
    ): KernelExpression => kernelApplication(
        'decode',
        [{ value: classifier }],
        kBecause(line, 'simplifier decoded classifier')
    );
    const kFree = (
        name: string,
        line: number
    ): KernelExpression => kernelFree(name, kBecause(line, `free ${name}`));
    const kExplicit = (value: KernelExpression) => ({
        plicity: 'explicit' as const,
        value
    });
    const kImplicit = (value: KernelExpression) => ({
        plicity: 'implicit' as const,
        value
    });
    const kWrapAt = (
        classifier: KernelExpression,
        value: KernelExpression,
        line: number
    ): KernelExpression => kernelCall(
        kFree(coreNames.get(symbols.wrap.name)!, line),
        [kImplicit(classifier), kExplicit(value)],
        kBecause(line, 'simplifier wrapper application')
    );
    const A = kFree(coreNames.get(symbols.A.name)!, 300);
    const zero = kFree(coreNames.get(symbols.zero.name)!, 301);
    const wrapped = kWrapAt(A, zero, 302);
    const predicate = kFree(coreNames.get(symbols.predicate.name)!, 303);
    const target = kDecode(kernelCall(
        predicate,
        [kExplicit(wrapped)],
        kBecause(303, 'simplifier wrapped target classifier')
    ), 303);
    const simplifiedTarget = kDecode(kernelCall(
        predicate,
        [kExplicit(zero)],
        kBecause(304, 'simplifier base target classifier')
    ), 304);
    const continuation = coreProofPlanExact(kFree(
        coreNames.get(symbols.base.name)!,
        305
    ));
    const simplification = simplifyCoreProofPlan({
        environment: compiled.environment,
        target,
        adapter: coreProofSimplifierAdapter(
            kernelFree(
                coreNames.get(symbols.equality.name)!,
                kBecause(306, 'simplifier equality adapter')
            ),
            kernelFree(
                coreNames.get(symbols.transport.name)!,
                kBecause(306, 'simplifier transport adapter')
            )
        ),
        rules: [coreProofSimplifierRule(
            'public.wrap',
            kernelFree(
                coreNames.get(symbols.rule.name)!,
                kBecause(307, 'simplifier rewrite rule')
            )
        )],
        continuation,
        provenance: kBecause(308, 'public corpus simplification')
    });
    if (simplification.rewriteCount !== 1) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'native.automation.simplified-transport.rewrites',
            'Simplifier owner did not perform the selected exact rewrite'
        );
    }
    const benchmark = buildBenchmarkCase({
        id: 'native.automation.simplified-transport',
        ordinal: 6,
        workspace,
        moduleId,
        type: target,
        previousPlan: simplification.plan,
        relevantPremises: [symbols.rule, symbols.base]
    });
    return nativeEntryBase({
        id: benchmark.benchmarkCase.id,
        track: 'bounded-automation',
        sourceOwner: 'proof-simplifier',
        referenceOwner: 'simplifyCoreProofPlan',
        features: ['explicit-equality-evidence', 'backward-transport'],
        expectedReferenceOutcome: 'accepted-complete',
        benchmarkCase: benchmark.benchmarkCase,
        attempt: patchAttempt(
            benchmark.benchmarkCase,
            simplification.plan,
            [symbols.rule, symbols.base]
        ),
        ownerEvidence: evidence(
            'proof-simplifier',
            CORE_PROOF_SIMPLIFIER_PROFILE.revision,
            [
                `checked rewrite count: ${simplification.rewriteCount}`,
                `accepted rule: ${simplification.trace[0].ruleId}`,
                'backward transport term was independently checked',
                'the simplified continuation proves the exact simplified target'
            ],
            portableCanonicalText({
                revision: simplification.revision,
                target,
                simplifiedTarget,
                rewriteCount: simplification.rewriteCount,
                trace: simplification.trace,
                transportTerm: simplification.transportTerm,
                plan: simplification.plan
            }, 'simplifierOwnerEvidence')
        )
    });
};

const trackMinimums: Readonly<Record<
    CoreLfProofAgentPublicCorpusTrack,
    number
>> = Object.freeze({
    'explicit-proof-construction': 2,
    'source-proof-management': 2,
    'bounded-automation': 2,
    'structures-classes-instances': 2,
    'maintenance-revision': 1,
    'lean4-manual-translation': 1
});

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const compareBuiltEntries = (
    left: BuiltCorpusEntry,
    right: BuiltCorpusEntry
): number => {
    const leftTrack =
        CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.trackOrder.indexOf(
            left.track
        );
    const rightTrack =
        CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.trackOrder.indexOf(
            right.track
        );
    return leftTrack - rightTrack || compareText(left.id, right.id);
};

/** Build the fixed corpus and freshly score every owner-generated baseline. */
export function createCoreLfProofAgentPublicCorpus():
CoreLfProofAgentPublicCorpus {
    let built: readonly BuiltCorpusEntry[];
    try {
        built = [
            ...buildNativeEntries(),
            buildSimplifierEntry(),
            ...buildClassEntries()
        ].sort(compareBuiltEntries);
    } catch (error: unknown) {
        if (error instanceof CoreLfProofAgentPublicCorpusError) throw error;
        return fail(
            'CORPUS_OWNER_FAILED',
            'corpus.entries',
            'A selected corpus owner failed during deterministic construction',
            error
        );
    }
    const ids = new Set(built.map(entry => entry.id));
    if (
        built.length !==
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.selectedCaseCount ||
        ids.size !== built.length
    ) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'corpus.entries',
            'Fixed corpus lost its exact ten unique case identities'
        );
    }
    const tracks = CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.trackOrder.map(
        id => ({
            id,
            minimumCases: trackMinimums[id],
            selectedCases: built.filter(entry => entry.track === id).length
        })
    );
    if (
        tracks.length !==
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.selectedTrackCount ||
        tracks.some(track => track.selectedCases < track.minimumCases)
    ) {
        return fail(
            'CORPUS_OWNER_FAILED',
            'corpus.tracks',
            'Fixed corpus no longer satisfies every representativeness minimum'
        );
    }
    const suite = createCoreLfProofAgentBenchmarkSuite({
        revision: CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.suiteRevision,
        cases: built.map(entry => entry.benchmarkCase)
    });
    const referenceRun = createCoreLfProofAgentBenchmarkRun({
        revision:
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.referenceRunRevision,
        provider: {
            id: 'emdash-reference-owners',
            revision: 'emdash-reference-owners-v1'
        },
        allowedProfiles: [
            CORE_LF_CLASS_CALL_ELABORATION_PROFILE.revision,
            CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision,
            CORE_LF_PROOF_MAINTENANCE_PROFILE.revision,
            CORE_OBVIOUS_PROOF_PROVIDER_PROFILE.revision,
            CORE_PROOF_PLAN_PROFILE.revision,
            CORE_PROOF_REFINE_TEMPLATE_PROFILE.revision,
            CORE_PROOF_SIMPLIFIER_PROFILE.revision
        ],
        seed: 'emdash-public-proof-agent-reference-v1',
        attempts: built.map(entry => entry.attempt)
    });
    const referenceReport = evaluateCoreLfProofAgentBenchmarkRun({
        suite,
        run: referenceRun
    });
    const outcomes = new Map(referenceReport.results.map(result => [
        result.caseId,
        result.outcome
    ] as const));
    const entries = built.map(entry => {
        const actualReferenceOutcome = outcomes.get(entry.id);
        if (actualReferenceOutcome !== entry.expectedReferenceOutcome) {
            return fail(
                'CORPUS_OUTCOME_MISMATCH',
                `corpus.entries.${entry.id}`,
                `Reference outcome '${String(actualReferenceOutcome)}' ` +
                    `does not match '${entry.expectedReferenceOutcome}'`
            );
        }
        return {
            id: entry.id,
            track: entry.track,
            origin: entry.origin,
            sourceOwner: entry.sourceOwner,
            referenceOwner: entry.referenceOwner,
            features: entry.features,
            caseId: entry.benchmarkCase.id,
            expectedReferenceOutcome: entry.expectedReferenceOutcome,
            actualReferenceOutcome,
            ownerEvidence: entry.ownerEvidence,
            referenceAttemptIsProofAuthority: false as const
        };
    });
    if (
        referenceReport.metrics.outcomes.acceptedComplete !== 9 ||
        referenceReport.metrics.outcomes.abstained !== 1 ||
        referenceReport.metrics.outcomes.acceptedIncomplete !== 0 ||
        referenceReport.metrics.outcomes.rejected !== 0
    ) {
        return fail(
            'CORPUS_OUTCOME_MISMATCH',
            'corpus.referenceReport.metrics.outcomes',
            'Reference run lost the exact nine-complete/one-abstained boundary'
        );
    }
    return freezePortable({
        revision: CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.revision,
        benchmarkProfileRevision:
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision,
        interchangeProfileRevision:
            CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.revision,
        tracks,
        entries,
        referenceReport,
        leanAttribution: {
            repository: 'leanprover/lean4' as const,
            checkpoint:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE
                    .leanSourceCheckpoint,
            sourcePath:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.leanSourcePath,
            sourceSha256:
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.leanSourceSha256,
            license: CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.leanLicense,
            correspondence:
                'Foo/FooComm/FooAssoc/FooAC-diamond-to-explicit-class-evidence' as const,
            manualTranslationOnly: true as const,
            parserParityClaimed: false as const
        },
        meaning:
            'representative-reference-baselines-freshly-scored-not-agent-results' as const,
        naturalLanguageReasoningRequired: false as const,
        hiddenProviderStateRetained: false as const,
        referenceAttemptsAreProofAuthority: false as const,
        curationLabelsAreKernelClaims: false as const
    }, 'proofAgentPublicCorpus');
}

const corpusCanonicalText = (
    corpus: CoreLfProofAgentPublicCorpus
): string => serializeCoreLfWorkspaceCanonicalJson(
    corpus,
    'proofAgentPublicCorpus'
);

/** Validate against a fresh fixed-corpus reconstruction and serialize it. */
export function serializeCoreLfProofAgentPublicCorpus(
    corpus: CoreLfProofAgentPublicCorpus
): string {
    const fresh = createCoreLfProofAgentPublicCorpus();
    let supplied: string;
    try {
        supplied = corpusCanonicalText(corpus);
    } catch (error: unknown) {
        return fail(
            'INVALID_CORPUS_ARTIFACT',
            'corpus',
            'Supplied corpus is not portable canonical data',
            error
        );
    }
    const expected = corpusCanonicalText(fresh);
    if (supplied !== expected) {
        return fail(
            'STALE_CORPUS_ARTIFACT',
            'corpus',
            'Supplied corpus differs from fresh owner reconstruction'
        );
    }
    return expected;
}

const corpusRecord = (
    value: unknown,
    path: string
): Record<string, unknown> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        Array.isArray(value) ||
        (
            Object.getPrototypeOf(value) !== Object.prototype &&
            Object.getPrototypeOf(value) !== null
        )
    ) {
        return fail(
            'INVALID_CORPUS_ARTIFACT',
            path,
            'Corpus text must contain one plain data record'
        );
    }
    return value as Record<string, unknown>;
};

const assertCorpusKeys = (
    record: Record<string, unknown>,
    expected: readonly string[],
    path: string
): void => {
    const actual = Object.keys(record).sort(compareText);
    const canonicalExpected = [...expected].sort(compareText);
    if (
        actual.length === canonicalExpected.length &&
        actual.every((key, index) => key === canonicalExpected[index])
    ) return;
    return fail(
        'INVALID_CORPUS_ARTIFACT',
        path,
        'Corpus has missing or unsupported top-level fields'
    );
};

/** Parse only exact canonical bytes for the freshly reconstructed fixed corpus. */
export function parseCoreLfProofAgentPublicCorpusText(
    sourceText: string
): CoreLfProofAgentPublicCorpus {
    if (typeof sourceText !== 'string' || sourceText.length === 0) {
        return fail(
            'INVALID_CORPUS_TEXT',
            'sourceText',
            'Corpus text must be nonempty'
        );
    }
    let value: unknown;
    try {
        value = JSON.parse(sourceText);
    } catch (error: unknown) {
        return fail(
            'INVALID_CORPUS_TEXT',
            'sourceText',
            'Corpus text is not exactly one JSON value',
            error
        );
    }
    const record = corpusRecord(value, 'corpus');
    assertCorpusKeys(record, [
        'revision',
        'benchmarkProfileRevision',
        'interchangeProfileRevision',
        'tracks',
        'entries',
        'referenceReport',
        'leanAttribution',
        'meaning',
        'naturalLanguageReasoningRequired',
        'hiddenProviderStateRetained',
        'referenceAttemptsAreProofAuthority',
        'curationLabelsAreKernelClaims'
    ], 'corpus');
    if (
        record.revision !==
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.revision ||
        record.benchmarkProfileRevision !==
            CORE_LF_PROOF_AGENT_BENCHMARK_PROFILE.revision ||
        record.interchangeProfileRevision !==
            CORE_LF_PROOF_AGENT_INTERCHANGE_PROFILE.revision
    ) {
        return fail(
            'UNSUPPORTED_CORPUS_REVISION',
            'corpus.revision',
            'Corpus uses an unsupported closed revision set'
        );
    }
    try {
        parseCoreLfProofAgentBenchmarkReportText(
            serializeCoreLfWorkspaceCanonicalJson(
                record.referenceReport,
                'suppliedCorpusReport'
            )
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_CORPUS_ARTIFACT',
            'corpus.benchmarkArtifacts',
            'Nested 12A artifacts failed strict interchange reconstruction',
            error
        );
    }
    const fresh = createCoreLfProofAgentPublicCorpus();
    const expected = corpusCanonicalText(fresh);
    let suppliedCanonical: string;
    try {
        suppliedCanonical = serializeCoreLfWorkspaceCanonicalJson(
            value,
            'suppliedProofAgentPublicCorpus'
        );
    } catch (error: unknown) {
        return fail(
            'INVALID_CORPUS_ARTIFACT',
            'corpus',
            'Corpus contains nonportable data',
            error
        );
    }
    if (suppliedCanonical !== expected) {
        return fail(
            'STALE_CORPUS_ARTIFACT',
            'corpus',
            'Corpus differs from fresh owner and evaluator reconstruction'
        );
    }
    if (sourceText !== expected) {
        return fail(
            'NONCANONICAL_CORPUS_TEXT',
            'sourceText',
            'Corpus text must be exact canonical serializer output'
        );
    }
    return fresh;
}
