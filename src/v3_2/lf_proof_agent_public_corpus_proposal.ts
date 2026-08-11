/**
 * Non-authorizing AGENT-EVAL-12B1 public-corpus/interchange proposal.
 *
 * This immutable record selects existing proof-management owners and an exact
 * representative case matrix. It creates no corpus, parser, export, runner,
 * package version, model invocation, or hosted effect.
 */

export const CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL_REVISION =
    'AGENT-EVAL-12B1-PROPOSAL-1' as const;

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const rawProposal = {
    revision: CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL_REVISION,
    row: 'AGENT-EVAL-12B1',
    status: 'ready-for-separate-review',
    recommendation:
        'implement-representative-browser-safe-lf-patch-corpus-and-interchange',
    parent: {
        governingPlanCheckpoint: '7aeb783',
        synchronizedAuditLedgerCheckpoint: '858126a',
        evaluatorSemanticCheckpoint: 'f46ff9a',
        publicPackageVersion: '0.2.0',
        publicPackageReleaseCheckpoint: 'ab513f7',
        hostedTypescriptConsumerCheckpoint: 'bd4146b',
        hostedGoalViewConsumerCheckpoint: '5c0d0c1',
        pathoutGraduationProposalCheckpoint: '85b560e',
        pathoutGraduationReviewCheckpoint: 'd7d7428',
        pathoutGraduationLedgerCheckpoint: '3135747',
        lean4SourceCheckpoint: 'f29e9e488ea8242c875806e4b0564820c2d553b2'
    },
    pinnedSources: [{
        id: 'proof-agent-evaluator',
        path: 'src/v3_2/lf_proof_agent_benchmark.ts',
        sha256:
            '9300877358e196045160e3bb059d644651f3d1a848e2211039c977be9910d3a4'
    }, {
        id: 'proof-plan',
        path: 'src/v3_2/proof_plan.ts',
        sha256:
            'd0d6a389f5dc1d8273d05ddec8809c13ac60d5af53d7ae982a7c0036e44e1d0e'
    }, {
        id: 'proof-template',
        path: 'src/v3_2/proof_template.ts',
        sha256:
            '07ac6f59d8793bf3b2d4ca55780099899f54dd60bbcd893546f41222f975dc37'
    }, {
        id: 'proof-simplifier',
        path: 'src/v3_2/proof_simplifier.ts',
        sha256:
            '4acb4b79046389ed6691c36dc2f72d8d00b88f3b0dede0d6ba2ae1bc286f7ae4'
    }, {
        id: 'premise-index',
        path: 'src/v3_2/lf_premise_index.ts',
        sha256:
            'e5a953a5c4c1792f9b452004f2b96ecf4a348a1c40d573fc55cf06845a37985b'
    }, {
        id: 'obvious-proof',
        path: 'src/v3_2/proof_obvious.ts',
        sha256:
            'dd88302db8015b63c5b154d9f9042f29f25994615e0720bda13064caf0a34f83'
    }, {
        id: 'proof-maintenance',
        path: 'src/v3_2/lf_proof_maintenance.ts',
        sha256:
            '1fc9dd4dbb6325c0298711569adc6334750d7f4fe8208c85cea395e0c0c48518'
    }, {
        id: 'class-inheritance-lowering',
        path: 'src/v3_2/lf_class_inheritance_lowering.ts',
        sha256:
            '8cb390429f69fe9982c0584a3d8ce0e4bc9c26bf41bbbbac1ec5d951bdc3943f'
    }, {
        id: 'instance-synthesis',
        path: 'src/v3_2/lf_instance_synthesis.ts',
        sha256:
            'b71a2df4c94a86fda7dce1cb646adb916e3299f7c1d8eb69c6f7fc0488f1e295'
    }, {
        id: 'class-call-elaboration',
        path: 'src/v3_2/lf_class_call_elaboration.ts',
        sha256:
            'b5177800a563843427a7b604c5875eff233d0716e5827ad8aee611544d5e5b16'
    }, {
        id: 'package-authoring',
        path: 'src/v3_2/package_authoring.ts',
        sha256:
            'b4324e7ae3ad9d8db2ec737c050e1444565b265b099832ac2fe39f5f701fe9b4'
    }, {
        id: 'package-workspace',
        path: 'src/v3_2/package_workspace.ts',
        sha256:
            '2d00f937d2484e7fc6c9d749faed53be7141556c9cf64e61b8f619d723daa33e'
    }, {
        id: 'package-manifest',
        path: 'packages/emdash/package.json',
        sha256:
            '21219b0ee9d55ed800760319754c961699bd4208d30f2a84bd5ad8126cb21d01'
    }],
    externalEvidence: {
        closerfans: {
            repository: '/home/user1/closerfans',
            consumerCheckpoint: 'bd4146b',
            sourcePath: 'templates/emdash_ts/development.emdash.ts',
            sourceSha256:
                '9e1ca3f6a8c76b92298762c96dbf890e8bc515c9e2fc7a2d01dc4d6cd48d6cbe',
            runnerPath: 'templates/emdash_ts/scripts/emdash.mts',
            runnerSha256:
                '4c9cf29312409f94ee881d128927a7c70ca7437c5d74d79d28d0d787d4eaddd5',
            role: 'later-additive-ordinary-node-host',
            mutationAuthorizedIn12B1: false
        },
        lean4: {
            repository: '/home/user1/lean4-source-code',
            checkpoint: 'f29e9e488ea8242c875806e4b0564820c2d553b2',
            sourcePath: 'tests/elab/diamond1.lean',
            sourceSha256:
                'ca443749e65db8cb1e399446e1a9221cea0a944eda197852d2191dd767cdd3b6',
            licensePath: 'LICENSE',
            licenseSha256:
                '8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e',
            license: 'Apache-2.0',
            use: 'manual-semantic-translation-with-attribution-not-source-parser'
        }
    },
    taskBoundary: {
        taskKind: 'lf-proof-plan-hole-patch',
        caseInput: 'canonical-CoreLfProofDevelopmentSourceSnapshot',
        attemptInput: 'abstain-or-one-inert-CoreProofPlanPatch',
        acceptanceAuthority: 'fresh-TypeScript-emdash-exact-closure-replay',
        pathoutPresentationIsCase: false,
        semanticProgramTaskFamilyAdded: false,
        evaluatorRevisionChanged: false,
        newCoreNodeCount: 0,
        newCheckerBranchCount: 0,
        newRuleCount: 0
    },
    tracks: [{
        id: 'explicit-proof-construction',
        minimumCases: 2
    }, {
        id: 'source-proof-management',
        minimumCases: 2
    }, {
        id: 'bounded-automation',
        minimumCases: 2
    }, {
        id: 'structures-classes-instances',
        minimumCases: 2
    }, {
        id: 'maintenance-revision',
        minimumCases: 1
    }, {
        id: 'lean4-manual-translation',
        minimumCases: 1
    }],
    caseMatrix: [{
        id: 'native.exact.local-premise',
        track: 'explicit-proof-construction',
        origin: 'emdash-native',
        sourceOwner: 'lf-proof-development-source',
        referenceOwner: 'coreProofPlanExact',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['named-hole', 'exact-premise', 'fresh-replay']
    }, {
        id: 'native.apply.explicit-premise',
        track: 'explicit-proof-construction',
        origin: 'emdash-native',
        sourceOwner: 'lf-proof-development-source',
        referenceOwner: 'coreProofPlanConstructor-as-apply',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['named-hole', 'one-step-apply', 'relevant-premise-rank']
    }, {
        id: 'native.have.checked-fact',
        track: 'source-proof-management',
        origin: 'emdash-native',
        sourceOwner: 'proof-plan',
        referenceOwner: 'coreProofPlanHave',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['contextual-have', 'retained-source-obligation']
    }, {
        id: 'native.refine.coupled-goals',
        track: 'source-proof-management',
        origin: 'emdash-native',
        sourceOwner: 'proof-template-and-goal-coupling',
        referenceOwner: 'coreProofPlanRefine',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['typed-placeholder', 'direct-goal-coupling']
    }, {
        id: 'native.automation.obvious-apply',
        track: 'bounded-automation',
        origin: 'emdash-native',
        sourceOwner: 'proof-obvious',
        referenceOwner: 'proposeCoreObviousProofPlanPatches',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['exact-premise-index', 'bounded-candidates', 'checked-replay']
    }, {
        id: 'native.automation.simplified-transport',
        track: 'bounded-automation',
        origin: 'emdash-native',
        sourceOwner: 'proof-simplifier',
        referenceOwner: 'simplifyCoreProofPlan',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['explicit-equality-evidence', 'backward-transport']
    }, {
        id: 'native.class.shared-diamond',
        track: 'structures-classes-instances',
        origin: 'emdash-native',
        sourceOwner: 'class-inheritance-lowering-and-instance-synthesis',
        referenceOwner: 'synthesizeCoreLfInstance',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['structure-parameters', 'ancestor-sharing', 'table-hit']
    }, {
        id: 'native.class.ambiguity-abstention',
        track: 'structures-classes-instances',
        origin: 'emdash-native',
        sourceOwner: 'instance-synthesis',
        referenceOwner: 'explicit-abstention',
        expectedReferenceOutcome: 'abstained',
        features: ['equal-priority-ambiguity', 'no-hidden-winner']
    }, {
        id: 'native.maintenance.changed-source',
        track: 'maintenance-revision',
        origin: 'emdash-native',
        sourceOwner: 'lf-proof-maintenance',
        referenceOwner: 'accepted-maintenance-candidate-patch',
        expectedReferenceOutcome: 'accepted-complete',
        features: ['previous-current-source', 'impact', 'stale-safe-replay']
    }, {
        id: 'lean4.diamond1.explicit-translation',
        track: 'lean4-manual-translation',
        origin: 'lean4-manual-translation',
        sourceOwner: 'tests/elab/diamond1.lean@f29e9e4',
        referenceOwner: 'elaborateCoreLfSaturatedClassCall',
        expectedReferenceOutcome: 'accepted-complete',
        features: [
            'binder-and-class-style-source',
            'multiple-inheritance',
            'shared-ancestor',
            'explicit-dictionary-erasure'
        ]
    }],
    plannedApi: {
        corpusModule: 'lf_proof_agent_public_corpus.ts',
        interchangeModule: 'lf_proof_agent_interchange.ts',
        profileConstant: 'CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE',
        createCorpus: 'createCoreLfProofAgentPublicCorpus',
        parseCorpus: 'parseCoreLfProofAgentPublicCorpusText',
        serializeCorpus: 'serializeCoreLfProofAgentPublicCorpus',
        parseCase: 'parseCoreLfProofAgentBenchmarkCaseText',
        parseSuite: 'parseCoreLfProofAgentBenchmarkSuiteText',
        parseAttempt: 'parseCoreLfProofAgentBenchmarkAttemptText',
        parseRun: 'parseCoreLfProofAgentBenchmarkRunText',
        parseReport: 'parseCoreLfProofAgentBenchmarkReportText',
        publicBarrelExportedIn12B1: false,
        nodeRunnerIncludedIn12B1: false
    },
    interchange: {
        revisionPolicy: 'exact-closed-revisions',
        unknownFieldPolicy: 'reject',
        canonicalOrder: 'track-then-case-id',
        canonicalByteIdentity: true,
        deepFrozen: true,
        staleCasePolicy: 'abort-not-score',
        naturalLanguageReasoningRequired: false,
        hiddenProviderStateRetained: false,
        referenceAttemptsAreProofAuthority: false,
        curationLabelsAreKernelClaims: false,
        providerUsageAuthority: 'provider-reported-unverified'
    },
    representativeness: {
        minimumTrackCount: 6,
        minimumCaseCount: 8,
        selectedTrackCount: 6,
        selectedCaseCount: 10,
        requiresCompleteOutcome: true,
        requiresAbstainedOrRejectedOutcome: true,
        claimsCoverageOfAllEmdashMathematics: false,
        claimsCurrentPublicAiProofWorkflow: true
    },
    semanticEffects: {
        proposalOnly: true,
        corpusCreated: false,
        parserCreated: false,
        benchmarkEvaluatorChanged: false,
        proofPlanChanged: false,
        simplifierChanged: false,
        premiseIndexChanged: false,
        classOrInstanceSynthesisChanged: false,
        publicBarrelChanged: false,
        packageVersionChanged: false,
        siblingRepositoryChanged: false,
        modelInvoked: false,
        hostedStateChanged: false
    },
    validation: {
        proposalTests: 'focused-direct',
        nearestOwnerTests: [
            'proof-agent-benchmark',
            'proof-plan-and-template',
            'proof-simplifier-and-obvious',
            'proof-maintenance',
            'class-inheritance-lowering-and-instance-scope'
        ],
        typecheck: true,
        focusedLint: true,
        staticNonExport: true,
        browserClosure: false,
        longAggregate: false
    },
    decision: {
        proposalIsSelfAuthorizing: false,
        separateImmutableReviewRequired: true,
        nextAfterApproval: 'implement-AGENT-EVAL-12B1-only'
    },
    doesNotAuthorize: [
        'changing the 12A evaluator task kind or acceptance authority',
        'counting PathOut qualification as an LF patch benchmark result',
        'a declaration, class, inductive, HIT, or tactic text parser',
        'a mutable proof server, authoritative MCP/LSP service, or hidden session',
        'a model/API/network/filesystem/process adapter in browser-safe semantics',
        'a new Core node, checker branch, runtime rule, proof rule, or axiom',
        'public barrel or package capability changes',
        'Node runner or browser product surface',
        'package version, npm/GitHub release, push, merge, or deployment',
        'CloserFans, Arrowgram, or active Lambdapi source mutation',
        'real-agent invocation, leaderboard, composite score, or performance SLA',
        'worktree, branch, tag, token, environment, or artifact cleanup'
    ]
} as const;

export type CoreLfProofAgentPublicCorpus12b1Proposal = typeof rawProposal;

export type CoreLfProofAgentPublicCorpus12b1ProposalErrorCode =
    | 'PUBLIC_CORPUS_PREREQUISITE_DRIFT'
    | 'PUBLIC_CORPUS_REPRESENTATIVENESS_DRIFT'
    | 'PUBLIC_CORPUS_AUTHORITY_DRIFT'
    | 'PUBLIC_CORPUS_PROPOSAL_DRIFT';

export class CoreLfProofAgentPublicCorpus12b1ProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfProofAgentPublicCorpus12b1ProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfProofAgentPublicCorpus12b1ProposalError';
    }
}

export const CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL =
    deepFreeze(rawProposal);

export function cloneCoreLfProofAgentPublicCorpus12b1Proposal():
CoreLfProofAgentPublicCorpus12b1Proposal {
    return JSON.parse(JSON.stringify(rawProposal)) as
        CoreLfProofAgentPublicCorpus12b1Proposal;
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreLfProofAgentPublicCorpus12b1Proposal(
    proposal: CoreLfProofAgentPublicCorpus12b1Proposal =
        CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL
): CoreLfProofAgentPublicCorpus12b1Proposal {
    if (
        proposal.parent.governingPlanCheckpoint !== '7aeb783' ||
        proposal.parent.synchronizedAuditLedgerCheckpoint !== '858126a' ||
        proposal.parent.evaluatorSemanticCheckpoint !== 'f46ff9a' ||
        proposal.parent.publicPackageVersion !== '0.2.0' ||
        proposal.parent.hostedTypescriptConsumerCheckpoint !== 'bd4146b' ||
        proposal.pinnedSources.length !== 13 ||
        new Set(proposal.pinnedSources.map(source => source.id)).size !== 13
    ) {
        throw new CoreLfProofAgentPublicCorpus12b1ProposalError(
            'PUBLIC_CORPUS_PREREQUISITE_DRIFT',
            'Public proof-agent corpus prerequisites drifted'
        );
    }

    const trackIds = proposal.tracks.map(track => track.id);
    const casesByTrack = new Map<string, number>();
    for (const entry of proposal.caseMatrix) {
        casesByTrack.set(entry.track, (casesByTrack.get(entry.track) ?? 0) + 1);
    }
    if (
        proposal.tracks.length < proposal.representativeness.minimumTrackCount ||
        proposal.caseMatrix.length <
            proposal.representativeness.minimumCaseCount ||
        proposal.representativeness.selectedTrackCount !== trackIds.length ||
        proposal.representativeness.selectedCaseCount !==
            proposal.caseMatrix.length ||
        new Set(trackIds).size !== trackIds.length ||
        new Set(proposal.caseMatrix.map(entry => entry.id)).size !==
            proposal.caseMatrix.length ||
        proposal.tracks.some(track =>
            (casesByTrack.get(track.id) ?? 0) < track.minimumCases
        ) ||
        proposal.caseMatrix.some(entry => !trackIds.includes(entry.track)) ||
        !proposal.caseMatrix.some(entry =>
            entry.expectedReferenceOutcome === 'accepted-complete'
        ) ||
        !proposal.caseMatrix.some(entry =>
            entry.expectedReferenceOutcome === 'abstained'
        )
    ) {
        throw new CoreLfProofAgentPublicCorpus12b1ProposalError(
            'PUBLIC_CORPUS_REPRESENTATIVENESS_DRIFT',
            'Public proof-agent corpus representativeness drifted'
        );
    }

    if (
        proposal.taskBoundary.taskKind !== 'lf-proof-plan-hole-patch' ||
        proposal.taskBoundary.pathoutPresentationIsCase ||
        proposal.taskBoundary.semanticProgramTaskFamilyAdded ||
        proposal.taskBoundary.newCoreNodeCount !== 0 ||
        proposal.taskBoundary.newCheckerBranchCount !== 0 ||
        proposal.taskBoundary.newRuleCount !== 0 ||
        proposal.plannedApi.publicBarrelExportedIn12B1 ||
        proposal.plannedApi.nodeRunnerIncludedIn12B1 ||
        !proposal.semanticEffects.proposalOnly ||
        proposal.semanticEffects.corpusCreated ||
        proposal.semanticEffects.parserCreated ||
        proposal.semanticEffects.publicBarrelChanged ||
        proposal.semanticEffects.packageVersionChanged ||
        proposal.semanticEffects.siblingRepositoryChanged ||
        proposal.semanticEffects.modelInvoked ||
        proposal.decision.proposalIsSelfAuthorizing ||
        !proposal.decision.separateImmutableReviewRequired
    ) {
        throw new CoreLfProofAgentPublicCorpus12b1ProposalError(
            'PUBLIC_CORPUS_AUTHORITY_DRIFT',
            'Public proof-agent corpus authority boundary drifted'
        );
    }

    if (!sameData(proposal, rawProposal)) {
        throw new CoreLfProofAgentPublicCorpus12b1ProposalError(
            'PUBLIC_CORPUS_PROPOSAL_DRIFT',
            'Public proof-agent corpus proposal drifted'
        );
    }
    return deepFreeze(proposal);
}
