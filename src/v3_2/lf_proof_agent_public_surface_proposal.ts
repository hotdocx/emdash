/**
 * Non-authorizing AGENT-EVAL-12B2 public benchmark-surface proposal.
 *
 * This immutable record selects a browser-safe package subpath, a stateless
 * repository Node adapter, and a lazy browser presentation. It changes no
 * barrel, package, command, browser product, capability record, version, or
 * release by itself.
 */

export const CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL_REVISION =
    'AGENT-EVAL-12B2-PROPOSAL-1' as const;

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
    revision: CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL_REVISION,
    row: 'AGENT-EVAL-12B2',
    status: 'ready-for-separate-review',
    recommendation:
        'add-browser-safe-benchmark-subpath-stateless-node-adapter-and-lazy-browser-view',
    parent: {
        governingPlanCheckpoint: '3e3fcf8',
        evaluatorSemanticCheckpoint: 'f46ff9a',
        corpusProposalCheckpoint: 'a181885',
        corpusReviewCheckpoint: 'd271c33',
        corpusSemanticCheckpoint: 'd0d3764',
        corpusLedgerCheckpoint: '3e3fcf8',
        publicPackageVersion: '0.2.0',
        publicPackageReleaseCheckpoint: 'ab513f7',
        nextPackageVersionAndReleaseOwner: 'AGENT-EVAL-12B3'
    },
    pinnedSources: [{
        id: 'proof-agent-evaluator',
        path: 'src/v3_2/lf_proof_agent_benchmark.ts',
        sha256:
            '9300877358e196045160e3bb059d644651f3d1a848e2211039c977be9910d3a4'
    }, {
        id: 'proof-agent-interchange',
        path: 'src/v3_2/lf_proof_agent_interchange.ts',
        sha256:
            '0df6d032d8f67162a499578e59f39f44fc724a08b4be4fa1a6a7c1bef5ce574d'
    }, {
        id: 'proof-agent-public-corpus',
        path: 'src/v3_2/lf_proof_agent_public_corpus.ts',
        sha256:
            '8d207b36ff5d4b645494bc696b681d23b08d0132b7d8b9831065b70a326c97e5'
    }, {
        id: 'package-core',
        path: 'src/v3_2/package_core.ts',
        sha256:
            '34e42cbb1fe6f3bf210e785bafda63b9ce9208da5dd4457e8aafd6fb6f7398a8'
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
        id: 'ai-native-capabilities',
        path: 'src/v3_2/ai_native_capabilities.ts',
        sha256:
            '8004d5e1f75f024de1a09678e905dd9130aebc71dad4f3b3e9a72f21aa488476'
    }, {
        id: 'package-manifest',
        path: 'packages/emdash/package.json',
        sha256:
            '21219b0ee9d55ed800760319754c961699bd4208d30f2a84bd5ad8126cb21d01'
    }, {
        id: 'package-build',
        path: 'packages/emdash/scripts/build-js.mjs',
        sha256:
            '64cb82a866df2c81ab817b3d2caeed9730b735e06faf981c7239df53c38ad888'
    }, {
        id: 'package-install-verifier',
        path: 'packages/emdash/scripts/verify-packed-install.mjs',
        sha256:
            '13fb183514f6bf2f4d9b68f3597164808142c8ce3413eeba85e1df2e888bac37'
    }, {
        id: 'package-release-preflight',
        path: 'packages/emdash/scripts/release-preflight.mjs',
        sha256:
            '3c972e38447b038cbd570f50cae9d9a79927986651ad2d3404f462f78f6eb82d'
    }, {
        id: 'package-tsconfig',
        path: 'packages/emdash/tsconfig.build.json',
        sha256:
            'a06e041b21322547de2c63774ba64d4ad6235519d3e3846b12b1e2693f27e04f'
    }, {
        id: 'package-readme',
        path: 'packages/emdash/README.md',
        sha256:
            'ca23a4561f0b7507002f257a4782f2719fb9088215d6ab2cb365e49f2f015325'
    }, {
        id: 'repository-dispatcher',
        path: 'scripts/emdash',
        sha256:
            '19961d9793becdc0490a7f93a6e4f9917a1e678f5ec1a606e7c75ade4ddd5521'
    }, {
        id: 'browser-loader',
        path: 'emdash-template/src/emdash_api.ts',
        sha256:
            '506d565ef74daaa854d9603ad87c9faee9f40711156e5d376be2b4ab739021e0'
    }, {
        id: 'browser-app',
        path: 'emdash-template/src/App.tsx',
        sha256:
            'f0cb81941262f48a23ba466ce57ac97584a450224fdc196b96b0fc19eb508530'
    }, {
        id: 'browser-closure-test',
        path: 'tests/v3_2_browser_directed_tests.ts',
        sha256:
            'cc4f6424c3a6a38a47cda9843ce641be26c79c54563b078a498d603ebb652314'
    }],
    measuredBoundary: {
        canonicalCorpusUtf8Bytes: 5884285,
        corpusTrackCount: 6,
        corpusCaseCount: 10,
        referenceAcceptedComplete: 9,
        referenceAbstained: 1,
        standaloneBrowserClosure: {
            esbuildVersion: '0.21.5',
            minifiedBytes: 548200,
            gzipBytes: 136817,
            sha256:
                '1d5bdf96b48358f827db94be37684eaaec5ba7ebcaa97f222d3fddb78eb5f3d4',
            measurementIsReleaseArtifactIdentity: false
        },
        browserInitialBaseline: {
            viteVersion: '5.4.19',
            minifiedBytes: 436361,
            gzipBytes: 117869,
            buildPassed: true
        }
    },
    publicPackageSurface: {
        newSubpath: '@hotdocx/emdash/benchmark',
        manifestExportKey: './benchmark',
        sourceEntry: 'src/v3_2/package_benchmark.ts',
        runtimeEsm: './dist/benchmark.js',
        runtimeCjs: './dist/benchmark.cjs',
        types: './dist/types/package_benchmark.d.ts',
        exportedOwners: [
            'lf_proof_agent_benchmark',
            'lf_proof_agent_interchange',
            'lf_proof_agent_public_corpus'
        ],
        existingExportOrder: [
            '.',
            './authoring',
            './workspace',
            './benchmark',
            './package.json'
        ],
        rootReexportsBenchmark: false,
        authoringReexportsBenchmark: false,
        workspaceReexportsBenchmark: false,
        browserSafe: true,
        nodeBuiltinDependency: false,
        packageVersionChangedIn12B2: false,
        npmBinAdded: false,
        installHookAdded: false,
        runtimeDependencyAdded: false,
        cliSourcePacked: false,
        releasePreflightRetainsNoBinPolicy: true
    },
    nodeRunner: {
        module: 'src/v3_2/lf_proof_agent_benchmark_cli.ts',
        example: 'examples/v3_2_proof_agent_benchmark_cli.ts',
        dispatcher: 'scripts/emdash benchmark',
        profileConstant: 'CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE',
        runFunction: 'runCoreLfProofAgentBenchmarkCli',
        defaultFormat: 'jsonl',
        formats: ['jsonl', 'text'],
        maximumRunInputBytes: 33554432,
        commands: [{
            id: 'catalog',
            syntax:
                './scripts/emdash benchmark catalog [--format jsonl|text]',
            jsonlOutput: 'compact-derived-non-authoritative-catalog'
        }, {
            id: 'case',
            syntax:
                './scripts/emdash benchmark case --case ID [--format jsonl|text]',
            jsonlOutput: 'exact-canonical-benchmark-case'
        }, {
            id: 'corpus',
            syntax:
                './scripts/emdash benchmark corpus [--format jsonl|text]',
            jsonlOutput: 'exact-canonical-full-corpus'
        }, {
            id: 'reference',
            syntax:
                './scripts/emdash benchmark reference [--format jsonl|text]',
            jsonlOutput: 'exact-canonical-reference-report'
        }, {
            id: 'evaluate',
            syntax:
                './scripts/emdash benchmark evaluate --run-file PATH ' +
                '[--format jsonl|text]',
            jsonlOutput: 'freshly-evaluated-exact-canonical-report'
        }],
        evaluateUsesStrictRunParser: true,
        evaluateFreshlyReplays: true,
        relativeRunPathBase: 'process-cwd',
        readsExactlyOneRunFile: true,
        scansDirectories: false,
        writesFiles: false,
        spawnsProvider: false,
        invokesModel: false,
        accessesNetwork: false,
        enforcesReportedResourceLimits: false,
        retainsSessionState: false,
        successExitCode: 0,
        errorExitCode: 2,
        errorIncludesStack: false,
        publishedAsNpmBin: false
    },
    browserPresentation: {
        loaderName: 'loadCoreProofAgentBenchmark',
        loaderTarget: '../../src/v3_2/lf_proof_agent_public_corpus.js',
        userTriggeredOnly: true,
        automaticallyBuildsCorpusOnPageLoad: false,
        automaticallySerializesFullCorpus: false,
        invokesModel: false,
        performsIo: false,
        displays: [
            'profile-and-evidence-boundary',
            'six-track-ten-case-catalog',
            'nine-accepted-one-abstained-reference-result',
            'case-owner-and-feature-attribution',
            'no-leaderboard-or-agent-performance-claim'
        ],
        initialChunkMaximumBytes: 465000,
        initialChunkMaximumGzipBytes: 130000,
        benchmarkLazyClosureMaximumBytes: 650000,
        benchmarkLazyClosureMaximumGzipBytes: 175000,
        initialChunkContainsCorpusRevision: false,
        lazyChunkContainsCorpusRevision: true
    },
    capabilityAndDocumentation: {
        capabilityRevisionFrom: 'emdash-ai-native-capabilities-v14',
        capabilityRevisionTo: 'emdash-ai-native-capabilities-v15',
        addImplementedProfiles: [
            'proof-agent-benchmark-evaluator',
            'proof-agent-canonical-interchange',
            'public-proof-agent-corpus',
            'proof-agent-benchmark-cli'
        ],
        addCommandFamily: 'benchmark',
        packageReadmeAddsFourthEntry: true,
        packageReadmeStatesReferenceRunIsNotProofAuthority: true,
        packageReadmeStatesNoModelOrProofServer: true,
        packageReadmeStatesNoNpmCli: true
    },
    implementationBoundary: {
        add: [
            'src/v3_2/package_benchmark.ts',
            'src/v3_2/lf_proof_agent_benchmark_cli.ts',
            'examples/v3_2_proof_agent_benchmark_cli.ts',
            'tests/v3_2_proof_agent_benchmark_cli_tests.ts',
            'tests/v3_2_proof_agent_browser_integration_tests.ts'
        ],
        modify: [
            'src/v3_2/ai_native_capabilities.ts',
            'scripts/emdash',
            'packages/emdash/package.json',
            'packages/emdash/README.md',
            'packages/emdash/tsconfig.build.json',
            'packages/emdash/scripts/build-js.mjs',
            'packages/emdash/scripts/verify-packed-install.mjs',
            'packages/emdash/scripts/release-preflight.mjs',
            'packages/emdash/scripts/release-preflight-tests.mjs',
            'emdash-template/src/emdash_api.ts',
            'emdash-template/src/App.tsx',
            'tests/v3_2_ai_proof_cli_tests.ts',
            'tests/v3_2_browser_directed_tests.ts',
            'tests/main_tests.ts'
        ],
        preserveUnchanged: [
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts'
        ],
        releasePreflightChange:
            'add-exact-benchmark-subpath-while-retaining-forbidden-bin-and-dependencies',
        changesCoreOrProofSemantics: false,
        changesCorpusOrInterchangeSemantics: false
    },
    validation: {
        proposalTests: 'focused-direct',
        implementationFocusedTests: [
            'proof-agent-interchange-and-public-corpus',
            'proof-agent-benchmark-cli',
            'proof-agent-browser-integration',
            'ai-native-capabilities',
            'browser-directed-closure',
            'npm-release-preflight'
        ],
        workspaceCheck: true,
        typecheck: true,
        focusedLint: true,
        browserTypecheckAndBuild: true,
        packageBuild: true,
        packedEsmConsumer: true,
        packedCjsConsumer: true,
        packedStrictNodeNextConsumer: true,
        packedBrowserConsumer: true,
        packageCoreOnlyExcludesBenchmarkClosure: true,
        diffHygiene: true,
        checkTsRequiredAbsentHumanWaiver: true,
        directStandingLongAggregateWaiverApplies: true,
        checkAll: false,
        lambdapi: false
    },
    semanticEffects: {
        proposalOnly: true,
        publicSubpathAdded: false,
        nodeRunnerAdded: false,
        browserProductChanged: false,
        capabilityRecordChanged: false,
        packageVersionChanged: false,
        packageReleased: false,
        siblingRepositoryChanged: false,
        modelInvoked: false,
        hostedStateChanged: false
    },
    decision: {
        proposalIsSelfAuthorizing: false,
        separateImmutableReviewRequired: true,
        nextAfterApproval: 'implement-AGENT-EVAL-12B2-only',
        nextAfterImplementation: 'freeze-AGENT-EVAL-12B3-release-contract'
    },
    doesNotAuthorize: [
        'changing 12A evaluation, 12B1 corpus, or interchange semantics',
        'a model/API invocation, provider callback, prompt, or network client',
        'a mutable proof server, authoritative MCP/LSP service, or hidden session',
        'claiming that outer run limits or provider usage were independently measured',
        'a leaderboard, composite score, performance SLA, or model comparison',
        'embedding the 5,884,285-byte corpus JSON in the initial browser chunk',
        'reexporting benchmark owners from core, authoring, or workspace entries',
        'an npm bin, install hook, runtime dependency, or packed CLI source',
        'a declaration, class, inductive, HIT, tactic, or general term parser',
        'a new Core node, checker branch, runtime rule, proof rule, or axiom',
        'package versioning, npm/GitHub release, push, merge, tag, or deployment',
        'CloserFans, Arrowgram, active Lambdapi, or mathematical source mutation',
        'real-agent invocation, hosted workspace mutation, or evidence publication',
        'worktree, branch, token, environment, or generated-artifact cleanup'
    ]
} as const;

export type CoreLfProofAgentPublicSurface12b2Proposal = typeof rawProposal;

export type CoreLfProofAgentPublicSurface12b2ProposalErrorCode =
    | 'PUBLIC_SURFACE_PREREQUISITE_DRIFT'
    | 'PUBLIC_SURFACE_PACKAGE_DRIFT'
    | 'PUBLIC_SURFACE_RUNNER_DRIFT'
    | 'PUBLIC_SURFACE_BROWSER_DRIFT'
    | 'PUBLIC_SURFACE_AUTHORITY_DRIFT'
    | 'PUBLIC_SURFACE_PROPOSAL_DRIFT';

export class CoreLfProofAgentPublicSurface12b2ProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfProofAgentPublicSurface12b2ProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfProofAgentPublicSurface12b2ProposalError';
    }
}

export const CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL =
    deepFreeze(rawProposal);

export function cloneCoreLfProofAgentPublicSurface12b2Proposal():
CoreLfProofAgentPublicSurface12b2Proposal {
    return JSON.parse(JSON.stringify(rawProposal)) as
        CoreLfProofAgentPublicSurface12b2Proposal;
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreLfProofAgentPublicSurface12b2Proposal(
    proposal: CoreLfProofAgentPublicSurface12b2Proposal =
        CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL
): CoreLfProofAgentPublicSurface12b2Proposal {
    if (
        proposal.parent.governingPlanCheckpoint !== '3e3fcf8' ||
        proposal.parent.corpusSemanticCheckpoint !== 'd0d3764' ||
        proposal.parent.corpusLedgerCheckpoint !== '3e3fcf8' ||
        proposal.parent.publicPackageVersion !== '0.2.0' ||
        proposal.pinnedSources.length !== 17 ||
        new Set(proposal.pinnedSources.map(source => source.id)).size !== 17 ||
        proposal.measuredBoundary.canonicalCorpusUtf8Bytes !== 5884285 ||
        proposal.measuredBoundary.corpusCaseCount !== 10
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ProposalError(
            'PUBLIC_SURFACE_PREREQUISITE_DRIFT',
            'Public proof-agent surface prerequisites drifted'
        );
    }

    if (
        proposal.publicPackageSurface.manifestExportKey !== './benchmark' ||
        proposal.publicPackageSurface.existingExportOrder.length !== 5 ||
        proposal.publicPackageSurface.rootReexportsBenchmark ||
        proposal.publicPackageSurface.authoringReexportsBenchmark ||
        proposal.publicPackageSurface.workspaceReexportsBenchmark ||
        !proposal.publicPackageSurface.browserSafe ||
        proposal.publicPackageSurface.nodeBuiltinDependency ||
        proposal.publicPackageSurface.packageVersionChangedIn12B2 ||
        proposal.publicPackageSurface.npmBinAdded ||
        proposal.publicPackageSurface.installHookAdded ||
        proposal.publicPackageSurface.runtimeDependencyAdded ||
        proposal.publicPackageSurface.cliSourcePacked ||
        !proposal.publicPackageSurface.releasePreflightRetainsNoBinPolicy
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ProposalError(
            'PUBLIC_SURFACE_PACKAGE_DRIFT',
            'Public proof-agent package boundary drifted'
        );
    }

    if (
        proposal.nodeRunner.commands.length !== 5 ||
        new Set(proposal.nodeRunner.commands.map(command => command.id))
            .size !== 5 ||
        proposal.nodeRunner.maximumRunInputBytes !== 33554432 ||
        !proposal.nodeRunner.evaluateUsesStrictRunParser ||
        !proposal.nodeRunner.evaluateFreshlyReplays ||
        !proposal.nodeRunner.readsExactlyOneRunFile ||
        proposal.nodeRunner.scansDirectories ||
        proposal.nodeRunner.writesFiles ||
        proposal.nodeRunner.spawnsProvider ||
        proposal.nodeRunner.invokesModel ||
        proposal.nodeRunner.accessesNetwork ||
        proposal.nodeRunner.enforcesReportedResourceLimits ||
        proposal.nodeRunner.retainsSessionState ||
        proposal.nodeRunner.publishedAsNpmBin
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ProposalError(
            'PUBLIC_SURFACE_RUNNER_DRIFT',
            'Public proof-agent Node runner boundary drifted'
        );
    }

    if (
        !proposal.browserPresentation.userTriggeredOnly ||
        proposal.browserPresentation.automaticallyBuildsCorpusOnPageLoad ||
        proposal.browserPresentation.automaticallySerializesFullCorpus ||
        proposal.browserPresentation.invokesModel ||
        proposal.browserPresentation.performsIo ||
        proposal.browserPresentation.initialChunkMaximumBytes > 465000 ||
        proposal.browserPresentation.initialChunkMaximumGzipBytes > 130000 ||
        proposal.browserPresentation.benchmarkLazyClosureMaximumBytes >
            650000 ||
        proposal.browserPresentation.benchmarkLazyClosureMaximumGzipBytes >
            175000 ||
        proposal.browserPresentation.initialChunkContainsCorpusRevision ||
        !proposal.browserPresentation.lazyChunkContainsCorpusRevision
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ProposalError(
            'PUBLIC_SURFACE_BROWSER_DRIFT',
            'Public proof-agent browser boundary drifted'
        );
    }

    if (
        !proposal.semanticEffects.proposalOnly ||
        proposal.semanticEffects.publicSubpathAdded ||
        proposal.semanticEffects.nodeRunnerAdded ||
        proposal.semanticEffects.browserProductChanged ||
        proposal.semanticEffects.capabilityRecordChanged ||
        proposal.semanticEffects.packageVersionChanged ||
        proposal.semanticEffects.packageReleased ||
        proposal.semanticEffects.siblingRepositoryChanged ||
        proposal.semanticEffects.modelInvoked ||
        proposal.semanticEffects.hostedStateChanged ||
        proposal.implementationBoundary.changesCoreOrProofSemantics ||
        proposal.implementationBoundary.changesCorpusOrInterchangeSemantics ||
        proposal.decision.proposalIsSelfAuthorizing ||
        !proposal.decision.separateImmutableReviewRequired
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ProposalError(
            'PUBLIC_SURFACE_AUTHORITY_DRIFT',
            'Public proof-agent surface authority boundary drifted'
        );
    }

    if (!sameData(proposal, rawProposal)) {
        throw new CoreLfProofAgentPublicSurface12b2ProposalError(
            'PUBLIC_SURFACE_PROPOSAL_DRIFT',
            'Public proof-agent surface proposal drifted'
        );
    }
    return deepFreeze(proposal);
}
