/**
 * Separate immutable review of AGENT-EVAL-12B2 proposal checkpoint ba49705.
 *
 * The review authorizes only the bounded public surface described below. It
 * grants no version, release, sibling, provider/model, or hosted authority.
 */

import {
    CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL,
    validateCoreLfProofAgentPublicSurface12b2Proposal
} from './lf_proof_agent_public_surface_proposal';

export const CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW_REVISION =
    'AGENT-EVAL-12B2-REVIEW-1' as const;

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const rawReview = {
    revision: CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW_REVISION,
    row: 'AGENT-EVAL-12B2',
    proposalCheckpoint: 'ba49705',
    proposalRevision:
        CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL.revision,
    proposalSha256:
        'c820786bd4974313fff2eae5e3d459f29d46a2a18a5c97690047fe324364e759',
    proposalTestSha256:
        'd1bccbc2049330e686a9a2c148c36351c29a902c19432c6f7ab374d031b7045b',
    decision: 'approved-for-AGENT-EVAL-12B2-bounded-implementation',
    authority: 'user-delegated-unattended-approval',
    humanMaySupersede: true,
    findings: {
        exact12b1CheckpointPinned: true,
        publicSubpathIsIsolated: true,
        nodeAdapterIsOuterAndStateless: true,
        npmNoBinPolicyRetained: true,
        corpusPayloadMeasured: true,
        browserLoadIsExplicitAndLazy: true,
        releaseRemains12b3: true,
        proposalIsNonAuthorizingWithoutThisReview: true
    },
    implementationConditions: [{
        id: 'unchanged-semantic-owners',
        requirement:
            '12A evaluation plus 12B1 corpus and interchange digests, ' +
            'revisions, case bytes, outcomes, and authority flags remain exact'
    }, {
        id: 'canonical-compact-catalog',
        requirement:
            'catalog JSONL has one exact revisioned canonical record derived ' +
            'from the rebuilt corpus, contains no case text, is deeply ' +
            'frozen, and states that it is neither task nor proof authority'
    }, {
        id: 'strict-run-file-boundary',
        requirement:
            'evaluate checks the raw byte limit before fatal UTF-8 decode, ' +
            'reads exactly one explicit path, and exposes stable errors ' +
            'without stacks or artifact contents'
    }, {
        id: 'fresh-evaluation-and-canonical-output',
        requirement:
            'evaluate uses the strict run parser then fresh unchanged 12A ' +
            'evaluation; every JSONL artifact command emits its owning ' +
            'canonical newline-terminated serializer bytes'
    }, {
        id: 'public-package-isolation',
        requirement:
            'only the new benchmark subpath exports benchmark owners; root, ' +
            'authoring, and workspace entries remain byte-exact and their ' +
            'isolated browser consumers exclude the corpus revision'
    }, {
        id: 'least-authority-package-policy',
        requirement:
            'release preflight still rejects bins, install hooks, runtime ' +
            'dependencies, scripts, and packed CLI source while accepting ' +
            'only the exact additive benchmark export'
    }, {
        id: 'transitive-browser-budget',
        requirement:
            'measure complete initial static and benchmark dynamic closures, ' +
            'not one guessed filename; enforce both raw and gzip caps and ' +
            'prove the corpus revision absent initially and present lazily'
    }, {
        id: 'browser-non-authority',
        requirement:
            'page load performs no corpus work; the explicit action presents ' +
            'fresh reference results as baseline evidence without serializing ' +
            'the full corpus, ranking models, or claiming performance'
    }, {
        id: 'installed-consumer-matrix',
        requirement:
            'packed ESM, CommonJS, strict NodeNext, and browser consumers use ' +
            'the benchmark subpath while a separate core-only consumer proves ' +
            'the benchmark closure is not acquired'
    }, {
        id: 'no-later-row-effects',
        requirement:
            '12B2 keeps package version 0.2.0 locally and performs no publish, ' +
            'release, sibling edit, real-agent run, hosted action, or ' +
            'aggregate-pass claim'
    }],
    validationAccepted: {
        proposalTests: 8,
        rootTypecheckPassed: true,
        focusedLintPassed: true,
        currentPackageBuildPassed: true,
        directBrowserTypecheckPassed: true,
        directBrowserBuildPassed: true,
        prescribedBrowserWrapperPassed: false,
        prescribedBrowserWrapperFailureRecorded: true,
        diffHygienePassed: true,
        longAggregateRun: false,
        longAggregateClaimed: false
    },
    semanticAuthorization: {
        addBenchmarkPackageEntry: true,
        addRepositoryNodeAdapter: true,
        addLazyBrowserPresentation: true,
        updateCapabilityRecord: true,
        updatePackageDocumentation: true,
        updatePackageBuildAndConsumerGates: true,
        updateExactReleasePreflightExports: true,
        change12aEvaluator: false,
        change12b1CorpusOrInterchange: false,
        changeCoreOrChecker: false,
        addRuntimeOrProofRule: false,
        reexportFromExistingPackageEntries: false,
        addNpmBinOrRuntimeDependency: false,
        changePackageVersion: false,
        publishOrRelease: false,
        mutateSiblingRepository: false,
        invokeProviderOrModel: false,
        mutateHostedState: false
    },
    nextAfterImplementation:
        'qualify-12B2-then-freeze-12B3-version-release-and-host-contract',
    doesNotAuthorize: [
        'semantic changes to 12A evaluation or 12B1 corpus/interchange',
        'a catalog or reference attempt as theorem or proof authority',
        'noncanonical JSONL, permissive UTF-8, unknown fields, or stale runs',
        'provider execution, a model/API client, prompt, callback, or network access',
        'a mutable proof server, authoritative MCP/LSP service, or hidden session',
        'a leaderboard, model comparison, composite score, or performance SLA',
        'eager browser corpus construction or initial-bundle corpus inclusion',
        'reexports from root, authoring, or workspace package entries',
        'an npm bin, install hook, dependency, packed CLI, or package script',
        'package versioning, npm/GitHub release, push, merge, tag, or deployment',
        'CloserFans, Arrowgram, active Lambdapi, or mathematical source mutation',
        'real-agent runs, hosted effects, or provider-resource enforcement claims',
        'history rewriting, worktree cleanup, or credential mutation'
    ]
} as const;

export type CoreLfProofAgentPublicSurface12b2Review = typeof rawReview;

export type CoreLfProofAgentPublicSurface12b2ReviewErrorCode =
    | 'PUBLIC_SURFACE_REVIEW_PROPOSAL_DRIFT'
    | 'PUBLIC_SURFACE_REVIEW_SCOPE_DRIFT'
    | 'PUBLIC_SURFACE_REVIEW_RECORD_DRIFT';

export class CoreLfProofAgentPublicSurface12b2ReviewError extends Error {
    constructor(
        public readonly code:
            CoreLfProofAgentPublicSurface12b2ReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfProofAgentPublicSurface12b2ReviewError';
    }
}

export const CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW =
    deepFreeze(rawReview);

export function cloneCoreLfProofAgentPublicSurface12b2Review():
CoreLfProofAgentPublicSurface12b2Review {
    return JSON.parse(JSON.stringify(rawReview)) as
        CoreLfProofAgentPublicSurface12b2Review;
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreLfProofAgentPublicSurface12b2Review(
    review: CoreLfProofAgentPublicSurface12b2Review =
        CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
): CoreLfProofAgentPublicSurface12b2Review {
    validateCoreLfProofAgentPublicSurface12b2Proposal();
    if (
        review.proposalCheckpoint !== 'ba49705' ||
        review.proposalRevision !==
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL.revision ||
        review.proposalSha256 !==
            'c820786bd4974313fff2eae5e3d459f29d46a2a18a5c97690047fe324364e759' ||
        review.findings.exact12b1CheckpointPinned !== true ||
        review.findings.releaseRemains12b3 !== true
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ReviewError(
            'PUBLIC_SURFACE_REVIEW_PROPOSAL_DRIFT',
            'Public proof-agent surface review proposal identity drifted'
        );
    }

    const conditionIds = review.implementationConditions.map(entry =>
        entry.id
    );
    if (
        review.decision !==
            'approved-for-AGENT-EVAL-12B2-bounded-implementation' ||
        review.implementationConditions.length !== 10 ||
        new Set(conditionIds).size !== 10 ||
        !conditionIds.includes('canonical-compact-catalog') ||
        !conditionIds.includes('strict-run-file-boundary') ||
        !conditionIds.includes('transitive-browser-budget') ||
        !conditionIds.includes('installed-consumer-matrix') ||
        !review.semanticAuthorization.addBenchmarkPackageEntry ||
        !review.semanticAuthorization.addRepositoryNodeAdapter ||
        !review.semanticAuthorization.addLazyBrowserPresentation ||
        review.semanticAuthorization.change12aEvaluator ||
        review.semanticAuthorization.change12b1CorpusOrInterchange ||
        review.semanticAuthorization.changeCoreOrChecker ||
        review.semanticAuthorization.addRuntimeOrProofRule ||
        review.semanticAuthorization.reexportFromExistingPackageEntries ||
        review.semanticAuthorization.addNpmBinOrRuntimeDependency ||
        review.semanticAuthorization.changePackageVersion ||
        review.semanticAuthorization.publishOrRelease ||
        review.semanticAuthorization.mutateSiblingRepository ||
        review.semanticAuthorization.invokeProviderOrModel ||
        review.semanticAuthorization.mutateHostedState ||
        review.validationAccepted.prescribedBrowserWrapperPassed ||
        !review.validationAccepted.prescribedBrowserWrapperFailureRecorded ||
        review.validationAccepted.longAggregateRun ||
        review.validationAccepted.longAggregateClaimed
    ) {
        throw new CoreLfProofAgentPublicSurface12b2ReviewError(
            'PUBLIC_SURFACE_REVIEW_SCOPE_DRIFT',
            'Public proof-agent surface review scope drifted'
        );
    }

    if (!sameData(review, rawReview)) {
        throw new CoreLfProofAgentPublicSurface12b2ReviewError(
            'PUBLIC_SURFACE_REVIEW_RECORD_DRIFT',
            'Public proof-agent surface review record drifted'
        );
    }
    return deepFreeze(review);
}
