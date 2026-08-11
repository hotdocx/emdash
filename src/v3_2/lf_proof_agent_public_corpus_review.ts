/**
 * Separate immutable review of AGENT-EVAL-12B1 proposal checkpoint a181885.
 *
 * The review authorizes only internal corpus/interchange implementation. It
 * grants no public export, runner, release, sibling, model, or hosted effect.
 */

import {
    CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL,
    validateCoreLfProofAgentPublicCorpus12b1Proposal
} from './lf_proof_agent_public_corpus_proposal';

export const CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW_REVISION =
    'AGENT-EVAL-12B1-REVIEW-1' as const;

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
    revision: CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW_REVISION,
    row: 'AGENT-EVAL-12B1',
    proposalCheckpoint: 'a181885',
    proposalRevision:
        CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL.revision,
    proposalSha256:
        'ecbd67496a99775c13357d9175b623200e20e79346d62b00b8773bc5e7d08a60',
    proposalTestSha256:
        'b128059af3803eb077fc37b9438e9ef299eb2bf3fab6acb7143f07064ecf71d9',
    decision: 'approved-for-AGENT-EVAL-12B1-internal-implementation',
    authority: 'user-delegated-unattended-approval',
    humanMaySupersede: true,
    findings: {
        exactPredecessorsPinned: true,
        sixTracksPinned: true,
        selectedCaseCount: 10,
        minimumCaseCount: 8,
        leanSourceAndLicensePinned: true,
        pathoutTaskKindKeptSeparate: true,
        evaluatorAuthorityUnchanged: true,
        publicBoundaryUnchanged: true,
        proposalIsNonAuthorizingWithoutThisReview: true
    },
    implementationConditions: [{
        id: 'unchanged-12a-case-contract',
        requirement:
            'every selected task must construct one valid canonical 12A case'
    }, {
        id: 'reference-owner-integration',
        requirement:
            'each non-abstaining reference owner must generate one ordinary ' +
            'patch accepted by fresh unchanged 12A replay'
    }, {
        id: 'no-label-substitution',
        requirement:
            'feature and origin labels cannot substitute for executable ' +
            'owner integration or checked replay'
    }, {
        id: 'ambiguity-honesty',
        requirement:
            'the ambiguity case must retain explicit finite synthesis ' +
            'evidence and abstention without an arbitrary hidden winner'
    }, {
        id: 'lean-translation-boundary',
        requirement:
            'the Lean-shaped case must record attribution and a manual ' +
            'semantic correspondence without claiming parser parity'
    }, {
        id: 'strict-canonical-interchange',
        requirement:
            'all exposed corpus and attempt/run/report text must reject ' +
            'unknown fields, stale identity, unsupported revisions, and ' +
            'noncanonical or nonportable data'
    }, {
        id: 'internal-only',
        requirement:
            '12B1 remains absent from public package barrels and has no Node ' +
            'runner, package version, sibling mutation, or model call'
    }],
    validationAccepted: {
        proposalTests: 8,
        nearestOwnerTests: 104,
        nearestOwnerSuites: 18,
        rootTypecheckPassed: true,
        focusedLintPassed: true,
        staticNonExportPassed: true,
        diffHygienePassed: true,
        longAggregateRun: false,
        longAggregateClaimed: false
    },
    semanticAuthorization: {
        addCorpusModule: true,
        addInterchangeModule: true,
        addFocusedTests: true,
        useExistingProofManagementOwners: true,
        useExistingClassAndInstanceOwners: true,
        useExisting12aEvaluator: true,
        change12aTaskKind: false,
        changeCoreOrChecker: false,
        addRuntimeOrProofRule: false,
        addParserForDeclarationsOrClasses: false,
        addPathoutTaskFamily: false,
        exportPublicPackageBarrel: false,
        addNodeRunner: false,
        changePackageVersion: false,
        publishOrRelease: false,
        mutateSiblingRepository: false,
        invokeModel: false,
        mutateHostedState: false
    },
    nextAfterImplementation:
        'qualify-12B1-then-audit-12B2-public-runner-and-package-surface',
    doesNotAuthorize: [
        'a corpus case which does not freshly reconstruct under 12A',
        'feature labels as checker or synthesis evidence',
        'an arbitrary winner for genuine instance ambiguity',
        'a PathOut presentation or qualification report as an LF patch case',
        'a new task kind, checker, Core node, runtime rule, or proof rule',
        'declaration, class, inductive, HIT, or tactic text parsing',
        'public package exports, browser product, or Node runner',
        'package versioning, npm/GitHub release, push, merge, or deployment',
        'CloserFans, Arrowgram, or active Lambdapi source mutation',
        'model invocation, leaderboard, performance SLA, or hosted action',
        'history rewriting, worktree cleanup, or credential mutation'
    ]
} as const;

export type CoreLfProofAgentPublicCorpus12b1Review = typeof rawReview;

export type CoreLfProofAgentPublicCorpus12b1ReviewErrorCode =
    | 'PUBLIC_CORPUS_REVIEW_PROPOSAL_DRIFT'
    | 'PUBLIC_CORPUS_REVIEW_SCOPE_DRIFT'
    | 'PUBLIC_CORPUS_REVIEW_RECORD_DRIFT';

export class CoreLfProofAgentPublicCorpus12b1ReviewError extends Error {
    constructor(
        public readonly code:
            CoreLfProofAgentPublicCorpus12b1ReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfProofAgentPublicCorpus12b1ReviewError';
    }
}

export const CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW =
    deepFreeze(rawReview);

export function cloneCoreLfProofAgentPublicCorpus12b1Review():
CoreLfProofAgentPublicCorpus12b1Review {
    return JSON.parse(JSON.stringify(rawReview)) as
        CoreLfProofAgentPublicCorpus12b1Review;
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreLfProofAgentPublicCorpus12b1Review(
    review: CoreLfProofAgentPublicCorpus12b1Review =
        CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW
): CoreLfProofAgentPublicCorpus12b1Review {
    validateCoreLfProofAgentPublicCorpus12b1Proposal();
    if (
        review.proposalCheckpoint !== 'a181885' ||
        review.proposalRevision !==
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL.revision ||
        review.proposalSha256 !==
            'ecbd67496a99775c13357d9175b623200e20e79346d62b00b8773bc5e7d08a60' ||
        review.findings.selectedCaseCount !==
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL
                .representativeness.selectedCaseCount
    ) {
        throw new CoreLfProofAgentPublicCorpus12b1ReviewError(
            'PUBLIC_CORPUS_REVIEW_PROPOSAL_DRIFT',
            'Public proof-agent corpus review proposal identity drifted'
        );
    }

    const conditionIds = review.implementationConditions.map(entry =>
        entry.id
    );
    if (
        review.decision !==
            'approved-for-AGENT-EVAL-12B1-internal-implementation' ||
        review.implementationConditions.length !== 7 ||
        new Set(conditionIds).size !== 7 ||
        !conditionIds.includes('reference-owner-integration') ||
        !conditionIds.includes('no-label-substitution') ||
        !conditionIds.includes('ambiguity-honesty') ||
        !review.semanticAuthorization.addCorpusModule ||
        !review.semanticAuthorization.addInterchangeModule ||
        review.semanticAuthorization.change12aTaskKind ||
        review.semanticAuthorization.changeCoreOrChecker ||
        review.semanticAuthorization.addRuntimeOrProofRule ||
        review.semanticAuthorization.exportPublicPackageBarrel ||
        review.semanticAuthorization.addNodeRunner ||
        review.semanticAuthorization.changePackageVersion ||
        review.semanticAuthorization.publishOrRelease ||
        review.semanticAuthorization.mutateSiblingRepository ||
        review.semanticAuthorization.invokeModel ||
        review.semanticAuthorization.mutateHostedState ||
        review.validationAccepted.longAggregateRun ||
        review.validationAccepted.longAggregateClaimed
    ) {
        throw new CoreLfProofAgentPublicCorpus12b1ReviewError(
            'PUBLIC_CORPUS_REVIEW_SCOPE_DRIFT',
            'Public proof-agent corpus review scope drifted'
        );
    }

    if (!sameData(review, rawReview)) {
        throw new CoreLfProofAgentPublicCorpus12b1ReviewError(
            'PUBLIC_CORPUS_REVIEW_RECORD_DRIFT',
            'Public proof-agent corpus review record drifted'
        );
    }
    return deepFreeze(review);
}
