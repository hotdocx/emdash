/**
 * Separate immutable review of PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G.
 *
 * This review approves only proposal checkpoint 85b560e and its exact digest.
 * The approval qualifies a root-source profile; it has no export or release
 * effect and grants no ordinary-user rule capability.
 */

import {
    CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL,
    validateCorePathoutLibraryGraduation0gProposal
} from './pathout_library_graduation_proposal';

export const CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW_REVISION =
    'PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G-REVIEW-1' as const;

const APPROVED_PROPOSAL_CHECKPOINT = '85b560e';
const APPROVED_PROPOSAL_SHA256 =
    'fc35b53dd151694069974b4df6ad3c04ee55cd5d8bacad34f9f21c47c8cee572';

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const authorization = {
    exactProfileId: 'emdash-v3.2-pathout-pathind-root-1',
    qualification: 'root-only-source-qualified',
    mathematicalOpaqueOwnerCount: 5,
    sealedSupportingOwnerCount: 9,
    totalLocalSealedDeclarationCount: 14,
    runtimeRuleCount: 39,
    proofRuleCount: 2,
    transparentDefinitionCount: 30,
    localSliceBoundaries: [
        '5/13/2/9',
        '5/12/0/6',
        '4/13/0/10',
        '0/1/0/5'
    ],
    fixedSourcePointAndArrowComputationQualified: true,
    internallyVaryingSourceActionQualified: true,
    selectedHigherActionQualified: true,
    compositionNormalFormQualified: true,
    compositionNormalFormTarget: 'stable-representable-precomposition',
    finitePresentationFormCount: 4,
    browserEvidenceMustRemainPinnedAndNonFresh: true,
    onlyExplicitNodeCheckMayClaimFreshTypeScriptEvidence: true,
    productionBackend: 'typescript-emdash',
    lambdapiRole: 'bounded-conformance-oracle',
    ordinaryUsersMayAddTransparentDefinitions: true,
    ordinaryUsersMayAddOpaqueOwners: false,
    ordinaryUsersMayAddRuntimeRules: false,
    ordinaryUsersMayAddProofRules: false,
    pathCategoryBridgeQualified: false,
    wholeTheoryMetatheoryQualified: false,
    contributorBarrelExportAuthorized: false,
    npmBarrelExportAuthorized: false,
    packageVersionOrReleaseAuthorized: false,
    integrationOrDeploymentAuthorized: false,
    activeLambdapiEditAuthorized: false,
    semanticImplementationRequired: false
} as const;

const rawReview = {
    revision: CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW_REVISION,
    status: 'approved-exact-root-source-graduation',
    approval: {
        approvedProposalRevision:
            CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL.revision,
        approvedProposalCheckpoint: APPROVED_PROPOSAL_CHECKPOINT,
        approvedProposalSha256: APPROVED_PROPOSAL_SHA256,
        authority: 'user-delegated-unattended-approval',
        humanDecisionSupersedes: true
    },
    recommendation: CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL,
    authorization,
    findings: [
        {
            id: 'PATHOUT-GRADUATION-FINDING-1',
            disposition: 'approve-exact-trust-partition',
            statement:
                'Five mathematical opaque owners and nine sealed supports ' +
                'are distinct from thirty transparent library definitions.'
        },
        {
            id: 'PATHOUT-GRADUATION-FINDING-2',
            disposition: 'approve-bounded-computation',
            statement:
                'Measured fixed-source, internally varying, selected ' +
                'higher, and composition behavior support graduation ' +
                'without a whole-theory metatheory claim.'
        },
        {
            id: 'PATHOUT-GRADUATION-FINDING-3',
            disposition: 'approve-honest-presentation',
            statement:
                'The browser and explicit Node evidence classes remain ' +
                'visibly different and add no second semantic engine.'
        },
        {
            id: 'PATHOUT-GRADUATION-FINDING-4',
            disposition: 'approve-root-only-not-publication',
            statement:
                'Root-source qualification completes STDLIB-8B but does ' +
                'not authorize a public barrel, package version, or release.'
        }
    ],
    decision: {
        status: 'approved',
        graduatedProfileId: 'emdash-v3.2-pathout-pathind-root-1',
        graduatedScope: 'root-only-source-qualified',
        pathoutTrustedLibraryGraduate0gComplete: true,
        stdlib8bComplete: true,
        semanticImplementationDelta: 0,
        publicDistributionApproved: false,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize:
        CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL.doesNotAuthorize,
    nextDependencyState: 'post-stdlib-8b-readiness-audit'
} as const;

export type CorePathoutLibraryGraduation0gReview = typeof rawReview;

export type CorePathoutLibraryGraduation0gReviewErrorCode =
    | 'PATHOUT_GRADUATION_REVIEW_DECISION_DRIFT'
    | 'PATHOUT_GRADUATION_REVIEW_PROPOSAL_DRIFT'
    | 'PATHOUT_GRADUATION_REVIEW_AUTHORIZATION_DRIFT';

export class CorePathoutLibraryGraduation0gReviewError extends Error {
    constructor(
        public readonly code: CorePathoutLibraryGraduation0gReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutLibraryGraduation0gReviewError';
    }
}

export const CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW =
    deepFreeze(rawReview);

export function cloneCorePathoutLibraryGraduation0gReview():
CorePathoutLibraryGraduation0gReview {
    return JSON.parse(JSON.stringify(rawReview)) as
        CorePathoutLibraryGraduation0gReview;
}

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCorePathoutLibraryGraduation0gReview(
    review: CorePathoutLibraryGraduation0gReview =
        CORE_PATHOUT_LIBRARY_GRADUATION_0G_REVIEW
): CorePathoutLibraryGraduation0gReview {
    validateCorePathoutLibraryGraduation0gProposal();
    if (
        review.approval.approvedProposalCheckpoint !==
            APPROVED_PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !==
            APPROVED_PROPOSAL_SHA256 ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        !sameData(review.decision, rawReview.decision)
    ) {
        throw new CorePathoutLibraryGraduation0gReviewError(
            'PATHOUT_GRADUATION_REVIEW_DECISION_DRIFT',
            'PathOut graduation review decision drifted'
        );
    }
    if (!sameData(
        review.recommendation,
        CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL
    )) {
        throw new CorePathoutLibraryGraduation0gReviewError(
            'PATHOUT_GRADUATION_REVIEW_PROPOSAL_DRIFT',
            'PathOut graduation review proposal drifted'
        );
    }
    const reviewScope = {
        revision: review.revision,
        status: review.status,
        authorization: review.authorization,
        findings: review.findings,
        doesNotAuthorize: review.doesNotAuthorize,
        nextDependencyState: review.nextDependencyState
    };
    const expectedScope = {
        revision: rawReview.revision,
        status: rawReview.status,
        authorization: rawReview.authorization,
        findings: rawReview.findings,
        doesNotAuthorize: rawReview.doesNotAuthorize,
        nextDependencyState: rawReview.nextDependencyState
    };
    if (!sameData(reviewScope, expectedScope)) {
        throw new CorePathoutLibraryGraduation0gReviewError(
            'PATHOUT_GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'PathOut graduation review authorization drifted'
        );
    }
    return deepFreeze(review);
}
