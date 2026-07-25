/**
 * Separate immutable record for the H-DTTLF-03/D-DTTLF-001 approval.
 *
 * The pre-review DIRECTED-GRADUATE-1 recommendation remains unchanged and
 * non-self-authorizing. This artifact grants authority only to its exact
 * opt-in combined TypeScript continuation profile.
 */

import {
    CORE_DIRECTED_GRADUATION_RECOMMENDATION,
    CoreDirectedGraduationRecommendationInput,
    validateCoreDirectedGraduationRecommendation
} from './directed_graduation_proposal';

export interface CoreDirectedGraduationReviewInput {
    readonly revision: 'DIRECTED-GRADUATE-1-REVIEWED';
    readonly status: 'reviewed-approved';
    readonly approval: {
        readonly gate: 'H-DTTLF-03';
        readonly decisionId: 'D-DTTLF-001';
        readonly decision: 'approved-as-proposed';
        readonly reviewedOn: '2026-07-24';
        readonly decisionEvidence:
            'Approve H-DTTLF-03/D-DTTLF-001 as proposed';
    };
    /**
     * Immutable snapshot of the exact pre-review proposal. Its
     * `authorityAuthorized: false` field remains historical evidence.
     */
    readonly recommendation: CoreDirectedGraduationRecommendationInput;
    readonly authorization: {
        readonly typescriptContinuationKernelAuthority:
            'authorized-exact-opt-in-combined-profile';
        readonly profileRevision: 'emdash-v3.2-dttlf-directed-1';
        readonly manifestContentHash:
            'sha256:5fbf855e044e3d24e1078289eebad4a3391d67747efcee3c5463c2bfb110a8c7';
        readonly baseOwnerSignatureIds: readonly string[];
        readonly candidateDeclarationIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
        readonly baseOwnerSignatureCount: 20;
        readonly candidateDeclarationCount: 9;
        readonly totalOwnerSignatureCount: 29;
        readonly directedRuntimeRuleCount: 7;
        readonly inheritedMvpRuntimeRuleCount: 3;
        readonly totalRuntimeRuleCount: 10;
        readonly proofTimeRuleCount: 0;
        readonly outerLfTransitionOrder:
            readonly ['zonk', 'beta', 'delta', 'reviewed-runtime'];
        readonly outerLfComparisonStepLimit: 256;
        readonly entryPoint: 'src/v3_2/index.ts';
        readonly factoryExport:
            'createCoreDirectedContinuationKernel';
        readonly browserEntryPoint: 'excluded';
        readonly deployedMvpProfile: 'unchanged';
        readonly releaseReady: false;
        readonly lambdapiProductionRuntimeDependency: 'forbidden';
        readonly additionalOwnersOrRulesAuthorized: false;
    };
    readonly lambdapiPolicy:
        CoreDirectedGraduationRecommendationInput['lambdapiPolicy'];
    readonly claimBoundary:
        CoreDirectedGraduationRecommendationInput['claimBoundary'];
    readonly residualRisks: readonly string[];
    readonly explicitDeferrals: readonly string[];
    readonly nonEffects: readonly string[];
    readonly nextDependencyState:
        'no-independent-ready-slice-without-new-consumer-or-h-dttlf-04';
}

export type CoreDirectedGraduationReviewErrorCode =
    | 'GRADUATION_REVIEW_DECISION_DRIFT'
    | 'GRADUATION_REVIEW_PREREQUISITE_DRIFT'
    | 'GRADUATION_REVIEW_PROPOSAL_DRIFT'
    | 'GRADUATION_REVIEW_AUTHORIZATION_DRIFT';

export class CoreDirectedGraduationReviewError extends Error {
    constructor(
        public readonly code: CoreDirectedGraduationReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedGraduationReviewError';
    }
}

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const manifest =
    CORE_DIRECTED_GRADUATION_RECOMMENDATION.candidateManifest;

const approvedManifestContentHash =
    'sha256:5fbf855e044e3d24e1078289eebad4a3391d67747efcee3c5463c2bfb110a8c7' as const;

const rawReview: CoreDirectedGraduationReviewInput = {
    revision: 'DIRECTED-GRADUATE-1-REVIEWED',
    status: 'reviewed-approved',
    approval: {
        gate: 'H-DTTLF-03',
        decisionId: 'D-DTTLF-001',
        decision: 'approved-as-proposed',
        reviewedOn: '2026-07-24',
        decisionEvidence:
            'Approve H-DTTLF-03/D-DTTLF-001 as proposed'
    },
    recommendation: cloneData(
        CORE_DIRECTED_GRADUATION_RECOMMENDATION
    ),
    authorization: {
        typescriptContinuationKernelAuthority:
            'authorized-exact-opt-in-combined-profile',
        profileRevision: manifest.revision,
        manifestContentHash: approvedManifestContentHash,
        baseOwnerSignatureIds:
            manifest.baseOwnerSignatures.map(entry => entry.owner),
        candidateDeclarationIds:
            manifest.candidateDeclarations.map(entry => entry.owner),
        runtimeRuleIds:
            manifest.runtimeRules.map(entry => entry.id),
        baseOwnerSignatureCount:
            manifest.composition.baseOwnerSignatureCount,
        candidateDeclarationCount:
            manifest.composition.candidateDeclarationCount,
        totalOwnerSignatureCount:
            manifest.composition.totalOwnerSignatureCount,
        directedRuntimeRuleCount:
            manifest.composition.directedRuntimeRuleCount,
        inheritedMvpRuntimeRuleCount:
            manifest.composition.inheritedMvpRuntimeRuleCount,
        totalRuntimeRuleCount:
            manifest.composition.totalRuntimeRuleCount,
        proofTimeRuleCount:
            manifest.composition.proofTimeRuleCount,
        outerLfTransitionOrder: [
            ...manifest.outerLf.transitionOrder
        ],
        outerLfComparisonStepLimit:
            manifest.outerLf.comparisonStepLimit,
        entryPoint:
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
                .productBoundary.entryPoint,
        factoryExport: 'createCoreDirectedContinuationKernel',
        browserEntryPoint:
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
                .productBoundary.browserEntryPoint,
        deployedMvpProfile:
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
                .productBoundary.deployedMvpProfile,
        releaseReady:
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
                .productBoundary.releaseReady,
        lambdapiProductionRuntimeDependency: 'forbidden',
        additionalOwnersOrRulesAuthorized: false
    },
    lambdapiPolicy: cloneData(
        CORE_DIRECTED_GRADUATION_RECOMMENDATION.lambdapiPolicy
    ),
    claimBoundary: cloneData(
        CORE_DIRECTED_GRADUATION_RECOMMENDATION.claimBoundary
    ),
    residualRisks: [
        ...CORE_DIRECTED_GRADUATION_RECOMMENDATION.residualRisks
    ],
    explicitDeferrals: [
        ...CORE_DIRECTED_GRADUATION_RECOMMENDATION.explicitDeferrals
    ],
    nonEffects: [
        'does not mutate the pre-review proposal',
        'does not enter the browser import graph',
        'does not mutate or replace emdash-v3.2-mvp-1',
        'does not authorize release readiness',
        'does not add an owner, runtime rule, or proof-time rule',
        'does not transfer another active definition body',
        'does not make Lambdapi a production runtime dependency',
        'does not authorize a withheld metatheory or performance claim',
        'does not open the groupoidal closure programme'
    ],
    nextDependencyState:
        'no-independent-ready-slice-without-new-consumer-or-h-dttlf-04'
};

export const CORE_DIRECTED_GRADUATION_REVIEW =
    deepFreeze(rawReview);

export function validateCoreDirectedGraduationReview(
    review: CoreDirectedGraduationReviewInput =
        CORE_DIRECTED_GRADUATION_REVIEW
): void {
    if (
        review.revision !== 'DIRECTED-GRADUATE-1-REVIEWED' ||
        review.status !== 'reviewed-approved' ||
        review.approval.gate !== 'H-DTTLF-03' ||
        review.approval.decisionId !== 'D-DTTLF-001' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.reviewedOn !== '2026-07-24' ||
        review.approval.decisionEvidence !==
            'Approve H-DTTLF-03/D-DTTLF-001 as proposed'
    ) {
        throw new CoreDirectedGraduationReviewError(
            'GRADUATION_REVIEW_DECISION_DRIFT',
            'The directed graduation review must preserve the exact ' +
            'H-DTTLF-03/D-DTTLF-001 approval'
        );
    }

    try {
        validateCoreDirectedGraduationRecommendation(
            review.recommendation
        );
    } catch (error: unknown) {
        throw new CoreDirectedGraduationReviewError(
            'GRADUATION_REVIEW_PREREQUISITE_DRIFT',
            'The approved directed graduation prerequisites drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }

    if (!sameData(
        review.recommendation,
        CORE_DIRECTED_GRADUATION_RECOMMENDATION
    ) || review.recommendation.candidateManifest.contentHash !==
        approvedManifestContentHash) {
        throw new CoreDirectedGraduationReviewError(
            'GRADUATION_REVIEW_PROPOSAL_DRIFT',
            'The reviewed directed graduation recommendation is not exact'
        );
    }

    if (
        !sameData(review.authorization, rawReview.authorization) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreDirectedGraduationReviewError(
            'GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'The H-DTTLF-03/D-DTTLF-001 authorization boundary drifted'
        );
    }
}

validateCoreDirectedGraduationReview();
