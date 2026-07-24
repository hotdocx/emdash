/**
 * Proposal and distinct review artifact for the TSK-2C / H-04 boundary.
 *
 * The pre-review recommendation remains immutable audit evidence. The
 * separate reviewed artifact records only the exact D-030 authorization and
 * changes no H-03 manifest, candidate runtime program, or executable rule.
 */

import {
    CORE_MVP_MANIFEST_PROPOSAL
} from './manifest';
import {
    CORE_MVP_RUNTIME_PROGRAM
} from './runtime';

export interface CoreRuntimeH04RecommendationInput {
    readonly status: string;
    readonly reviewGate: string;
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly runtimeRuleIds: readonly string[];
    readonly claims: {
        readonly termination: {
            readonly recommendation: string;
            readonly scope: string;
            readonly evidence: readonly string[];
        };
        readonly confluence: {
            readonly recommendation: string;
            readonly scope: string;
            readonly evidence: readonly string[];
        };
        readonly subjectReduction: {
            readonly recommendation: string;
            readonly scope: string;
            readonly evidence: readonly string[];
        };
        readonly trustedRules: {
            readonly recommendation: string;
            readonly scope: string;
        };
    };
    readonly trustedAssumptions: readonly string[];
    readonly nonExecutableEvidenceIds: readonly string[];
    readonly claimsAuthorized: boolean;
}

export interface CoreRuntimeH04ReviewApprovalInput {
    readonly gate: string;
    readonly decision: string;
    readonly decisionId: string;
    readonly reviewedOn: string;
}

export interface CoreRuntimeH04ReviewInput {
    readonly status: string;
    /**
     * Immutable snapshot of the exact pre-review input. Its
     * `claimsAuthorized: false` field remains historical evidence rather
     * than being retroactively rewritten.
     */
    readonly recommendation: CoreRuntimeH04RecommendationInput;
    readonly approval: CoreRuntimeH04ReviewApprovalInput;
    readonly authorization: {
        readonly termination: string;
        readonly deterministicBoundedEvaluationAndComparison: string;
        readonly trustedRuntimeRules: string;
        readonly generalConfluence: string;
        readonly typescriptSubjectReduction: string;
    };
    readonly subjectReductionOracle: string;
    readonly executableRuleIds: readonly string[];
    readonly mechanismsOutsideAuthorization: readonly string[];
    readonly additionalRuntimeRulesAuthorized: boolean;
}

export type CoreRuntimeMetatheoryErrorCode =
    | 'H04_RECOMMENDATION_MISMATCH'
    | 'H04_REVIEW_APPROVAL_MISMATCH'
    | 'H04_REVIEW_RECOMMENDATION_MISMATCH'
    | 'H04_REVIEW_BOUNDARY_MISMATCH';

export class CoreRuntimeMetatheoryError extends Error {
    constructor(
        public readonly code: CoreRuntimeMetatheoryErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreRuntimeMetatheoryError';
    }
}

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

const nonExecutableEvidenceIds = CORE_MVP_MANIFEST_PROPOSAL.rules
    .filter(rule => rule.authority !== 'runtime-reduction')
    .map(rule => rule.id);

const rawRecommendation: CoreRuntimeH04RecommendationInput = {
    status: 'proposed-awaiting-h04',
    reviewGate: 'H-04',
    manifestRevision: CORE_MVP_RUNTIME_PROGRAM.manifestRevision,
    manifestContentHash: CORE_MVP_RUNTIME_PROGRAM.manifestContentHash,
    runtimeRuleIds: CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id),
    claims: {
        termination: {
            recommendation: 'authorize-exact-fragment',
            scope: 'three-h03-reviewed-runtime-rules',
            evidence: [
                'global-full-projection-count-strictly-decreases',
                'matched-subterms-are-not-duplicated',
                'finite-core-syntax'
            ]
        },
        confluence: {
            recommendation: 'withhold-general-claim',
            scope: 'abstract-rewrite-relation',
            evidence: [
                'pairwise-rigid-root-discrimination-only',
                'left-patterns-are-nonlinear',
                'nested-critical-pairs-not-closed'
            ]
        },
        subjectReduction: {
            recommendation: 'withhold-typescript-theorem',
            scope: 'three-h03-reviewed-runtime-rules',
            evidence: [
                'exact-elaborated-result-classifiers',
                'bounded-lambdapi-differential-probes',
                'full-redex-checking-needs-unselected-classifier-computation'
            ]
        },
        trustedRules: {
            recommendation: 'authorize-exact-h03-runtime-set-only',
            scope: 'content-hashed-core-mvp-runtime-program'
        }
    },
    trustedAssumptions: [
        'finite-well-scoped-core-input',
        'content-hashed-h03-manifest-integrity',
        'lambdapi-remains-subject-reduction-oracle'
    ],
    nonExecutableEvidenceIds,
    claimsAuthorized: false
};

const sameRecommendation = (
    left: CoreRuntimeH04RecommendationInput,
    right: CoreRuntimeH04RecommendationInput
): boolean => JSON.stringify(left) === JSON.stringify(right);

const sameReviewData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const cloneReviewData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

/**
 * Reject any change to the exact H-04 review input before a decision is
 * recorded. A later approved artifact must be a distinct revision.
 */
export function validateCoreRuntimeH04Recommendation(
    recommendation: CoreRuntimeH04RecommendationInput
): void {
    if (!sameRecommendation(recommendation, rawRecommendation)) {
        throw new CoreRuntimeMetatheoryError(
            'H04_RECOMMENDATION_MISMATCH',
            'Runtime metatheory recommendation differs from the TSK-2C ' +
            'H-04 review input'
        );
    }
}

export const CORE_RUNTIME_H04_RECOMMENDATION = deepFreeze(
    rawRecommendation
);

validateCoreRuntimeH04Recommendation(CORE_RUNTIME_H04_RECOMMENDATION);

const expectedH04Approval: CoreRuntimeH04ReviewApprovalInput = {
    gate: 'H-04',
    decision: 'approved-as-proposed',
    decisionId: 'D-030',
    reviewedOn: '2026-07-24'
};

const expectedAuthorization: CoreRuntimeH04ReviewInput['authorization'] = {
    termination: 'authorized-exact-fragment',
    deterministicBoundedEvaluationAndComparison: 'authorized',
    trustedRuntimeRules: 'authorized-exact-h03-runtime-set-only',
    generalConfluence: 'withheld',
    typescriptSubjectReduction: 'withheld'
};

const expectedMechanismsOutsideAuthorization = [
    'proof-time-comparison',
    'intentional-runtime-non-conversion',
    'excluded-owner-rules',
    'declaration-unfolding',
    'generic-call-beta'
] as const;

const rawH04Review: CoreRuntimeH04ReviewInput = {
    status: 'reviewed-approved',
    recommendation: cloneReviewData(
        CORE_RUNTIME_H04_RECOMMENDATION
    ),
    approval: expectedH04Approval,
    authorization: expectedAuthorization,
    subjectReductionOracle: 'lambdapi',
    executableRuleIds: CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id),
    mechanismsOutsideAuthorization: expectedMechanismsOutsideAuthorization,
    additionalRuntimeRulesAuthorized: false
};

/**
 * Validate the exact approved H-04 boundary without changing the proposal,
 * reviewed H-03 manifest, or candidate runtime program.
 */
export function validateCoreRuntimeH04Review(
    review: CoreRuntimeH04ReviewInput
): void {
    if (
        review.status !== 'reviewed-approved' ||
        !sameReviewData(review.approval, expectedH04Approval)
    ) {
        throw new CoreRuntimeMetatheoryError(
            'H04_REVIEW_APPROVAL_MISMATCH',
            'Runtime metatheory review does not record the exact H-04 ' +
            'approval of D-030'
        );
    }
    if (!sameRecommendation(
        review.recommendation,
        CORE_RUNTIME_H04_RECOMMENDATION
    )) {
        throw new CoreRuntimeMetatheoryError(
            'H04_REVIEW_RECOMMENDATION_MISMATCH',
            'Runtime metatheory review differs from the approved D-030 ' +
            'recommendation'
        );
    }
    validateCoreRuntimeH04Recommendation(review.recommendation);

    if (
        !sameReviewData(review.authorization, expectedAuthorization) ||
        review.subjectReductionOracle !== 'lambdapi' ||
        !sameReviewData(
            review.executableRuleIds,
            CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id)
        ) ||
        !sameReviewData(
            review.mechanismsOutsideAuthorization,
            expectedMechanismsOutsideAuthorization
        ) ||
        review.additionalRuntimeRulesAuthorized !== false
    ) {
        throw new CoreRuntimeMetatheoryError(
            'H04_REVIEW_BOUNDARY_MISMATCH',
            'Runtime metatheory review exceeds or weakens the exact ' +
            'D-030 authorization boundary'
        );
    }
}

/**
 * The distinct H-04-reviewed claim boundary.
 *
 * This artifact authorizes only termination for the exact fragment, the
 * deterministic bounded mechanisms, and the three H-03 runtime rules.
 * General confluence and a standalone TypeScript subject-reduction theorem
 * remain withheld; Lambdapi remains the subject-reduction oracle.
 */
export const CORE_RUNTIME_H04_REVIEW = deepFreeze(rawH04Review);

validateCoreRuntimeH04Review(CORE_RUNTIME_H04_REVIEW);
