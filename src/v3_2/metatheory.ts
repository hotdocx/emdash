/**
 * Review proposal for the TSK-2C / H-04 trusted-rule boundary.
 *
 * This artifact records evidence and recommendations only. It does not change
 * the H-03 manifest, authorize a claim, or add an executable rule.
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

export type CoreRuntimeMetatheoryErrorCode =
    'H04_RECOMMENDATION_MISMATCH';

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
