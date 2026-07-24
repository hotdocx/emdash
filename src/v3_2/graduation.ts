/**
 * Frozen GRADUATE-1A recommendation for the H-05 product-authority gate.
 *
 * This proposal does not authorize its own recommendation. A distinct
 * post-review artifact must record any H-05 decision. The proposal binds the
 * exact H-03 product profile to the H-04 claim boundary, completed TSK-3
 * differential matrix, and completed legacy deletion.
 */

import {
    CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT
} from './checker';
import {
    CORE_MVP_DIFFERENTIAL_COMPLETION,
    validateCoreMvpDifferentialCompletion
} from './differential_higher_cell';
import {
    CORE_MVP_MANIFEST,
    validateCoreMvpManifest
} from './manifest';
import {
    CORE_RUNTIME_H04_REVIEW,
    validateCoreRuntimeH04Review
} from './metatheory';
import {
    LEGACY_MIGRATION_COMPLETION,
    validateLegacyMigrationCompletion
} from './migration';

export interface CoreMvpGraduationRecommendationInput {
    readonly revision: 'GRADUATE-1A';
    readonly status: 'proposed-awaiting-h05';
    readonly reviewGate: 'H-05';
    readonly decisionId: 'D-039';
    readonly productAuthority: {
        readonly recommendation:
            'approve-typescript-as-authoritative-deployed-mvp-kernel';
        readonly scope: 'exact-h03-reviewed-profile';
        readonly manifestRevision: string;
        readonly manifestContentHash: string;
        readonly ownerIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
        readonly browserEntryPoint: 'src/v3_2/browser.ts';
        readonly lambdapiProductionRuntimeDependency: false;
    };
    readonly lambdapiPolicy: {
        readonly recommendation:
            'retain-as-selected-change-acceptance-authority';
        readonly mathematicalSpecification: 'active';
        readonly frozenCorpusCiOracle: 'required';
        readonly subjectReductionOracle: 'required';
        readonly perTermProductionCheck: 'not-required';
        readonly acceptanceTriggers: readonly string[];
        readonly changesNotRequiringNewAuthorityReview: readonly string[];
    };
    readonly claimBoundary: {
        readonly termination: 'authorized-exact-fragment';
        readonly deterministicBoundedEvaluationAndComparison: 'authorized';
        readonly trustedRuntimeRules:
            'authorized-exact-h03-runtime-set-only';
        readonly generalConfluence: 'withheld';
        readonly typescriptSubjectReduction: 'withheld';
        readonly additionalRuntimeRulesAuthorized: false;
    };
    readonly evidence: {
        readonly parityStatus: 'frozen-fragment-parity-complete';
        readonly ownerCaseCount: 16;
        readonly runtimeRuleCaseCount: 3;
        readonly higherCellPackageCount: 2;
        readonly unclosedParityRows: 0;
        readonly migrationRevision: 'MIGRATE-2';
        readonly deletedLegacyTargetCount: 36;
        readonly compatibilityApiRetained: false;
        readonly validationGates: readonly string[];
    };
    readonly performanceBoundary: {
        readonly mechanism:
            'explicitly-bounded-runtime-comparison';
        readonly checkerComparisonStepLimit: 256;
        readonly deploymentEvidence:
            'standalone-browser-typecheck-and-production-build-green';
        readonly performanceClaim:
            'no-latency-throughput-or-scale-sla';
        readonly followUp:
            'measure-representative-workloads-before-performance-claim';
    };
    readonly maintenanceBoundary: {
        readonly legacyTargetsRemoved: 36;
        readonly compatibilityLayerRetained: false;
        readonly dualMaintenanceScope:
            'selected-owner-rule-and-metatheory-boundary-changes';
        readonly rationale:
            'retained-because-typescript-subject-reduction-is-withheld';
    };
    readonly releaseFollowUps: readonly {
        readonly id: string;
        readonly disposition: string;
        readonly blocksGraduation: false;
    }[];
    readonly nonEffects: readonly string[];
    readonly decisionQuestion: string;
    readonly authorityAuthorized: false;
}

export interface CoreMvpGraduationReviewApprovalInput {
    readonly gate: 'H-05';
    readonly decision: 'approved-as-proposed';
    readonly decisionId: 'D-039';
    readonly reviewedOn: '2026-07-24';
}

export interface CoreMvpGraduationReviewInput {
    readonly revision: 'GRADUATE-1B';
    readonly status: 'reviewed-approved';
    /**
     * Immutable snapshot of the exact pre-review proposal. Its
     * `authorityAuthorized: false` field remains historical evidence.
     */
    readonly recommendation: CoreMvpGraduationRecommendationInput;
    readonly approval: CoreMvpGraduationReviewApprovalInput;
    readonly authorization: {
        readonly typescriptDeployedRuntimeAuthority:
            'authorized-exact-frozen-profile';
        readonly lambdapiProductionRuntimeDependency: 'forbidden';
        readonly lambdapiMathematicalSpecification: 'retained';
        readonly frozenCorpusCiOracle: 'required';
        readonly subjectReductionOracle: 'required';
        readonly selectedChangeAcceptanceAuthority: 'retained';
        readonly perTermProductionCheck: 'not-required';
    };
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly ownerIds: readonly string[];
    readonly runtimeRuleIds: readonly string[];
    readonly acceptanceTriggers: readonly string[];
    readonly changesNotRequiringNewAuthorityReview: readonly string[];
    readonly generalConfluence: 'withheld';
    readonly typescriptSubjectReduction: 'withheld';
    readonly additionalOwnersOrRulesAuthorized: false;
    readonly performanceSlaAuthorized: false;
    readonly releaseReady: false;
    readonly nextSlice: 'RELEASE-READY';
}

export type CoreMvpGraduationErrorCode =
    | 'GRADUATION_EVIDENCE_MISMATCH'
    | 'GRADUATION_RECOMMENDATION_MISMATCH'
    | 'GRADUATION_REVIEW_APPROVAL_MISMATCH'
    | 'GRADUATION_REVIEW_RECOMMENDATION_MISMATCH'
    | 'GRADUATION_REVIEW_BOUNDARY_MISMATCH';

export class CoreMvpGraduationError extends Error {
    constructor(
        public readonly code: CoreMvpGraduationErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreMvpGraduationError';
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

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const expectedManifestIdentity = {
    revision: 'emdash-v3.2-mvp-1',
    contentHash:
        'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0',
    ownerIds: [
        'groupoid-universe',
        'category-universe',
        'decode',
        'object-classifier',
        'functor-classifier',
        'hom-classifier',
        'transfor-classifier',
        'hom-category',
        'transfor-category',
        'functor-object',
        'functor-hom-full',
        'functor-hom-capped',
        'transfor-component-full',
        'transfor-component-capped',
        'transfor-hom-full',
        'transfor-hom-capped'
    ],
    runtimeRuleIds: [
        'projection.functor-hom.evaluate',
        'projection.transfor-component.evaluate',
        'projection.transfor-hom.evaluate'
    ]
} as const;

const expectedAcceptanceTriggers = [
    'selected-owner-signature-change',
    'selected-runtime-rule-shape-or-authority-change',
    'owner-or-rule-promotion-into-product-profile',
    'termination-confluence-or-subject-reduction-claim-change',
    'shared-corpus-backend-binding-change'
] as const;

const expectedNonAuthorityChanges = [
    'implementation-refactor-preserving-frozen-profile',
    'surface-or-diagnostic-change-preserving-core-boundary',
    'packaging-change-preserving-browser-import-boundary'
] as const;

const expectedValidationGates = [
    'focused-graduation-and-evidence-tests',
    'shared-fragment-lambdapi-differential-probes',
    'root-check-ts',
    'bounded-active-lambdapi-check',
    'standalone-browser-typecheck-and-production-build',
    'full-repository-check-all'
] as const;

const expectedReleaseFollowUps = [{
    id: 'C-18',
    disposition: 'complete-backend-diagnostic-remapping-at-release-ready',
    blocksGraduation: false
}, {
    id: 'PERFORMANCE-BASELINE',
    disposition: 'required-before-any-performance-sla',
    blocksGraduation: false
}, {
    id: 'RELEASE-POLICY-SYNC',
    disposition:
        'synchronize-docs-manifests-examples-and-residual-oracle-policy',
    blocksGraduation: false
}] as const;

const expectedNonEffects = [
    'does-not-authorize-general-confluence',
    'does-not-claim-standalone-typescript-subject-reduction',
    'does-not-add-or-promote-an-owner-or-rule',
    'does-not-make-lambdapi-a-production-runtime-dependency',
    'does-not-complete-release-ready',
    'does-not-trigger-h02-or-h06'
] as const;

const expectedH04Authorization = {
    termination: 'authorized-exact-fragment',
    deterministicBoundedEvaluationAndComparison: 'authorized',
    trustedRuntimeRules: 'authorized-exact-h03-runtime-set-only',
    generalConfluence: 'withheld',
    typescriptSubjectReduction: 'withheld'
} as const;

const expectedDecisionQuestion =
    'Approve H-05/D-039 as proposed: graduate the TypeScript checker and ' +
    'evaluator as the authoritative deployed runtime kernel for exactly ' +
    'emdash-v3.2-mvp-1 (16 owners and 3 runtime rules), with no Lambdapi ' +
    'production dependency, while retaining Lambdapi as the active ' +
    'mathematical specification, fixed-corpus CI and subject-reduction ' +
    'oracle, and acceptance authority for the five listed semantic-boundary ' +
    'changes?';

const expectedRecommendation: CoreMvpGraduationRecommendationInput = {
    revision: 'GRADUATE-1A',
    status: 'proposed-awaiting-h05',
    reviewGate: 'H-05',
    decisionId: 'D-039',
    productAuthority: {
        recommendation:
            'approve-typescript-as-authoritative-deployed-mvp-kernel',
        scope: 'exact-h03-reviewed-profile',
        manifestRevision: expectedManifestIdentity.revision,
        manifestContentHash: expectedManifestIdentity.contentHash,
        ownerIds: expectedManifestIdentity.ownerIds,
        runtimeRuleIds: expectedManifestIdentity.runtimeRuleIds,
        browserEntryPoint: 'src/v3_2/browser.ts',
        lambdapiProductionRuntimeDependency: false
    },
    lambdapiPolicy: {
        recommendation:
            'retain-as-selected-change-acceptance-authority',
        mathematicalSpecification: 'active',
        frozenCorpusCiOracle: 'required',
        subjectReductionOracle: 'required',
        perTermProductionCheck: 'not-required',
        acceptanceTriggers: expectedAcceptanceTriggers,
        changesNotRequiringNewAuthorityReview: expectedNonAuthorityChanges
    },
    claimBoundary: {
        termination: 'authorized-exact-fragment',
        deterministicBoundedEvaluationAndComparison: 'authorized',
        trustedRuntimeRules:
            'authorized-exact-h03-runtime-set-only',
        generalConfluence: 'withheld',
        typescriptSubjectReduction: 'withheld',
        additionalRuntimeRulesAuthorized: false
    },
    evidence: {
        parityStatus: 'frozen-fragment-parity-complete',
        ownerCaseCount: 16,
        runtimeRuleCaseCount: 3,
        higherCellPackageCount: 2,
        unclosedParityRows: 0,
        migrationRevision: 'MIGRATE-2',
        deletedLegacyTargetCount: 36,
        compatibilityApiRetained: false,
        validationGates: expectedValidationGates
    },
    performanceBoundary: {
        mechanism: 'explicitly-bounded-runtime-comparison',
        checkerComparisonStepLimit: 256,
        deploymentEvidence:
            'standalone-browser-typecheck-and-production-build-green',
        performanceClaim: 'no-latency-throughput-or-scale-sla',
        followUp:
            'measure-representative-workloads-before-performance-claim'
    },
    maintenanceBoundary: {
        legacyTargetsRemoved: 36,
        compatibilityLayerRetained: false,
        dualMaintenanceScope:
            'selected-owner-rule-and-metatheory-boundary-changes',
        rationale:
            'retained-because-typescript-subject-reduction-is-withheld'
    },
    releaseFollowUps: expectedReleaseFollowUps,
    nonEffects: expectedNonEffects,
    decisionQuestion: expectedDecisionQuestion,
    authorityAuthorized: false
};

const validateGraduationEvidence = (): void => {
    validateCoreMvpManifest(CORE_MVP_MANIFEST);
    validateCoreRuntimeH04Review(CORE_RUNTIME_H04_REVIEW);
    validateCoreMvpDifferentialCompletion(
        CORE_MVP_DIFFERENTIAL_COMPLETION
    );
    validateLegacyMigrationCompletion(LEGACY_MIGRATION_COMPLETION);

    const actualManifestIdentity = {
        revision: CORE_MVP_MANIFEST.revision,
        contentHash: CORE_MVP_MANIFEST.contentHash,
        ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
        runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
    };
    const evidenceMatches =
        sameData(actualManifestIdentity, expectedManifestIdentity) &&
        CORE_RUNTIME_H04_REVIEW.status === 'reviewed-approved' &&
        CORE_RUNTIME_H04_REVIEW.approval.decisionId === 'D-030' &&
        sameData(
            CORE_RUNTIME_H04_REVIEW.authorization,
            expectedH04Authorization
        ) &&
        CORE_RUNTIME_H04_REVIEW.subjectReductionOracle === 'lambdapi' &&
        CORE_RUNTIME_H04_REVIEW.additionalRuntimeRulesAuthorized === false &&
        CORE_MVP_DIFFERENTIAL_COMPLETION.status ===
            expectedRecommendation.evidence.parityStatus &&
        CORE_MVP_DIFFERENTIAL_COMPLETION.ownerCases.length === 16 &&
        CORE_MVP_DIFFERENTIAL_COMPLETION.ruleCases.length === 3 &&
        CORE_MVP_DIFFERENTIAL_COMPLETION.higherCellCases.length === 2 &&
        CORE_MVP_DIFFERENTIAL_COMPLETION.unclosedRows.length === 0 &&
        LEGACY_MIGRATION_COMPLETION.revision === 'MIGRATE-2' &&
        LEGACY_MIGRATION_COMPLETION.status === 'complete' &&
        LEGACY_MIGRATION_COMPLETION.deletedFiles.length === 36 &&
        LEGACY_MIGRATION_COMPLETION.compatibilityApiRetained === false &&
        LEGACY_MIGRATION_COMPLETION.browserEntryPoint ===
            'src/v3_2/browser.ts' &&
        CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT === 256;

    if (!evidenceMatches) {
        throw new CoreMvpGraduationError(
            'GRADUATION_EVIDENCE_MISMATCH',
            'GRADUATE-1A evidence differs from the reviewed manifest, ' +
            'H-04 boundary, TSK-3 completion, or MIGRATE-2 result'
        );
    }
};

/**
 * Reject any change to the exact H-05 review input. Approval must be
 * recorded separately and must not mutate this historical proposal.
 */
export function validateCoreMvpGraduationRecommendation(
    recommendation: CoreMvpGraduationRecommendationInput
): void {
    validateGraduationEvidence();
    if (!sameData(recommendation, expectedRecommendation)) {
        throw new CoreMvpGraduationError(
            'GRADUATION_RECOMMENDATION_MISMATCH',
            'MVP graduation recommendation differs from the GRADUATE-1A ' +
            'H-05 review input'
        );
    }
}

export const CORE_MVP_GRADUATION_RECOMMENDATION = deepFreeze(
    expectedRecommendation
);

validateCoreMvpGraduationRecommendation(
    CORE_MVP_GRADUATION_RECOMMENDATION
);

const expectedReviewApproval: CoreMvpGraduationReviewApprovalInput = {
    gate: 'H-05',
    decision: 'approved-as-proposed',
    decisionId: 'D-039',
    reviewedOn: '2026-07-24'
};

const expectedReviewAuthorization:
    CoreMvpGraduationReviewInput['authorization'] = {
        typescriptDeployedRuntimeAuthority:
            'authorized-exact-frozen-profile',
        lambdapiProductionRuntimeDependency: 'forbidden',
        lambdapiMathematicalSpecification: 'retained',
        frozenCorpusCiOracle: 'required',
        subjectReductionOracle: 'required',
        selectedChangeAcceptanceAuthority: 'retained',
        perTermProductionCheck: 'not-required'
    };

const expectedReview: CoreMvpGraduationReviewInput = {
    revision: 'GRADUATE-1B',
    status: 'reviewed-approved',
    recommendation: cloneData(
        CORE_MVP_GRADUATION_RECOMMENDATION
    ),
    approval: expectedReviewApproval,
    authorization: expectedReviewAuthorization,
    manifestRevision:
        CORE_MVP_GRADUATION_RECOMMENDATION
            .productAuthority.manifestRevision,
    manifestContentHash:
        CORE_MVP_GRADUATION_RECOMMENDATION
            .productAuthority.manifestContentHash,
    ownerIds: [
        ...CORE_MVP_GRADUATION_RECOMMENDATION
            .productAuthority.ownerIds
    ],
    runtimeRuleIds: [
        ...CORE_MVP_GRADUATION_RECOMMENDATION
            .productAuthority.runtimeRuleIds
    ],
    acceptanceTriggers: [
        ...CORE_MVP_GRADUATION_RECOMMENDATION
            .lambdapiPolicy.acceptanceTriggers
    ],
    changesNotRequiringNewAuthorityReview: [
        ...CORE_MVP_GRADUATION_RECOMMENDATION
            .lambdapiPolicy.changesNotRequiringNewAuthorityReview
    ],
    generalConfluence: 'withheld',
    typescriptSubjectReduction: 'withheld',
    additionalOwnersOrRulesAuthorized: false,
    performanceSlaAuthorized: false,
    releaseReady: false,
    nextSlice: 'RELEASE-READY'
};

/**
 * Validate the exact H-05 approval without mutating the pre-review proposal
 * or widening any H-03/H-04 boundary.
 */
export function validateCoreMvpGraduationReview(
    review: CoreMvpGraduationReviewInput
): void {
    if (
        review.revision !== 'GRADUATE-1B' ||
        review.status !== 'reviewed-approved' ||
        !sameData(review.approval, expectedReviewApproval)
    ) {
        throw new CoreMvpGraduationError(
            'GRADUATION_REVIEW_APPROVAL_MISMATCH',
            'MVP graduation review does not record the exact H-05 ' +
            'approval of D-039'
        );
    }
    if (!sameData(
        review.recommendation,
        CORE_MVP_GRADUATION_RECOMMENDATION
    )) {
        throw new CoreMvpGraduationError(
            'GRADUATION_REVIEW_RECOMMENDATION_MISMATCH',
            'MVP graduation review differs from the approved D-039 ' +
            'recommendation'
        );
    }
    validateCoreMvpGraduationRecommendation(review.recommendation);

    if (!sameData(review, expectedReview)) {
        throw new CoreMvpGraduationError(
            'GRADUATION_REVIEW_BOUNDARY_MISMATCH',
            'MVP graduation review exceeds or weakens the exact D-039 ' +
            'authorization boundary'
        );
    }
}

/**
 * The distinct H-05-reviewed product-authority boundary.
 *
 * TypeScript now owns deployed checking only for the exact frozen profile.
 * Lambdapi retains the approved mathematical, oracle, and selected-change
 * acceptance roles without becoming a production runtime dependency.
 * RELEASE-READY remains a separate tranche.
 */
export const CORE_MVP_GRADUATION_REVIEW = deepFreeze(expectedReview);

validateCoreMvpGraduationReview(CORE_MVP_GRADUATION_REVIEW);
