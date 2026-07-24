/**
 * Frozen RELEASE-1C completion record for the exact v3.2 MVP profile.
 *
 * This record closes release work without mutating the historical manifest,
 * graduation review, or RELEASE-1B policy. It distinguishes current release
 * blockers from conditional future gates and out-of-profile capabilities.
 */

import {
    CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT
} from './checker';
import {
    CORE_MVP_GRADUATION_REVIEW,
    validateCoreMvpGraduationReview
} from './graduation';
import {
    LEGACY_MIGRATION_COMPLETION,
    validateLegacyMigrationCompletion
} from './migration';
import {
    CORE_RUNTIME_H04_REVIEW,
    validateCoreRuntimeH04Review
} from './metatheory';
import {
    CORE_MVP_RELEASE_POLICY,
    validateCoreMvpReleasePolicy
} from './release';

export interface CoreMvpReleaseCompletionInput {
    readonly revision: 'RELEASE-1C';
    readonly status: 'release-ready-exact-profile';
    readonly completedOn: '2026-07-24';
    readonly releasePolicyRevision: 'RELEASE-1B';
    readonly graduationRevision: 'GRADUATE-1B';
    readonly productProfile: {
        readonly manifestRevision: 'emdash-v3.2-mvp-1';
        readonly manifestContentHash: string;
        readonly ownerIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
        readonly deployedAuthority:
            'typescript-checker-evaluator-exact-profile';
        readonly browserEntryPoint: 'src/v3_2/browser.ts';
        readonly productionLambdapiDependency: false;
    };
    readonly completedReleaseSlices:
        readonly ['RELEASE-1A', 'RELEASE-1B', 'RELEASE-1C'];
    readonly releaseCriteria: {
        readonly coverageCapabilityCount: 21;
        readonly allCoverageCapabilitiesComplete: true;
        readonly sourceMappedDiagnostics: 'complete';
        readonly mandatoryConformance: 'complete';
        readonly publicPolicySynchronization: 'complete';
        readonly legacyMigration: 'complete';
        readonly browserPackaging: 'complete';
        readonly fullRepositoryGate: 'complete';
    };
    readonly performanceBoundary: {
        readonly checkerComparisonStepLimit: 256;
        readonly boundMeaning: 'global-runtime-rewrite-step-budget';
        readonly terminationScope:
            'exact-three-rule-finite-core-fragment';
        readonly wallClockGuarantee: 'none';
        readonly latencyThroughputOrScaleSla: 'none';
        readonly benchmarkRequiredForCurrentRelease: false;
        readonly futurePerformanceClaimRequires:
            'representative-workload-measurement-and-separate-review';
        readonly observedValidationTimingIsSla: false;
    };
    readonly residualBoundary: {
        readonly releaseBlockers: readonly string[];
        readonly conditionalFutureGates: readonly {
            readonly id: 'H-02' | 'H-06';
            readonly state: 'not-triggered';
            readonly releaseDisposition: string;
        }[];
        readonly outsideFrozenProfile: readonly string[];
    };
    readonly lambdapiPolicy: {
        readonly mathematicalSpecification: 'active';
        readonly frozenCorpusCiOracle: 'required';
        readonly subjectReductionOracle: 'required';
        readonly selectedChangeAcceptanceAuthority: 'retained';
        readonly perTermProductionCheck: 'not-required';
        readonly acceptanceTriggers: readonly string[];
    };
    readonly claimBoundary: {
        readonly termination: 'authorized-exact-fragment';
        readonly deterministicBoundedEvaluationAndComparison: 'authorized';
        readonly trustedRuntimeRules:
            'authorized-exact-h03-runtime-set-only';
        readonly generalConfluence: 'withheld';
        readonly typescriptSubjectReduction: 'withheld';
        readonly additionalOwnersOrRulesAuthorized: false;
        readonly performanceSlaAuthorized: false;
    };
    readonly validation: {
        readonly validatedOn: '2026-07-24';
        readonly allPassed: true;
        readonly focusedCommand: string;
        readonly conformanceCommand:
            './scripts/pnpmw run check:conformance';
        readonly browserTypecheckCommand: string;
        readonly browserBuildCommand: string;
        readonly typescriptGateCommand: './scripts/pnpmw run check:ts';
        readonly boundedKernelCommand:
            'EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check';
        readonly repositoryGateCommand:
            'EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all';
        readonly diffCheckCommand: 'git diff --check';
    };
    readonly releaseReady: true;
    readonly nextSlice: null;
}

export type CoreMvpReleaseCompletionErrorCode =
    | 'RELEASE_COMPLETION_EVIDENCE_MISMATCH'
    | 'RELEASE_COMPLETION_BOUNDARY_MISMATCH';

export class CoreMvpReleaseCompletionError extends Error {
    constructor(
        public readonly code: CoreMvpReleaseCompletionErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreMvpReleaseCompletionError';
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

const expectedCompletion: CoreMvpReleaseCompletionInput = {
    revision: 'RELEASE-1C',
    status: 'release-ready-exact-profile',
    completedOn: '2026-07-24',
    releasePolicyRevision: 'RELEASE-1B',
    graduationRevision: 'GRADUATE-1B',
    productProfile: {
        manifestRevision: 'emdash-v3.2-mvp-1',
        manifestContentHash:
            CORE_MVP_RELEASE_POLICY.productProfile.manifestContentHash,
        ownerIds: [
            ...CORE_MVP_RELEASE_POLICY.productProfile.ownerIds
        ],
        runtimeRuleIds: [
            ...CORE_MVP_RELEASE_POLICY.productProfile.runtimeRuleIds
        ],
        deployedAuthority:
            'typescript-checker-evaluator-exact-profile',
        browserEntryPoint: 'src/v3_2/browser.ts',
        productionLambdapiDependency: false
    },
    completedReleaseSlices: [
        'RELEASE-1A',
        'RELEASE-1B',
        'RELEASE-1C'
    ],
    releaseCriteria: {
        coverageCapabilityCount: 21,
        allCoverageCapabilitiesComplete: true,
        sourceMappedDiagnostics: 'complete',
        mandatoryConformance: 'complete',
        publicPolicySynchronization: 'complete',
        legacyMigration: 'complete',
        browserPackaging: 'complete',
        fullRepositoryGate: 'complete'
    },
    performanceBoundary: {
        checkerComparisonStepLimit: 256,
        boundMeaning: 'global-runtime-rewrite-step-budget',
        terminationScope:
            'exact-three-rule-finite-core-fragment',
        wallClockGuarantee: 'none',
        latencyThroughputOrScaleSla: 'none',
        benchmarkRequiredForCurrentRelease: false,
        futurePerformanceClaimRequires:
            'representative-workload-measurement-and-separate-review',
        observedValidationTimingIsSla: false
    },
    residualBoundary: {
        releaseBlockers: [],
        conditionalFutureGates: [{
            id: 'H-02',
            state: 'not-triggered',
            releaseDisposition:
                'not-required-without-a-displayed-owner-failure'
        }, {
            id: 'H-06',
            state: 'not-triggered',
            releaseDisposition:
                'not-required-without-measured-text-parser-need'
        }],
        outsideFrozenProfile: [
            'conformance-only-owner-or-rule-promotion',
            'proof-time-and-intentional-non-conversion-execution',
            'generic-beta-eta-and-declaration-unfolding',
            'general-higher-order-unification',
            'textual-parser',
            'general-confluence-theorem',
            'standalone-typescript-subject-reduction-theorem',
            'latency-throughput-or-scale-sla'
        ]
    },
    lambdapiPolicy: {
        mathematicalSpecification: 'active',
        frozenCorpusCiOracle: 'required',
        subjectReductionOracle: 'required',
        selectedChangeAcceptanceAuthority: 'retained',
        perTermProductionCheck: 'not-required',
        acceptanceTriggers: [
            ...CORE_MVP_RELEASE_POLICY
                .lambdapiPolicy.acceptanceTriggers
        ]
    },
    claimBoundary: {
        termination: 'authorized-exact-fragment',
        deterministicBoundedEvaluationAndComparison: 'authorized',
        trustedRuntimeRules:
            'authorized-exact-h03-runtime-set-only',
        generalConfluence: 'withheld',
        typescriptSubjectReduction: 'withheld',
        additionalOwnersOrRulesAuthorized: false,
        performanceSlaAuthorized: false
    },
    validation: {
        validatedOn: '2026-07-24',
        allPassed: true,
        focusedCommand:
            'node --require ts-node/register --test ' +
            'tests/v3_2_release_completion_tests.ts ' +
            'tests/v3_2_release_policy_tests.ts ' +
            'tests/v3_2_browser_api_tests.ts',
        conformanceCommand:
            './scripts/pnpmw run check:conformance',
        browserTypecheckCommand:
            './scripts/pnpmw --dir emdash-template --ignore-workspace ' +
            'exec tsc --noEmit -p tsconfig.json',
        browserBuildCommand:
            './scripts/pnpmw --dir emdash-template --ignore-workspace ' +
            'exec vite build',
        typescriptGateCommand: './scripts/pnpmw run check:ts',
        boundedKernelCommand:
            'EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check',
        repositoryGateCommand:
            'EMDASH_TYPECHECK_TIMEOUT=60s ./scripts/pnpmw run check:all',
        diffCheckCommand: 'git diff --check'
    },
    releaseReady: true,
    nextSlice: null
};

const validateCompletionEvidence = (): void => {
    validateCoreMvpReleasePolicy(CORE_MVP_RELEASE_POLICY);
    validateCoreMvpGraduationReview(CORE_MVP_GRADUATION_REVIEW);
    validateLegacyMigrationCompletion(LEGACY_MIGRATION_COMPLETION);
    validateCoreRuntimeH04Review(CORE_RUNTIME_H04_REVIEW);

    const evidenceMatches =
        CORE_MVP_RELEASE_POLICY.revision ===
            expectedCompletion.releasePolicyRevision &&
        CORE_MVP_RELEASE_POLICY.releaseReady === false &&
        CORE_MVP_RELEASE_POLICY.nextSlice === 'RELEASE-1C' &&
        CORE_MVP_GRADUATION_REVIEW.revision ===
            expectedCompletion.graduationRevision &&
        CORE_MVP_GRADUATION_REVIEW.releaseReady === false &&
        LEGACY_MIGRATION_COMPLETION.status === 'complete' &&
        LEGACY_MIGRATION_COMPLETION.compatibilityApiRetained === false &&
        CORE_RUNTIME_H04_REVIEW.status === 'reviewed-approved' &&
        sameData(
            CORE_RUNTIME_H04_REVIEW.authorization,
            {
                termination: 'authorized-exact-fragment',
                deterministicBoundedEvaluationAndComparison: 'authorized',
                trustedRuntimeRules:
                    'authorized-exact-h03-runtime-set-only',
                generalConfluence: 'withheld',
                typescriptSubjectReduction: 'withheld'
            }
        ) &&
        CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT ===
            expectedCompletion.performanceBoundary
                .checkerComparisonStepLimit;

    if (!evidenceMatches) {
        throw new CoreMvpReleaseCompletionError(
            'RELEASE_COMPLETION_EVIDENCE_MISMATCH',
            'RELEASE-1C evidence differs from the completed migration, ' +
            'approved claim boundary, RELEASE-1B policy, or runtime limit'
        );
    }
}

/**
 * Reject drift from the exact release-completion boundary.
 *
 * Plan statuses, public documents, package commands, and browser reachability
 * are verified by the focused completion test rather than imported here.
 */
export function validateCoreMvpReleaseCompletion(
    completion: CoreMvpReleaseCompletionInput
): void {
    validateCompletionEvidence();
    if (!sameData(completion, expectedCompletion)) {
        throw new CoreMvpReleaseCompletionError(
            'RELEASE_COMPLETION_BOUNDARY_MISMATCH',
            'MVP release completion differs from the exact RELEASE-1C ' +
            'profile, residual, performance, validation, or claim boundary'
        );
    }
}

export const CORE_MVP_RELEASE_COMPLETION = deepFreeze(
    expectedCompletion
);

validateCoreMvpReleaseCompletion(CORE_MVP_RELEASE_COMPLETION);
