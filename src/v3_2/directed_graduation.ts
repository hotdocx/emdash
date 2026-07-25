/**
 * Authoritative opt-in continuation facade for the exact H-DTTLF-03 profile.
 *
 * This module does not alter the deployed MVP or browser entry point. It
 * exposes the reviewed directed catalog through one named root-only factory
 * and freezes the separate continuation conformance lane.
 */

import {
    CoreDirected1cCatalog
} from './directed_1c';
import {
    CORE_DIRECTED_GRADUATION_MANIFEST
} from './directed_graduation_proposal';
import {
    CORE_DIRECTED_GRADUATION_REVIEW,
    validateCoreDirectedGraduationReview
} from './directed_graduation_review';
import {
    Provenance,
    provenance
} from './kernel';

export interface CoreDirectedContinuationProfileInput {
    readonly revision: 'emdash-v3.2-dttlf-directed-1';
    readonly status: 'authoritative-opt-in';
    readonly reviewRevision: 'DIRECTED-GRADUATE-1-REVIEWED';
    readonly decisionId: 'D-DTTLF-001';
    readonly manifestContentHash:
        'sha256:5fbf855e044e3d24e1078289eebad4a3391d67747efcee3c5463c2bfb110a8c7';
    readonly entryPoint: 'src/v3_2/index.ts';
    readonly factoryExport: 'createCoreDirectedContinuationKernel';
    readonly signatureClosure: {
        readonly baseCount: 20;
        readonly candidateCount: 9;
        readonly totalCount: 29;
        readonly ownerIds: readonly string[];
    };
    readonly runtimeClosure: {
        readonly directedCount: 7;
        readonly inheritedMvpCount: 3;
        readonly totalCount: 10;
        readonly ruleIds: readonly string[];
        readonly proofTimeRuleCount: 0;
    };
    readonly outerLf: {
        readonly transitionOrder:
            readonly ['zonk', 'beta', 'delta', 'reviewed-runtime'];
        readonly comparisonStepLimit: 256;
        readonly oneSharedBudget: true;
        readonly eta: 'disabled';
        readonly arbitraryUserRules: 'excluded';
    };
    readonly conformance: {
        readonly command:
            './scripts/pnpmw run check:directed-conformance';
        readonly scriptBody: string;
        readonly continuationGate:
            './scripts/pnpmw run check:continuation';
        readonly continuationGateBody: string;
        readonly timeoutSeconds: 60;
        readonly environment: 'EMDASH_RUN_LAMBDAPI_PROBES=1';
        readonly testFile:
            'tests/v3_2_directed_1c_tests.ts';
        readonly mandatoryForProfileChanges: true;
        readonly mandatoryInFrozenMvpCheckAll: false;
        readonly fixedCorpus: {
            readonly typescriptPositiveConsumerCount: 1;
            readonly typescriptNegativeFamilyOrPairCount: 2;
            readonly generatedLambdapiPositiveCount: 1;
            readonly generatedLambdapiNegativeCount: 1;
            readonly subjectReductionConversionWitnesses:
                readonly [
                    'outer-beta-section-evaluation',
                    'sigma-telescope-fibre'
                ];
        };
    };
    readonly productBoundary: {
        readonly authority:
            'typescript-checker-evaluator-exact-opt-in-profile';
        readonly browserEntryPoint: 'excluded';
        readonly deployedMvpProfile: 'unchanged';
        readonly releaseReady: false;
        readonly lambdapiProductionRuntimeDependency: false;
    };
    readonly lambdapiPolicy: {
        readonly mathematicalSpecification: 'active';
        readonly fixedGraduationCorpus: 'required';
        readonly positiveAndNegativeOracle: 'required';
        readonly subjectReductionOracle: 'required';
        readonly selectedChangeAcceptanceAuthority: 'retained';
        readonly perTermRuntimeCheck: 'not-required';
        readonly acceptanceTriggers: readonly string[];
    };
    readonly claimBoundary: {
        readonly deterministicBoundedChecking:
            'authorized-exact-profile';
        readonly boundedStopping: 'authorized';
        readonly inheritedMvpThreeRuleTermination:
            'preserved-for-subprogram-only';
        readonly combinedTermination: 'withheld';
        readonly unrestrictedNormalization: 'withheld';
        readonly confluence: 'withheld';
        readonly typescriptSubjectReduction: 'withheld';
        readonly performanceSla: 'withheld';
        readonly additionalOwnerOrRuleAuthority: false;
    };
}

export type CoreDirectedContinuationProfileErrorCode =
    | 'CONTINUATION_PROFILE_REVIEW_DRIFT'
    | 'CONTINUATION_PROFILE_IMPLEMENTATION_DRIFT'
    | 'CONTINUATION_PROFILE_BOUNDARY_DRIFT';

export class CoreDirectedContinuationProfileError extends Error {
    constructor(
        public readonly code: CoreDirectedContinuationProfileErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedContinuationProfileError';
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

const directedConformanceScriptBody =
    'timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 ' +
    'node --require ts-node/register --test ' +
    'tests/v3_2_directed_1c_tests.ts';

const continuationGateBody =
    './scripts/pnpmw run check:all && ' +
    './scripts/pnpmw run check:directed-conformance';

const manifest = CORE_DIRECTED_GRADUATION_MANIFEST;
const review = CORE_DIRECTED_GRADUATION_REVIEW;

const expectedProfile: CoreDirectedContinuationProfileInput = {
    revision: manifest.revision,
    status: 'authoritative-opt-in',
    reviewRevision: review.revision,
    decisionId: review.approval.decisionId,
    manifestContentHash: review.authorization.manifestContentHash,
    entryPoint: review.authorization.entryPoint,
    factoryExport: review.authorization.factoryExport,
    signatureClosure: {
        baseCount: manifest.composition.baseOwnerSignatureCount,
        candidateCount:
            manifest.composition.candidateDeclarationCount,
        totalCount: manifest.composition.totalOwnerSignatureCount,
        ownerIds: [
            ...review.authorization.baseOwnerSignatureIds,
            ...review.authorization.candidateDeclarationIds
        ]
    },
    runtimeClosure: {
        directedCount: manifest.composition.directedRuntimeRuleCount,
        inheritedMvpCount:
            manifest.composition.inheritedMvpRuntimeRuleCount,
        totalCount: manifest.composition.totalRuntimeRuleCount,
        ruleIds: [...review.authorization.runtimeRuleIds],
        proofTimeRuleCount: manifest.composition.proofTimeRuleCount
    },
    outerLf: {
        transitionOrder: [...manifest.outerLf.transitionOrder],
        comparisonStepLimit: manifest.outerLf.comparisonStepLimit,
        oneSharedBudget: manifest.composition.oneSharedOuterLfBudget,
        eta: manifest.outerLf.eta,
        arbitraryUserRules: manifest.outerLf.arbitraryUserRules
    },
    conformance: {
        command:
            './scripts/pnpmw run check:directed-conformance',
        scriptBody: directedConformanceScriptBody,
        continuationGate:
            './scripts/pnpmw run check:continuation',
        continuationGateBody,
        timeoutSeconds: 60,
        environment: 'EMDASH_RUN_LAMBDAPI_PROBES=1',
        testFile: 'tests/v3_2_directed_1c_tests.ts',
        mandatoryForProfileChanges: true,
        mandatoryInFrozenMvpCheckAll: false,
        fixedCorpus: {
            typescriptPositiveConsumerCount:
                review.recommendation.evidence
                    .typescriptPositiveConsumerCount,
            typescriptNegativeFamilyOrPairCount:
                review.recommendation.evidence
                    .typescriptNegativeFamilyOrPairCount,
            generatedLambdapiPositiveCount:
                review.recommendation.evidence
                    .generatedLambdapiPositiveCount,
            generatedLambdapiNegativeCount:
                review.recommendation.evidence
                    .generatedLambdapiNegativeCount,
            subjectReductionConversionWitnesses: [
                'outer-beta-section-evaluation',
                'sigma-telescope-fibre'
            ]
        }
    },
    productBoundary: {
        authority:
            'typescript-checker-evaluator-exact-opt-in-profile',
        browserEntryPoint: 'excluded',
        deployedMvpProfile: 'unchanged',
        releaseReady: false,
        lambdapiProductionRuntimeDependency: false
    },
    lambdapiPolicy: {
        mathematicalSpecification:
            review.lambdapiPolicy.mathematicalSpecification,
        fixedGraduationCorpus:
            review.lambdapiPolicy.fixedGraduationCorpus,
        positiveAndNegativeOracle:
            review.lambdapiPolicy.positiveAndNegativeOracle,
        subjectReductionOracle:
            review.lambdapiPolicy.subjectReductionOracle,
        selectedChangeAcceptanceAuthority:
            review.lambdapiPolicy.selectedChangeAcceptanceAuthority,
        perTermRuntimeCheck:
            review.lambdapiPolicy.perTermRuntimeCheck,
        acceptanceTriggers: [
            ...review.lambdapiPolicy.acceptanceTriggers
        ]
    },
    claimBoundary: {
        deterministicBoundedChecking: 'authorized-exact-profile',
        boundedStopping: 'authorized',
        inheritedMvpThreeRuleTermination:
            review.claimBoundary.inheritedMvpThreeRuleTermination,
        combinedTermination:
            review.claimBoundary.combinedTermination,
        unrestrictedNormalization:
            review.claimBoundary.unrestrictedNormalization,
        confluence: review.claimBoundary.confluence,
        typescriptSubjectReduction:
            review.claimBoundary.typescriptSubjectReduction,
        performanceSla: review.claimBoundary.performanceSla,
        additionalOwnerOrRuleAuthority:
            review.claimBoundary.additionalOwnerOrRuleAuthority
    }
};

const validateLiveCatalog = (): void => {
    const catalog = CoreDirected1cCatalog.create();
    catalog.createChecker().validateEnvironment();
    const declarationIds =
        manifest.candidateDeclarations.map(entry => entry.coreName);
    const liveDeclarationIds =
        catalog.environment.declarations.map(entry => entry.name);
    const directedRuleIds = manifest.runtimeRules
        .filter(entry => entry.executionPhase === 'catalog-runtime')
        .map(entry => entry.id);

    if (
        !sameData(liveDeclarationIds, declarationIds) ||
        !sameData(catalog.runtimeProgram.ruleIds, directedRuleIds)
    ) {
        throw new CoreDirectedContinuationProfileError(
            'CONTINUATION_PROFILE_IMPLEMENTATION_DRIFT',
            'The live directed catalog differs from the reviewed profile'
        );
    }
};

export function validateCoreDirectedContinuationProfile(
    profile: CoreDirectedContinuationProfileInput =
        CORE_DIRECTED_CONTINUATION_PROFILE
): void {
    try {
        validateCoreDirectedGraduationReview(
            CORE_DIRECTED_GRADUATION_REVIEW
        );
    } catch (error: unknown) {
        throw new CoreDirectedContinuationProfileError(
            'CONTINUATION_PROFILE_REVIEW_DRIFT',
            'The approved directed graduation review drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    validateLiveCatalog();
    if (!sameData(profile, expectedProfile)) {
        throw new CoreDirectedContinuationProfileError(
            'CONTINUATION_PROFILE_BOUNDARY_DRIFT',
            'The authoritative opt-in continuation profile drifted'
        );
    }
}

export const CORE_DIRECTED_CONTINUATION_PROFILE =
    deepFreeze(expectedProfile);

/**
 * Create the exact reviewed root-only continuation checker/evaluator catalog.
 *
 * Callers extend the returned persistent environment with their own
 * declarations and obtain a checker through `catalog.createChecker(...)`.
 */
export function createCoreDirectedContinuationKernel(
    source: Provenance = provenance(
        'derived',
        'authoritative emdash-v3.2-dttlf-directed-1 continuation kernel'
    )
): CoreDirected1cCatalog {
    validateCoreDirectedContinuationProfile();
    return CoreDirected1cCatalog.create(source);
}

validateCoreDirectedContinuationProfile();
