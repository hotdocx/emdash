/**
 * Frozen RELEASE-1B product/conformance policy.
 *
 * GRADUATE-1B authorizes the TypeScript checker/evaluator for one exact
 * manifest. This artifact makes the retained Lambdapi roles operational at
 * the repository gate while keeping them out of the browser runtime.
 */

import {
    CORE_MVP_DIFFERENTIAL_COMPLETION,
    validateCoreMvpDifferentialCompletion
} from './differential_higher_cell';
import {
    CORE_MVP_GRADUATION_REVIEW,
    validateCoreMvpGraduationReview
} from './graduation';
import {
    CORE_MVP_MANIFEST,
    validateCoreMvpManifest
} from './manifest';

export interface CoreMvpReleasePolicyInput {
    readonly revision: 'RELEASE-1B';
    readonly status: 'policy-synchronized';
    readonly graduationRevision: 'GRADUATE-1B';
    readonly decisionId: 'D-039';
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
    readonly conformance: {
        readonly command: './scripts/pnpmw run check:conformance';
        readonly scriptBody: string;
        readonly repositoryGate: './scripts/pnpmw run check:all';
        readonly repositoryGateBody: string;
        readonly timeoutSeconds: 60;
        readonly environment: 'EMDASH_RUN_LAMBDAPI_PROBES=1';
        readonly testFiles: readonly string[];
        readonly oracleProcessCount: 3;
        readonly mandatoryInRepositoryGate: true;
        readonly sharedCorpus: {
            readonly ownerCaseCount: 16;
            readonly runtimeRuleCaseCount: 3;
            readonly higherCellPackageCount: 2;
            readonly unclosedRowCount: 0;
        };
    };
    readonly lambdapiPolicy: {
        readonly mathematicalSpecification: 'active';
        readonly frozenCorpusCiOracle: 'required';
        readonly subjectReductionOracle: 'required';
        readonly selectedChangeAcceptanceAuthority: 'retained';
        readonly perTermProductionCheck: 'not-required';
        readonly acceptanceTriggers: readonly string[];
        readonly changesNotRequiringNewAuthorityReview: readonly string[];
    };
    readonly synchronizedArtifacts: {
        readonly publicDocumentation: readonly string[];
        readonly browserExample: 'emdash-template/src/App.tsx';
        readonly packageManifest: 'package.json';
        readonly browserManifestExport: 'CORE_MVP_MANIFEST';
    };
    readonly diagnostics: {
        readonly sourceMappedBackendDiagnostics: 'complete';
        readonly rawBackendDiagnosticsPreserved: true;
    };
    readonly surfaceBoundary: {
        readonly typedAstConstruction: 'supported';
        readonly stringParser: 'not-implemented';
        readonly h02Triggered: false;
        readonly h06Triggered: false;
    };
    readonly generalConfluence: 'withheld';
    readonly typescriptSubjectReduction: 'withheld';
    readonly additionalOwnersOrRulesAuthorized: false;
    readonly performanceSlaAuthorized: false;
    readonly releaseReady: false;
    readonly nextSlice: 'RELEASE-1C';
}

export type CoreMvpReleasePolicyErrorCode =
    | 'RELEASE_POLICY_EVIDENCE_MISMATCH'
    | 'RELEASE_POLICY_BOUNDARY_MISMATCH';

export class CoreMvpReleasePolicyError extends Error {
    constructor(
        public readonly code: CoreMvpReleasePolicyErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreMvpReleasePolicyError';
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

const conformanceTestFiles = [
    'tests/v3_2_differential_owner_tests.ts',
    'tests/v3_2_differential_rule_tests.ts',
    'tests/v3_2_differential_higher_cell_tests.ts'
] as const;

const conformanceScriptBody =
    'timeout 60s env EMDASH_RUN_LAMBDAPI_PROBES=1 ' +
    'node --require ts-node/register --test ' +
    conformanceTestFiles.join(' ');

const repositoryGateBody =
    './scripts/pnpmw run check:ts && ' +
    './scripts/pnpmw run check:conformance && make -C emdash2 ci';

const expectedPolicy: CoreMvpReleasePolicyInput = {
    revision: 'RELEASE-1B',
    status: 'policy-synchronized',
    graduationRevision: 'GRADUATE-1B',
    decisionId: 'D-039',
    productProfile: {
        manifestRevision: 'emdash-v3.2-mvp-1',
        manifestContentHash: CORE_MVP_MANIFEST.contentHash,
        ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
        runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id),
        deployedAuthority:
            'typescript-checker-evaluator-exact-profile',
        browserEntryPoint: 'src/v3_2/browser.ts',
        productionLambdapiDependency: false
    },
    conformance: {
        command: './scripts/pnpmw run check:conformance',
        scriptBody: conformanceScriptBody,
        repositoryGate: './scripts/pnpmw run check:all',
        repositoryGateBody,
        timeoutSeconds: 60,
        environment: 'EMDASH_RUN_LAMBDAPI_PROBES=1',
        testFiles: conformanceTestFiles,
        oracleProcessCount: 3,
        mandatoryInRepositoryGate: true,
        sharedCorpus: {
            ownerCaseCount: 16,
            runtimeRuleCaseCount: 3,
            higherCellPackageCount: 2,
            unclosedRowCount: 0
        }
    },
    lambdapiPolicy: {
        mathematicalSpecification: 'active',
        frozenCorpusCiOracle: 'required',
        subjectReductionOracle: 'required',
        selectedChangeAcceptanceAuthority: 'retained',
        perTermProductionCheck: 'not-required',
        acceptanceTriggers: [
            ...CORE_MVP_GRADUATION_REVIEW.acceptanceTriggers
        ],
        changesNotRequiringNewAuthorityReview: [
            ...CORE_MVP_GRADUATION_REVIEW
                .changesNotRequiringNewAuthorityReview
        ]
    },
    synchronizedArtifacts: {
        publicDocumentation: [
            'README.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md',
            'emdash-template/README.md'
        ],
        browserExample: 'emdash-template/src/App.tsx',
        packageManifest: 'package.json',
        browserManifestExport: 'CORE_MVP_MANIFEST'
    },
    diagnostics: {
        sourceMappedBackendDiagnostics: 'complete',
        rawBackendDiagnosticsPreserved: true
    },
    surfaceBoundary: {
        typedAstConstruction: 'supported',
        stringParser: 'not-implemented',
        h02Triggered: false,
        h06Triggered: false
    },
    generalConfluence: 'withheld',
    typescriptSubjectReduction: 'withheld',
    additionalOwnersOrRulesAuthorized: false,
    performanceSlaAuthorized: false,
    releaseReady: false,
    nextSlice: 'RELEASE-1C'
};

const validateReleaseEvidence = (): void => {
    validateCoreMvpManifest(CORE_MVP_MANIFEST);
    validateCoreMvpDifferentialCompletion(
        CORE_MVP_DIFFERENTIAL_COMPLETION
    );
    validateCoreMvpGraduationReview(CORE_MVP_GRADUATION_REVIEW);

    const review = CORE_MVP_GRADUATION_REVIEW;
    const completion = CORE_MVP_DIFFERENTIAL_COMPLETION;
    const evidenceMatches =
        review.revision === expectedPolicy.graduationRevision &&
        review.approval.decisionId === expectedPolicy.decisionId &&
        review.authorization.typescriptDeployedRuntimeAuthority ===
            'authorized-exact-frozen-profile' &&
        review.authorization.lambdapiProductionRuntimeDependency ===
            'forbidden' &&
        review.authorization.frozenCorpusCiOracle === 'required' &&
        review.authorization.subjectReductionOracle === 'required' &&
        review.authorization.selectedChangeAcceptanceAuthority ===
            'retained' &&
        sameData(
            review.ownerIds,
            expectedPolicy.productProfile.ownerIds
        ) &&
        sameData(
            review.runtimeRuleIds,
            expectedPolicy.productProfile.runtimeRuleIds
        ) &&
        completion.ownerCases.length ===
            expectedPolicy.conformance.sharedCorpus.ownerCaseCount &&
        completion.ruleCases.length ===
            expectedPolicy.conformance.sharedCorpus.runtimeRuleCaseCount &&
        completion.higherCellCases.length ===
            expectedPolicy.conformance.sharedCorpus
                .higherCellPackageCount &&
        completion.unclosedRows.length === 0;

    if (!evidenceMatches) {
        throw new CoreMvpReleasePolicyError(
            'RELEASE_POLICY_EVIDENCE_MISMATCH',
            'RELEASE-1B evidence differs from the H-05-approved profile, ' +
            'retained Lambdapi roles, or frozen shared corpus'
        );
    }
};

/**
 * Reject drift from the exact RELEASE-1B policy boundary.
 *
 * File contents and package scripts are checked separately by the release
 * policy test so this browser-neutral source module remains Node-free.
 */
export function validateCoreMvpReleasePolicy(
    policy: CoreMvpReleasePolicyInput
): void {
    validateReleaseEvidence();
    if (!sameData(policy, expectedPolicy)) {
        throw new CoreMvpReleasePolicyError(
            'RELEASE_POLICY_BOUNDARY_MISMATCH',
            'MVP release policy differs from the synchronized RELEASE-1B ' +
            'product, conformance, documentation, or non-claim boundary'
        );
    }
}

export const CORE_MVP_RELEASE_POLICY = deepFreeze(expectedPolicy);

validateCoreMvpReleasePolicy(CORE_MVP_RELEASE_POLICY);
