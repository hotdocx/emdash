/**
 * Exact reviewed decision for the generic systematic-transfer engine
 * boundary.
 *
 * This records H-DTTLF-SCALE-02/D-DTTLF-SCALE-002 without granting any
 * active declaration, runtime rule, proof-time rule, product profile, or
 * mechanical-transfer qualification.
 */

export interface CoreLfScaleEngineReviewInput {
    readonly revision: 'SCALE-ENGINE-2-REVIEWED';
    readonly gate: 'H-DTTLF-SCALE-02';
    readonly decision: 'D-DTTLF-SCALE-002';
    readonly status: 'approved';
    readonly approvedOn: '2026-07-25';
    readonly stableEngineBoundary: readonly [
        'shared-immutable-transfer-ir',
        'generic-declaration-compiler',
        'generic-local-runtime-compiler-and-matcher',
        'explicit-transitive-runtime-fragment-composition',
        'separate-proof-time-compiler-and-constraint-engine'
    ];
    readonly defaultAcquisition: {
        readonly typedSpecifications:
            'direct-scoped-typescript-builder';
        readonly extraction:
            'small-fail-closed-checked-adapters';
        readonly canonicalTermPatternParser:
            'deferred-until-acquisition-is-measured-bottleneck';
    };
    readonly generatedArtifactPolicy: {
        readonly specifications: 'committed-reviewed-artifacts';
        readonly semanticPolicy: 'separate-committed-reviewed-artifact';
        readonly productionLambdapiDependency: false;
    };
    readonly failClosedBoundary: readonly [
        'wildcards',
        'binder-dependent-or-higher-order-captures',
        'inductives',
        'tactic-body-delta',
        'declaration-or-runtime-dependency-gaps',
        'new-rule-shapes'
    ];
    readonly authorizes: readonly [
        'representative-stress-work',
        'small-checked-extraction-adapters',
        'smallest-explicit-engine-rows'
    ];
    readonly doesNotAuthorize: readonly [
        'active-semantic-declaration',
        'active-runtime-rule',
        'active-proof-time-rule',
        'product-profile-expansion',
        'browser-export',
        'lambdapi-source-change',
        'mathematical-theorem',
        'mechanical-transfer-qualification'
    ];
}

export type CoreLfScaleEngineReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_DRIFT';

export class CoreLfScaleEngineReviewError extends Error {
    constructor(
        public readonly code: CoreLfScaleEngineReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleEngineReviewError';
    }
}

const rawReview: CoreLfScaleEngineReviewInput = {
    revision: 'SCALE-ENGINE-2-REVIEWED',
    gate: 'H-DTTLF-SCALE-02',
    decision: 'D-DTTLF-SCALE-002',
    status: 'approved',
    approvedOn: '2026-07-25',
    stableEngineBoundary: [
        'shared-immutable-transfer-ir',
        'generic-declaration-compiler',
        'generic-local-runtime-compiler-and-matcher',
        'explicit-transitive-runtime-fragment-composition',
        'separate-proof-time-compiler-and-constraint-engine'
    ],
    defaultAcquisition: {
        typedSpecifications: 'direct-scoped-typescript-builder',
        extraction: 'small-fail-closed-checked-adapters',
        canonicalTermPatternParser:
            'deferred-until-acquisition-is-measured-bottleneck'
    },
    generatedArtifactPolicy: {
        specifications: 'committed-reviewed-artifacts',
        semanticPolicy: 'separate-committed-reviewed-artifact',
        productionLambdapiDependency: false
    },
    failClosedBoundary: [
        'wildcards',
        'binder-dependent-or-higher-order-captures',
        'inductives',
        'tactic-body-delta',
        'declaration-or-runtime-dependency-gaps',
        'new-rule-shapes'
    ],
    authorizes: [
        'representative-stress-work',
        'small-checked-extraction-adapters',
        'smallest-explicit-engine-rows'
    ],
    doesNotAuthorize: [
        'active-semantic-declaration',
        'active-runtime-rule',
        'active-proof-time-rule',
        'product-profile-expansion',
        'browser-export',
        'lambdapi-source-change',
        'mathematical-theorem',
        'mechanical-transfer-qualification'
    ]
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const CORE_LF_SCALE_ENGINE_REVIEW = deepFreeze(rawReview);

export function validateCoreLfScaleEngineReview(
    review: CoreLfScaleEngineReviewInput =
        CORE_LF_SCALE_ENGINE_REVIEW
): void {
    if (
        review.gate !== 'H-DTTLF-SCALE-02' ||
        review.decision !== 'D-DTTLF-SCALE-002' ||
        review.status !== 'approved' ||
        review.generatedArtifactPolicy
            .productionLambdapiDependency !== false
    ) {
        throw new CoreLfScaleEngineReviewError(
            'INVALID_REVIEW_DECISION',
            'SCALE engine review does not preserve approved ' +
                'H-DTTLF-SCALE-02/D-DTTLF-SCALE-002'
        );
    }
    if (!sameData(review, rawReview)) {
        throw new CoreLfScaleEngineReviewError(
            'REVIEW_DRIFT',
            'SCALE engine review differs from the exact approved ' +
                'D-DTTLF-SCALE-002 content'
        );
    }
}

validateCoreLfScaleEngineReview();
