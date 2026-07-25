/**
 * Exact reviewed decision for the systematic-transfer architecture.
 *
 * This records revised H-DTTLF-SCALE-01 without granting a semantic owner,
 * runtime rule, proof-time rule, product profile, or canonical term parser.
 */

export interface CoreLfScaleArchitectureReviewInput {
    readonly revision: 'SCALE-ARCHITECTURE-1-REVIEWED';
    readonly gate: 'H-DTTLF-SCALE-01';
    readonly decision: 'D-DTTLF-SCALE-001R';
    readonly status: 'approved';
    readonly approvedOn: '2026-07-24';
    readonly mandatoryArchitecture: {
        readonly transferIr:
            'immutable-backend-neutral-module-or-fragment-spec';
        readonly initialProducer: 'typed-typescript-scoped-builder';
        readonly engines: readonly [
            'generic-declaration-compiler',
            'generic-runtime-rule-compiler-and-matcher',
            'separate-generic-proof-time-unification-engine'
        ];
        readonly bodyKinds: readonly [
            'absent',
            'explicit-term',
            'checked-tactic-source'
        ];
        readonly authorityPolicyOverlay: 'separate-and-immutable';
    };
    readonly canonicalExportRoles: readonly [
        'inventory',
        'drift-detection',
        'exact-extraction',
        'conformance',
        'optional-later-bulk-parser-or-generator'
    ];
    readonly oldMainEvidence: {
        readonly reusable: readonly [
            'raw-versus-elaborated-rewrite-rules',
            'capture-aware-pattern-substitution',
            'scope-restricted-higher-order-patterns',
            'occurs-check-and-constraint-revisiting',
            'symmetric-unification-rules-producing-constraints'
        ];
        readonly rejectedArchitecture: readonly [
            'mutable-global-rule-registries',
            'category-specific-term-cases',
            'stored-named-hoas-closures',
            'untyped-unification-rule-registration',
            'fail-soft-rule-errors'
        ];
    };
    readonly productionLambdapiDependency: false;
    readonly authorizes: readonly [
        'SCALE-0B-transfer-ir-and-builder',
        'representation-only-conformance-witnesses'
    ];
    readonly doesNotAuthorize: readonly [
        'canonical-term-parser',
        'new-semantic-declaration',
        'new-runtime-rule',
        'new-proof-time-rule',
        'product-profile-expansion',
        'browser-export',
        'lambdapi-source-change',
        'mechanical-transfer-qualification'
    ];
}

export type CoreLfScaleArchitectureReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_DRIFT';

export class CoreLfScaleArchitectureReviewError extends Error {
    constructor(
        public readonly code: CoreLfScaleArchitectureReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleArchitectureReviewError';
    }
}

const rawReview: CoreLfScaleArchitectureReviewInput = {
    revision: 'SCALE-ARCHITECTURE-1-REVIEWED',
    gate: 'H-DTTLF-SCALE-01',
    decision: 'D-DTTLF-SCALE-001R',
    status: 'approved',
    approvedOn: '2026-07-24',
    mandatoryArchitecture: {
        transferIr: 'immutable-backend-neutral-module-or-fragment-spec',
        initialProducer: 'typed-typescript-scoped-builder',
        engines: [
            'generic-declaration-compiler',
            'generic-runtime-rule-compiler-and-matcher',
            'separate-generic-proof-time-unification-engine'
        ],
        bodyKinds: [
            'absent',
            'explicit-term',
            'checked-tactic-source'
        ],
        authorityPolicyOverlay: 'separate-and-immutable'
    },
    canonicalExportRoles: [
        'inventory',
        'drift-detection',
        'exact-extraction',
        'conformance',
        'optional-later-bulk-parser-or-generator'
    ],
    oldMainEvidence: {
        reusable: [
            'raw-versus-elaborated-rewrite-rules',
            'capture-aware-pattern-substitution',
            'scope-restricted-higher-order-patterns',
            'occurs-check-and-constraint-revisiting',
            'symmetric-unification-rules-producing-constraints'
        ],
        rejectedArchitecture: [
            'mutable-global-rule-registries',
            'category-specific-term-cases',
            'stored-named-hoas-closures',
            'untyped-unification-rule-registration',
            'fail-soft-rule-errors'
        ]
    },
    productionLambdapiDependency: false,
    authorizes: [
        'SCALE-0B-transfer-ir-and-builder',
        'representation-only-conformance-witnesses'
    ],
    doesNotAuthorize: [
        'canonical-term-parser',
        'new-semantic-declaration',
        'new-runtime-rule',
        'new-proof-time-rule',
        'product-profile-expansion',
        'browser-export',
        'lambdapi-source-change',
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

export const CORE_LF_SCALE_ARCHITECTURE_REVIEW =
    deepFreeze(rawReview);

export function validateCoreLfScaleArchitectureReview(
    review: CoreLfScaleArchitectureReviewInput =
        CORE_LF_SCALE_ARCHITECTURE_REVIEW
): void {
    if (
        review.gate !== 'H-DTTLF-SCALE-01' ||
        review.decision !== 'D-DTTLF-SCALE-001R' ||
        review.status !== 'approved' ||
        review.productionLambdapiDependency !== false
    ) {
        throw new CoreLfScaleArchitectureReviewError(
            'INVALID_REVIEW_DECISION',
            'SCALE architecture review does not preserve approved ' +
                'H-DTTLF-SCALE-01/D-DTTLF-SCALE-001R'
        );
    }
    if (!sameData(review, rawReview)) {
        throw new CoreLfScaleArchitectureReviewError(
            'REVIEW_DRIFT',
            'SCALE architecture review differs from the exact approved ' +
                'D-DTTLF-SCALE-001R content'
        );
    }
}

validateCoreLfScaleArchitectureReview();
