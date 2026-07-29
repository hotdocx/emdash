/**
 * SCALE-KIND-PI-1 executable outer-LF product-sort audit.
 *
 * Lambdapi implements a lambda-Pi logical framework, not a calculus with
 * native quantification over its `TYPE` sort. A Pi domain annotation must
 * itself have sort TYPE; the body may have sort TYPE or KIND and determines
 * the product sort. Object-language polymorphism therefore uses an explicit
 * universe of codes and a decoding family.
 */

export const CORE_LF_SCALE_KIND_PI_AUDIT_REVISION =
    'SCALE-KIND-PI-1-AUDIT-1' as const;

const CORE_LF_SCALE_KIND_PI_DECISION_QUESTION =
    'Approve H-DTTLF-LF-SORT-01/D-DTTLF-LF-SORT-001 as proposed.' as const;

export type CoreLfProductSort = 'TYPE' | 'KIND';

export interface CoreLfProductSortCell {
    readonly domainAnnotationSort: CoreLfProductSort;
    readonly bodySort: CoreLfProductSort;
    readonly accepted: boolean;
    readonly resultSort?: CoreLfProductSort;
    readonly rejection?: 'KIND-domain-annotation';
}

export interface CoreLfScaleKindPiAudit {
    readonly revision: typeof CORE_LF_SCALE_KIND_PI_AUDIT_REVISION;
    readonly row: 'SCALE-KIND-PI-1';
    readonly authority: 'Lambdapi-lambda-Pi';
    readonly productSortMatrix: readonly [
        CoreLfProductSortCell,
        CoreLfProductSortCell,
        CoreLfProductSortCell,
        CoreLfProductSortCell
    ];
    readonly nativeUniverseAxiom: {
        readonly judgment: 'TYPE : KIND';
        readonly typeInType: false;
        readonly kindIsCoreExpression: false;
    };
    readonly explicitCodeUniverse: {
        readonly schematicDeclarations: readonly [
            'Type : TYPE',
            'El : Type -> TYPE'
        ];
        readonly activeEmdashAnalogue: readonly [
            'Grpd : TYPE',
            'τ : Grpd -> TYPE'
        ];
        readonly compilerMayInventIt: false;
    };
    readonly verdict:
        'preserve-current-checker-and-use-explicit-code-universes';
    readonly measuredCorrection: {
        readonly checkerSemanticChange: false;
        readonly coreTermChange: false;
        readonly lambdapiSourceChange: false;
        readonly previousBoundaryLabel:
            'kind-level-binder-compilation';
        readonly correctedBoundaryLabel:
            'implicit-native-TYPE-parameter-encoding';
        readonly renameMisleadingTypeInTypeTest: true;
        readonly addFourCellMatrixAndCodeUniverseWitness: true;
        readonly nextInductiveConsumerUsesExplicitCodes: true;
    };
    readonly doesNotAuthorize: readonly [
        'TYPE-in-TYPE',
        'KIND-domain-products',
        'native-higher-kinded-quantification',
        'implicit-code-universe-invention',
        'checker-or-Core-semantic-change',
        'generated-eliminator-semantics',
        'Lambdapi-source-change',
        'browser-or-release-promotion',
        'bulk-transfer-or-parser-work',
        'remote-or-history-rewriting-Git-operation'
    ];
    readonly decision: {
        readonly humanGate: 'H-DTTLF-LF-SORT-01';
        readonly decisionId: 'D-DTTLF-LF-SORT-001';
        readonly status: 'proposal-only';
        readonly question: typeof CORE_LF_SCALE_KIND_PI_DECISION_QUESTION;
    };
}

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

const rawAudit: CoreLfScaleKindPiAudit = {
    revision: CORE_LF_SCALE_KIND_PI_AUDIT_REVISION,
    row: 'SCALE-KIND-PI-1',
    authority: 'Lambdapi-lambda-Pi',
    productSortMatrix: [
        {
            domainAnnotationSort: 'TYPE',
            bodySort: 'TYPE',
            accepted: true,
            resultSort: 'TYPE'
        },
        {
            domainAnnotationSort: 'TYPE',
            bodySort: 'KIND',
            accepted: true,
            resultSort: 'KIND'
        },
        {
            domainAnnotationSort: 'KIND',
            bodySort: 'TYPE',
            accepted: false,
            rejection: 'KIND-domain-annotation'
        },
        {
            domainAnnotationSort: 'KIND',
            bodySort: 'KIND',
            accepted: false,
            rejection: 'KIND-domain-annotation'
        }
    ],
    nativeUniverseAxiom: {
        judgment: 'TYPE : KIND',
        typeInType: false,
        kindIsCoreExpression: false
    },
    explicitCodeUniverse: {
        schematicDeclarations: [
            'Type : TYPE',
            'El : Type -> TYPE'
        ],
        activeEmdashAnalogue: [
            'Grpd : TYPE',
            'τ : Grpd -> TYPE'
        ],
        compilerMayInventIt: false
    },
    verdict:
        'preserve-current-checker-and-use-explicit-code-universes',
    measuredCorrection: {
        checkerSemanticChange: false,
        coreTermChange: false,
        lambdapiSourceChange: false,
        previousBoundaryLabel:
            'kind-level-binder-compilation',
        correctedBoundaryLabel:
            'implicit-native-TYPE-parameter-encoding',
        renameMisleadingTypeInTypeTest: true,
        addFourCellMatrixAndCodeUniverseWitness: true,
        nextInductiveConsumerUsesExplicitCodes: true
    },
    doesNotAuthorize: [
        'TYPE-in-TYPE',
        'KIND-domain-products',
        'native-higher-kinded-quantification',
        'implicit-code-universe-invention',
        'checker-or-Core-semantic-change',
        'generated-eliminator-semantics',
        'Lambdapi-source-change',
        'browser-or-release-promotion',
        'bulk-transfer-or-parser-work',
        'remote-or-history-rewriting-Git-operation'
    ],
    decision: {
        humanGate: 'H-DTTLF-LF-SORT-01',
        decisionId: 'D-DTTLF-LF-SORT-001',
        status: 'proposal-only',
        question: CORE_LF_SCALE_KIND_PI_DECISION_QUESTION
    }
};

export const CORE_LF_SCALE_KIND_PI_AUDIT = deepFreeze(rawAudit);

export type CoreLfScaleKindPiAuditErrorCode =
    | 'INVALID_PRODUCT_SORT_MATRIX'
    | 'AUDIT_BOUNDARY_DRIFT';

export class CoreLfScaleKindPiAuditError extends Error {
    constructor(
        public readonly code: CoreLfScaleKindPiAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleKindPiAuditError';
    }
}

const fail = (
    code: CoreLfScaleKindPiAuditErrorCode,
    message: string
): never => {
    throw new CoreLfScaleKindPiAuditError(code, message);
};

export function validateCoreLfScaleKindPiAudit(
    audit: CoreLfScaleKindPiAudit = CORE_LF_SCALE_KIND_PI_AUDIT
): CoreLfScaleKindPiAudit {
    const expectedMatrix = [
        'TYPE:TYPE:true:TYPE:',
        'TYPE:KIND:true:KIND:',
        'KIND:TYPE:false::KIND-domain-annotation',
        'KIND:KIND:false::KIND-domain-annotation'
    ];
    const actualMatrix = audit.productSortMatrix.map(cell =>
        [
            cell.domainAnnotationSort,
            cell.bodySort,
            String(cell.accepted),
            cell.resultSort ?? '',
            cell.rejection ?? ''
        ].join(':')
    );
    if (
        actualMatrix.length !== expectedMatrix.length ||
        actualMatrix.some((cell, index) => cell !== expectedMatrix[index])
    ) {
        return fail(
            'INVALID_PRODUCT_SORT_MATRIX',
            'SCALE-KIND-PI-1 product-sort matrix drifted'
        );
    }
    if (
        audit.revision !== CORE_LF_SCALE_KIND_PI_AUDIT_REVISION ||
        audit.authority !== 'Lambdapi-lambda-Pi' ||
        audit.nativeUniverseAxiom.judgment !== 'TYPE : KIND' ||
        audit.nativeUniverseAxiom.typeInType ||
        audit.nativeUniverseAxiom.kindIsCoreExpression ||
        audit.explicitCodeUniverse.compilerMayInventIt ||
        audit.verdict !==
            'preserve-current-checker-and-use-explicit-code-universes' ||
        audit.measuredCorrection.checkerSemanticChange ||
        audit.measuredCorrection.coreTermChange ||
        audit.measuredCorrection.lambdapiSourceChange ||
        audit.measuredCorrection.correctedBoundaryLabel !==
            'implicit-native-TYPE-parameter-encoding' ||
        audit.decision.status !== 'proposal-only' ||
        audit.decision.question !==
            CORE_LF_SCALE_KIND_PI_DECISION_QUESTION
    ) {
        return fail(
            'AUDIT_BOUNDARY_DRIFT',
            'SCALE-KIND-PI-1 authority or non-effect boundary drifted'
        );
    }
    return audit;
}
