/**
 * Executable SYNTAX-PARITY-1C3 category/displayed-family result audit.
 *
 * The selected operations already exist on CoreCategoricalProgram. This
 * artifact freezes only their proposed mathematical text heads and the
 * checked result contract needed to route them through the existing parser.
 * It changes no parser, resolver, Core, checker, runtime, or kernel behavior.
 */

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const resultOperations = [
    {
        sourceName: 'constantd',
        arity: 2,
        argumentKinds: ['category', 'category'],
        directMethod: 'constantDisplayedFamily',
        resultKind: 'displayed-family'
    },
    {
        sourceName: 'functord',
        arity: 2,
        argumentKinds: ['category', 'displayed-family'],
        directMethod: 'displayedFunctorFamily',
        resultKind: 'displayed-family'
    },
    {
        sourceName: 'sectionMotive',
        arity: 1,
        argumentKinds: ['term'],
        directMethod: 'dependentSectionMotive',
        resultKind: 'displayed-family'
    },
    {
        sourceName: 'sectionTarget',
        arity: 1,
        argumentKinds: ['term'],
        directMethod: 'dependentSectionTarget',
        resultKind: 'displayed-family'
    },
    {
        sourceName: 'sectionCategory',
        arity: 3,
        argumentKinds: ['term', 'term', 'term'],
        directMethod: 'dependentSectionCategoryAt',
        resultKind: 'category'
    },
    {
        sourceName: 'productd',
        arity: 2,
        argumentKinds: ['displayed-family', 'displayed-family'],
        directMethod: 'displayedProduct',
        resultKind: 'displayed-family'
    },
    {
        sourceName: 'fibre',
        arity: 2,
        argumentKinds: ['displayed-family', 'term'],
        directMethod: 'fibre',
        resultKind: 'category'
    },
    {
        sourceName: 'sigma',
        arity: 1,
        argumentKinds: ['displayed-family'],
        directMethod: 'totalCategory',
        resultKind: 'category'
    },
    {
        sourceName: 'transfd',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'displayedTransforCategory',
        resultKind: 'category'
    },
    {
        sourceName: 'functor',
        arity: 2,
        argumentKinds: ['category', 'category'],
        directMethod: 'functorCategory',
        resultKind: 'category'
    },
    {
        sourceName: 'product',
        arity: 2,
        argumentKinds: ['category', 'category'],
        directMethod: 'productCategory',
        resultKind: 'category'
    },
    {
        sourceName: 'pullback',
        arity: 2,
        argumentKinds: ['displayed-family', 'term'],
        directMethod: 'pullbackFamily',
        resultKind: 'displayed-family'
    }
] as const;

export const CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT = deepFreeze({
    revision: 'SYNTAX-PARITY-1C3-RESULT-CONSTRUCTOR-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1C2B-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            'afb1277a1517412e4cfcfc99d63a5259390b8ab9'
    },
    measuredBoundary: {
        directMethodCount: 13,
        canonicalTextHeadCount: 12,
        normalizedAlias: {
            method: 'substituteFamily',
            canonicalDirectMethod: 'pullbackFamily',
            canonicalTextHead: 'pullback'
        },
        currentRootResultKinds: ['term'],
        selectedRootResultKinds: [
            'term',
            'category',
            'displayed-family'
        ],
        locatedNodeKindsAdded: 0,
        parserGrammarProductionsAdded: 0,
        conclusion:
            'all selected constructions are direct-green; the remaining ' +
            'seam is typed result routing and recursive argument resolution'
    },
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-08',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-008',
        row: 'SYNTAX-PARITY-1C3',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        operations: resultOperations,
        resolverDesign: {
            expectedKindsAdded: ['category', 'displayed-family'],
            strategy:
                'select one of the existing term resolver or two small ' +
                'checked result resolvers over the same located tree',
            recursiveCategoryPositions:
                'resolve category identifiers or exact category-valued ' +
                'constructor expressions recursively',
            recursiveFamilyPositions:
                'resolve displayed-family identifiers or exact family-' +
                'valued constructor expressions recursively',
            termPositions:
                'resolve through the existing term resolver and sole apply ' +
                'ladder',
            ownership:
                'call only existing typed CoreCategoricalProgram methods; ' +
                'the program remains the classifier, base, endpoint, ' +
                'profile, foreign-value, and internal-coherence authority'
        },
        exactPositiveSources: [
            'constantd K A',
            'functord A B',
            'sectionMotive G',
            'sectionTarget G',
            'sectionCategory G k M',
            'productd B C',
            'fibre B k',
            'sigma B',
            'transfd FF GG',
            'functor A C',
            'product A C',
            'pullback B F',
            'id (fibre (productd B C) k)',
            'sigma (productd (pullback B F) (pullback C F))'
        ],
        exactNegativeClasses: [
            'wrong root result expectation',
            'missing or extra constructor argument',
            'wrong category, displayed-family, or term argument kind',
            'foreign category, displayed family, or term',
            'displayed product factors over different bases',
            'pullback functor with the wrong target',
            'fibre point in the wrong base category',
            'incompatible displayed-transformation endpoints',
            'owner unavailable under the selected profile'
        ],
        nonEffects: [
            'no new located node, parser grammar, parser dependency, or AST',
            'no second checker, resolver architecture, or action table',
            'no new mathematical owner or categorical program method',
            'no new Core node, checker, evaluator, runtime, or proof rule',
            'no external naturality or coherence evidence',
            'no compound binder-annotation grammar or arbitrary family inference',
            'no Lambdapi declaration, rule, profile, or transfer input',
            'no browser preset, book prose, scale row, or publication'
        ]
    }
} as const);

export type CoreCategoricalTextResultConstructorAudit =
    typeof CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT;

export type CoreCategoricalTextResultConstructorAuditErrorCode =
    | 'REVISION_DRIFT'
    | 'OPERATION_DRIFT'
    | 'RESULT_CONTRACT_DRIFT'
    | 'ALIAS_DRIFT';

export class CoreCategoricalTextResultConstructorAuditError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextResultConstructorAuditErrorCode,
        detail: string
    ) {
        super(`${code}: ${detail}`);
        this.name = 'CoreCategoricalTextResultConstructorAuditError';
    }
}

const sameJson = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreCategoricalTextResultConstructorAudit(
    audit: CoreCategoricalTextResultConstructorAudit =
        CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT
): CoreCategoricalTextResultConstructorAudit {
    if (
        audit.revision !==
            'SYNTAX-PARITY-1C3-RESULT-CONSTRUCTOR-AUDIT-1' ||
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1C2B-CATEGORICAL-TEXT-1'
    ) {
        throw new CoreCategoricalTextResultConstructorAuditError(
            'REVISION_DRIFT',
            'The frozen prerequisite or audit revision changed'
        );
    }
    if (!sameJson(audit.proposal.operations, resultOperations)) {
        throw new CoreCategoricalTextResultConstructorAuditError(
            'OPERATION_DRIFT',
            'The twelve canonical result operations changed'
        );
    }
    if (!sameJson(
        audit.measuredBoundary.selectedRootResultKinds,
        ['term', 'category', 'displayed-family']
    )) {
        throw new CoreCategoricalTextResultConstructorAuditError(
            'RESULT_CONTRACT_DRIFT',
            'The selected checked result contract changed'
        );
    }
    if (
        audit.measuredBoundary.normalizedAlias.method !==
            'substituteFamily' ||
        audit.measuredBoundary.normalizedAlias.canonicalTextHead !==
            'pullback'
    ) {
        throw new CoreCategoricalTextResultConstructorAuditError(
            'ALIAS_DRIFT',
            'The pullback/substitution normalization changed'
        );
    }
    return audit;
}
