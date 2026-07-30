/**
 * Executable SYNTAX-PARITY-1C0 constructor-text audit.
 *
 * This audit reclassifies the post-1B3 residual mathematical constructors
 * and freezes the first bounded 1C proposal. It changes no parser, resolver,
 * categorical program, Core, checker, runtime, Lambdapi, or browser behavior.
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

const ordinaryStructuralOperations = [
    {
        sourceName: 'id',
        arity: 1,
        argumentKinds: ['category'],
        directMethod: 'identityFunctor',
        resultKind: 'term'
    },
    {
        sourceName: 'compose',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'composeFunctors',
        resultKind: 'term'
    },
    {
        sourceName: 'pair',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'functorPair',
        resultKind: 'term'
    },
    {
        sourceName: 'map',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'productMap',
        resultKind: 'term'
    },
    {
        sourceName: 'pi1',
        arity: 2,
        argumentKinds: ['category', 'category'],
        directMethod: 'productLeftProjection',
        resultKind: 'term'
    },
    {
        sourceName: 'pi2',
        arity: 2,
        argumentKinds: ['category', 'category'],
        directMethod: 'productRightProjection',
        resultKind: 'term'
    }
] as const;

const rawAudit = {
    revision: 'SYNTAX-PARITY-1C0-CONSTRUCTOR-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1B3-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            '3dcf25ec008bb3d30723e3251c222e88acc216a3'
    },
    measuredTextSurface: {
        locatedNodeKinds: [
            'identifier',
            'left-associated-application',
            'intrinsic-mode-lambda'
        ],
        explicitOperationHeads: [
            'indexOf',
            'fibrePair',
            'composeCells'
        ],
        rootResultKinds: ['term'],
        exactOrdinaryFailure: {
            source: 'compose G F',
            phase: 'resolution',
            code: 'UNKNOWN_IDENTIFIER',
            identifier: 'compose',
            startColumn: 1,
            endColumn: 8
        },
        conclusion:
            'ordinary structural owners are direct-green and fail only ' +
            'because their reserved operation heads are not routed'
    },
    residualInventory: [
        {
            id: 'ordinary-structural-term-constructors',
            status: 'dependency-ready-mechanical-route',
            methods: ordinaryStructuralOperations.map(
                operation => operation.directMethod
            ),
            requiredDesign:
                'six fixed application spines over recursively resolved ' +
                'term arguments or checked category identifiers',
            row: 'SYNTAX-PARITY-1C1'
        },
        {
            id: 'displayed-and-fibred-term-constructors',
            status: 'gated-typed-argument-kind-audit',
            methods: [
                'displayedProductLeftProjection',
                'displayedProductRightProjection',
                'displayedProductPair',
                'displayedProductSwap',
                'displayedProductDiagonal',
                'displayedFunctorFullAction',
                'displayedFunctorInternalCell',
                'sigmaProjection',
                'pullbackDisplayedFunctor',
                'dependentPair',
                'familyTransport',
                'sigmaArrow',
                'pullbackTotal',
                'composeDisplayedTransfor'
            ],
            alreadyTextual: ['indexOf', 'fibrePair', 'composeCells'],
            requiredDesign:
                'finite operation descriptors with explicit family, term, ' +
                'category, and Hom-boundary argument kinds; no action guess',
            row: 'SYNTAX-PARITY-1C2'
        },
        {
            id: 'category-and-family-valued-constructors',
            status: 'gated-typed-result-contract-audit',
            methods: [
                'constantDisplayedFamily',
                'displayedFunctorFamily',
                'dependentSectionMotive',
                'dependentSectionTarget',
                'dependentSectionCategoryAt',
                'displayedProduct',
                'fibre',
                'totalCategory',
                'displayedTransforCategory',
                'functorCategory',
                'productCategory',
                'pullbackFamily',
                'substituteFamily'
            ],
            normalizedAliases: [
                {
                    method: 'substituteFamily',
                    canonicalTextHead: 'pullback'
                }
            ],
            requiredDesign:
                'reuse the same located parser with a checked category or ' +
                'displayed-family result contract; do not add a second ' +
                'checker or infer dependent families from text',
            row: 'SYNTAX-PARITY-1C3'
        },
        {
            id: 'host-context-and-observation-operations',
            status: 'graduation-classification-required',
            methods: [
                'groupedSequentialContext',
                'groupedSequentialObject',
                'inspect',
                'serializeCategory',
                'compareCategories',
                'compareDisplayedFamilies',
                'compare',
                'compile'
            ],
            requiredDesign:
                'classify host fixture/context construction and observations ' +
                'as non-expression operations unless a mathematical witness ' +
                'demonstrates a missing source term',
            row: 'SYNTAX-PARITY-GRADUATE-1'
        }
    ],
    oneCSplit: [
        {
            row: 'SYNTAX-PARITY-1C1',
            status: 'selected-non-self-authorizing-proposal',
            scope: 'six ordinary structural term constructors'
        },
        {
            row: 'SYNTAX-PARITY-1C2',
            status: 'gated',
            scope: 'remaining selected displayed and fibred term constructors'
        },
        {
            row: 'SYNTAX-PARITY-1C3',
            status: 'gated',
            scope: 'category and displayed-family result constructors'
        },
        {
            row: 'SYNTAX-PARITY-GRADUATE-1',
            status: 'gated',
            scope: 'freeze exact mathematical-expression target and residuals'
        }
    ],
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-05',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-005',
        row: 'SYNTAX-PARITY-1C1',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'add the complete ordinary structural term algebra before ' +
            'introducing non-term result contracts or displayed argument ' +
            'kinds',
        operations: ordinaryStructuralOperations,
        resolverDesign: {
            locatedNodeKindsAdded: 0,
            parserGrammarAdded: 0,
            strategy:
                'recognize six exact reserved fixed-arity application ' +
                'spines before the existing generic application route',
            termArguments:
                'resolve recursively through the existing term resolver',
            categoryArguments:
                'accept only category identifiers from the immutable ' +
                'environment in this row',
            ownership:
                'call the six existing typed CoreCategoricalProgram methods; ' +
                'they remain the sole endpoint and classifier authorities',
            ordinaryApplication:
                'every non-reserved spine continues through the sole apply ' +
                'path'
        },
        exactPositiveSources: [
            'id A',
            'compose G F',
            'pair F H',
            'map F P',
            'pi1 B C',
            'pi2 B C'
        ],
        requiredDirectEquality: [
            'backend-neutral explicit Core',
            'inferred functor classifier',
            'existing identity/composition/product/projection/pair/map owner'
        ],
        exactNegativeClasses: [
            'missing or extra constructor argument',
            'wrong category-versus-term argument kind',
            'foreign category or term',
            'composition with incompatible middle categories',
            'pair components without one shared source',
            'ordinary structural owner unavailable under the selected profile'
        ],
        reviewerEffect:
            'none; the editable reviewer already accepts arbitrary source, ' +
            'and another preset is not required for this mechanical slice',
        implementationFiles: [
            'src/v3_2/categorical_text.ts',
            'tests/v3_2_categorical_text_constructor_tests.ts',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md'
        ],
        nonEffects: [
            'no category or displayed-family result syntax',
            'no displayed/fibred constructor syntax',
            'no new mathematical owner or categorical program method',
            'no new Core node, checker, evaluator, runtime, or proof rule',
            'no new expected contract, action table, or parser dependency',
            'no Lambdapi declaration, rule, profile, or transfer input',
            'no browser preset, book prose, scale row, or publication'
        ]
    },
    proposedImplementationDelta: {
        privateLocatedNodeKinds: 0,
        parserGrammarProductions: 0,
        reservedOperationDescriptors: 6,
        categoryIdentifierResolver: 1,
        programMethods: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 0
    },
    semanticDelta: {
        parserNodeKinds: 0,
        textResolverBranches: 0,
        programMethods: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 0
    }
} as const;

export type CoreCategoricalTextConstructorAuditInput = typeof rawAudit;

export type CoreCategoricalTextConstructorAuditErrorCode =
    | 'TEXT_CONSTRUCTOR_PREREQUISITE_DRIFT'
    | 'TEXT_CONSTRUCTOR_MEASUREMENT_DRIFT'
    | 'TEXT_CONSTRUCTOR_INVENTORY_DRIFT'
    | 'TEXT_CONSTRUCTOR_PROPOSAL_DRIFT'
    | 'TEXT_CONSTRUCTOR_BOUNDARY_DRIFT';

export class CoreCategoricalTextConstructorAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextConstructorAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalTextConstructorAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextConstructorAudit = (
    audit: CoreCategoricalTextConstructorAuditInput =
        CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1B3-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.implementationCheckpoint !==
            '3dcf25ec008bb3d30723e3251c222e88acc216a3'
    ) {
        throw new CoreCategoricalTextConstructorAuditError(
            'TEXT_CONSTRUCTOR_PREREQUISITE_DRIFT',
            'Constructor text audit prerequisite changed'
        );
    }

    if (
        audit.measuredTextSurface.exactOrdinaryFailure.code !==
            'UNKNOWN_IDENTIFIER' ||
        audit.measuredTextSurface.exactOrdinaryFailure.identifier !==
            'compose' ||
        !sameData(
            audit.measuredTextSurface.explicitOperationHeads,
            ['indexOf', 'fibrePair', 'composeCells']
        )
    ) {
        throw new CoreCategoricalTextConstructorAuditError(
            'TEXT_CONSTRUCTOR_MEASUREMENT_DRIFT',
            'The measured post-1B3 constructor seam changed'
        );
    }

    if (
        !sameData(
            audit.oneCSplit.map(entry => entry.row),
            [
                'SYNTAX-PARITY-1C1',
                'SYNTAX-PARITY-1C2',
                'SYNTAX-PARITY-1C3',
                'SYNTAX-PARITY-GRADUATE-1'
            ]
        ) ||
        audit.residualInventory[0]?.methods.length !== 6 ||
        audit.residualInventory[1]?.methods.length !== 14 ||
        audit.residualInventory[2]?.methods.length !== 13
    ) {
        throw new CoreCategoricalTextConstructorAuditError(
            'TEXT_CONSTRUCTOR_INVENTORY_DRIFT',
            'The bounded residual constructor inventory changed'
        );
    }

    if (
        audit.proposal.gate !==
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-05' ||
        audit.proposal.decision !==
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-005' ||
        audit.proposal.row !== 'SYNTAX-PARITY-1C1' ||
        audit.proposal.status !==
            'deeply-frozen-non-self-authorizing-proposal' ||
        !sameData(
            audit.proposal.operations.map(
                operation => operation.sourceName
            ),
            ['id', 'compose', 'pair', 'map', 'pi1', 'pi2']
        )
    ) {
        throw new CoreCategoricalTextConstructorAuditError(
            'TEXT_CONSTRUCTOR_PROPOSAL_DRIFT',
            'The bounded ordinary-constructor proposal changed'
        );
    }

    if (
        Object.values(audit.semanticDelta).some(value => value !== 0) ||
        audit.proposedImplementationDelta.programMethods !== 0 ||
        audit.proposedImplementationDelta.coreOwners !== 0 ||
        audit.proposedImplementationDelta
            .checkerOrEvaluatorBranches !== 0 ||
        audit.proposedImplementationDelta
            .lambdapiDeclarationsOrRules !== 0
    ) {
        throw new CoreCategoricalTextConstructorAuditError(
            'TEXT_CONSTRUCTOR_BOUNDARY_DRIFT',
            'The audit or proposal crossed its zero-semantic-delta boundary'
        );
    }
};
