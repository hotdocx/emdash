/**
 * Executable SYNTAX-PARITY-1C2 displayed/fibred constructor audit.
 *
 * This audit distinguishes constructors that need named text heads from
 * observations already expressible by recursive generic application. It
 * freezes only the first mechanical 1C2A proposal and changes no parser,
 * resolver, categorical program, Core, checker, runtime, Lambdapi, or
 * browser behavior.
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

const canonicalDisplayedOperations = [
    {
        sourceName: 'pi1d',
        arity: 2,
        argumentKinds: ['displayed-family', 'displayed-family'],
        directMethod: 'displayedProductLeftProjection',
        resultKind: 'term'
    },
    {
        sourceName: 'pi2d',
        arity: 2,
        argumentKinds: ['displayed-family', 'displayed-family'],
        directMethod: 'displayedProductRightProjection',
        resultKind: 'term'
    },
    {
        sourceName: 'paird',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'displayedProductPair',
        resultKind: 'term'
    },
    {
        sourceName: 'swapd',
        arity: 2,
        argumentKinds: ['displayed-family', 'displayed-family'],
        directMethod: 'displayedProductSwap',
        resultKind: 'term'
    },
    {
        sourceName: 'diagd',
        arity: 1,
        argumentKinds: ['displayed-family'],
        directMethod: 'displayedProductDiagonal',
        resultKind: 'term'
    },
    {
        sourceName: 'sigmaProj',
        arity: 1,
        argumentKinds: ['displayed-family'],
        directMethod: 'sigmaProjection',
        resultKind: 'term'
    },
    {
        sourceName: 'pullbackFunctord',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'pullbackDisplayedFunctor',
        resultKind: 'term'
    },
    {
        sourceName: 'sigmaPair',
        arity: 3,
        argumentKinds: ['displayed-family', 'term', 'term'],
        directMethod: 'dependentPair',
        resultKind: 'term'
    },
    {
        sourceName: 'transport',
        arity: 2,
        argumentKinds: ['displayed-family', 'term'],
        directMethod: 'familyTransport',
        resultKind: 'term'
    },
    {
        sourceName: 'sigmaArrow',
        arity: 5,
        argumentKinds: [
            'displayed-family',
            'term',
            'term',
            'term',
            'term'
        ],
        directMethod: 'sigmaArrow',
        resultKind: 'term'
    },
    {
        sourceName: 'pullbackTotal',
        arity: 2,
        argumentKinds: ['term', 'displayed-family'],
        directMethod: 'pullbackTotal',
        resultKind: 'term'
    },
    {
        sourceName: 'composeTransfd',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'composeDisplayedTransfor',
        resultKind: 'term'
    }
] as const;

const rawAudit = {
    revision:
        'SYNTAX-PARITY-1C2-DISPLAYED-CONSTRUCTOR-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1C1-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            'be437f3a7d64a6a554578036f76621322d5626fc'
    },
    correctedResidualInventory: {
        reason:
            'the 1C0 split correctly gated displayed constructors, but its ' +
            'fourteen-method list inherited an aspirational 0A claim that ' +
            'eta p u was already generic application and therefore omitted ' +
            'two genuine higher-action constructors',
        genericApplicationAlreadyTextual: [
            {
                source: 'eta x',
                directMethod: 'displayedTransforComponent',
                expectedResult: 'equal-explicit-core'
            },
            {
                source: 'eta x u',
                directMethod: 'displayedTransforPoint',
                expectedResult: 'equal-explicit-core'
            }
        ],
        explicitActionConstructorsStillRequired: [
            'displayedFunctorFullAction',
            'displayedFunctorInternalCell',
            'displayedTransforNaturality',
            'displayedTransforInternalHomAction'
        ],
        exactNonGenericWitness: {
            source: 'eta p u',
            currentCode: 'CATEGORICAL_REJECTION',
            reason:
                'a displayed transformation accepts a base object for its ' +
                'component; its transported base-arrow naturality cell is ' +
                'an existing distinct internalized construction'
        },
        conclusion:
            'component and point observations need no alias, while four ' +
            'whole or higher internalized constructions require an explicit ' +
            'later constructor route'
    },
    split: [
        {
            row: 'SYNTAX-PARITY-1C2A',
            status: 'selected-non-self-authorizing-proposal',
            scope:
                'twelve canonical displayed-product, comprehension, ' +
                'transport, totalization, and Transfd-composition terms'
        },
        {
            row: 'SYNTAX-PARITY-1C2B',
            status: 'gated',
            scope:
                'four explicit whole/higher internalized action ' +
                'constructors after a dedicated notation and expected-shape ' +
                'review'
        },
        {
            row: 'SYNTAX-PARITY-1C3',
            status: 'gated',
            scope:
                'category and displayed-family result constructors'
        }
    ],
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-06',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-006',
        row: 'SYNTAX-PARITY-1C2A',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'make the complete mechanical displayed structural and ' +
            'comprehension term algebra textual before separately naming ' +
            'whole/higher action observations',
        operations: canonicalDisplayedOperations,
        resolverDesign: {
            locatedNodeKindsAdded: 0,
            parserGrammarAdded: 0,
            strategy:
                'recognize twelve exact reserved fixed-arity application ' +
                'spines before the existing generic application route',
            termArguments:
                'resolve recursively through the existing term resolver',
            familyArguments:
                'accept only displayed-family identifiers from the ' +
                'immutable environment until 1C3 supplies checked ' +
                'family-valued expressions',
            homBoundaryArguments:
                'none; Hom boundaries remain typed generic-application ' +
                'arguments and are not fabricated by these constructors',
            ownership:
                'call the twelve existing CoreCategoricalProgram methods; ' +
                'the program remains the sole classifier, endpoint, scope, ' +
                'and profile authority',
            ordinaryApplication:
                'every non-reserved spine continues through the sole apply ' +
                'path'
        },
        exactPositiveSources: [
            'pi1d B C',
            'pi2d B C',
            'paird FF GG',
            'swapd B C',
            'diagd B',
            'sigmaProj E',
            'pullbackFunctord FF F',
            'sigmaPair E x u',
            'transport E p',
            'sigmaArrow E u v p alpha',
            'pullbackTotal F E',
            'composeTransfd theta eta'
        ],
        requiredDirectEquality: [
            'backend-neutral explicit Core',
            'inferred rich categorical classifier',
            'existing Productd, Sigma, pullback, transport, totalization, ' +
                'and generic composition ownership'
        ],
        exactNegativeClasses: [
            'missing or extra constructor argument',
            'wrong displayed-family-versus-term argument kind',
            'foreign displayed family or term',
            'displayed product base or shared-source mismatch',
            'dependent pair base/fibre mismatch',
            'transport arrow base mismatch',
            'Sigma arrow source, target, transport, or fibre mismatch',
            'pullback substitution endpoint mismatch',
            'displayed transformation composition endpoint mismatch',
            'constructor unavailable under the selected profile'
        ],
        reviewerEffect:
            'none; the editable reviewer already accepts arbitrary source ' +
            'and this mechanical algebra needs no additional preset',
        implementationFiles: [
            'src/v3_2/categorical_text.ts',
            'tests/v3_2_categorical_text_displayed_constructor_tests.ts',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md'
        ],
        nonEffects: [
            'no component or point alias already expressible by whitespace ' +
                'application',
            'no whole/higher action constructor from the gated 1C2B row',
            'no category or displayed-family result syntax from 1C3',
            'no new mathematical owner or categorical program method',
            'no new Core node, checker, evaluator, runtime, or proof rule',
            'no new expected-action table or parser dependency',
            'no Lambdapi declaration, rule, profile, or transfer input',
            'no browser preset, book prose, scale row, or publication'
        ]
    },
    proposedImplementationDelta: {
        privateLocatedNodeKinds: 0,
        parserGrammarProductions: 0,
        reservedOperationDescriptors: 12,
        displayedFamilyIdentifierResolver: 1,
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

export type CoreCategoricalTextDisplayedConstructorAuditInput =
    typeof rawAudit;

export type CoreCategoricalTextDisplayedConstructorAuditErrorCode =
    | 'TEXT_DISPLAYED_CONSTRUCTOR_PREREQUISITE_DRIFT'
    | 'TEXT_DISPLAYED_CONSTRUCTOR_INVENTORY_DRIFT'
    | 'TEXT_DISPLAYED_CONSTRUCTOR_PROPOSAL_DRIFT'
    | 'TEXT_DISPLAYED_CONSTRUCTOR_BOUNDARY_DRIFT';

export class CoreCategoricalTextDisplayedConstructorAuditError
    extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextDisplayedConstructorAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalTextDisplayedConstructorAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_DISPLAYED_CONSTRUCTOR_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextDisplayedConstructorAudit = (
    audit: CoreCategoricalTextDisplayedConstructorAuditInput =
        CORE_CATEGORICAL_TEXT_DISPLAYED_CONSTRUCTOR_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1C1-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.implementationCheckpoint !==
            'be437f3a7d64a6a554578036f76621322d5626fc'
    ) {
        throw new CoreCategoricalTextDisplayedConstructorAuditError(
            'TEXT_DISPLAYED_CONSTRUCTOR_PREREQUISITE_DRIFT',
            'Displayed-constructor audit prerequisite changed'
        );
    }

    if (
        !sameData(
            audit.correctedResidualInventory
                .genericApplicationAlreadyTextual
                .map(entry => entry.source),
            ['eta x', 'eta x u']
        ) ||
        !sameData(
            audit.correctedResidualInventory
                .explicitActionConstructorsStillRequired,
            [
                'displayedFunctorFullAction',
                'displayedFunctorInternalCell',
                'displayedTransforNaturality',
                'displayedTransforInternalHomAction'
            ]
        ) ||
        audit.correctedResidualInventory.exactNonGenericWitness
            .currentCode !== 'CATEGORICAL_REJECTION'
    ) {
        throw new CoreCategoricalTextDisplayedConstructorAuditError(
            'TEXT_DISPLAYED_CONSTRUCTOR_INVENTORY_DRIFT',
            'The measured generic-versus-explicit action split changed'
        );
    }

    if (
        audit.proposal.gate !==
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-06' ||
        audit.proposal.decision !==
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-006' ||
        audit.proposal.row !== 'SYNTAX-PARITY-1C2A' ||
        audit.proposal.status !==
            'deeply-frozen-non-self-authorizing-proposal' ||
        !sameData(
            audit.proposal.operations.map(
                operation => operation.sourceName
            ),
            [
                'pi1d',
                'pi2d',
                'paird',
                'swapd',
                'diagd',
                'sigmaProj',
                'pullbackFunctord',
                'sigmaPair',
                'transport',
                'sigmaArrow',
                'pullbackTotal',
                'composeTransfd'
            ]
        )
    ) {
        throw new CoreCategoricalTextDisplayedConstructorAuditError(
            'TEXT_DISPLAYED_CONSTRUCTOR_PROPOSAL_DRIFT',
            'The bounded displayed-constructor proposal changed'
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
        throw new CoreCategoricalTextDisplayedConstructorAuditError(
            'TEXT_DISPLAYED_CONSTRUCTOR_BOUNDARY_DRIFT',
            'The audit or proposal crossed its zero-semantic-delta boundary'
        );
    }
};
