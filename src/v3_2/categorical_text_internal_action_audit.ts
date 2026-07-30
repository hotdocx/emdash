/**
 * Executable SYNTAX-PARITY-1C2B whole/higher internal-action audit.
 *
 * The four proposed text heads construct existing first-class mathematical
 * terms. Subsequent application remains the sole generic application route.
 * This file changes no parser, resolver, program, Core, checker, runtime,
 * Lambdapi, or browser behavior.
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

const internalActionOperations = [
    {
        sourceName: 'fullAction',
        arity: 3,
        argumentKinds: ['term', 'term', 'term'],
        directMethod: 'displayedFunctorFullAction',
        resultClassifier: 'functor',
        genericContinuation: 'fullAction FF x y p'
    },
    {
        sourceName: 'cell',
        arity: 3,
        argumentKinds: ['term', 'term', 'term'],
        directMethod: 'displayedFunctorInternalCell',
        resultClassifier: 'hom',
        genericContinuation: 'none'
    },
    {
        sourceName: 'naturality',
        arity: 3,
        argumentKinds: ['term', 'term', 'term'],
        directMethod: 'displayedTransforNaturality',
        resultClassifier: 'hom',
        genericContinuation: 'none'
    },
    {
        sourceName: 'internalHomAction',
        arity: 2,
        argumentKinds: ['term', 'term'],
        directMethod: 'displayedTransforInternalHomAction',
        resultClassifier: 'functor',
        genericContinuation:
            'internalHomAction FF GG eta'
    }
] as const;

const rawAudit = {
    revision: 'SYNTAX-PARITY-1C2B-INTERNAL-ACTION-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision:
            'SYNTAX-PARITY-1C2A-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            'c1bd21eec9456a3600e22b1ef0dc8084958fd123'
    },
    authority: {
        canonicalDisplayedCellNotation: 'cell(FF,p,u)',
        activeOwners: [
            'tapp1_func',
            'fdapp1_int_cell',
            'tdapp1_int_cell',
            'tdapp1_int_func_transfd'
        ],
        rule:
            'construct only terms already classified by ' +
            'CoreCategoricalProgram; never request an external ' +
            'naturality or functoriality witness'
    },
    measuredDistinctions: [
        {
            source: 'fullAction FF x y',
            directMethod: 'displayedFunctorFullAction',
            resultClassifier: 'functor',
            reason:
                'the iterable Hom-to-functor action is first-class; ' +
                'generic FF p selects its capped transport functor instead'
        },
        {
            source: 'cell FF p u',
            directMethod: 'displayedFunctorInternalCell',
            resultClassifier: 'hom',
            reason:
                'FF p u is an object-level transported application, while ' +
                'cell FF p u is the internalized displayed laxity arrow'
        },
        {
            source: 'naturality eta p u',
            directMethod: 'displayedTransforNaturality',
            resultClassifier: 'hom',
            reason:
                'eta p u cannot mean component application because p is a ' +
                'base arrow; the named term constructs the transported ' +
                'internal naturality cell'
        },
        {
            source: 'internalHomAction FF GG',
            directMethod:
                'displayedTransforInternalHomAction',
            resultClassifier: 'functor',
            reason:
                'the coherent Transfd-to-internal-Hom action is a ' +
                'first-class functor whose object and next-Hom actions ' +
                'remain generic applications'
        }
    ],
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-07',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-007',
        row: 'SYNTAX-PARITY-1C2B',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'make the four already implemented first-class whole/higher ' +
            'internalized actions textual without adding aliases for ' +
            'generic component, point, or action observations',
        operations: internalActionOperations,
        resolverDesign: {
            locatedNodeKindsAdded: 0,
            parserGrammarAdded: 0,
            strategy:
                'recognize four exact reserved fixed-arity application ' +
                'spines before the existing generic application route',
            arguments:
                'resolve every operand recursively as a checked term',
            ownership:
                'call the four existing CoreCategoricalProgram methods; ' +
                'the program remains sole classifier, endpoint, scope, ' +
                'profile, and internal-coherence authority',
            continuation:
                'application to p, eta, a Hom boundary, or a later cell ' +
                'continues through generic apply and its existing expected-' +
                'shape contract',
            redundantRoutes:
                'eta x and eta x u remain generic whitespace application; ' +
                'FF p u remains the distinct object-level route'
        },
        exactPositiveSources: [
            'fullAction FF x y',
            'fullAction FF x y p',
            'cell FF p u',
            'naturality eta p u',
            'internalHomAction FF GG',
            'internalHomAction FF GG eta'
        ],
        exactNegativeClasses: [
            'missing constructor argument',
            'wrong subject classifier',
            'wrong base object, arrow, or fibre object',
            'incompatible displayed-functor endpoints',
            'foreign term',
            'constructor unavailable under the selected profile',
            'eta p u retained as rejected generic component application'
        ],
        implementationFiles: [
            'src/v3_2/categorical_text.ts',
            'tests/v3_2_categorical_text_internal_action_tests.ts',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md'
        ],
        nonEffects: [
            'no alias for displayedTransforComponent or ' +
                'displayedTransforPoint',
            'no category or displayed-family result syntax from 1C3',
            'no mathematical owner or categorical program method',
            'no Core node, checker, evaluator, runtime, or proof rule',
            'no expected-action table or parser dependency',
            'no external naturality or functoriality evidence',
            'no Lambdapi declaration, rule, profile, or transfer input',
            'no browser preset, book prose, scale row, or publication'
        ]
    },
    proposedImplementationDelta: {
        privateLocatedNodeKinds: 0,
        parserGrammarProductions: 0,
        reservedOperationDescriptors: 4,
        programMethods: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 0
    },
    semanticDelta: {
        parserNodeKinds: 0,
        programMethods: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 0
    }
} as const;

export type CoreCategoricalTextInternalActionAuditInput =
    typeof rawAudit;

export type CoreCategoricalTextInternalActionAuditErrorCode =
    | 'TEXT_INTERNAL_ACTION_PREREQUISITE_DRIFT'
    | 'TEXT_INTERNAL_ACTION_AUTHORITY_DRIFT'
    | 'TEXT_INTERNAL_ACTION_PROPOSAL_DRIFT'
    | 'TEXT_INTERNAL_ACTION_BOUNDARY_DRIFT';

export class CoreCategoricalTextInternalActionAuditError
    extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextInternalActionAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalTextInternalActionAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextInternalActionAudit = (
    audit: CoreCategoricalTextInternalActionAuditInput =
        CORE_CATEGORICAL_TEXT_INTERNAL_ACTION_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1C2A-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.implementationCheckpoint !==
            'c1bd21eec9456a3600e22b1ef0dc8084958fd123'
    ) {
        throw new CoreCategoricalTextInternalActionAuditError(
            'TEXT_INTERNAL_ACTION_PREREQUISITE_DRIFT',
            'Internal-action audit prerequisite changed'
        );
    }

    if (
        audit.authority.canonicalDisplayedCellNotation !==
            'cell(FF,p,u)' ||
        !sameData(audit.authority.activeOwners, [
            'tapp1_func',
            'fdapp1_int_cell',
            'tdapp1_int_cell',
            'tdapp1_int_func_transfd'
        ]) ||
        !sameData(
            audit.measuredDistinctions.map(entry =>
                entry.resultClassifier
            ),
            ['functor', 'hom', 'hom', 'functor']
        )
    ) {
        throw new CoreCategoricalTextInternalActionAuditError(
            'TEXT_INTERNAL_ACTION_AUTHORITY_DRIFT',
            'Internal-action ownership or classifier evidence changed'
        );
    }

    if (
        audit.proposal.gate !==
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-07' ||
        audit.proposal.decision !==
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-007' ||
        audit.proposal.row !== 'SYNTAX-PARITY-1C2B' ||
        audit.proposal.status !==
            'deeply-frozen-non-self-authorizing-proposal' ||
        !sameData(
            audit.proposal.operations.map(operation =>
                operation.sourceName
            ),
            [
                'fullAction',
                'cell',
                'naturality',
                'internalHomAction'
            ]
        )
    ) {
        throw new CoreCategoricalTextInternalActionAuditError(
            'TEXT_INTERNAL_ACTION_PROPOSAL_DRIFT',
            'The bounded internal-action proposal changed'
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
        throw new CoreCategoricalTextInternalActionAuditError(
            'TEXT_INTERNAL_ACTION_BOUNDARY_DRIFT',
            'The audit or proposal crossed its zero-semantic-delta boundary'
        );
    }
};
