/**
 * Executable SYNTAX-PARITY-1B0 structural-text audit.
 *
 * This audit measures the first post-modes presentation seam and freezes a
 * bounded proposal. It changes no text, categorical-program, Core, checker,
 * runtime, Lambdapi, or browser behavior.
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

const rawAudit = {
    revision: 'SYNTAX-PARITY-1B0-STRUCTURAL-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1A-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            '2e7cc3c44802a5218858ca6747e7591d3bfc4859'
    },
    measuredSeam: {
        capability: 'displayed-functor-weakening',
        exactSource: 'λ^fd a : E. s (indexOf a)',
        currentTextFailure: {
            phase: 'resolution',
            code: 'UNKNOWN_IDENTIFIER',
            identifier: 'indexOf',
            startColumn: 16,
            endColumn: 23
        },
        directMethods: [
            'displayedFunctorLambda',
            'apply',
            'indexOf'
        ],
        directRule: 'categorical.displayed-functor-weakening',
        directCoreOwners: [
            'emdash.categorical.section-pullback',
            'emdash.categorical.sigma-first-projection'
        ],
        conclusion:
            'presentation-only contextual operation seam; the direct ' +
            'factorer and internalized kernel construction are already green'
    },
    oneBSplit: [
        {
            row: 'SYNTAX-PARITY-1B1',
            status: 'selected-non-self-authorizing-proposal',
            scope: 'contextual index and displayed weakening'
        },
        {
            row: 'SYNTAX-PARITY-1B2',
            status: 'gated',
            scope:
                'independent displayed sibling binders and fibrePair'
        },
        {
            row: 'SYNTAX-PARITY-1B3',
            status: 'gated',
            scope:
                'bounded genuine dependent and mixed displayed telescopes'
        }
    ],
    firstProposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-02',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-002',
        row: 'SYNTAX-PARITY-1B1',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'close the smallest measured structural text seam before ' +
            'introducing multi-binder context syntax',
        operation: {
            sourceName: 'indexOf',
            arity: 1,
            directMethod: 'indexOf',
            admissibleArgument:
                'an active callback-local displayed slot accepted by the ' +
                'existing categorical program'
        },
        resolverDesign: {
            locatedNodeKindsAdded: 0,
            parserGrammarAdded: 0,
            strategy:
                'factor exact fixed-arity application-spine recognition ' +
                'shared with composeCells, then dispatch the reserved ' +
                'indexOf head to CoreCategoricalProgram.indexOf',
            scopeEnforcement:
                'delegate profile and active-slot validation to the existing ' +
                'typed program; text supplies no contextual-index semantics',
            ordinaryApplication:
                'all non-reserved spines continue through the sole apply path'
        },
        exactPositiveSource:
            'λ^fd a : E. s (indexOf a)',
        requiredDirectEquality: [
            'backend-neutral explicit Core',
            'inferred and expected type',
            'categorical.displayed-functor-weakening rule',
            'section-pullback and sigma-first-projection ownership'
        ],
        exactNegativeClasses: [
            'indexOf applied outside an active displayed callback slot',
            'indexOf under an unavailable program profile',
            'indexOf with zero or more than one argument',
            'indexOf of a closed or foreign term',
            'wrong displayed-functor source or target family'
        ],
        reviewerPreset: {
            id: 'displayed-functor-weakening',
            label: 'Displayed weakening',
            required: true,
            runner:
                'the same browser-safe text adapter and existing checker'
        },
        implementationFiles: [
            'src/v3_2/categorical_text.ts',
            'tests/v3_2_categorical_text_structural_tests.ts',
            'src/v3_2/browser_reviewer.ts',
            'tests/v3_2_browser_reviewer_tests.ts',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md'
        ],
        nonEffects: [
            'no new mathematical owner or categorical program method',
            'no new Core node, checker, evaluator, or runtime rule',
            'no external naturality or coherence premise',
            'no Lambdapi declaration, rule, profile, or production process',
            'no second parser, resolver, action table, or browser semantics',
            'no multi-binder, telescope, fibrePair, or 1C constructor syntax'
        ],
        followingRows: [
            'SYNTAX-PARITY-1B2-independent-siblings',
            'SYNTAX-PARITY-1B3-dependent-mixed-telescopes',
            'SYNTAX-PARITY-1C-remaining-mathematical-constructors',
            'SYNTAX-PARITY-GRADUATE-1'
        ]
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

export type CoreCategoricalTextStructuralAuditInput = typeof rawAudit;

export type CoreCategoricalTextStructuralAuditErrorCode =
    | 'TEXT_STRUCTURAL_PREREQUISITE_DRIFT'
    | 'TEXT_STRUCTURAL_MEASUREMENT_DRIFT'
    | 'TEXT_STRUCTURAL_SPLIT_DRIFT'
    | 'TEXT_STRUCTURAL_PROPOSAL_DRIFT'
    | 'TEXT_STRUCTURAL_BOUNDARY_DRIFT';

export class CoreCategoricalTextStructuralAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextStructuralAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalTextStructuralAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextStructuralAudit = (
    audit: CoreCategoricalTextStructuralAuditInput =
        CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1A-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.implementationCheckpoint !==
            '2e7cc3c44802a5218858ca6747e7591d3bfc4859'
    ) {
        throw new CoreCategoricalTextStructuralAuditError(
            'TEXT_STRUCTURAL_PREREQUISITE_DRIFT',
            'Structural text audit prerequisite changed'
        );
    }

    if (
        audit.measuredSeam.exactSource !==
            'λ^fd a : E. s (indexOf a)' ||
        audit.measuredSeam.currentTextFailure.code !==
            'UNKNOWN_IDENTIFIER' ||
        !sameData(
            audit.measuredSeam.directMethods,
            ['displayedFunctorLambda', 'apply', 'indexOf']
        )
    ) {
        throw new CoreCategoricalTextStructuralAuditError(
            'TEXT_STRUCTURAL_MEASUREMENT_DRIFT',
            'The measured contextual-index seam changed'
        );
    }

    if (
        !sameData(
            audit.oneBSplit.map(entry => entry.row),
            [
                'SYNTAX-PARITY-1B1',
                'SYNTAX-PARITY-1B2',
                'SYNTAX-PARITY-1B3'
            ]
        ) ||
        audit.oneBSplit[0]?.status !==
            'selected-non-self-authorizing-proposal'
    ) {
        throw new CoreCategoricalTextStructuralAuditError(
            'TEXT_STRUCTURAL_SPLIT_DRIFT',
            'The bounded 1B sequencing changed'
        );
    }

    if (
        audit.firstProposal.gate !==
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-02' ||
        audit.firstProposal.decision !==
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-002' ||
        audit.firstProposal.operation.sourceName !== 'indexOf' ||
        audit.firstProposal.operation.arity !== 1 ||
        audit.firstProposal.status !==
            'deeply-frozen-non-self-authorizing-proposal'
    ) {
        throw new CoreCategoricalTextStructuralAuditError(
            'TEXT_STRUCTURAL_PROPOSAL_DRIFT',
            'The bounded 1B1 proposal changed'
        );
    }

    if (
        Object.values(audit.semanticDelta).some(value => value !== 0)
    ) {
        throw new CoreCategoricalTextStructuralAuditError(
            'TEXT_STRUCTURAL_BOUNDARY_DRIFT',
            'Read-only structural text audit installed behavior'
        );
    }
};
