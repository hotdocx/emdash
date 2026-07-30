/**
 * Executable SYNTAX-PARITY-GRADUATE-0A audit.
 *
 * This artifact measures the post-1C3 text/direct-TypeScript boundary. It
 * classifies host declarations and observations as deliberately non-textual
 * and isolates one remaining direct-green mathematical parser gap: nested
 * ordinary functorial abstraction. It changes no runtime behavior.
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

const operationHeads = [
    'indexOf',
    'fibrePair',
    'composeCells',
    'fullAction',
    'cell',
    'naturality',
    'internalHomAction',
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
    'composeTransfd',
    'id',
    'compose',
    'pair',
    'map',
    'pi1',
    'pi2',
    'sectionCategory',
    'fibre',
    'sigma',
    'transfd',
    'functor',
    'product',
    'constantd',
    'functord',
    'sectionMotive',
    'sectionTarget',
    'productd',
    'pullback'
] as const;

const deliberatelyHostSide = {
    checkedDeclarationsAndAssumptions: [
        'category',
        'displayedFamily',
        'contravariantCategoryFamily',
        'section',
        'displayedFunctor',
        'displayedTransfor',
        'object',
        'functor',
        'hom',
        'homBoundary'
    ],
    contextFixtureHelpers: [
        'groupedSequentialContext',
        'groupedSequentialObject'
    ],
    observations: [
        'displayedTransforClassifierCompatibility',
        'displayedFunctorClassifierCompatibility',
        'inspect',
        'serializeCategory',
        'dependentTargetCategoryCompatibility',
        'compareCategories',
        'compareDisplayedFamilies',
        'compare',
        'compile'
    ]
} as const;

export const CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT = deepFreeze({
    revision: 'SYNTAX-PARITY-GRADUATE-0A-AUDIT-1',
    status: 'graduation-blocked-by-one-measured-parser-gap',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1C3-CATEGORICAL-TEXT-1',
        resultSyntaxCheckpoint:
            '126023e5ce8ab31f28730e1be508da11083084b4',
        resultSyntaxLedgerCheckpoint:
            '2cc66da'
    },
    currentTextEnvelope: {
        locatedNodeKinds: [
            'identifier',
            'left-associated-application',
            'intrinsic-mode-lambda'
        ],
        environmentKinds: [
            'category',
            'term',
            'displayed-family',
            'hom-boundary'
        ],
        resultAndExpectedKinds: [
            'term',
            'category',
            'displayed-family',
            'ordinary-functor',
            'dependent-section',
            'displayed-functor',
            'displayed-context-functor',
            'displayed-dependent-context-functor',
            'displayed-transfor'
        ],
        binderModes: ['f', 'n', 'fd', 'nd'],
        displayedContextShapes: [
            'one-independent-sibling-group',
            'one-genuine-edge-[1,1]',
            'mixed-telescope-[1,2,1]'
        ],
        operationHeads,
        operationHeadCount: 37,
        genericApplicationRoutes: 1,
        parserOrCheckerArchitectures: 1
    },
    publicMethodClassification: {
        originalAuditMethodCount: 68,
        deliberatelyHostSide,
        deliberatelyHostSideMethodCount: 21,
        mathematicalExpressionMethodCount: 47,
        normalizedAliases: [{
            method: 'substituteFamily',
            canonicalMethod: 'pullbackFamily',
            canonicalTextHead: 'pullback'
        }],
        contextHelperConclusion:
            'groupedSequentialContext/groupedSequentialObject construct ' +
            'host fixtures and observations; their reviewed mathematical ' +
            'binder presentations are the 1B2/1B3 text forms',
        observationConclusion:
            'inspection, comparison, serialization, compatibility, and ' +
            'compilation consume expressions and remain reviewer/API commands'
    },
    nonBlockingResiduals: [
        {
            id: 'compound-binder-annotation-sugar',
            classification: 'optional-presentation-convenience',
            reason:
                'annotations remain optional because checked expected ' +
                'contracts already supply every reviewed binder classifier'
        },
        {
            id: 'arbitrary-displayed-telescope-depth',
            classification: 'direct-semantic-capability-boundary',
            reason:
                'the direct displayedDependentContextLambda itself supports ' +
                'only the reviewed two- and four-binding shapes'
        },
        {
            id: 'arbitrary-pointwise-coherence-synthesis',
            classification: 'direct-semantic-capability-boundary',
            reason:
                'the direct API intentionally fails closed unless an ' +
                'internal functorial/natural factorization exists'
        },
        {
            id: 'mixed-nested-n-fd-nd-abstractions',
            classification: 'unreviewed-direct-semantic-boundary',
            reason:
                'there is no selected positive direct nested-classifier ' +
                'witness comparable to the ordinary exchange construction'
        }
    ],
    blockingGap: {
        id: 'nested-ordinary-functorial-abstraction',
        classification: 'direct-green-typed-resolver-seam',
        source: 'λ^f x : A. λ^f y : B. E y x',
        directMethod: 'lambda',
        directResultKind: 'functor',
        currentFailure: {
            phase: 'resolution',
            code: 'UNSUPPORTED_NESTED_ABSTRACTION',
            innerStartColumn: 12
        },
        directEvidence: [
            'src/v3_2/categorical_bracket_demo.ts exchange example',
            'tests/v3_2_categorical_bracket_tests.ts nested curry evidence'
        ],
        conclusion:
            'graduating while retaining this failure would contradict ' +
            'parity with a reviewed mathematical direct-TypeScript example'
    },
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-09',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-009',
        row: 'SYNTAX-PARITY-1D1',
        status: 'deeply-frozen-non-self-authorizing-correction-proposal',
        objective:
            'close the sole measured direct-green parser gap before syntax ' +
            'graduation',
        contract:
            'add an optional recursively typed ordinary-functor ' +
            'bodyExpected contract to the existing ordinary-functor ' +
            'expectation',
        lowering:
            'when an ordinary lambda body is another lambda, resolve it ' +
            'through the existing root-lambda dispatcher using bodyExpected; ' +
            'the outer CoreCategoricalProgram.lambda validates that the ' +
            'inner classifier equals its target category',
        exactPositiveSource:
            'λ^f x : A. λ^f y : B. E y x',
        recursiveDepth:
            'finite depth described explicitly by the recursive expected tree',
        exactNegativeClasses: [
            'nested lambda without bodyExpected',
            'bodyExpected supplied for a non-lambda body',
            'wrong inner mode',
            'wrong inner source annotation',
            'inner functor with target incompatible with the outer target',
            'foreign category or term',
            'escaped slot or unsupported bracket body'
        ],
        nonEffects: [
            'no new token, located node, grammar production, or parser dependency',
            'no category-expression decomposition or inference heuristic',
            'no new mathematical owner or categorical program method',
            'no new Core/checker/evaluator/runtime/proof rule',
            'no nested n, fd, nd, arbitrary displayed context, or coherence synthesis',
            'no Lambdapi, browser preset, book, scale, or publication change'
        ]
    }
} as const);

export type CoreCategoricalTextGraduationAudit =
    typeof CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT;

export type CoreCategoricalTextGraduationAuditErrorCode =
    | 'GRADUATION_PREREQUISITE_DRIFT'
    | 'GRADUATION_HEAD_DRIFT'
    | 'GRADUATION_HOST_CLASSIFICATION_DRIFT'
    | 'GRADUATION_GAP_DRIFT'
    | 'GRADUATION_PROPOSAL_DRIFT';

export class CoreCategoricalTextGraduationAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextGraduationAuditErrorCode,
        detail: string
    ) {
        super(`${code}: ${detail}`);
        this.name = 'CoreCategoricalTextGraduationAuditError';
    }
}

const sameJson = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreCategoricalTextGraduationAudit(
    audit: CoreCategoricalTextGraduationAudit =
        CORE_CATEGORICAL_TEXT_GRADUATION_AUDIT
): CoreCategoricalTextGraduationAudit {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1C3-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.resultSyntaxCheckpoint !==
            '126023e5ce8ab31f28730e1be508da11083084b4'
    ) {
        throw new CoreCategoricalTextGraduationAuditError(
            'GRADUATION_PREREQUISITE_DRIFT',
            'The graduated input revision or checkpoint changed'
        );
    }
    if (
        audit.currentTextEnvelope.operationHeadCount !== 37 ||
        !sameJson(
            audit.currentTextEnvelope.operationHeads,
            operationHeads
        )
    ) {
        throw new CoreCategoricalTextGraduationAuditError(
            'GRADUATION_HEAD_DRIFT',
            'The exact post-1C3 operation-head inventory changed'
        );
    }
    if (
        audit.publicMethodClassification
            .deliberatelyHostSideMethodCount !== 21 ||
        !sameJson(
            audit.publicMethodClassification.deliberatelyHostSide,
            deliberatelyHostSide
        )
    ) {
        throw new CoreCategoricalTextGraduationAuditError(
            'GRADUATION_HOST_CLASSIFICATION_DRIFT',
            'The deliberate host/expression boundary changed'
        );
    }
    if (
        audit.blockingGap.id !==
            'nested-ordinary-functorial-abstraction' ||
        audit.blockingGap.currentFailure.code !==
            'UNSUPPORTED_NESTED_ABSTRACTION'
    ) {
        throw new CoreCategoricalTextGraduationAuditError(
            'GRADUATION_GAP_DRIFT',
            'The measured direct-green nested gap changed'
        );
    }
    if (
        audit.proposal.row !== 'SYNTAX-PARITY-1D1' ||
        audit.proposal.contract !==
            'add an optional recursively typed ordinary-functor ' +
            'bodyExpected contract to the existing ordinary-functor ' +
            'expectation'
    ) {
        throw new CoreCategoricalTextGraduationAuditError(
            'GRADUATION_PROPOSAL_DRIFT',
            'The bounded nested-ordinary correction changed'
        );
    }
    return audit;
}
