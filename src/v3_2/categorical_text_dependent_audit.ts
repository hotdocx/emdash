/**
 * Executable SYNTAX-PARITY-1B3 dependent-context text audit.
 *
 * This freezes one bounded presentation proposal over the already
 * implemented two-level and `a; b,c; d` displayed contextual compilers. It
 * changes no parser, resolver, categorical program, Core, checker, runtime,
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

const rawAudit = {
    revision: 'SYNTAX-PARITY-1B3-DEPENDENT-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1B2-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            'ba34771074363f4c5b33814269b8822d4d2362bb',
        directProfiles: [
            'fibred-displayed-chain-1',
            'fibred-displayed-chain-2a'
        ]
    },
    measuredSeam: {
        capability:
            'genuine-and-mixed-dependent-displayed-context-abstraction',
        exactSources: {
            edge:
                'λ^fd (a : A; b : B). a',
            mixed:
                'λ^fd (a : A; b : B, c : C; d : D). fibrePair b c'
        },
        currentTextFailure: {
            phase: 'parsing',
            code: 'UNEXPECTED_TOKEN',
            startColumn: 12,
            endColumn: 13,
            detail:
                'Semicolon dependency levels require the later ' +
                'SYNTAX-PARITY-1B3 profile'
        },
        directMethod: 'displayedDependentContextLambda',
        recursiveMethods: [
            'apply',
            'fibrePair',
            'indexOf'
        ],
        directRules: {
            edge: 'categorical.displayed-dependent-context-bracket',
            mixed:
                'categorical.displayed-mixed-dependent-context-bracket'
        },
        exactDirectShapes: [
            {
                groupSizes: [1, 1],
                meaning: 'one genuine displayed dependency edge'
            },
            {
                groupSizes: [1, 2, 1],
                meaning:
                    'two dependency transitions with independent middle ' +
                    'siblings'
            }
        ],
        ownership:
            'family bases and source order drive the existing dependency ' +
            'planner; Sigma, pullback, product, pairing, and internalized-' +
            'cell owners remain inside the direct compiler',
        conclusion:
            'semicolon presentation and grouped expected-family seam; no ' +
            'missing dependent-context algorithm or categorical owner'
    },
    notationDecision: {
        separatorMeaning: {
            comma:
                'independent siblings at one dependency level',
            semicolon:
                'successive displayed dependency levels'
        },
        exactAnnotated: {
            edge:
                'λ^fd (a : A; b : B). a',
            mixed:
                'λ^fd (a : A; b : B, c : C; d : D). fibrePair b c'
        },
        exactAnnotationFree: {
            edge:
                'λ^fd (a; b). a',
            mixed:
                'λ^fd (a; b, c; d). fibrePair b c'
        },
        interpretation:
            'semicolon/comma structure presents dependency levels; the ' +
            'existing direct program still derives and validates every ' +
            'dependency edge from the ordered family bases',
        rejectedAlternatives: [
            {
                syntax:
                    'λ^fd a. λ^fd b. body',
                reason:
                    'nested unary displayed functors do not present the ' +
                    'existing dependent-context construction or its total ' +
                    'base'
            },
            {
                syntax:
                    'λ^fd (a : A, b : B). body',
                reason:
                    'a comma would falsely assert that a and b are ' +
                    'independent siblings'
            },
            {
                syntax:
                    'arbitrary semicolon/comma dependency graph',
                reason:
                    'the direct TypeScript method owns only group sizes ' +
                    '[1,1] and [1,2,1]; arbitrary depth remains a semantic ' +
                    'capability absence'
            },
            {
                syntax:
                    'dependency flags supplied by the text frontend',
                reason:
                    'dependency is checked from family bases and source ' +
                    'order, never asserted by an unchecked flag'
            }
        ]
    },
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-04',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-004',
        row: 'SYNTAX-PARITY-1B3',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'present exactly the existing two-level genuine edge and ' +
            'three-level mixed displayed telescope through the same ' +
            'recursive text adapter',
        privateLocatedDesign: {
            nodeKindsAdded: 0,
            strategy:
                'activate semicolon-separated immutable bindingGroups in ' +
                'the existing private lambda payload',
            parser:
                'inside one parenthesized binder, commas extend the current ' +
                'dependency level and semicolons begin the next nonempty ' +
                'level',
            names:
                'portable and unique across the complete telescope',
            exactGroupSizes: [
                [1, 1],
                [1, 2, 1]
            ],
            arbitraryDepth: false,
            exportedRawSyntax: false
        },
        expectedContract: {
            kind: 'displayed-dependent-context-functor',
            sourceGroups:
                'one immutable expected displayed-family group per parsed ' +
                'dependency level',
            target: 'one expected displayed target family',
            annotations:
                'optional and checked positionally within sourceGroups',
            noFamilyInference:
                'annotation omission uses expected families; the resolver ' +
                'does not synthesize or decompose a dependent family term'
        },
        resolverDesign: {
            binderMode: 'fd',
            abstractionMethod: 'displayedDependentContextLambda',
            bindings:
                'check exact group cardinality, flatten in source order, ' +
                'and pass only name/family pairs to the existing method',
            callback:
                'extend one immutable environment with every returned token ' +
                'and resolve the body recursively exactly once',
            operations:
                'retain the existing exact indexOf, fibrePair, composeCells, ' +
                'and sole generic apply routes',
            dependency:
                'the text shape selects only a supported presentation; the ' +
                'direct program validates bases, dependency plan, target, ' +
                'slots, and internal factorization'
        },
        positives: [
            'annotated and annotation-free two-level edge',
            'annotated and annotation-free a; b,c; d mixed telescope',
            'outer, middle-sibling, deepest, recursive application, and ' +
                'typed-pair body occurrences',
            'direct/text explicit-Core, classifier, trace, binding/group, ' +
                'object, and applicable internalized-arrow equality'
        ],
        exactNegativeClasses: [
            'empty dependency level, trailing semicolon, or malformed group',
            'duplicate names across dependency levels',
            'wrong group count or group cardinality',
            'wrong-kind or wrong-family optional annotation',
            'wrong binder mode or expected-contract kind',
            'predecessor profile or unavailable four-binding mixed shape',
            'wrong middle, deepest, or target family base',
            'reordered siblings or unsupported three-binding/deeper shape',
            'escaped or foreign slots and unsupported contextual body',
            'arbitrary nested abstraction or general dependent-family syntax'
        ],
        reviewerPreset: {
            id: 'displayed-mixed-telescope',
            label: 'Displayed mixed telescope',
            required: true,
            source:
                'λ^fd (a : A; b : B, c : C; d : D). fibrePair b c',
            runner:
                'the same browser-safe text adapter and existing checker'
        },
        nonEffects: [
            'no new mathematical owner, dependency planner, or kernel rule',
            'no new categorical program method or contextual factorization ' +
                'case',
            'no new Core node, checker, evaluator, runtime, or proof branch',
            'no external equality, naturality, functoriality, or coherence ' +
                'premise',
            'no arbitrary-depth telescope, general dependent family ' +
                'expression, or nested abstraction',
            'no Lambdapi declaration/rule, semantic profile, or transfer ' +
                'input',
            'no second parser, resolver, checker, or browser semantics'
        ],
        followingRows: [
            'SYNTAX-PARITY-1C-remaining-mathematical-constructors',
            'SYNTAX-PARITY-GRADUATE-1',
            'BOOK-DELTA-0A'
        ]
    },
    proposedImplementationDelta: {
        privateLocatedNodeKinds: 0,
        privateDependencySeparators: 1,
        expectedContractVariants: 1,
        textResolverRoutes: 1,
        programMethods: 0,
        contextualFactorizationCases: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 1
    },
    semanticDelta: {
        parserNodeKinds: 0,
        textResolverBranches: 0,
        programMethods: 0,
        contextualFactorizationCases: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 0
    }
} as const;

export type CoreCategoricalTextDependentAuditInput = typeof rawAudit;

export type CoreCategoricalTextDependentAuditErrorCode =
    | 'TEXT_DEPENDENT_PREREQUISITE_DRIFT'
    | 'TEXT_DEPENDENT_MEASUREMENT_DRIFT'
    | 'TEXT_DEPENDENT_NOTATION_DRIFT'
    | 'TEXT_DEPENDENT_PROPOSAL_DRIFT'
    | 'TEXT_DEPENDENT_BOUNDARY_DRIFT';

export class CoreCategoricalTextDependentAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextDependentAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalTextDependentAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextDependentAudit = (
    audit: CoreCategoricalTextDependentAuditInput =
        CORE_CATEGORICAL_TEXT_DEPENDENT_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1B2-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.implementationCheckpoint !==
            'ba34771074363f4c5b33814269b8822d4d2362bb'
    ) {
        throw new CoreCategoricalTextDependentAuditError(
            'TEXT_DEPENDENT_PREREQUISITE_DRIFT',
            'Dependent-context text prerequisite changed'
        );
    }

    if (
        audit.measuredSeam.currentTextFailure.code !==
            'UNEXPECTED_TOKEN' ||
        audit.measuredSeam.currentTextFailure.startColumn !== 12 ||
        audit.measuredSeam.directMethod !==
            'displayedDependentContextLambda' ||
        !sameData(
            audit.measuredSeam.exactDirectShapes.map(
                shape => shape.groupSizes
            ),
            [[1, 1], [1, 2, 1]]
        )
    ) {
        throw new CoreCategoricalTextDependentAuditError(
            'TEXT_DEPENDENT_MEASUREMENT_DRIFT',
            'The measured dependent-context seam changed'
        );
    }

    if (
        audit.notationDecision.separatorMeaning.comma !==
            'independent siblings at one dependency level' ||
        audit.notationDecision.separatorMeaning.semicolon !==
            'successive displayed dependency levels' ||
        audit.notationDecision.exactAnnotated.mixed !==
            'λ^fd (a : A; b : B, c : C; d : D). fibrePair b c'
    ) {
        throw new CoreCategoricalTextDependentAuditError(
            'TEXT_DEPENDENT_NOTATION_DRIFT',
            'Dependent-context separator semantics changed'
        );
    }

    if (
        audit.proposal.gate !==
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-04' ||
        audit.proposal.decision !==
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-004' ||
        audit.proposal.expectedContract.kind !==
            'displayed-dependent-context-functor' ||
        audit.proposal.resolverDesign.abstractionMethod !==
            'displayedDependentContextLambda' ||
        audit.proposal.reviewerPreset.id !==
            'displayed-mixed-telescope'
    ) {
        throw new CoreCategoricalTextDependentAuditError(
            'TEXT_DEPENDENT_PROPOSAL_DRIFT',
            'The bounded dependent-context proposal changed'
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
        throw new CoreCategoricalTextDependentAuditError(
            'TEXT_DEPENDENT_BOUNDARY_DRIFT',
            'The audit or proposal crossed its zero-semantic-delta boundary'
        );
    }
};
