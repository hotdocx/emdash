/**
 * Executable SYNTAX-PARITY-1B2 independent-sibling text audit.
 *
 * This audit freezes one bounded presentation proposal over the already
 * implemented displayed contextual compiler. It changes no parser, resolver,
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

const rawAudit = {
    revision: 'SYNTAX-PARITY-1B2-SIBLING-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-PARITY-1B1-CATEGORICAL-TEXT-1',
        implementationCheckpoint:
            '9f663555a1edbedcb99e97f1271154ff36913f05'
    },
    measuredSeam: {
        capability: 'independent-displayed-sibling-abstraction',
        exactSource:
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)',
        currentTextFailure: {
            phase: 'parsing',
            code: 'UNEXPECTED_TOKEN',
            startColumn: 6,
            endColumn: 7,
            detail: "Expected an identifier, found '('"
        },
        directMethods: [
            'displayedContextLambda',
            'fibrePair',
            'apply'
        ],
        directRule: 'categorical.displayed-context-bracket',
        directPrerequisites: [
            'displayed-product-left-projection',
            'displayed-product-right-projection',
            'generic-category-composition',
            'displayed-product-pair'
        ],
        authority:
            'the active transparent fibrewise product plus existing fixed-' +
            'base projection/pairing owners; no Product_catd head',
        conclusion:
            'presentation-only multi-binding seam; object, base-arrow, and ' +
            'higher coherence remain owned by the existing direct compiler'
    },
    notationDecision: {
        selected:
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)',
        annotationFree:
            'λ^fd (b, c). fibrePair (FF b) (GG c)',
        separatorMeaning: {
            comma:
                'independent siblings at one dependency level',
            semicolon:
                'successive dependency levels, reserved for ' +
                'SYNTAX-PARITY-1B3'
        },
        rejectedAlternatives: [
            {
                syntax: 'λ^fd b. λ^fd c. body',
                reason:
                    'nested unary displayed abstractions do not represent ' +
                    'the direct API sibling block or its fibrewise product ' +
                    'context'
            },
            {
                syntax:
                    'displayedContextLambda((b:B,c:C), body)',
                reason:
                    'method-call spelling exposes the host API instead of ' +
                    'the mathematical binder while adding no capability'
            },
            {
                syntax: 'infer sibling families by decomposing a Core term',
                reason:
                    'the text adapter must use immutable expected typing ' +
                    'information, not inspect private product provenance or ' +
                    'guess a decomposition'
            }
        ]
    },
    proposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-03',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-003',
        row: 'SYNTAX-PARITY-1B2',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'present one finite independent displayed sibling group and ' +
            'typed fibre pairing through the existing recursive compiler',
        privateLocatedDesign: {
            nodeKindsAdded: 0,
            strategy:
                'generalize the private lambda payload to immutable ordered ' +
                'binding groups; existing unary syntax is a singleton group',
            implementedGrammar:
                'one parenthesized comma-separated group with at least two ' +
                'portable names and independently optional annotations',
            futureCompatibility:
                'retain the group shape so 1B3 may add semicolon-separated ' +
                'dependency levels without another surface type theory',
            exportedRawSyntax: false
        },
        expectedContract: {
            kind: 'displayed-context-functor',
            orderedSources:
                'one expected displayed family per source binding',
            target: 'one expected displayed target family',
            annotations:
                'optional and checked positionally against orderedSources',
            ownership:
                'displayedContextLambda validates count, common base, target ' +
                'base, and independent sibling dependency structure'
        },
        resolverDesign: {
            binderMode: 'fd',
            abstractionMethod: 'displayedContextLambda',
            callback:
                'extend one immutable environment with all sibling tokens ' +
                'and resolve the body recursively exactly once',
            operation: {
                sourceName: 'fibrePair',
                arity: 2,
                directMethod: 'fibrePair'
            },
            application:
                'all non-reserved application spines continue through the ' +
                'sole CoreCategoricalProgram.apply ladder',
            factorization:
                'delegate slot, closed displayed application, and typed-pair ' +
                'factorization to the existing contextual compiler'
        },
        exactPositiveSources: [
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)',
            'λ^fd (b, c). fibrePair (FF b) (GG c)'
        ],
        requiredDirectEquality: [
            'backend-neutral explicit Core',
            'inferred and expected displayed-functor classifier',
            'categorical.displayed-context-bracket lowering trace',
            'ordered binding names and source families',
            'object and internalized-arrow observations',
            'displayed projection, composition, and pairing ownership'
        ],
        exactNegativeClasses: [
            'empty, singleton, malformed, or trailing-comma sibling group',
            'duplicate sibling names',
            'expected source-family count mismatch',
            'wrong-kind or wrong-family optional annotation',
            'source siblings or target over different bases',
            'wrong expected kind or binder mode',
            'fibrePair with the wrong arity or outside an active context',
            'fibrePair branches over different hidden base slots',
            'semicolon-dependent telescope withheld to 1B3',
            'nested abstraction or unsupported contextual body'
        ],
        reviewerPreset: {
            id: 'displayed-sibling-pairing',
            label: 'Displayed sibling pairing',
            required: true,
            runner:
                'the same browser-safe text adapter and existing checker'
        },
        implementationFiles: [
            'src/v3_2/categorical_text.ts',
            'tests/v3_2_categorical_text_sibling_tests.ts',
            'src/v3_2/browser_reviewer.ts',
            'tests/v3_2_browser_reviewer_tests.ts',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md'
        ],
        nonEffects: [
            'no new mathematical owner, Product_catd head, or kernel rule',
            'no new categorical program method or direct factorization case',
            'no new Core node, checker, evaluator, or runtime/proof rule',
            'no external naturality or coherence premise',
            'no Lambdapi declaration, rule, profile, or production process',
            'no second parser, resolver, action table, or browser semantics',
            'no semicolon telescope, genuine dependency edge, or 1C syntax'
        ],
        followingRows: [
            'SYNTAX-PARITY-1B3-dependent-mixed-telescopes',
            'SYNTAX-PARITY-1C-remaining-mathematical-constructors',
            'SYNTAX-PARITY-GRADUATE-1',
            'BOOK-DELTA-0A'
        ]
    },
    proposedImplementationDelta: {
        privateLocatedNodeKinds: 0,
        privateBinderGroupForms: 1,
        expectedContractVariants: 1,
        textResolverRoutes: 1,
        fixedOperationSpines: 1,
        programMethods: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserPresets: 1
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

export type CoreCategoricalTextSiblingAuditInput = typeof rawAudit;

export type CoreCategoricalTextSiblingAuditErrorCode =
    | 'TEXT_SIBLING_PREREQUISITE_DRIFT'
    | 'TEXT_SIBLING_MEASUREMENT_DRIFT'
    | 'TEXT_SIBLING_NOTATION_DRIFT'
    | 'TEXT_SIBLING_PROPOSAL_DRIFT'
    | 'TEXT_SIBLING_BOUNDARY_DRIFT';

export class CoreCategoricalTextSiblingAuditError extends Error {
    constructor(
        public readonly code: CoreCategoricalTextSiblingAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalTextSiblingAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_SIBLING_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextSiblingAudit = (
    audit: CoreCategoricalTextSiblingAuditInput =
        CORE_CATEGORICAL_TEXT_SIBLING_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-PARITY-1B1-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.implementationCheckpoint !==
            '9f663555a1edbedcb99e97f1271154ff36913f05'
    ) {
        throw new CoreCategoricalTextSiblingAuditError(
            'TEXT_SIBLING_PREREQUISITE_DRIFT',
            'Independent-sibling text prerequisite changed'
        );
    }

    if (
        audit.measuredSeam.exactSource !==
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)' ||
        audit.measuredSeam.currentTextFailure.code !==
            'UNEXPECTED_TOKEN' ||
        !sameData(
            audit.measuredSeam.directMethods,
            ['displayedContextLambda', 'fibrePair', 'apply']
        )
    ) {
        throw new CoreCategoricalTextSiblingAuditError(
            'TEXT_SIBLING_MEASUREMENT_DRIFT',
            'The measured independent-sibling seam changed'
        );
    }

    if (
        audit.notationDecision.separatorMeaning.comma !==
            'independent siblings at one dependency level' ||
        !audit.notationDecision.separatorMeaning.semicolon.includes(
            'SYNTAX-PARITY-1B3'
        ) ||
        audit.notationDecision.rejectedAlternatives.length !== 3
    ) {
        throw new CoreCategoricalTextSiblingAuditError(
            'TEXT_SIBLING_NOTATION_DRIFT',
            'The selected sibling/dependency notation boundary changed'
        );
    }

    if (
        audit.proposal.gate !==
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-03' ||
        audit.proposal.decision !==
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-003' ||
        audit.proposal.row !== 'SYNTAX-PARITY-1B2' ||
        audit.proposal.status !==
            'deeply-frozen-non-self-authorizing-proposal' ||
        audit.proposal.expectedContract.kind !==
            'displayed-context-functor' ||
        audit.proposal.resolverDesign.operation.sourceName !==
            'fibrePair' ||
        audit.proposal.resolverDesign.operation.arity !== 2
    ) {
        throw new CoreCategoricalTextSiblingAuditError(
            'TEXT_SIBLING_PROPOSAL_DRIFT',
            'The bounded 1B2 proposal changed'
        );
    }

    if (
        Object.values(audit.semanticDelta).some(value => value !== 0)
    ) {
        throw new CoreCategoricalTextSiblingAuditError(
            'TEXT_SIBLING_BOUNDARY_DRIFT',
            'Read-only sibling text audit installed behavior'
        );
    }
};
