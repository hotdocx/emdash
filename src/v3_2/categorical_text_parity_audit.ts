/**
 * Executable SYNTAX-PARITY-0A inventory.
 *
 * This audit classifies the complete public CoreCategoricalProgram method
 * surface against the current text adapter. It changes no parser, resolver,
 * categorical program, Core owner, checker, evaluator, or browser behavior.
 */

import {
    CoreCategoricalProgram
} from './categorical_program';

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

type CoreCategoricalProgramPublicMethodName = {
    [Name in keyof CoreCategoricalProgram]-?:
        CoreCategoricalProgram[Name] extends
            (...arguments_: never[]) => unknown
            ? Name
            : never;
}[keyof CoreCategoricalProgram] & string;

export type CoreCategoricalTextParityClassification =
    | 'already-text-complete'
    | 'mechanical-syntax-route'
    | 'typed-resolver-seam'
    | 'semantic-capability-absent'
    | 'deliberately-non-textual-host-behavior';

export interface CoreCategoricalTextParityWitness {
    readonly sourceOrOperation: string;
    readonly directEvidence: string;
    readonly requiredResult: string;
}

export interface CoreCategoricalTextParityCapability {
    readonly id: string;
    readonly apiMethods:
        readonly CoreCategoricalProgramPublicMethodName[];
    readonly profile: string;
    readonly classifierContract: string;
    readonly scopedBindings: string;
    readonly dependencyAndVariance: string;
    readonly actionOwnership: string;
    readonly recursiveBodyGrammar: string;
    readonly proposedText: string;
    readonly locatedSyntax:
        | 'sufficient'
        | 'requires-typed-expected-contract'
        | 'requires-structural-form'
        | 'not-applicable';
    readonly classification:
        CoreCategoricalTextParityClassification;
    readonly positive: CoreCategoricalTextParityWitness;
    readonly negative: CoreCategoricalTextParityWitness;
    readonly firstImplementationRow:
        | 'already'
        | 'SYNTAX-PARITY-1A'
        | 'SYNTAX-PARITY-1B'
        | 'SYNTAX-PARITY-1C'
        | 'not-textual'
        | 'semantic-boundary';
}

const capabilities = [
    {
        id: 'closed-name-environment',
        apiMethods: [
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
        profile: 'the profile that owns the supplied closed value',
        classifierContract:
            'Host construction creates checked closed categories, families, ' +
            'terms, and Hom boundaries; text resolves immutable names.',
        scopedBindings:
            'No text binder; occurrences use category, displayed-family, ' +
            'term, or Hom-boundary environment entries.',
        dependencyAndVariance:
            'Retained by each checked value rather than reconstructed from ' +
            'its textual name.',
        actionOwnership:
            'The direct constructors and existing Core classifiers own all ' +
            'object/arrow/coherence data.',
        recursiveBodyGrammar: 'identifier occurrence',
        proposedText:
            'A, E, F, alpha, x, and p name host-supplied checked values; ' +
            'text does not declare new global owners.',
        locatedSyntax: 'sufficient',
        classification: 'deliberately-non-textual-host-behavior',
        positive: {
            sourceOrOperation: 'F x and F p',
            directEvidence:
                'tests/v3_2_categorical_text_tests.ts host environment',
            requiredResult:
                'Text occurrences resolve to the object-identical checked ' +
                'values supplied by the direct TypeScript program.'
        },
        negative: {
            sourceOrOperation: 'unknown or wrong-kind identifier',
            directEvidence:
                'SYNTAX-1A UNKNOWN_IDENTIFIER/EXPECTED_TERM tests',
            requiredResult:
                'Reject at the exact identifier span without creating a ' +
                'declaration or hole.'
        },
        firstImplementationRow: 'not-textual'
    },
    {
        id: 'derived-category-and-family-constructors',
        apiMethods: [
            'oppositeCategory',
            'displayedCategoryCategory',
            'constantDisplayedFamily',
            'oppositeDisplayedFamily',
            'displayedFunctorFamily',
            'mixedDisplayedFunctorFamily',
            'mixedDisplayedHomFamily',
            'mixedDisplayedTransforFamily',
            'dependentSectionMotive',
            'dependentSectionTarget',
            'dependentSectionCategoryAt',
            'displayedProduct',
            'fibre',
            'totalCategory',
            'displayedFunctorCategory',
            'displayedTransforCategory',
            'functorCategory',
            'homCategory',
            'productCategory',
            'pullbackFamily',
            'substituteFamily'
        ],
        profile: 'constructor-specific reviewed root profile',
        classifierContract:
            'Arguments are checked categories, displayed families, or ' +
            'functors; results may be categories or displayed families.',
        scopedBindings:
            'No new variable, but displayed-family results require a typed ' +
            'text value kind beyond the current category/term union.',
        dependencyAndVariance:
            'Includes ordinary products/functor/Hom categories, displayed ' +
            'pullback, mixed variance, and dependent-section targets.',
        actionOwnership:
            'Each direct method delegates to the existing internalized ' +
            'owner and profile runtime.',
        recursiveBodyGrammar:
            'finite constructor argument list over recursively resolved names',
        proposedText:
            'Functor(A,B), Hom(C,x,y), Product(A,B), E[x], Sigma(E), ' +
            'Productd(E,D), and pullback(E,F); final notation remains ' +
            'separately reviewable.',
        locatedSyntax: 'requires-structural-form',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'Productd(E,D) and pullback(E,F)',
            directEvidence:
                'fibred-product/dependent-target direct-program tests',
            requiredResult:
                'Text and direct constructors yield equal serialized ' +
                'categories/families under the same profile.'
        },
        negative: {
            sourceOrOperation: 'Productd(E,D) over different bases',
            directEvidence: 'CoreCategoricalProgram DISPLAYED_BASE_MISMATCH',
            requiredResult:
                'Preserve the direct typed rejection; never coerce families.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1C'
    },
    {
        id: 'ordinary-structural-constructors',
        apiMethods: [
            'productLeftProjection',
            'productRightProjection',
            'composeFunctors',
            'identityFunctor',
            'functorPair',
            'productMap'
        ],
        profile: 'ordinary reviewed structural basis',
        classifierContract:
            'Typed ordinary categories and functors determine every source ' +
            'and target.',
        scopedBindings: 'No new binding; arguments resolve recursively.',
        dependencyAndVariance: 'ordinary covariant categorical structure',
        actionOwnership:
            'Existing identity, composition, product, projection, pairing, ' +
            'and map owners.',
        recursiveBodyGrammar: 'finite constructor/application spine',
        proposedText:
            'id(A), compose(G,F), pair(F,G), map(F,G), pi1(A,B), pi2(A,B)',
        locatedSyntax: 'requires-structural-form',
        classification: 'mechanical-syntax-route',
        positive: {
            sourceOrOperation: 'compose(G,F)',
            directEvidence: 'ordinary structural and bracket tests',
            requiredResult:
                'Equal explicit Core and inferred functor classifier.'
        },
        negative: {
            sourceOrOperation: 'compose(F,G) with reversed endpoints',
            directEvidence: 'direct composition classifier rejection',
            requiredResult: 'Reject the exact constructor span.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1C'
    },
    {
        id: 'displayed-and-fibred-structural-constructors',
        apiMethods: [
            'displayedProductLeftProjection',
            'displayedProductRightProjection',
            'displayedProductPair',
            'displayedProductSwap',
            'displayedProductDiagonal',
            'displayedFunctorFullAction',
            'displayedFunctorInternalCell',
            'displayedInternalHomEndpointFamily',
            'sigmaProjection',
            'pullbackDisplayedFunctor',
            'dependentPair',
            'familyTransport',
            'sigmaArrow',
            'pullbackTotal',
            'indexOf'
        ],
        profile: 'fibred-structure through displayed-ND-higher profiles',
        classifierContract:
            'Families, base objects/arrows, fibre objects/arrows, and ' +
            'expected higher-action classifiers remain explicit and typed.',
        scopedBindings:
            'Some operations consume active displayed slots or recover their ' +
            'hidden base index.',
        dependencyAndVariance:
            'displayed dependency with covariant, contravariant, and ' +
            'internalized arrow/higher action selected by classifiers',
        actionOwnership:
            'Existing Productd/Sigma/pullback/transport/internal-Hom owners; ' +
            'no external naturality equation.',
        recursiveBodyGrammar:
            'finite typed constructor forms over terms, families, and slots',
        proposedText:
            'fibrePair, sigmaPair, transport, pullback, indexOf, and explicit ' +
            'higher-action forms before later notation consolidation',
        locatedSyntax: 'requires-structural-form',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'fibrePair b c and transport(E,p)',
            directEvidence:
                'fibred-structure/weaken-reindex/ND-higher tests',
            requiredResult:
                'Text routes call the same methods and preserve object and ' +
                'internalized-arrow observations.'
        },
        negative: {
            sourceOrOperation: 'indexOf outside an active displayed slot',
            directEvidence: 'direct profile/scope rejection corpus',
            requiredResult:
                'Fail closed; do not fabricate a base variable.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1B'
    },
    {
        id: 'grouped-and-sequential-context-constructors',
        apiMethods: [
            'groupedSequentialContext',
            'groupedSequentialObject'
        ],
        profile: 'fibred-grouped-sequential-1 and descendants',
        classifierContract:
            'A base category plus an ordered family dependency graph ' +
            'determines sequential Sigma/pullback and grouped presentations.',
        scopedBindings:
            'Introduces an ordered telescope with independent sibling groups.',
        dependencyAndVariance:
            'displayed dependency; independent siblings share a base while ' +
            'later families may depend on prior total contexts',
        actionOwnership:
            'Existing Sigma, pullback, fibrewise product, projection, and ' +
            'comparison mechanisms.',
        recursiveBodyGrammar:
            'explicit finite telescope and recursively resolved object tuple',
        proposedText:
            'an explicit telescope/context form; no claim that nested unary ' +
            'lambdas encode every grouped presentation',
        locatedSyntax: 'requires-structural-form',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'a; b,c; d',
            directEvidence:
                'displayed-chain-2A grouped/dependent context tests',
            requiredResult:
                'Preserve the direct dependency plan and both object/arrow ' +
                'observations.'
        },
        negative: {
            sourceOrOperation: 'a family referencing an unavailable slot',
            directEvidence: 'context-dependency planner negative corpus',
            requiredResult: 'Reject at the family/telescope span.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1B'
    },
    {
        id: 'typed-application-and-action-ladder',
        apiMethods: [
            'apply',
            'displayedTransforComponent',
            'displayedTransforPoint',
            'displayedTransforNaturality',
            'displayedInternalHom',
            'displayedTransforInternalHomAction'
        ],
        profile: 'subject/action-specific reviewed profile',
        classifierContract:
            'Subject, argument, expected shape, and classifier select the ' +
            'existing fapp/tapp/displayed/higher action.',
        scopedBindings:
            'Applications introduce no binding but may consume bound tokens.',
        dependencyAndVariance:
            'ordinary/displayed and object/arrow/transfor/higher, including ' +
            'contravariance already represented in classifiers',
        actionOwnership:
            'CoreCategoricalProgram.apply and the internalized rich action ' +
            'constructors; never a text-owned owner table.',
        recursiveBodyGrammar:
            'left-associated application with recursively typed subterms',
        proposedText:
            'whitespace application; exact expected shape propagates only ' +
            'where the classifier does not uniquely select an action',
        locatedSyntax: 'requires-typed-expected-contract',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'F x, F p, eta x, eta x u, eta p u',
            directEvidence:
                'categorical-text, fibred-transfd, and ND-higher tests',
            requiredResult:
                'Equal explicit Core for every promoted object/arrow/higher ' +
                'route.'
        },
        negative: {
            sourceOrOperation: 'an ambiguous or wrong-dimensional action',
            directEvidence:
                'MISSING_EXPECTED_ACTION_SHAPE and classifier negatives',
            requiredResult:
                'Require expected information or reject; never guess.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1A'
    },
    {
        id: 'ordinary-functorial-abstraction',
        apiMethods: ['lambda'],
        profile: 'reviewed-usability-2a1 and descendants',
        classifierContract:
            'Expected ordinary source/target categories plus a ^f binder.',
        scopedBindings:
            'One hygienic object slot with recursive zero/one/many occurrence.',
        dependencyAndVariance: 'ordinary covariant functorial abstraction',
        actionOwnership:
            'Existing bracket compiler generates weakening, exchange, ' +
            'contraction, pairing, evaluation, and composition.',
        recursiveBodyGrammar:
            'identifiers and arbitrary nested supported applications',
        proposedText: 'λ^f x [: A]. body',
        locatedSyntax: 'sufficient',
        classification: 'already-text-complete',
        positive: {
            sourceOrOperation: 'λ^f x. F x y0',
            directEvidence:
                'SYNTAX-1A direct/text fixed-inner-evaluation equality test',
            requiredResult:
                'Equal explicit Core, classifier, and structural prerequisites.'
        },
        negative: {
            sourceOrOperation: 'λ^f x : B. F x with expected source A',
            directEvidence: 'SYNTAX-1A annotation comparison negatives',
            requiredResult: 'Reject the annotation span.'
        },
        firstImplementationRow: 'already'
    },
    {
        id: 'natural-indexed-abstraction',
        apiMethods: ['dependentLambda'],
        profile:
            'reviewed-usability-2a1 eta; usability-dependent-1a composition',
        classifierContract:
            'Expected target displayed family supplies the base category and ' +
            'dependent-section result.',
        scopedBindings:
            'One natural base-object slot, with indexed family classifiers.',
        dependencyAndVariance: 'natural variation and displayed dependency',
        actionOwnership:
            'Existing section evaluation and generic Catd composition.',
        recursiveBodyGrammar:
            'section eta and supported nested indexed application composition',
        proposedText:
            'λ^n k [: K]. s k; λ^n k. (FF k) (s k)',
        locatedSyntax: 'requires-typed-expected-contract',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'λ^n k. (FF k) (s k)',
            directEvidence:
                'dependent-eta and dependent-composition direct tests',
            requiredResult:
                'Equal dependent section Core and retained indexed body IR.'
        },
        negative: {
            sourceOrOperation: 'λ^n k. d k under the wrong target family',
            directEvidence: 'dependent-eta wrong-family test',
            requiredResult: 'Preserve CLASSIFIER_ARGUMENT_MISMATCH.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1A'
    },
    {
        id: 'independent-displayed-context-abstraction',
        apiMethods: [
            'fibrePair',
            'displayedContextLambda'
        ],
        profile: 'fibred-displayed-bracket-1 and descendants',
        classifierContract:
            'Finite independent displayed siblings over one base and one ' +
            'target family.',
        scopedBindings:
            'Multiple fibre slots in a shared-minimal-base sibling group.',
        dependencyAndVariance:
            'displayed functorial siblings; weakening, contraction, and ' +
            'symmetry are fibrewise structural operations',
        actionOwnership:
            'Existing displayed product/projection/pairing and recursive ' +
            'contextual compiler.',
        recursiveBodyGrammar:
            'finite supported application/pair bodies over all sibling slots',
        proposedText:
            'an explicit displayedContextLambda/telescope plus fibrePair',
        locatedSyntax: 'requires-structural-form',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'lambda over b,c with fibrePair b c',
            directEvidence: 'displayed-bracket tests',
            requiredResult:
                'Equal direct bracket and object/internalized-arrow evidence.'
        },
        negative: {
            sourceOrOperation: 'siblings over different bases',
            directEvidence: 'displayed-context negative partition',
            requiredResult: 'Reject without inventing a reindexing equality.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1B'
    },
    {
        id: 'dependent-displayed-context-abstraction',
        apiMethods: ['displayedDependentContextLambda'],
        profile: 'fibred-displayed-chain-1/2a and descendants',
        classifierContract:
            'Ordered binding families and target family are checked against ' +
            'the dependency plan.',
        scopedBindings:
            'One genuine dependency edge and the reviewed mixed a; b,c; d ' +
            'telescope.',
        dependencyAndVariance:
            'genuine displayed dependency with independent sibling subgroups',
        actionOwnership:
            'Existing Sigma/pullback/product and internalized cell owners.',
        recursiveBodyGrammar:
            'reviewed finite dependent/mixed contextual body grammar',
        proposedText:
            'an explicit dependent displayed telescope; not silently encoded ' +
            'as arbitrary nested unary lambdas',
        locatedSyntax: 'requires-structural-form',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'a; b,c; d dependent context',
            directEvidence: 'displayed-chain and chain-2A tests',
            requiredResult:
                'Equal direct lowering at object and internalized-arrow level.'
        },
        negative: {
            sourceOrOperation: 'arbitrary deeper/mixed dependency graph',
            directEvidence: 'displayed graduation exact residual boundary',
            requiredResult: 'Report unsupported context shape exactly.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1B'
    },
    {
        id: 'displayed-functorial-abstraction',
        apiMethods: [
            'displayedFunctorLambda',
            'nestedDisplayedFunctorLambda',
            'mixedDisplayedFunctorLambda',
            'mixedDisplayedFunctorTowerLambda'
        ],
        profile:
            'fibred-binder-1 and descendants; direct mixed introduction ' +
            'remains an opt-in later profile',
        classifierContract:
            'Expected source and target displayed families select ^fd.',
        scopedBindings:
            'One displayed object slot with a hidden base slot owned by the ' +
            'contextual compiler; the direct tower method retains one ' +
            'positive outer slot and a finite negative inner array.',
        dependencyAndVariance: 'functorial variation, displayed dependency',
        actionOwnership:
            'Existing displayed identity and generic comp_fapp0 at Catd_cat.',
        recursiveBodyGrammar:
            'identity, eta, finite nested application composition, and ' +
            'qualified weakening/reindexing; the direct mixed profile adds ' +
            'F[c](a) | G(mixed-body), and its tower method adds exact ' +
            'F[c](a1)...(an) eta plus closed target maps',
        proposedText:
            'λ^fd a [: E]. a; λ^fd a. GG (FF a)',
        locatedSyntax: 'requires-typed-expected-contract',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation: 'λ^fd a. GG (FF a)',
            directEvidence: 'fibred-binder direct composition test',
            requiredResult:
                'Equal comp_fapp0 Core with chainLength 2 evidence.'
        },
        negative: {
            sourceOrOperation: 'λ^fd a. wrong a',
            directEvidence: 'fibred-binder wrong-family test',
            requiredResult: 'Preserve exact family classifier rejection.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1A'
    },
    {
        id: 'displayed-natural-abstraction-and-composition',
        apiMethods: [
            'displayedTransforContextLambda',
            'displayedTransforDependentContextLambda',
            'displayedTransforLambda',
            'identityCell',
            'composeCells',
            'composeDisplayedTransfor'
        ],
        profile: 'fibred-transfd-1 and descendants',
        classifierContract:
            'Expected source/target displayed functors select ^nd; component ' +
            'composition requires adjacent indexed-transfor endpoints.',
        scopedBindings:
            'The compact contextual method hides one natural base slot and ' +
            'exposes one natural fibre-object slot; the direct dependent-' +
            'context method exposes a finite canonical telescope over one ' +
            'hidden final-base slot; the retained component method exposes ' +
            'the natural base slot directly.',
        dependencyAndVariance: 'natural variation, displayed dependency',
        actionOwnership:
            'Existing displayed component owner and generic category ' +
            'composition at Functord_cat.',
        recursiveBodyGrammar:
            'compact point eta and finite factorable point identity, plus ' +
            'the same direct factorer over a finite canonical telescope, ' +
            'retained whole-fibre component eta and finite recursive ' +
            'typed-cell composition',
        proposedText:
            'λ^nd a [: E]. eta a; retained λ^nd k [: K]. eta k; ' +
            'λ^nd k. ' +
            'composeCells (theta k) (eta k)',
        locatedSyntax: 'requires-typed-expected-contract',
        classification: 'typed-resolver-seam',
        positive: {
            sourceOrOperation:
                'λ^nd k. composeCells (theta k) (eta k)',
            directEvidence: 'DISPLAYED-ND-1A recursive composition tests',
            requiredResult:
                'Equal coherent outer Transfd composition and retained cell IR.'
        },
        negative: {
            sourceOrOperation:
                'λ^nd k. composeCells (rho k) (eta k) with bad endpoints',
            directEvidence: 'DISPLAYED-ND-1A non-adjacent-endpoint test',
            requiredResult:
                'Reject; never promote arbitrary pointwise components.'
        },
        firstImplementationRow: 'SYNTAX-PARITY-1A'
    },
    {
        id: 'inspection-comparison-and-compilation',
        apiMethods: [
            'displayedTransforClassifierCompatibility',
            'displayedFunctorClassifierCompatibility',
            'inspect',
            'serializeCategory',
            'dependentTargetCategoryCompatibility',
            'compareCategories',
            'compareDisplayedFamilies',
            'compare',
            'compile'
        ],
        profile: 'the profile of the inspected values',
        classifierContract:
            'Consumes already constructed values and returns trace, ' +
            'comparison, serialization, or compiled explicit Core.',
        scopedBindings: 'No source binder or mathematical term constructor.',
        dependencyAndVariance:
            'Observes existing classifiers without changing their semantics.',
        actionOwnership:
            'Existing checker, conversion, proof comparison, and compiler.',
        recursiveBodyGrammar: 'not applicable',
        proposedText:
            'Reviewer/UI commands around an elaborated term, not expression ' +
            'grammar.',
        locatedSyntax: 'not-applicable',
        classification: 'deliberately-non-textual-host-behavior',
        positive: {
            sourceOrOperation: 'inspect/compile the parsed result',
            directEvidence: 'all text and reviewer tests',
            requiredResult: 'Use the same public observations after parsing.'
        },
        negative: {
            sourceOrOperation: 'treat compare or compile as a term former',
            directEvidence: 'API return types are not CoreCategoricalTerm',
            requiredResult: 'Keep these operations outside expression syntax.'
        },
        firstImplementationRow: 'not-textual'
    },
    {
        id: 'general-coherence-and-arbitrary-contexts',
        apiMethods: [],
        profile: 'absent from the direct TypeScript target itself',
        classifierContract:
            'No direct method accepts arbitrary pointwise data or an ' +
            'unbounded dependency graph and synthesizes coherence.',
        scopedBindings: 'unbounded/arbitrary',
        dependencyAndVariance: 'arbitrary mixed variance and dependency',
        actionOwnership: 'no existing internal owner/factorer',
        recursiveBodyGrammar:
            'outside the finite direct-TypeScript capability envelope',
        proposedText: 'none until a semantic capability is separately added',
        locatedSyntax: 'not-applicable',
        classification: 'semantic-capability-absent',
        positive: {
            sourceOrOperation: 'none',
            directEvidence: 'displayed graduation residual-gap records',
            requiredResult:
                'Do not claim textual parity for a capability the direct API ' +
                'does not possess.'
        },
        negative: {
            sourceOrOperation: 'arbitrary pointwise ^fd/^nd body',
            directEvidence: 'direct factorers fail closed',
            requiredResult:
                'Report semantic-capability-absent rather than parser failure.'
        },
        firstImplementationRow: 'semantic-boundary'
    }
] as const satisfies readonly CoreCategoricalTextParityCapability[];

type InventoriedMethod = typeof capabilities[number]['apiMethods'][number];

/**
 * A public-method addition to CoreCategoricalProgram fails type checking until
 * the parity audit classifies it.
 */
export const CORE_CATEGORICAL_TEXT_PARITY_METHOD_COVERAGE:
    Exclude<
        CoreCategoricalProgramPublicMethodName,
        InventoriedMethod
    > extends never
        ? true
        : never = true;

const rawAudit = {
    revision: 'SYNTAX-PARITY-0A-AUDIT-1',
    status: 'completed-zero-behavior-delta-audit',
    prerequisite: {
        textRevision: 'SYNTAX-1A-CATEGORICAL-TEXT-1',
        reviewerCheckpoint:
            '18ca2547bb2f5795127a6589d0531bba87317f19'
    },
    startingTextSurface: {
        locatedNodes: [
            'identifier',
            'left-associated-application',
            'intrinsic-mode-lambda'
        ],
        environmentKinds: [
            'category',
            'term',
            'hom-boundary'
        ],
        expectedKinds: [
            'term',
            'ordinary-functor'
        ],
        parserModeGrammar: 'alphabetic-mode-suffix',
        implementedModes: ['f'],
        rootExpectedApplicationShapeOnly: true,
        nestedLambdaImplemented: false,
        displayedFamilyBindingImplemented: false,
        structuralConstructorSpineImplemented: false
    },
    capabilities,
    measuredCoverage: {
        publicProgramMethods: 84,
        capabilityRows: 14,
        classificationRows: {
            alreadyTextComplete: 1,
            mechanicalSyntaxRoute: 1,
            typedResolverSeam: 9,
            semanticCapabilityAbsent: 1,
            deliberatelyNonTextualHostBehavior: 2
        }
    },
    firstProposal: {
        gate: 'H-DTTLF-PRODUCT-SYNTAX-PARITY-01',
        decision: 'D-DTTLF-PRODUCT-SYNTAX-PARITY-001',
        row: 'SYNTAX-PARITY-1A',
        status: 'deeply-frozen-non-self-authorizing-proposal',
        objective:
            'complete the three already implemented single-binder modes ' +
            'before structural telescope/constructor parity',
        selectedModes: ['n', 'fd', 'nd'],
        selectedDirectMethods: [
            'dependentLambda',
            'displayedFunctorLambda',
            'displayedTransforLambda',
            'composeCells',
            'apply'
        ],
        requestContractAdditions: {
            bindingKinds: ['displayed-family'],
            expectedKinds: [
                'dependent-section',
                'displayed-functor',
                'displayed-transfor'
            ],
            operationSpines: [
                {
                    sourceName: 'composeCells',
                    arity: 2,
                    directMethod: 'composeCells'
                }
            ]
        },
        acceptedBodies: {
            n: [
                'section-eta',
                'indexed-section-composition'
            ],
            fd: [
                'identity',
                'eta',
                'finite-nested-application-composition',
                'qualified-weakening-reindexing'
            ],
            nd: [
                'component-eta',
                'finite-recursive-composeCells'
            ]
        },
        exactPositiveSources: [
            'λ^n k : K. (FF k) (s k)',
            'λ^fd a : E. GG (FF a)',
            'λ^nd k : K. composeCells (theta k) (eta k)'
        ],
        exactNegativeClasses: [
            'wrong-annotation-kind-or-classifier',
            'unavailable-program-profile',
            'wrong-family-or-functor-endpoints',
            'non-adjacent-cell-composition',
            'pointwise-but-not-internalizable-body',
            'nested-or-multi-binder-form-deferred-to-1B'
        ],
        implementationFiles: [
            'src/v3_2/categorical_text.ts',
            'tests/v3_2_categorical_text_parity_tests.ts',
            'src/v3_2/browser_reviewer.ts',
            'tests/v3_2_browser_reviewer_tests.ts',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md',
            'docs/TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md'
        ],
        acceptance: [
            'each positive text term equals its direct TypeScript explicit Core',
            'inferred and expected classifiers agree',
            'direct abstraction rule and recursive body evidence agree',
            'all negative classes retain exact source spans',
            'browser and Node use the same adapter',
            'no external naturality or coherence witness is accepted'
        ],
        followingRows: [
            'SYNTAX-PARITY-1B-contexts-and-fibred-structure',
            'SYNTAX-PARITY-1C-remaining-mathematical-constructors',
            'SYNTAX-PARITY-GRADUATE-1'
        ]
    },
    semanticDelta: {
        parserNodeKinds: 0,
        resolverBranches: 0,
        programMethods: 0,
        coreOwners: 0,
        checkerOrEvaluatorBranches: 0,
        lambdapiDeclarationsOrRules: 0,
        browserBehavior: 0
    }
} as const;

export type CoreCategoricalTextParityAuditInput = typeof rawAudit;

export type CoreCategoricalTextParityAuditErrorCode =
    | 'TEXT_PARITY_PREREQUISITE_DRIFT'
    | 'TEXT_PARITY_METHOD_COVERAGE_DRIFT'
    | 'TEXT_PARITY_CLASSIFICATION_DRIFT'
    | 'TEXT_PARITY_PROPOSAL_DRIFT'
    | 'TEXT_PARITY_BOUNDARY_DRIFT';

export class CoreCategoricalTextParityAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalTextParityAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalTextParityAuditError';
    }
}

export const CORE_CATEGORICAL_TEXT_PARITY_AUDIT =
    deepFreeze(rawAudit);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export const validateCoreCategoricalTextParityAudit = (
    audit: CoreCategoricalTextParityAuditInput =
        CORE_CATEGORICAL_TEXT_PARITY_AUDIT
): void => {
    if (
        audit.prerequisite.textRevision !==
            'SYNTAX-1A-CATEGORICAL-TEXT-1' ||
        audit.prerequisite.reviewerCheckpoint !==
            '18ca2547bb2f5795127a6589d0531bba87317f19'
    ) {
        throw new CoreCategoricalTextParityAuditError(
            'TEXT_PARITY_PREREQUISITE_DRIFT',
            'Syntax-parity audit prerequisite changed'
        );
    }

    const methods = audit.capabilities.flatMap(
        capability => capability.apiMethods
    );
    if (
        methods.length !== audit.measuredCoverage.publicProgramMethods ||
        new Set(methods).size !== methods.length
    ) {
        throw new CoreCategoricalTextParityAuditError(
            'TEXT_PARITY_METHOD_COVERAGE_DRIFT',
            'Public categorical method coverage is missing or duplicated'
        );
    }

    const classificationCounts = {
        alreadyTextComplete: audit.capabilities.filter(
            entry => entry.classification === 'already-text-complete'
        ).length,
        mechanicalSyntaxRoute: audit.capabilities.filter(
            entry => entry.classification === 'mechanical-syntax-route'
        ).length,
        typedResolverSeam: audit.capabilities.filter(
            entry => entry.classification === 'typed-resolver-seam'
        ).length,
        semanticCapabilityAbsent: audit.capabilities.filter(
            entry => entry.classification === 'semantic-capability-absent'
        ).length,
        deliberatelyNonTextualHostBehavior: audit.capabilities.filter(
            entry =>
                entry.classification ===
                    'deliberately-non-textual-host-behavior'
        ).length
    };
    if (
        audit.capabilities.length !==
            audit.measuredCoverage.capabilityRows ||
        !sameData(
            classificationCounts,
            audit.measuredCoverage.classificationRows
        )
    ) {
        throw new CoreCategoricalTextParityAuditError(
            'TEXT_PARITY_CLASSIFICATION_DRIFT',
            'Syntax-parity capability classification changed'
        );
    }

    if (
        !sameData(
            audit.firstProposal.selectedModes,
            ['n', 'fd', 'nd']
        ) ||
        !sameData(
            audit.firstProposal.selectedDirectMethods,
            [
                'dependentLambda',
                'displayedFunctorLambda',
                'displayedTransforLambda',
                'composeCells',
                'apply'
            ]
        ) ||
        audit.firstProposal.status !==
            'deeply-frozen-non-self-authorizing-proposal'
    ) {
        throw new CoreCategoricalTextParityAuditError(
            'TEXT_PARITY_PROPOSAL_DRIFT',
            'The bounded first syntax-parity proposal changed'
        );
    }

    if (
        Object.values(audit.semanticDelta).some(value => value !== 0) ||
        audit.startingTextSurface.implementedModes.length !== 1 ||
        audit.startingTextSurface.implementedModes[0] !== 'f'
    ) {
        throw new CoreCategoricalTextParityAuditError(
            'TEXT_PARITY_BOUNDARY_DRIFT',
            'Read-only syntax-parity audit installed behavior'
        );
    }
};
