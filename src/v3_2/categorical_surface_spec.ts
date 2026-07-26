/**
 * Executable USABILITY-1A specification for categorical binders and
 * type-directed application.
 *
 * This file installs no surface syntax, Core owner, or computation rule. It
 * freezes the judgments that the USABILITY-1B/1C compiler must implement and
 * records which targets are already available, merely active in Lambdapi, or
 * deliberately unavailable. Backend spellings remain in the separate
 * binding tables at the bottom of the file.
 */

import {
    CORE_DIRECTED_1C_REVIEW,
    validateCoreDirected1cReview
} from './directed_1c_review';
import {
    LAMBDAPI_V32_OWNER_BINDINGS
} from './lambdapi';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export type CoreCategoricalVariation =
    | 'functorial'
    | 'natural'
    | 'object-only';

export type CoreCategoricalPolarity =
    | 'covariant'
    | 'contravariant';

export type CoreCategoricalCellLevel =
    | 'object'
    | 'arrow'
    | 'transfor'
    | 'higher';

export type CoreCategoricalDependency =
    | 'ordinary'
    | 'displayed';

export type CoreCategoricalAbstractionLayer =
    | 'outer-lf'
    | 'categorical';

export type CoreCategoricalSubjectClassifier =
    | 'outer-lf-pi'
    | 'ordinary-functor'
    | 'ordinary-transfor'
    | 'dependent-section'
    | 'displayed-functor'
    | 'displayed-transfor';

export type CoreCategoricalSubjectForm =
    | 'term'
    | 'classifier-family';

export type CoreCategoricalArgumentDimension =
    | 'lf-term'
    | 'object'
    | 'arrow'
    | 'hom-boundary';

export type CoreCategoricalExpectedShape =
    | 'lf-value'
    | 'object-value'
    | 'whole-hom-action'
    | 'arrow-value'
    | 'whole-point-evaluator'
    | 'point-component'
    | 'whole-off-diagonal-action'
    | 'off-diagonal-value'
    | 'dependent-object'
    | 'whole-section-action'
    | 'dependent-arrow'
    | 'fibre-functor'
    | 'transport-functor'
    | 'whole-laxity-transfor'
    | 'whole-displayed-component-evaluator'
    | 'displayed-component';

export type CoreCategoricalCandidateTargetId =
    | 'section-object-evaluation'
    | 'section-hom-full'
    | 'section-hom-capped'
    | 'displayed-functor-fibre'
    | 'displayed-functor-transport'
    | 'displayed-functor-laxity'
    | 'displayed-transfor-component-full'
    | 'displayed-transfor-component-capped';

export type CoreCategoricalApplicationTargetId =
    | 'outer-lf-call'
    | CoreOwnerId
    | CoreCategoricalCandidateTargetId;

export type CoreCategoricalImplementationStatus =
    | 'integrated-outer-lf'
    | 'integrated-core'
    | 'reviewed-continuation'
    | 'active-kernel-untransferred'
    | 'not-active';

export type CoreCategoricalSurfaceDisposition =
    | 'eligible'
    | 'requires-owner-transfer'
    | 'requires-usability-2a'
    | 'requires-naturality-gate'
    | 'unsupported-authority-gap';

export interface CoreCategoricalAxisSpecification {
    readonly axis:
        | 'plicity'
        | 'variation'
        | 'polarity'
        | 'cell-level'
        | 'dependency';
    readonly values: readonly string[];
    readonly source:
        | 'surface-or-expected-type'
        | 'binder-capability'
        | 'classifier-and-opposite'
        | 'inferred-classifier'
        | 'classifier-and-context';
    readonly rule: string;
}

export interface CoreCategoricalAbstractionJudgment {
    readonly id:
        | 'outer-lf-abstraction'
        | 'ordinary-functorial-abstraction'
        | 'natural-indexed-abstraction'
        | 'object-only-abstraction';
    readonly layer: CoreCategoricalAbstractionLayer;
    readonly variation: CoreCategoricalVariation | 'independent';
    readonly expectedClassifier:
        | 'outer-lf-pi'
        | 'ordinary-functor'
        | 'displayed-or-indexed-family'
        | 'object-family-without-arrow-action';
    readonly lowering:
        | 'kernel-lambda'
        | 'categorical-contextual-ir'
        | 'restricted-object-family';
    readonly implementationStage:
        | 'available'
        | 'USABILITY-1B'
        | 'USABILITY-2A'
        | 'notation-and-capability-review';
    readonly rule: string;
}

export interface CoreCategoricalApplicationJudgment {
    readonly id: string;
    readonly layer: CoreCategoricalAbstractionLayer;
    readonly subjectClassifier: CoreCategoricalSubjectClassifier;
    readonly subjectForm: CoreCategoricalSubjectForm;
    readonly argumentDimension: CoreCategoricalArgumentDimension;
    readonly expectedShape: CoreCategoricalExpectedShape;
    readonly dependency: CoreCategoricalDependency;
    readonly target: CoreCategoricalApplicationTargetId;
    readonly consumesSubjectTerm: boolean;
    readonly implementationStatus: CoreCategoricalImplementationStatus;
    readonly surfaceDisposition: CoreCategoricalSurfaceDisposition;
    readonly rule: string;
}

export type CoreCategoricalStructuralTargetId =
    | 'identity-functor'
    | 'constant-functor-abstraction'
    | 'exchange-functor-abstraction'
    | 'diagonal-functor-abstraction'
    | 'product-category'
    | 'product-left-projection'
    | 'product-right-projection'
    | 'product-pair'
    | 'product-map'
    | 'evaluation-functor'
    | 'functor-composition'
    | 'curry-package'
    | 'uncurry-package';

export interface CoreCategoricalStructuralPrerequisite {
    readonly order: number;
    readonly target: CoreCategoricalStructuralTargetId;
    readonly use:
        | 'identity'
        | 'weakening'
        | 'exchange'
        | 'contraction'
        | 'context-product'
        | 'context-projection'
        | 'context-pairing'
        | 'componentwise-map'
        | 'application'
        | 'composition'
        | 'nested-abstraction';
    readonly implementationStatus: 'active-kernel-untransferred';
    readonly firstConsumer: 'USABILITY-1C';
}

export interface CoreCategoricalDiagnosticSpecification {
    readonly code:
        | 'AMBIGUOUS_ABSTRACTION_LAYER'
        | 'MISSING_EXPECTED_ACTION_SHAPE'
        | 'CLASSIFIER_ARGUMENT_MISMATCH'
        | 'OBJECT_ONLY_ARROW_USE'
        | 'POLARITY_MISMATCH'
        | 'MISSING_STRUCTURAL_OWNER'
        | 'UNAVAILABLE_DEPENDENT_ACTION'
        | 'UNAVAILABLE_DISPLAYED_ACTION'
        | 'RESERVED_NATURALITY_ACTION';
    readonly requiredPayload: readonly string[];
    readonly condition: string;
}

export interface CoreCategoricalSurfaceSpecification {
    readonly revision: 'USABILITY-1A';
    readonly status: 'specified-no-semantic-installation';
    readonly architectureDecision:
        'outer-lf-and-categorical-abstraction-are-distinct';
    readonly applicationDecision:
        'classifier-argument-expectation-select-explicit-owner';
    readonly contextualIrDecision:
        'first-order-locally-nameless-usage-and-provenance';
    readonly notationPolicy: {
        readonly canonicalNaturalBinder: ':^n';
        readonly functorialBinder:
            'internal-typescript-mode-final-notation-unsettled';
        readonly objectOnlyBinder:
            'internal-typescript-mode-final-notation-unsettled';
    };
    readonly axes: readonly CoreCategoricalAxisSpecification[];
    readonly abstractions:
        readonly CoreCategoricalAbstractionJudgment[];
    readonly applications:
        readonly CoreCategoricalApplicationJudgment[];
    readonly contextualIr: {
        readonly nodes: readonly [
            'slot-reference',
            'explicit-core-term',
            'typed-application',
            'typed-pair',
            'typed-composition'
        ];
        readonly annotations: readonly [
            'ordered-context',
            'free-slot-usage',
            'result-classifier',
            'cell-level',
            'polarity',
            'dependency',
            'source-provenance'
        ];
        readonly loweringRequirements: readonly [
            'discard-is-explicit-weakening',
            'duplication-is-explicit-contraction',
            'permutation-is-explicit-exchange',
            'application-is-evaluation-after-pairing'
        ];
        readonly storage:
            'ergonomic-callback-immediately-reified-to-first-order-ir';
    };
    readonly structuralPrerequisites:
        readonly CoreCategoricalStructuralPrerequisite[];
    readonly diagnostics:
        readonly CoreCategoricalDiagnosticSpecification[];
    readonly nonEffects: readonly string[];
}

export interface CoreCategoricalApplicationQuery {
    readonly layer: CoreCategoricalAbstractionLayer;
    readonly subjectClassifier: CoreCategoricalSubjectClassifier;
    readonly subjectForm: CoreCategoricalSubjectForm;
    readonly argumentDimension: CoreCategoricalArgumentDimension;
    readonly expectedShape?: CoreCategoricalExpectedShape;
    readonly dependency: CoreCategoricalDependency;
}

export type CoreCategoricalSurfaceErrorCode =
    | CoreCategoricalDiagnosticSpecification['code']
    | 'INVALID_SPECIFICATION'
    | 'INVALID_BACKEND_BINDING'
    | 'SPECIFICATION_DRIFT';

export class CoreCategoricalSurfaceError extends Error {
    constructor(
        public readonly code: CoreCategoricalSurfaceErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalSurfaceError';
    }
}

const axes: readonly CoreCategoricalAxisSpecification[] = [
    {
        axis: 'plicity',
        values: ['explicit', 'implicit'] satisfies readonly Plicity[],
        source: 'surface-or-expected-type',
        rule: 'Plicity changes argument recovery, not categorical variation.'
    },
    {
        axis: 'variation',
        values: ['functorial', 'natural', 'object-only'],
        source: 'binder-capability',
        rule:
            'Variation states the admissible action; object-only is not ' +
            'groupoidality.'
    },
    {
        axis: 'polarity',
        values: ['covariant', 'contravariant'],
        source: 'classifier-and-opposite',
        rule:
            'Contravariance is represented through the opposite-category ' +
            'classifier, not an owner-named binder mode.'
    },
    {
        axis: 'cell-level',
        values: ['object', 'arrow', 'transfor', 'higher'],
        source: 'inferred-classifier',
        rule:
            'Cell level is inferred from classifiers and the argument, not ' +
            'chosen from fapp/tapp owner spellings.'
    },
    {
        axis: 'dependency',
        values: ['ordinary', 'displayed'],
        source: 'classifier-and-context',
        rule:
            'Displayed dependency belongs to the classifier/context and is ' +
            'not flattened into the variation axis.'
    }
];

const abstractions: readonly CoreCategoricalAbstractionJudgment[] = [
    {
        id: 'outer-lf-abstraction',
        layer: 'outer-lf',
        variation: 'independent',
        expectedClassifier: 'outer-lf-pi',
        lowering: 'kernel-lambda',
        implementationStage: 'available',
        rule:
            'An outer dependent Pi checks a KernelLambda and eliminates by ' +
            'ordinary Core call; BinderMode metadata does not promote it to ' +
            'a categorical functor.'
    },
    {
        id: 'ordinary-functorial-abstraction',
        layer: 'categorical',
        variation: 'functorial',
        expectedClassifier: 'ordinary-functor',
        lowering: 'categorical-contextual-ir',
        implementationStage: 'USABILITY-1B',
        rule:
            'A categorical abstraction checks its object and arrow action ' +
            'and lowers by typed categorical bracket abstraction.'
    },
    {
        id: 'natural-indexed-abstraction',
        layer: 'categorical',
        variation: 'natural',
        expectedClassifier: 'displayed-or-indexed-family',
        lowering: 'categorical-contextual-ir',
        implementationStage: 'USABILITY-2A',
        rule:
            'The canonical :^n mode uses active indexed/displayed owners and ' +
            'must fail when a required displayed structural action is absent.'
    },
    {
        id: 'object-only-abstraction',
        layer: 'categorical',
        variation: 'object-only',
        expectedClassifier: 'object-family-without-arrow-action',
        lowering: 'restricted-object-family',
        implementationStage: 'notation-and-capability-review',
        rule:
            'Object-only input supplies no arrow action and cannot be ' +
            'silently checked as an ordinary functor.'
    }
];

const applications:
readonly CoreCategoricalApplicationJudgment[] = [
    {
        id: 'outer-lf.call',
        layer: 'outer-lf',
        subjectClassifier: 'outer-lf-pi',
        subjectForm: 'term',
        argumentDimension: 'lf-term',
        expectedShape: 'lf-value',
        dependency: 'ordinary',
        target: 'outer-lf-call',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-outer-lf',
        surfaceDisposition: 'eligible',
        rule: 'Dependent LF application remains ordinary Core call.'
    },
    {
        id: 'functor.object',
        layer: 'categorical',
        subjectClassifier: 'ordinary-functor',
        subjectForm: 'term',
        argumentDimension: 'object',
        expectedShape: 'object-value',
        dependency: 'ordinary',
        target: 'functor-object',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'eligible',
        rule: 'F applied to x : Obj A selects the object action.'
    },
    {
        id: 'functor.hom.full',
        layer: 'categorical',
        subjectClassifier: 'ordinary-functor',
        subjectForm: 'term',
        argumentDimension: 'hom-boundary',
        expectedShape: 'whole-hom-action',
        dependency: 'ordinary',
        target: 'functor-hom-full',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'eligible',
        rule:
            'A whole Hom-category action request selects the full action; it ' +
            'does not invent an arrow argument.'
    },
    {
        id: 'functor.hom.capped',
        layer: 'categorical',
        subjectClassifier: 'ordinary-functor',
        subjectForm: 'term',
        argumentDimension: 'arrow',
        expectedShape: 'arrow-value',
        dependency: 'ordinary',
        target: 'functor-hom-capped',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'eligible',
        rule: 'F applied to f : Hom A x y selects the capped arrow action.'
    },
    {
        id: 'transfor.component.full',
        layer: 'categorical',
        subjectClassifier: 'ordinary-transfor',
        subjectForm: 'classifier-family',
        argumentDimension: 'object',
        expectedShape: 'whole-point-evaluator',
        dependency: 'ordinary',
        target: 'transfor-component-full',
        consumesSubjectTerm: false,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'eligible',
        rule:
            'The full point evaluator is requested from the F/G transfor ' +
            'classifier; a concrete transfor term is never silently erased.'
    },
    {
        id: 'transfor.component.capped',
        layer: 'categorical',
        subjectClassifier: 'ordinary-transfor',
        subjectForm: 'term',
        argumentDimension: 'object',
        expectedShape: 'point-component',
        dependency: 'ordinary',
        target: 'transfor-component-capped',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'eligible',
        rule: 'A concrete transfor at one object selects its point component.'
    },
    {
        id: 'transfor.hom.full',
        layer: 'categorical',
        subjectClassifier: 'ordinary-transfor',
        subjectForm: 'term',
        argumentDimension: 'hom-boundary',
        expectedShape: 'whole-off-diagonal-action',
        dependency: 'ordinary',
        target: 'transfor-hom-full',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'requires-naturality-gate',
        rule:
            'The full off-diagonal action is representable but its external ' +
            'ordinary naturality surface is not yet promoted.'
    },
    {
        id: 'transfor.hom.capped',
        layer: 'categorical',
        subjectClassifier: 'ordinary-transfor',
        subjectForm: 'term',
        argumentDimension: 'arrow',
        expectedShape: 'off-diagonal-value',
        dependency: 'ordinary',
        target: 'transfor-hom-capped',
        consumesSubjectTerm: true,
        implementationStatus: 'integrated-core',
        surfaceDisposition: 'requires-naturality-gate',
        rule:
            'The active kernel explicitly reserves this capped ordinary ' +
            'naturality action until its external API is promoted.'
    },
    {
        id: 'section.object',
        layer: 'categorical',
        subjectClassifier: 'dependent-section',
        subjectForm: 'term',
        argumentDimension: 'object',
        expectedShape: 'dependent-object',
        dependency: 'displayed',
        target: 'section-object-evaluation',
        consumesSubjectTerm: true,
        implementationStatus: 'reviewed-continuation',
        surfaceDisposition: 'eligible',
        rule:
            'A reviewed dependent section at a base object selects the ' +
            'DIRECTED-1C section evaluator.'
    },
    {
        id: 'section.hom.full',
        layer: 'categorical',
        subjectClassifier: 'dependent-section',
        subjectForm: 'term',
        argumentDimension: 'hom-boundary',
        expectedShape: 'whole-section-action',
        dependency: 'displayed',
        target: 'section-hom-full',
        consumesSubjectTerm: true,
        implementationStatus: 'active-kernel-untransferred',
        surfaceDisposition: 'requires-owner-transfer',
        rule:
            'Whole section action exists in the active kernel but is not in ' +
            'the reviewed TypeScript continuation.'
    },
    {
        id: 'section.hom.capped',
        layer: 'categorical',
        subjectClassifier: 'dependent-section',
        subjectForm: 'term',
        argumentDimension: 'arrow',
        expectedShape: 'dependent-arrow',
        dependency: 'displayed',
        target: 'section-hom-capped',
        consumesSubjectTerm: true,
        implementationStatus: 'active-kernel-untransferred',
        surfaceDisposition: 'requires-owner-transfer',
        rule:
            'Section action at one base arrow requires its active kernel ' +
            'candidate transfer before surface exposure.'
    },
    {
        id: 'displayed-functor.fibre',
        layer: 'categorical',
        subjectClassifier: 'displayed-functor',
        subjectForm: 'term',
        argumentDimension: 'object',
        expectedShape: 'fibre-functor',
        dependency: 'displayed',
        target: 'displayed-functor-fibre',
        consumesSubjectTerm: true,
        implementationStatus: 'active-kernel-untransferred',
        surfaceDisposition: 'requires-usability-2a',
        rule:
            'Base-object projection of a displayed functor is staged for the ' +
            'first displayed usability slice.'
    },
    {
        id: 'displayed-functor.transport',
        layer: 'categorical',
        subjectClassifier: 'displayed-functor',
        subjectForm: 'term',
        argumentDimension: 'arrow',
        expectedShape: 'transport-functor',
        dependency: 'displayed',
        target: 'displayed-functor-transport',
        consumesSubjectTerm: true,
        implementationStatus: 'active-kernel-untransferred',
        surfaceDisposition: 'requires-usability-2a',
        rule:
            'A base arrow selects the active heterogeneous fibre transport ' +
            'functor only after displayed owner qualification.'
    },
    {
        id: 'displayed-functor.laxity',
        layer: 'categorical',
        subjectClassifier: 'displayed-functor',
        subjectForm: 'term',
        argumentDimension: 'arrow',
        expectedShape: 'whole-laxity-transfor',
        dependency: 'displayed',
        target: 'displayed-functor-laxity',
        consumesSubjectTerm: true,
        implementationStatus: 'not-active',
        surfaceDisposition: 'unsupported-authority-gap',
        rule:
            'The active kernel deliberately defers the whole displayed ' +
            'laxity transfor and exposes only component-level cells.'
    },
    {
        id: 'displayed-transfor.component.full',
        layer: 'categorical',
        subjectClassifier: 'displayed-transfor',
        subjectForm: 'classifier-family',
        argumentDimension: 'object',
        expectedShape: 'whole-displayed-component-evaluator',
        dependency: 'displayed',
        target: 'displayed-transfor-component-full',
        consumesSubjectTerm: false,
        implementationStatus: 'active-kernel-untransferred',
        surfaceDisposition: 'requires-usability-2a',
        rule:
            'The full displayed component evaluator is classifier-derived; ' +
            'a concrete displayed transfor is not discarded.'
    },
    {
        id: 'displayed-transfor.component.capped',
        layer: 'categorical',
        subjectClassifier: 'displayed-transfor',
        subjectForm: 'term',
        argumentDimension: 'object',
        expectedShape: 'displayed-component',
        dependency: 'displayed',
        target: 'displayed-transfor-component-capped',
        consumesSubjectTerm: true,
        implementationStatus: 'active-kernel-untransferred',
        surfaceDisposition: 'requires-usability-2a',
        rule:
            'A concrete displayed transfor at a base object selects its ' +
            'capped fibre component after qualification.'
    }
];

const structuralPrerequisites:
readonly CoreCategoricalStructuralPrerequisite[] = [
    ['identity-functor', 'identity'],
    ['constant-functor-abstraction', 'weakening'],
    ['exchange-functor-abstraction', 'exchange'],
    ['diagonal-functor-abstraction', 'contraction'],
    ['product-category', 'context-product'],
    ['product-left-projection', 'context-projection'],
    ['product-right-projection', 'context-projection'],
    ['product-pair', 'context-pairing'],
    ['product-map', 'componentwise-map'],
    ['evaluation-functor', 'application'],
    ['functor-composition', 'composition'],
    ['curry-package', 'nested-abstraction'],
    ['uncurry-package', 'nested-abstraction']
].map(([target, use], order) => ({
    order,
    target: target as CoreCategoricalStructuralTargetId,
    use: use as CoreCategoricalStructuralPrerequisite['use'],
    implementationStatus: 'active-kernel-untransferred' as const,
    firstConsumer: 'USABILITY-1C' as const
}));

const diagnostics:
readonly CoreCategoricalDiagnosticSpecification[] = [
    {
        code: 'AMBIGUOUS_ABSTRACTION_LAYER',
        requiredPayload: [
            'binder',
            'expected-classifier',
            'outer-lf-candidate',
            'categorical-candidate',
            'source-span'
        ],
        condition:
            'Neither syntax nor expected classifier distinguishes outer LF ' +
            'abstraction from categorical abstraction.'
    },
    {
        code: 'MISSING_EXPECTED_ACTION_SHAPE',
        requiredPayload: [
            'subject-classifier',
            'argument-dimension',
            'candidate-targets',
            'source-span'
        ],
        condition:
            'Classifier and argument leave more than one full/capped or ' +
            'displayed action target.'
    },
    {
        code: 'CLASSIFIER_ARGUMENT_MISMATCH',
        requiredPayload: [
            'subject-classifier',
            'argument-classifier',
            'expected-shape',
            'candidate-targets',
            'source-span'
        ],
        condition:
            'No application judgment matches the synthesized subject and ' +
            'argument classifiers.'
    },
    {
        code: 'OBJECT_ONLY_ARROW_USE',
        requiredPayload: [
            'binder',
            'variation',
            'arrow-use',
            'source-span'
        ],
        condition:
            'An object-only binder is demanded at arrow or higher action.'
    },
    {
        code: 'POLARITY_MISMATCH',
        requiredPayload: [
            'binder',
            'declared-polarity',
            'required-polarity',
            'classifier',
            'source-span'
        ],
        condition:
            'A use requires covariance where the contextual classifier ' +
            'provides an opposite/contravariant input, or conversely.'
    },
    {
        code: 'MISSING_STRUCTURAL_OWNER',
        requiredPayload: [
            'operation',
            'semantic-owner',
            'first-consumer',
            'source-span'
        ],
        condition:
            'Bracket lowering requires an active structural owner not yet ' +
            'present in the TypeScript continuation.'
    },
    {
        code: 'UNAVAILABLE_DEPENDENT_ACTION',
        requiredPayload: [
            'subject-classifier',
            'argument-dimension',
            'semantic-owner',
            'implementation-status',
            'source-span'
        ],
        condition:
            'A section action exists in the kernel but has not been ' +
            'transferred into the reviewed continuation.'
    },
    {
        code: 'UNAVAILABLE_DISPLAYED_ACTION',
        requiredPayload: [
            'subject-classifier',
            'argument-dimension',
            'expected-shape',
            'semantic-owner',
            'implementation-status',
            'source-span'
        ],
        condition:
            'Displayed action awaits USABILITY-2A qualification or is not an ' +
            'active kernel owner.'
    },
    {
        code: 'RESERVED_NATURALITY_ACTION',
        requiredPayload: [
            'subject-classifier',
            'argument-dimension',
            'semantic-owner',
            'authority-policy',
            'source-span'
        ],
        condition:
            'The explicit Core can represent an ordinary off-diagonal action ' +
            'whose active external naturality API remains reserved.'
    }
];

const rawSpecification: CoreCategoricalSurfaceSpecification = {
    revision: 'USABILITY-1A',
    status: 'specified-no-semantic-installation',
    architectureDecision:
        'outer-lf-and-categorical-abstraction-are-distinct',
    applicationDecision:
        'classifier-argument-expectation-select-explicit-owner',
    contextualIrDecision:
        'first-order-locally-nameless-usage-and-provenance',
    notationPolicy: {
        canonicalNaturalBinder: ':^n',
        functorialBinder:
            'internal-typescript-mode-final-notation-unsettled',
        objectOnlyBinder:
            'internal-typescript-mode-final-notation-unsettled'
    },
    axes,
    abstractions,
    applications,
    contextualIr: {
        nodes: [
            'slot-reference',
            'explicit-core-term',
            'typed-application',
            'typed-pair',
            'typed-composition'
        ],
        annotations: [
            'ordered-context',
            'free-slot-usage',
            'result-classifier',
            'cell-level',
            'polarity',
            'dependency',
            'source-provenance'
        ],
        loweringRequirements: [
            'discard-is-explicit-weakening',
            'duplication-is-explicit-contraction',
            'permutation-is-explicit-exchange',
            'application-is-evaluation-after-pairing'
        ],
        storage:
            'ergonomic-callback-immediately-reified-to-first-order-ir'
    },
    structuralPrerequisites,
    diagnostics,
    nonEffects: [
        'does not reinterpret KernelLambda as a categorical functor',
        'does not standardize :^f or :^o Lambdapi notation',
        'does not install structural or displayed candidate owners',
        'does not expose reserved ordinary naturality actions',
        'does not parse Lambdapi source text',
        'does not change the frozen MVP manifest or browser entry point'
    ]
};

export interface CoreCategoricalBackendBinding {
    readonly target:
        | CoreCategoricalCandidateTargetId
        | CoreCategoricalStructuralTargetId;
    readonly serializedName: string;
    readonly authority:
        | 'active-symbol'
        | 'active-transparent-definition'
        | 'explicitly-deferred-symbol';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: string;
        readonly sourceFragment: string;
        readonly auditedOn: '2026-07-26';
    };
}

const candidateBindings:
readonly CoreCategoricalBackendBinding[] = [
    {
        target: 'section-object-evaluation',
        serializedName: 'piapp0',
        authority: 'active-transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '8c. Section categories and Pi action',
            sourceFragment: 'symbol piapp0 : Π [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'section-hom-full',
        serializedName: 'piapp1_func',
        authority: 'active-transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '16c. Section action and displayed laxity cells',
            sourceFragment: 'symbol piapp1_func [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'section-hom-capped',
        serializedName: 'piapp1_fapp0',
        authority: 'active-transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '16c. Section action and displayed laxity cells',
            sourceFragment: 'symbol piapp1_fapp0 [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'displayed-functor-fibre',
        serializedName: 'Fibre_func',
        authority: 'active-transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '15. Displayed functor and transfor fibre notation',
            sourceFragment: 'symbol Fibre_func [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'displayed-functor-transport',
        serializedName: 'functord_transport_func',
        authority: 'active-transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '16a. Displayed internal hom action',
            sourceFragment: 'symbol functord_transport_func [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'displayed-functor-laxity',
        serializedName: 'functord_laxity_transf',
        authority: 'explicitly-deferred-symbol',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '16b. Identity-specialized displayed hom action',
            sourceFragment:
                'symbol functord_laxity_transf [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'displayed-transfor-component-full',
        serializedName: 'tdapp0_func',
        authority: 'active-symbol',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '15. Displayed functor and transfor fibre notation',
            sourceFragment: 'symbol tdapp0_func [K : Cat]',
            auditedOn: '2026-07-26'
        }
    },
    {
        target: 'displayed-transfor-component-capped',
        serializedName: 'tdapp0_fapp0',
        authority: 'active-symbol',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '15. Displayed functor and transfor fibre notation',
            sourceFragment: 'symbol tdapp0_fapp0 [K : Cat]',
            auditedOn: '2026-07-26'
        }
    }
];

const structuralBindings:
readonly CoreCategoricalBackendBinding[] = [
    [
        'identity-functor',
        'id_func',
        '3e. Ordinary identity and composition',
        'active-transparent-definition'
    ],
    [
        'constant-functor-abstraction',
        'Const_func_func',
        '17c. Ordinary functor structural logic',
        'active-symbol'
    ],
    [
        'exchange-functor-abstraction',
        'sym_func_func',
        '17c. Ordinary functor structural logic',
        'active-symbol'
    ],
    [
        'diagonal-functor-abstraction',
        'diag_func_func',
        '17c. Ordinary functor structural logic',
        'active-symbol'
    ],
    [
        'product-category',
        'Product_cat',
        '5a. Product categories',
        'active-symbol'
    ],
    [
        'product-left-projection',
        'Product_projL_func',
        '5a. Product categories',
        'active-symbol'
    ],
    [
        'product-right-projection',
        'Product_projR_func',
        '5a. Product categories',
        'active-symbol'
    ],
    [
        'product-pair',
        'Product_pair',
        '5a. Product categories',
        'active-transparent-definition'
    ],
    [
        'product-map',
        'Product_map_func',
        '7a. Product functor action',
        'active-symbol'
    ],
    [
        'evaluation-functor',
        'Eval_func',
        '7b. Evaluation',
        'active-symbol'
    ],
    [
        'functor-composition',
        'comp_cat_fapp0',
        '3e. Ordinary identity and composition',
        'active-transparent-definition'
    ],
    [
        'curry-package',
        'curry_func_func',
        '7c. Ordinary curry',
        'active-transparent-definition'
    ],
    [
        'uncurry-package',
        'uncurry_func_func',
        '7c. Ordinary curry',
        'active-transparent-definition'
    ],
].map(([target, serializedName, section, authority]) => ({
    target: target as CoreCategoricalStructuralTargetId,
    serializedName,
    authority: authority as CoreCategoricalBackendBinding['authority'],
    provenance: {
        authorityPath: 'emdash2/emdash3_2.lp' as const,
        section,
        sourceFragment:
            serializedName === 'Product_cat' ||
            serializedName === 'Product_pair' ||
            serializedName === 'Product_projL_func' ||
            serializedName === 'Product_projR_func' ||
            serializedName === 'Const_func_func' ||
            serializedName === 'Product_map_func'
                ? `injective symbol ${serializedName}`
                : `symbol ${serializedName}`,
        auditedOn: '2026-07-26' as const
    }
}));

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const fail = (
    code: CoreCategoricalSurfaceErrorCode,
    message: string
): never => {
    throw new CoreCategoricalSurfaceError(code, message);
};

export const CORE_CATEGORICAL_SURFACE_SPECIFICATION =
    deepFreeze(rawSpecification);

export const LAMBDAPI_V32_CATEGORICAL_SURFACE_BINDINGS = deepFreeze([
    ...candidateBindings,
    ...structuralBindings
] as const);

const matchApplicationQuery = (
    row: CoreCategoricalApplicationJudgment,
    query: CoreCategoricalApplicationQuery
): boolean =>
    row.layer === query.layer &&
    row.subjectClassifier === query.subjectClassifier &&
    row.subjectForm === query.subjectForm &&
    row.argumentDimension === query.argumentDimension &&
    row.dependency === query.dependency &&
    (
        query.expectedShape === undefined ||
        row.expectedShape === query.expectedShape
    );

/**
 * Resolve an application judgment without exposing unavailable candidates.
 *
 * The real USABILITY-1B elaborator will synthesize this query from typed
 * terms. Keeping the classifier here explicit makes the pre-implementation
 * decision deterministic and directly testable.
 */
export function selectCoreCategoricalApplication(
    query: CoreCategoricalApplicationQuery
): CoreCategoricalApplicationJudgment {
    const candidates =
        CORE_CATEGORICAL_SURFACE_SPECIFICATION.applications.filter(row =>
            matchApplicationQuery(row, query)
        );

    if (candidates.length === 0) {
        fail(
            'CLASSIFIER_ARGUMENT_MISMATCH',
            `No categorical application matches ${query.layer} ` +
            `${query.subjectClassifier}/${query.subjectForm} at ` +
            `${query.argumentDimension} with dependency ${query.dependency}` +
            (
                query.expectedShape === undefined
                    ? ''
                    : ` and expected shape ${query.expectedShape}`
            )
        );
    }
    if (candidates.length > 1) {
        fail(
            'MISSING_EXPECTED_ACTION_SHAPE',
            `Application ${query.subjectClassifier}/${query.argumentDimension} ` +
            'requires an expected action shape; candidates are ' +
            candidates.map(candidate => candidate.target).join(', ')
        );
    }

    const selected = candidates[0];
    switch (selected.surfaceDisposition) {
        case 'eligible':
            return selected;
        case 'requires-owner-transfer':
            fail(
                'UNAVAILABLE_DEPENDENT_ACTION',
                `Application requires untransferred active owner ` +
                `'${selected.target}'`
            );
        case 'requires-usability-2a':
        case 'unsupported-authority-gap':
            fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                `Application requires displayed target '${selected.target}' ` +
                `with status ${selected.implementationStatus}`
            );
        case 'requires-naturality-gate':
            fail(
                'RESERVED_NATURALITY_ACTION',
                `Application target '${selected.target}' is representable but ` +
                'its external ordinary naturality surface remains reserved'
            );
    }
}

const validateUnique = (
    label: string,
    values: readonly string[]
): void => {
    if (new Set(values).size !== values.length) {
        fail('INVALID_SPECIFICATION', `${label} contains a duplicate`);
    }
};

export function validateCoreCategoricalSurfaceSpecification(
    specification:
        CoreCategoricalSurfaceSpecification =
            CORE_CATEGORICAL_SURFACE_SPECIFICATION,
    bindings:
        readonly CoreCategoricalBackendBinding[] =
            LAMBDAPI_V32_CATEGORICAL_SURFACE_BINDINGS
): void {
    if (
        specification.revision !== 'USABILITY-1A' ||
        specification.status !== 'specified-no-semantic-installation' ||
        specification.architectureDecision !==
            'outer-lf-and-categorical-abstraction-are-distinct' ||
        specification.applicationDecision !==
            'classifier-argument-expectation-select-explicit-owner'
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'USABILITY-1A architecture boundary drifted'
        );
    }

    validateUnique(
        'axis catalog',
        specification.axes.map(axis => axis.axis)
    );
    validateUnique(
        'abstraction catalog',
        specification.abstractions.map(abstraction => abstraction.id)
    );
    validateUnique(
        'application catalog',
        specification.applications.map(application => application.id)
    );
    validateUnique(
        'application judgment keys',
        specification.applications.map(application => [
            application.layer,
            application.subjectClassifier,
            application.subjectForm,
            application.argumentDimension,
            application.expectedShape,
            application.dependency
        ].join(':'))
    );
    validateUnique(
        'structural prerequisite catalog',
        specification.structuralPrerequisites.map(entry => entry.target)
    );
    validateUnique(
        'diagnostic catalog',
        specification.diagnostics.map(diagnostic => diagnostic.code)
    );

    const expectedAxes = [
        'plicity',
        'variation',
        'polarity',
        'cell-level',
        'dependency'
    ];
    if (
        !sameData(
            specification.axes.map(axis => axis.axis),
            expectedAxes
        )
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'USABILITY-1A must preserve five orthogonal binder axes'
        );
    }

    const coreTargets = specification.applications.filter(
        application => application.implementationStatus === 'integrated-core'
    );
    for (const application of coreTargets) {
        if (!(application.target in CORE_OWNER_SCHEMAS)) {
            fail(
                'INVALID_SPECIFICATION',
                `Integrated target '${application.target}' is not a Core owner`
            );
        }
        const owner = application.target as CoreOwnerId;
        if (!(owner in LAMBDAPI_V32_OWNER_BINDINGS)) {
            fail(
                'INVALID_BACKEND_BINDING',
                `Integrated target '${owner}' has no active backend binding`
            );
        }
    }

    const expectedCoreTargets: readonly CoreOwnerId[] = [
        'functor-object',
        'functor-hom-full',
        'functor-hom-capped',
        'transfor-component-full',
        'transfor-component-capped',
        'transfor-hom-full',
        'transfor-hom-capped'
    ];
    if (
        !sameData(
            coreTargets.map(application => application.target),
            expectedCoreTargets
        )
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'Integrated application target order or membership drifted'
        );
    }
    const expectedProjectionMetadata = {
        'functor-object': [
            'functor-action',
            'object',
            'evaluator',
            'diagonal'
        ],
        'functor-hom-full': [
            'functor-action',
            'hom',
            'full',
            'diagonal'
        ],
        'functor-hom-capped': [
            'functor-action',
            'hom',
            'capped',
            'diagonal'
        ],
        'transfor-component-full': [
            'transfor-action',
            'object',
            'full',
            'diagonal'
        ],
        'transfor-component-capped': [
            'transfor-action',
            'object',
            'capped',
            'diagonal'
        ],
        'transfor-hom-full': [
            'transfor-action',
            'hom',
            'full',
            'off-diagonal'
        ],
        'transfor-hom-capped': [
            'transfor-action',
            'hom',
            'capped',
            'off-diagonal'
        ]
    } as const;
    for (const owner of expectedCoreTargets) {
        const schema = CORE_OWNER_SCHEMAS[owner];
        if (
            schema.kind !== 'projection' ||
            !sameData(
                [
                    schema.family,
                    schema.dimension,
                    schema.extent,
                    schema.variance
                ],
                expectedProjectionMetadata[
                    owner as keyof typeof expectedProjectionMetadata
                ]
            )
        ) {
            fail(
                'INVALID_SPECIFICATION',
                `Application target '${owner}' projection metadata drifted`
            );
        }
    }

    try {
        validateCoreDirected1cReview(CORE_DIRECTED_1C_REVIEW);
    } catch (error: unknown) {
        fail(
            'INVALID_SPECIFICATION',
            'The reviewed dependent section evaluator prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    const sectionObject = specification.applications.find(
        application => application.target === 'section-object-evaluation'
    );
    if (
        sectionObject?.implementationStatus !== 'reviewed-continuation' ||
        !CORE_DIRECTED_1C_REVIEW.authorization.ownerIds.includes(
            'section-object-evaluation'
        )
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'Section object application must reuse reviewed DIRECTED-1C'
        );
    }

    if (
        specification.applications.find(
            application => application.target === 'transfor-hom-capped'
        )?.surfaceDisposition !== 'requires-naturality-gate'
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'Reserved ordinary naturality action was promoted implicitly'
        );
    }
    if (
        specification.applications.find(
            application => application.target ===
                'displayed-functor-laxity'
        )?.implementationStatus !== 'not-active'
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'Deferred whole displayed laxity was treated as active'
        );
    }

    validateUnique(
        'backend binding target catalog',
        bindings.map(binding => binding.target)
    );
    const requiredBindingTargets = new Set<string>([
        ...specification.applications
            .filter(application =>
                application.target !== 'outer-lf-call' &&
                !(application.target in CORE_OWNER_SCHEMAS)
            )
            .map(application => application.target),
        ...specification.structuralPrerequisites.map(entry => entry.target)
    ]);
    if (
        bindings.length !== requiredBindingTargets.size ||
        bindings.some(binding => !requiredBindingTargets.has(binding.target))
    ) {
        fail(
            'INVALID_BACKEND_BINDING',
            'Categorical candidate/structural binding coverage drifted'
        );
    }
    for (const binding of bindings) {
        if (
            binding.provenance.authorityPath !==
                'emdash2/emdash3_2.lp' ||
            binding.provenance.auditedOn !== '2026-07-26' ||
            binding.serializedName.length === 0 ||
            binding.provenance.sourceFragment.length === 0
        ) {
            fail(
                'INVALID_BACKEND_BINDING',
                `Invalid active authority binding for '${binding.target}'`
            );
        }
    }

    const semanticData = JSON.stringify(specification);
    if (
        /piapp|fapp[01]|tapp[01]|tdapp|Fibre_func|emdash2\//u.test(
            semanticData
        )
    ) {
        fail(
            'INVALID_SPECIFICATION',
            'Backend names leaked into the semantic USABILITY-1A data'
        );
    }

    if (!sameData(specification, rawSpecification)) {
        fail(
            'SPECIFICATION_DRIFT',
            'USABILITY-1A exact specification content drifted'
        );
    }
    if (
        !sameData(bindings, [
            ...candidateBindings,
            ...structuralBindings
        ])
    ) {
        fail(
            'SPECIFICATION_DRIFT',
            'USABILITY-1A exact backend evidence drifted'
        );
    }
}

validateCoreCategoricalSurfaceSpecification();
