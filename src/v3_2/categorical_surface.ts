/**
 * USABILITY-1B through USABILITY-2A1 categorical surface and contextual IR.
 *
 * The builder supports the first dependency-ready vertical slice:
 *
 * - typed explicit Core leaves;
 * - scoped categorical object slots;
 * - classifier-directed ordinary functor application;
 * - whole Hom-action requests; and
 * - functorial eta abstraction; and
 * - structural bracket abstraction through the active ordinary basis; and
 * - one honest indexed/displayed section-eta abstraction; and
 * - the approved non-eta displayed section-composition witness when its
 *   explicit USABILITY-DEPENDENT-1A capability is enabled; and
 * - the first direct displayed-functor identity/eta/composition abstraction
 *   when its FIBRED-BINDER-1 capability is enabled; and
 * - direct displayed-transfor eta plus recursively typed vertical component
 *   composition when its FIBRED-TRANSFD-1 capability is enabled.
 *
 * Callback tokens and callbacks are temporary construction devices. The
 * recorded abstraction body is immutable first-order locally nameless data,
 * and the compiled result is existing explicit Core. Unsupported
 * General open indexed bracket abstraction and unsupported higher actions
 * remain fail-closed.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_PREREQUISITES,
    CoreCategoricalDependentPrerequisiteId,
    coreCategoricalDependentCoreName
} from './categorical_dependent_transfer';
import {
    CoreCategoricalDependentCompositionPrerequisiteId,
    coreCategoricalDependentCompositionCoreName
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CoreCategoricalStructuralPrerequisiteId,
    coreCategoricalStructuralCoreName,
    coreCategoricalStructuralSymbolCoreName
} from './categorical_structural_transfer';
import {
    coreCategoricalFibredProductCoreName
} from './categorical_fibred_product_transfer';
import {
    coreCategoricalFibredStructureCoreName
} from './categorical_fibred_structure_transfer';
import {
    coreCategoricalFibredTransfdCoreName
} from './categorical_fibred_transfd_transfer';
import {
    coreCategoricalFibredWeakenReindexCoreName
} from './categorical_fibred_weaken_reindex_transfer';
import {
    coreCategoricalDisplayedEvaluationCoreName
} from './categorical_displayed_evaluation_transfer';
import {
    coreCategoricalDisplayedChainCoreName
} from './categorical_displayed_chain_transfer';
import {
    coreCategoricalDisplayedNdHigherFoundationCoreName
} from './categorical_displayed_nd_higher_foundation_contract';
import {
    coreCategoricalMixedModeCoreName
} from './categorical_mixed_mode_contract';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
} from './categorical_fibred_dependent_target_transfer';
import {
    CoreCategoricalAbstractionJudgment,
    CoreCategoricalAbstractionLayer,
    CoreCategoricalApplicationJudgment,
    CoreCategoricalCellLevel,
    CoreCategoricalDependency,
    CoreCategoricalDiagnosticSpecification,
    CoreCategoricalExpectedShape,
    CoreCategoricalPolarity,
    CoreCategoricalVariation,
    CORE_CATEGORICAL_SURFACE_SPECIFICATION,
    selectCoreCategoricalApplication
} from './categorical_surface_spec';
import type {
    CoreCategoricalCategoryObjectReifier
} from './categorical_classifier_reifier';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from './directed_1a';
import {
    CORE_DIRECTED_1B_PRIMITIVE_NAMES
} from './directed_1b';
import {
    CORE_DIRECTED_1C_PRIMITIVE_NAMES
} from './directed_1c';
import {
    ElaboratedSurfaceTerm,
    V32ElaborationError,
    elaborateSurfaceOperationFromOperands
} from './elaborator';
import {
    KernelExpression,
    Plicity,
    Provenance,
    SourceSpan,
    assertSafeIdentifier,
    formatSourceSpan,
    kernelApplication,
    kernelAssertScoped,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance,
    sourceSpan
} from './kernel';
import {
    CoreType,
    coreObjectCategoryEquals,
    coreTypeEquals,
    coreTypeForCategoryObject,
    coreTypeObjectCategory
} from './surface';

const CORE_CATEGORICAL_TERM = Symbol('CoreCategoricalTerm');
const CORE_CATEGORICAL_SLOT = Symbol('CoreCategoricalSlot');
const CORE_CATEGORICAL_BOUNDARY = Symbol('CoreCategoricalBoundary');

const dependentApplicationQualification = Object.freeze({
    transferredTargets: Object.freeze([
        ...CORE_CATEGORICAL_DEPENDENT_PREREQUISITES.map(
            prerequisite => prerequisite.id
        ),
        'displayed-transfor-component-capped' as const
    ])
});

export interface CoreCategoricalTerm {
    readonly [CORE_CATEGORICAL_TERM]: true;
}

export interface CoreCategoricalSlotToken extends CoreCategoricalTerm {
    readonly [CORE_CATEGORICAL_SLOT]: true;
}

export interface CoreCategoricalHomBoundary {
    readonly [CORE_CATEGORICAL_BOUNDARY]: true;
}

export interface CoreCategoricalSlotUsage {
    readonly index: number;
    readonly count: number;
}

/**
 * A fibre-object classifier whose index is a locally nameless contextual
 * slot, not a Core De Bruijn variable.
 *
 * This classifier exists only in the first-order categorical construction
 * IR. It cannot be passed to the closed Core checker until an enclosing
 * dependent abstraction has eliminated the contextual index.
 */
export interface CoreCategoricalIndexedObjectClassifier {
    readonly tag: 'indexed-object';
    /** Shared locally nameless scope base. */
    readonly baseCategory: KernelExpression;
    /** Actual displayed-family domain; defaults to the shared scope base. */
    readonly familyBaseCategory?: KernelExpression;
    readonly family: KernelExpression;
    readonly index: number;
}

/**
 * A displayed functor projected at one contextual base slot.
 *
 * Like `indexed-object`, this classifier is construction-only. The enclosing
 * approved dependent abstraction must eliminate its locally nameless index
 * before explicit Core reaches the checker.
 */
export interface CoreCategoricalIndexedFunctorClassifier {
    readonly tag: 'indexed-functor';
    /** Shared locally nameless scope base. */
    readonly baseCategory: KernelExpression;
    readonly sourceFamilyBaseCategory?: KernelExpression;
    readonly targetFamilyBaseCategory?: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly index: number;
    /**
     * Exact displayed family of which this fibre functor is also an object.
     * Present only after recognizing the canonical `Functor_catd` owner.
     */
    readonly underlyingObjectFamily?: KernelExpression;
    readonly underlyingObjectFamilyBaseCategory?: KernelExpression;
}

/**
 * A coherent displayed transformation projected at one contextual base slot.
 *
 * The classifier is construction-only. The enclosing direct `:^nd`
 * abstraction must eliminate the slot before explicit Core is checked.
 */
export interface CoreCategoricalIndexedTransforClassifier {
    readonly tag: 'indexed-transfor';
    readonly baseCategory: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly sourceFunctor: KernelExpression;
    readonly targetFunctor: KernelExpression;
    readonly index: number;
}

/**
 * One fibre object of a source or target family inside the canonical nested
 * `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)` classifier.
 *
 * Both indices are locally nameless construction indices. No open endpoint
 * family is serialized into Core; the active kernel sections retain its
 * mixed variance.
 */
export interface CoreCategoricalNestedIndexedObjectClassifier {
    readonly tag: 'nested-indexed-object';
    readonly outerBaseCategory: KernelExpression;
    readonly outerIndex: number;
    readonly innerBaseCategory: KernelExpression;
    readonly innerIndex: number;
    readonly classifierFamily: KernelExpression;
    readonly sourceSection: KernelExpression;
    readonly targetSection: KernelExpression;
    readonly endpoint: 'source' | 'target';
}

export type CoreCategoricalClassifier =
    | CoreType
    | CoreCategoricalIndexedObjectClassifier
    | CoreCategoricalIndexedFunctorClassifier
    | CoreCategoricalIndexedTransforClassifier
    | CoreCategoricalNestedIndexedObjectClassifier;

export interface CoreCategoricalDependentContinuationApplicationJudgment {
    readonly id: 'indexed-fibre-functor.object';
    readonly layer: 'categorical';
    readonly subjectClassifier: 'indexed-fibre-functor';
    readonly subjectForm: 'term';
    readonly argumentDimension: 'object';
    readonly expectedShape: 'object-value';
    readonly dependency: 'displayed';
    readonly target: 'indexed-fibre-functor-object';
    readonly consumesSubjectTerm: true;
    readonly implementationStatus: 'reviewed-continuation';
    readonly surfaceDisposition: 'eligible';
    readonly rule: string;
}

/**
 * This continuation row is intentionally outside the frozen sixteen-row
 * USABILITY-1A application partition. It records only the approved D-003
 * contextual application needed by the first non-eta dependent witness.
 */
export const CORE_CATEGORICAL_DEPENDENT_CONTINUATION_APPLICATION:
CoreCategoricalDependentContinuationApplicationJudgment = Object.freeze({
    id: 'indexed-fibre-functor.object',
    layer: 'categorical',
    subjectClassifier: 'indexed-fibre-functor',
    subjectForm: 'term',
    argumentDimension: 'object',
    expectedShape: 'object-value',
    dependency: 'displayed',
    target: 'indexed-fibre-functor-object',
    consumesSubjectTerm: true,
    implementationStatus: 'reviewed-continuation',
    surfaceDisposition: 'eligible',
    rule:
        'A displayed functor projected at the same contextual base index ' +
        'acts on an indexed object of its source family.'
});

export interface CoreCategoricalDisplayedEvaluationApplicationJudgment {
    readonly id:
        | 'displayed-evaluation.varying-argument'
        | 'displayed-evaluation.fixed-argument';
    readonly layer: 'categorical';
    readonly subjectClassifier:
        'indexed-constant-domain-functor-family-object';
    readonly subjectForm: 'term';
    readonly argumentDimension: 'object';
    readonly expectedShape: 'object-value';
    readonly dependency: 'displayed';
    readonly target:
        | 'displayed-evaluation-varying-object'
        | 'displayed-evaluation-fixed-object';
    readonly consumesSubjectTerm: true;
    readonly implementationStatus: 'reviewed-continuation';
    readonly surfaceDisposition: 'eligible';
    readonly rule: string;
}

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_VARYING_APPLICATION:
CoreCategoricalDisplayedEvaluationApplicationJudgment = Object.freeze({
    id: 'displayed-evaluation.varying-argument',
    layer: 'categorical',
    subjectClassifier:
        'indexed-constant-domain-functor-family-object',
    subjectForm: 'term',
    argumentDimension: 'object',
    expectedShape: 'object-value',
    dependency: 'displayed',
    target: 'displayed-evaluation-varying-object',
    consumesSubjectTerm: true,
    implementationStatus: 'reviewed-continuation',
    surfaceDisposition: 'eligible',
    rule:
        'A recursively compiled object of ' +
        'Functor_catd(Const_(Op K)(A),B) evaluates at a recursively ' +
        'compiled object of Const_K(A).'
});

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_FIXED_APPLICATION:
CoreCategoricalDisplayedEvaluationApplicationJudgment = Object.freeze({
    id: 'displayed-evaluation.fixed-argument',
    layer: 'categorical',
    subjectClassifier:
        'indexed-constant-domain-functor-family-object',
    subjectForm: 'term',
    argumentDimension: 'object',
    expectedShape: 'object-value',
    dependency: 'displayed',
    target: 'displayed-evaluation-fixed-object',
    consumesSubjectTerm: true,
    implementationStatus: 'reviewed-continuation',
    surfaceDisposition: 'eligible',
    rule:
        'A recursively compiled object of ' +
        'Functor_catd(Const_(Op K)(A),B) evaluates at a closed object of A ' +
        'through Terminal_funcd and the existing constant-section package.'
});

type CoreCategoricalStoredApplicationJudgment =
    | CoreCategoricalApplicationJudgment
    | CoreCategoricalDependentContinuationApplicationJudgment
    | CoreCategoricalDisplayedEvaluationApplicationJudgment;

export type CoreCategoricalContextualIr =
    | {
        readonly tag: 'slot-reference';
        readonly index: number;
        readonly hint: string;
        readonly type: CoreCategoricalClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'explicit-core-term';
        readonly term: KernelExpression;
        readonly type: CoreCategoricalClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-application';
        readonly judgmentId: string;
        readonly target:
            CoreCategoricalStoredApplicationJudgment['target'];
        readonly subject: CoreCategoricalContextualIr;
        readonly argument:
            | CoreCategoricalContextualIr
            | CoreCategoricalHomBoundaryIr;
        readonly type: CoreCategoricalClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-cell-composition';
        readonly outer: CoreCategoricalContextualIr;
        readonly inner: CoreCategoricalContextualIr;
        readonly type: CoreCategoricalIndexedTransforClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-pair';
        readonly left: CoreCategoricalContextualIr;
        readonly right: CoreCategoricalContextualIr;
        readonly type: CoreCategoricalIndexedObjectClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-nested-displayed-application';
        readonly subject: CoreCategoricalContextualIr;
        readonly base: CoreCategoricalContextualIr;
        readonly argument: CoreCategoricalContextualIr;
        readonly type: CoreCategoricalNestedIndexedObjectClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'nested-displayed-abstraction';
        readonly name: string;
        readonly innerBaseCategory: KernelExpression;
        readonly subject: CoreCategoricalContextualIr;
        readonly body: CoreCategoricalContextualIr;
        readonly type: CoreCategoricalIndexedObjectClassifier;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'categorical-abstraction';
        readonly name: string;
        readonly sourceCategory: KernelExpression;
        readonly targetCategory: KernelExpression;
        readonly body: CoreCategoricalContextualIr;
        readonly type: CoreCategoricalClassifier;
        readonly provenance: Provenance;
    };

export interface CoreCategoricalHomBoundaryIr {
    readonly tag: 'hom-boundary';
    readonly category: KernelExpression;
    readonly sourceEndpoint: CoreCategoricalContextualIr;
    readonly targetEndpoint: CoreCategoricalContextualIr;
    readonly provenance: Provenance;
}

interface CoreCategoricalAbstractionEvidenceBase {
    readonly name: string;
    readonly plicity: Plicity;
    readonly polarity: 'covariant';
    readonly cellLevel: 'object';
    readonly sourceCategory: KernelExpression;
    readonly body: CoreCategoricalContextualIr;
    readonly result: CoreCategoricalContextualIr;
    readonly structuralPrerequisites:
        readonly CoreCategoricalStructuralPrerequisiteId[];
    readonly dependentPrerequisites:
        readonly CoreCategoricalDependentApplicationPrerequisiteId[];
    readonly provenance: Provenance;
}

export interface CoreCategoricalDisplayedTelescopeLayerEvidence {
    readonly layerIndex: number;
    readonly baseCategory: KernelExpression;
    readonly bindingNames: readonly string[];
    readonly sourceFamilies: readonly KernelExpression[];
    readonly sourceFamily: KernelExpression;
}

export type CoreCategoricalAbstractionEvidence =
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                | 'categorical.eta'
                | 'categorical.bracket';
            readonly variation: 'functorial';
            readonly dependency: 'ordinary';
            readonly targetCategory: KernelExpression;
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                | 'categorical.dependent-eta'
                | 'categorical.dependent-section-composition';
            readonly variation: 'natural';
            readonly dependency: 'displayed';
            readonly targetFamily: KernelExpression;
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                | 'categorical.displayed-functor-identity'
                | 'categorical.displayed-functor-eta'
                | 'categorical.displayed-functor-composition'
                | 'categorical.displayed-functor-weakening';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly sourceFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly chainLength: number;
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                'categorical.displayed-context-bracket';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly bindingNames: readonly string[];
            readonly sourceFamilies: readonly KernelExpression[];
            readonly sourceFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly contextSize: number;
            readonly contextRelation:
                'shared-minimal-base-siblings';
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                'categorical.displayed-dependent-context-bracket';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly bindingNames: readonly [string, string];
            readonly sourceFamilies:
                readonly [KernelExpression, KernelExpression];
            readonly sourceFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly contextRootCategory: KernelExpression;
            readonly totalBaseCategory: KernelExpression;
            readonly liftedPrefixFamily: KernelExpression;
            readonly contextSize: 2;
            readonly contextRelation:
                'one-genuine-dependency-edge';
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                'categorical.displayed-mixed-dependent-context-bracket';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly bindingNames:
                readonly [string, string, string, string];
            readonly sourceFamilies:
                readonly [
                    KernelExpression,
                    KernelExpression,
                    KernelExpression,
                    KernelExpression
                ];
            readonly liftedBindingFamilies:
                readonly [
                    KernelExpression,
                    KernelExpression,
                    KernelExpression,
                    KernelExpression
                ];
            readonly sourceFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly contextRootCategory: KernelExpression;
            readonly firstTotalBaseCategory: KernelExpression;
            readonly groupedMiddleFamily: KernelExpression;
            readonly totalBaseCategory: KernelExpression;
            readonly contextSize: 4;
            readonly siblingGroup: readonly [string, string];
            readonly contextRelation:
                'two-dependency-transitions-with-middle-siblings';
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                'categorical.displayed-generic-dependent-context-bracket';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly bindingNames: readonly string[];
            readonly sourceFamilies: readonly KernelExpression[];
            readonly liftedBindingFamilies:
                readonly KernelExpression[];
            readonly sourceFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly contextRootCategory: KernelExpression;
            readonly finalBaseCategory: KernelExpression;
            readonly layers:
                readonly CoreCategoricalDisplayedTelescopeLayerEvidence[];
            readonly contextSize: number;
            readonly contextRelation:
                'arbitrary-finite-canonical-layer-fold';
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                'categorical.mixed-nested-displayed-eta';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly outerBaseCategory: KernelExpression;
            readonly innerBaseCategory: KernelExpression;
            readonly classifierFamily: KernelExpression;
            readonly sourceSection: KernelExpression;
            readonly targetSection: KernelExpression;
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                'categorical.direct-mixed-displayed-functor';
            readonly variation: 'functorial';
            readonly dependency: 'displayed';
            readonly bindingNames:
                readonly [string, string, string];
            readonly bindingModes:
                readonly ['natural', 'functorial', 'functorial'];
            readonly outerSourceFamily: KernelExpression;
            readonly innerSourceFamily: KernelExpression;
            readonly rootSourceFamily: KernelExpression;
            readonly initialTargetFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly resultFamily: KernelExpression;
            readonly rootKind:
                | 'closed-coherent-subject'
                | 'bound-outer-identity'
                | 'outer-value-weakening'
                | 'recursive-pair';
            readonly rootSourceFamilies:
                readonly KernelExpression[];
            readonly initialTargetFamilies:
                readonly KernelExpression[];
            readonly leafCount: number;
            readonly outerUsageCount: number;
            readonly innerUsageCount: number;
            readonly sourceChainLength: number;
            readonly targetChainLength: number;
            readonly pairNodeCount: number;
            readonly pairDepth: number;
            readonly contextSize: 3;
            readonly contextRelation:
                'natural-base-then-two-functorial-fibre-binders';
        }
    )
    | (
        CoreCategoricalAbstractionEvidenceBase & {
            readonly rule:
                | 'categorical.displayed-transfor-eta'
                | 'categorical.displayed-transfor-composition';
            readonly variation: 'natural';
            readonly dependency: 'displayed';
            readonly sourceFamily: KernelExpression;
            readonly targetFamily: KernelExpression;
            readonly sourceFunctor: KernelExpression;
            readonly targetFunctor: KernelExpression;
        }
    );

export interface CoreCategoricalTermInspection {
    readonly type: CoreCategoricalClassifier;
    readonly usage: readonly CoreCategoricalSlotUsage[];
    readonly ir: CoreCategoricalContextualIr;
    readonly abstractions:
        readonly CoreCategoricalAbstractionEvidence[];
    readonly dependentPrerequisites:
        readonly CoreCategoricalDependentApplicationPrerequisiteId[];
    readonly lowered: boolean;
}

export type CoreCategoricalDependentApplicationPrerequisiteId =
    | 'section-object-evaluation'
    | 'displayed-identity'
    | 'sigma-projection-pullback'
    | 'sigma-pi-uncurrying-proof'
    | 'displayed-transfor-component-capped'
    | 'displayed-transfor-higher-cell'
    | 'sigma-first-projection'
    | 'section-pullback-functor'
    | 'constant-displayed-family-object'
    | 'internal-product-functor'
    | 'displayed-product-left-projection'
    | 'displayed-product-right-projection'
    | 'displayed-product-pair'
    | 'stable-functor-family'
    | 'displayed-evaluation'
    | 'displayed-terminal'
    | 'constant-section-functor'
    | 'sigma-functord-section'
    | 'mixed-functor-target-action'
    | 'mixed-functor-source-action'
    | 'mixed-functor-product-distributor'
    | 'mixed-functor-weakening'
    | CoreCategoricalDependentPrerequisiteId
    | CoreCategoricalDependentCompositionPrerequisiteId;

export interface CoreCategoricalScopedBuilderOptions {
    /**
     * Optional reviewed runtime-backed canonical category-object reifier.
     * It changes only construction-time type metadata; final generic Core LF
     * checking remains mandatory and the elaborated term is never changed.
     */
    readonly categoryObjectReifier?:
        CoreCategoricalCategoryObjectReifier;
    /**
     * Enable only the approved D-003 section-composition continuation. The
     * default preserves the reviewed USABILITY-2A1 eta-only envelope.
     */
    readonly dependentSectionComposition?: boolean;
    /**
     * Enable only the FIBRED-BINDER-1 direct displayed-functor
     * identity/eta/composition contract.
     */
    readonly displayedFunctorAbstraction?: boolean;
    /**
     * Enable the FIBRED-TRANSFD-1 coherent component-eta abstraction and
     * DISPLAYED-ND-1A recursive typed vertical component composition.
     */
    readonly displayedTransforAbstraction?: boolean;
    /**
     * Enable only the existing-authority FIBRED-WEAKEN-REINDEX-1
     * contextual-index weakening and displayed reindexing contract.
     */
    readonly displayedWeakeningReindexing?: boolean;
    /**
     * Enable only the reviewed DISPLAYED-BRACKET-1A finite independent
     * sibling compiler and typed fibre-pair construction node.
     */
    readonly displayedContextualAbstraction?: boolean;
    /**
     * Enable only the two DISPLAYED-EVAL-1A recursive typed-application
     * judgments over the stable constant-domain `Functor_catd` family.
     */
    readonly displayedEvaluation?: boolean;
    /**
     * Enable only DISPLAYED-CHAIN-1A's recursive compiler for one genuine
     * dependency edge `k : K; a : A[k]; b : B[(k,a)]`.
     */
    readonly displayedDependentContextualAbstraction?: boolean;
    /**
     * Enable D-DTTLF-USABILITY-026's arbitrary finite canonical sibling-layer
     * fold. The flat binding list must carry literal family bases and must
     * contain at least two Sigma-separated layers.
     */
    readonly displayedGenericTelescope?: boolean;
    /**
     * Enable only MIXED-NEST-1A's exact recursive eta/factorization for an
     * already-coherent object of the canonical mixed nested Hom family.
     */
    readonly mixedNestedFactorization?: boolean;
    /**
     * Enable D-DTTLF-USABILITY-043's direct recursive mixed introduction.
     * The injected Core name is the already transferred
     * `Functor_catd_fapp0_func`; this surface does not import its transfer
     * audit graph or any contextual-curry module.
     */
    readonly directMixedIntroduction?: {
        readonly mixedFunctorFamilyCoreName: string;
        readonly mixedFunctorFamilyPartialCoreName: string;
        readonly mixedProductDistributorCoreName: string;
        readonly mixedConstantWeakeningCoreName: string;
    };
}

export interface CoreCategoricalBinderOptions {
    readonly plicity?: Plicity;
    readonly variation?: CoreCategoricalVariation;
    readonly polarity?: CoreCategoricalPolarity;
    readonly cellLevel?: CoreCategoricalCellLevel;
    readonly dependency?: CoreCategoricalDependency;
    readonly provenance?: Provenance;
}

export interface CoreCategoricalAbstractionRequest {
    readonly requestedLayer?: CoreCategoricalAbstractionLayer;
    readonly expectedClassifier?:
        | 'outer-lf-pi'
        | 'ordinary-functor'
        | 'displayed-or-indexed-family';
    readonly provenance?: Provenance;
}

export type CoreCategoricalFrontendErrorCode =
    | CoreCategoricalDiagnosticSpecification['code']
    | 'INVALID_TERM'
    | 'FOREIGN_TERM'
    | 'ESCAPED_SLOT'
    | 'EXPECTED_FUNCTOR'
    | 'UNLOWERED_CONTEXT';

export class CoreCategoricalFrontendError extends Error {
    constructor(
        public readonly code: CoreCategoricalFrontendErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly underlying?: Error
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreCategoricalFrontendError';
    }
}

type TemporaryCategoricalNode =
    | {
        readonly tag: 'explicit-core-term';
        readonly term: KernelExpression;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'slot-token';
        readonly ordinal: number;
        readonly hint: string;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-application';
        readonly judgment: CoreCategoricalStoredApplicationJudgment;
        readonly subject: InternalCoreCategoricalTerm;
        readonly argument:
            | InternalCoreCategoricalTerm
            | InternalCoreCategoricalHomBoundary;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-cell-composition';
        readonly outer: InternalCoreCategoricalTerm;
        readonly inner: InternalCoreCategoricalTerm;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-pair';
        readonly left: InternalCoreCategoricalTerm;
        readonly right: InternalCoreCategoricalTerm;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'typed-nested-displayed-application';
        readonly subject: InternalCoreCategoricalTerm;
        readonly base: InternalCoreCategoricalTerm;
        readonly argument: InternalCoreCategoricalTerm;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'nested-displayed-abstraction';
        readonly baseOrdinal: number;
        readonly fibreOrdinal: number;
        readonly name: string;
        readonly innerBaseCategory: KernelExpression;
        readonly subject: InternalCoreCategoricalTerm;
        readonly body: InternalCoreCategoricalTerm;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'categorical-abstraction';
        readonly ordinal: number;
        readonly name: string;
        readonly sourceCategory: KernelExpression;
        readonly targetCategory: KernelExpression;
        readonly body: InternalCoreCategoricalTerm;
        readonly provenance: Provenance;
    };

interface InternalCoreCategoricalTerm extends CoreCategoricalTerm {
    readonly builderIdentity: symbol;
    readonly node: TemporaryCategoricalNode;
    readonly type: InternalCoreCategoricalClassifier;
    readonly usage: InternalCategoricalUsage;
    readonly closed?: ElaboratedSurfaceTerm;
    readonly abstractions:
        readonly CoreCategoricalAbstractionEvidence[];
    readonly [CORE_CATEGORICAL_SLOT]?: true;
    /**
     * Frontend semantic origin for the exact structural weakening
     * `λ a :^fd E. s[indexOf(a)]`. It is not serialized into Core.
     */
    readonly displayedSectionWeakening?: {
        readonly section: InternalCoreCategoricalTerm;
    };
    /**
     * The fibre functor obtained by projecting that weakening at a base
     * point. This lets object application lower to `s[k]` without claiming a
     * new kernel rewrite for the transparent point functor.
     */
    readonly displayedWeakeningFibre?: {
        readonly section: InternalCoreCategoricalTerm;
        readonly basePoint: InternalCoreCategoricalTerm;
    };
}

interface InternalCoreCategoricalTermMetadata {
    readonly displayedSectionWeakening?: {
        readonly section: InternalCoreCategoricalTerm;
    };
    readonly displayedWeakeningFibre?: {
        readonly section: InternalCoreCategoricalTerm;
        readonly basePoint: InternalCoreCategoricalTerm;
    };
}

interface InternalCoreCategoricalIndexedObjectClassifier {
    readonly tag: 'indexed-object';
    readonly baseCategory: KernelExpression;
    readonly familyBaseCategory?: KernelExpression;
    readonly family: KernelExpression;
    readonly indexOrdinal: number;
}

interface InternalCoreCategoricalIndexedFunctorClassifier {
    readonly tag: 'indexed-functor';
    readonly baseCategory: KernelExpression;
    readonly sourceFamilyBaseCategory?: KernelExpression;
    readonly targetFamilyBaseCategory?: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly indexOrdinal: number;
    readonly underlyingObjectFamily?: KernelExpression;
    readonly underlyingObjectFamilyBaseCategory?: KernelExpression;
}

interface InternalCoreCategoricalIndexedTransforClassifier {
    readonly tag: 'indexed-transfor';
    readonly baseCategory: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly sourceFunctor: KernelExpression;
    readonly targetFunctor: KernelExpression;
    readonly indexOrdinal: number;
}

interface InternalCoreCategoricalNestedIndexedObjectClassifier {
    readonly tag: 'nested-indexed-object';
    readonly outerBaseCategory: KernelExpression;
    readonly outerIndexOrdinal: number;
    readonly innerBaseCategory: KernelExpression;
    readonly innerIndexOrdinal: number;
    readonly classifierFamily: KernelExpression;
    readonly sourceSection: KernelExpression;
    readonly targetSection: KernelExpression;
    readonly endpoint: 'source' | 'target';
}

type InternalCoreCategoricalClassifier =
    | CoreType
    | InternalCoreCategoricalIndexedObjectClassifier
    | InternalCoreCategoricalIndexedFunctorClassifier
    | InternalCoreCategoricalIndexedTransforClassifier
    | InternalCoreCategoricalNestedIndexedObjectClassifier;

interface CoreCategoricalMixedNestedFunctorShape {
    readonly outerBaseCategory: KernelExpression;
    readonly innerBaseCategory: KernelExpression;
    readonly classifierFamily: KernelExpression;
    readonly sourceSection: KernelExpression;
    readonly targetSection: KernelExpression;
}

interface CoreCategoricalMixedFunctorFamilyShape {
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
}

interface CoreCategoricalDirectMixedLeafFactorization {
    readonly tag: 'leaf';
    readonly rootExpression: KernelExpression;
    readonly rootRecovered: ElaboratedSurfaceTerm['recovered'];
    readonly rootKind:
        | 'closed-coherent-subject'
        | 'bound-outer-identity'
        | 'outer-value-weakening';
    readonly rootBaseUsageCount: 0 | 1;
    readonly rootSourceFamily: KernelExpression;
    readonly sourceChain: readonly InternalCoreCategoricalTerm[];
    readonly initialTargetFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
}

interface CoreCategoricalDirectMixedTargetFactorization {
    readonly tag: 'target-map';
    readonly child: CoreCategoricalDirectMixedFactorization;
    readonly mapper: InternalCoreCategoricalTerm;
    readonly targetFamily: KernelExpression;
}

interface CoreCategoricalDirectMixedPairFactorization {
    readonly tag: 'pair';
    readonly left: CoreCategoricalDirectMixedFactorization;
    readonly right: CoreCategoricalDirectMixedFactorization;
    readonly targetFamily: KernelExpression;
}

type CoreCategoricalDirectMixedFactorization =
    | CoreCategoricalDirectMixedLeafFactorization
    | CoreCategoricalDirectMixedTargetFactorization
    | CoreCategoricalDirectMixedPairFactorization;

interface CoreCategoricalDirectMixedSourceFactorization {
    readonly rootSourceFamily: KernelExpression;
    readonly sourceChain: readonly InternalCoreCategoricalTerm[];
}

interface CoreCategoricalCompiledDirectMixedFactorization {
    readonly compilation: CoreCategoricalDisplayedContextualCompilation;
    readonly recovered: ElaboratedSurfaceTerm['recovered'];
    readonly leafCount: number;
    readonly outerUsageCount: number;
    readonly innerUsageCount: number;
    readonly baseUsageCount: number;
    readonly sourceChainLength: number;
    readonly targetChainLength: number;
    readonly pairNodeCount: number;
    readonly pairDepth: number;
    readonly rootKinds: readonly CoreCategoricalDirectMixedLeafFactorization[
        'rootKind'
    ][];
    readonly rootSourceFamilies: readonly KernelExpression[];
    readonly initialTargetFamilies: readonly KernelExpression[];
}

interface InternalCoreCategoricalHomBoundary
extends CoreCategoricalHomBoundary {
    readonly builderIdentity: symbol;
    readonly category: KernelExpression;
    readonly sourceEndpoint: InternalCoreCategoricalTerm;
    readonly targetEndpoint: InternalCoreCategoricalTerm;
    readonly usage: InternalCategoricalUsage;
    readonly provenance: Provenance;
}

const DEFAULT_CATEGORICAL_SPAN = sourceSpan(
    '<categorical-surface>',
    1,
    1
);

type InternalCategoricalUsage =
    readonly (readonly [ordinal: number, count: number])[];

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object'
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const copyCoreType = (type: CoreType): CoreType => {
    switch (type.tag) {
        case 'category':
            return { tag: 'category' };
        case 'object':
            return { tag: 'object', category: type.category };
        case 'functor':
            return {
                tag: 'functor',
                sourceCategory: type.sourceCategory,
                targetCategory: type.targetCategory
            };
        case 'hom':
            return {
                tag: 'hom',
                category: type.category,
                sourceObject: type.sourceObject,
                targetObject: type.targetObject
            };
        case 'transfor':
            return {
                tag: 'transfor',
                sourceCategory: type.sourceCategory,
                targetCategory: type.targetCategory,
                sourceFunctor: type.sourceFunctor,
                targetFunctor: type.targetFunctor
            };
        case 'dependent-section':
            return {
                tag: 'dependent-section',
                category: type.category,
                baseCategory: type.baseCategory,
                family: type.family
            };
        case 'displayed-functor':
            return {
                tag: 'displayed-functor',
                category: type.category,
                baseCategory: type.baseCategory,
                sourceFamily: type.sourceFamily,
                targetFamily: type.targetFamily
            };
        case 'displayed-transfor':
            return {
                tag: 'displayed-transfor',
                category: type.category,
                baseCategory: type.baseCategory,
                sourceFamily: type.sourceFamily,
                targetFamily: type.targetFamily,
                sourceFunctor: type.sourceFunctor,
                targetFunctor: type.targetFunctor
            };
        default: {
            const exhaustive: never = type;
            return exhaustive;
        }
    }
};

const copyInternalClassifier = (
    classifier: InternalCoreCategoricalClassifier
): InternalCoreCategoricalClassifier => {
    if (classifier.tag === 'indexed-object') {
        return {
            tag: 'indexed-object',
            baseCategory: classifier.baseCategory,
            ...(classifier.familyBaseCategory === undefined
                ? {}
                : {
                    familyBaseCategory:
                        classifier.familyBaseCategory
                }),
            family: classifier.family,
            indexOrdinal: classifier.indexOrdinal
        };
    }
    if (classifier.tag === 'indexed-functor') {
        return {
            tag: 'indexed-functor',
            baseCategory: classifier.baseCategory,
            ...(classifier.sourceFamilyBaseCategory === undefined
                ? {}
                : {
                    sourceFamilyBaseCategory:
                        classifier.sourceFamilyBaseCategory
                }),
            ...(classifier.targetFamilyBaseCategory === undefined
                ? {}
                : {
                    targetFamilyBaseCategory:
                        classifier.targetFamilyBaseCategory
                }),
            sourceFamily: classifier.sourceFamily,
            targetFamily: classifier.targetFamily,
            indexOrdinal: classifier.indexOrdinal,
            ...(classifier.underlyingObjectFamily === undefined
                ? {}
                : {
                    underlyingObjectFamily:
                        classifier.underlyingObjectFamily
                }),
            ...(
                classifier.underlyingObjectFamilyBaseCategory === undefined
                    ? {}
                    : {
                        underlyingObjectFamilyBaseCategory:
                            classifier
                                .underlyingObjectFamilyBaseCategory
                    }
            )
        };
    }
    if (classifier.tag === 'indexed-transfor') {
        return {
            tag: 'indexed-transfor',
            baseCategory: classifier.baseCategory,
            sourceFamily: classifier.sourceFamily,
            targetFamily: classifier.targetFamily,
            sourceFunctor: classifier.sourceFunctor,
            targetFunctor: classifier.targetFunctor,
            indexOrdinal: classifier.indexOrdinal
        };
    }
    if (classifier.tag === 'nested-indexed-object') {
        return {
            tag: 'nested-indexed-object',
            outerBaseCategory: classifier.outerBaseCategory,
            outerIndexOrdinal: classifier.outerIndexOrdinal,
            innerBaseCategory: classifier.innerBaseCategory,
            innerIndexOrdinal: classifier.innerIndexOrdinal,
            classifierFamily: classifier.classifierFamily,
            sourceSection: classifier.sourceSection,
            targetSection: classifier.targetSection,
            endpoint: classifier.endpoint
        };
    }
    return copyCoreType(classifier);
};

interface InternalCoreCategoricalIndexedObjectView {
    readonly baseCategory: KernelExpression;
    readonly familyBaseCategory: KernelExpression;
    readonly family: KernelExpression;
    readonly indexOrdinal: number;
}

/**
 * Recover the object-family view retained by a canonical rich classifier.
 * This is construction metadata only; it neither emits a coercion nor adds a
 * convertibility rule to Core.
 */
const indexedObjectView = (
    classifier: InternalCoreCategoricalClassifier
): InternalCoreCategoricalIndexedObjectView | undefined => {
    if (classifier.tag === 'indexed-object') {
        return {
            baseCategory: classifier.baseCategory,
            familyBaseCategory:
                classifier.familyBaseCategory ?? classifier.baseCategory,
            family: classifier.family,
            indexOrdinal: classifier.indexOrdinal
        };
    }
    if (
        classifier.tag === 'indexed-functor' &&
        classifier.underlyingObjectFamily !== undefined
    ) {
        return {
            baseCategory: classifier.baseCategory,
            familyBaseCategory:
                classifier.underlyingObjectFamilyBaseCategory ??
                classifier.baseCategory,
            family: classifier.underlyingObjectFamily,
            indexOrdinal: classifier.indexOrdinal
        };
    }
    return undefined;
};

const indexedFunctorSourceBase = (
    classifier: InternalCoreCategoricalIndexedFunctorClassifier
): KernelExpression =>
    classifier.sourceFamilyBaseCategory ?? classifier.baseCategory;

const indexedFunctorTargetBase = (
    classifier: InternalCoreCategoricalIndexedFunctorClassifier
): KernelExpression =>
    classifier.targetFamilyBaseCategory ?? classifier.baseCategory;

const mergeUsage = (
    ...usages: readonly InternalCategoricalUsage[]
): InternalCategoricalUsage => {
    const merged = new Map<number, number>();
    for (const usage of usages) {
        for (const [ordinal, count] of usage) {
            merged.set(ordinal, (merged.get(ordinal) ?? 0) + count);
        }
    }
    return Object.freeze(
        [...merged.entries()].map(entry =>
            Object.freeze(entry) as readonly [number, number]
        )
    );
};

const usageCount = (
    usage: InternalCategoricalUsage,
    ordinal: number
): number => usage.find(entry => entry[0] === ordinal)?.[1] ?? 0;

const removeUsage = (
    usage: InternalCategoricalUsage,
    ordinal: number
): InternalCategoricalUsage => Object.freeze(
    usage.filter(entry => entry[0] !== ordinal)
);

const usageIntersects = (
    usage: InternalCategoricalUsage,
    ordinals: ReadonlySet<number>
): boolean => usage.some(([ordinal]) => ordinals.has(ordinal));

const mergePrerequisites = (
    ...lists: readonly (
        readonly CoreCategoricalStructuralPrerequisiteId[]
    )[]
): readonly CoreCategoricalStructuralPrerequisiteId[] => {
    const result: CoreCategoricalStructuralPrerequisiteId[] = [];
    for (const list of lists) {
        for (const prerequisite of list) {
            if (!result.includes(prerequisite)) {
                result.push(prerequisite);
            }
        }
    }
    return Object.freeze(result);
};

const mergeDependentPrerequisites = (
    ...lists: readonly (
        readonly CoreCategoricalDependentApplicationPrerequisiteId[]
    )[]
): readonly CoreCategoricalDependentApplicationPrerequisiteId[] => {
    const result: CoreCategoricalDependentApplicationPrerequisiteId[] = [];
    for (const list of lists) {
        for (const prerequisite of list) {
            if (!result.includes(prerequisite)) {
                result.push(prerequisite);
            }
        }
    }
    return Object.freeze(result);
};

const collectDependentPrerequisites = (
    term: CoreCategoricalContextualIr
): readonly CoreCategoricalDependentApplicationPrerequisiteId[] => {
    const result: CoreCategoricalDependentApplicationPrerequisiteId[] = [];
    const add = (
        prerequisite: CoreCategoricalDependentApplicationPrerequisiteId
    ): void => {
        if (!result.includes(prerequisite)) result.push(prerequisite);
    };
    const visitBoundary = (
        boundary: CoreCategoricalHomBoundaryIr
    ): void => {
        visit(boundary.sourceEndpoint);
        visit(boundary.targetEndpoint);
    };
    const visit = (current: CoreCategoricalContextualIr): void => {
        switch (current.tag) {
            case 'slot-reference':
            case 'explicit-core-term':
                return;
            case 'typed-application':
                if (
                    current.target ===
                        'section-object-evaluation' ||
                    current.target === 'displayed-functor-fibre' ||
                    current.target === 'displayed-functor-transport' ||
                    current.target ===
                        'displayed-transfor-component-capped'
                ) {
                    add(
                        current.target ===
                            'displayed-transfor-component-capped'
                            ? 'displayed-transfor-component-capped'
                            : current.target
                    );
                }
                visit(current.subject);
                if (current.argument.tag === 'hom-boundary') {
                    visitBoundary(current.argument);
                } else {
                    visit(current.argument);
                }
                return;
            case 'typed-cell-composition':
                visit(current.outer);
                visit(current.inner);
                add('generic-category-composition');
                return;
            case 'typed-pair':
                visit(current.left);
                visit(current.right);
                return;
            case 'typed-nested-displayed-application':
                visit(current.subject);
                visit(current.base);
                visit(current.argument);
                return;
            case 'nested-displayed-abstraction':
                visit(current.subject);
                visit(current.body);
                return;
            case 'categorical-abstraction':
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };
    visit(term);
    return Object.freeze(result);
};

interface CoreCategoricalContextualCompilation {
    readonly term: KernelExpression;
    readonly targetCategory: KernelExpression;
    readonly structuralPrerequisites:
        readonly CoreCategoricalStructuralPrerequisiteId[];
}

type CoreCategoricalWiring =
ReadonlyMap<number, CoreCategoricalContextualCompilation>;

interface CoreCategoricalDisplayedContextualCompilation {
    readonly term: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly identity: boolean;
    readonly structuralPrerequisites:
        readonly CoreCategoricalStructuralPrerequisiteId[];
    readonly dependentPrerequisites:
        readonly CoreCategoricalDependentApplicationPrerequisiteId[];
}

interface CoreCategoricalDisplayedFamilyTree {
    readonly family: KernelExpression;
    readonly ordinal?: number;
    readonly left?: CoreCategoricalDisplayedFamilyTree;
    readonly right?: CoreCategoricalDisplayedFamilyTree;
}

type CoreCategoricalDisplayedWiring =
ReadonlyMap<number, CoreCategoricalDisplayedContextualCompilation>;

const abstractionById = (
    id: CoreCategoricalAbstractionJudgment['id']
): CoreCategoricalAbstractionJudgment => {
    const judgment =
        CORE_CATEGORICAL_SURFACE_SPECIFICATION.abstractions.find(
            candidate => candidate.id === id
        );
    if (!judgment) {
        throw new Error(`Missing frozen abstraction judgment '${id}'`);
    }
    return judgment;
};

/**
 * Resolve the abstraction layer from syntax and/or an expected classifier.
 */
export function selectCoreCategoricalAbstraction(
    request: CoreCategoricalAbstractionRequest
): CoreCategoricalAbstractionJudgment {
    const nodeProvenance = request.provenance ?? provenance(
        'surface',
        'categorical abstraction selection',
        DEFAULT_CATEGORICAL_SPAN
    );
    const expectedLayer = request.expectedClassifier === undefined
        ? undefined
        : request.expectedClassifier === 'outer-lf-pi'
            ? 'outer-lf'
            : 'categorical';

    if (
        request.requestedLayer !== undefined &&
        expectedLayer !== undefined &&
        request.requestedLayer !== expectedLayer
    ) {
        throw new CoreCategoricalFrontendError(
            'CLASSIFIER_ARGUMENT_MISMATCH',
            nodeProvenance,
            `Requested ${request.requestedLayer} abstraction but expected ` +
            `${request.expectedClassifier}`
        );
    }

    const layer = request.requestedLayer ?? expectedLayer;
    if (layer === undefined) {
        throw new CoreCategoricalFrontendError(
            'AMBIGUOUS_ABSTRACTION_LAYER',
            nodeProvenance,
            'Abstraction needs either explicit outer-LF/categorical syntax ' +
            'or an expected Pi/functor classifier'
        );
    }
    if (layer === 'outer-lf') {
        return abstractionById('outer-lf-abstraction');
    }
    return request.expectedClassifier ===
        'displayed-or-indexed-family'
        ? abstractionById('natural-indexed-abstraction')
        : abstractionById('ordinary-functorial-abstraction');
}

/**
 * Builder-local categorical surface. There is no global token registry.
 */
export class CoreCategoricalScopedBuilder {
    private readonly builderIdentity = Symbol(
        'CoreCategoricalScopedBuilder'
    );
    private readonly activeTokenOrdinals: number[] = [];
    private nextTokenOrdinal = 0;
    private readonly activeDisplayedBases =
        new Map<number, InternalCoreCategoricalTerm>();
    private readonly options:
        Readonly<CoreCategoricalScopedBuilderOptions>;

    constructor(
        private readonly defaultProvenance: Provenance = provenance(
            'derived',
            'scoped categorical surface builder',
            DEFAULT_CATEGORICAL_SPAN
        ),
        options: CoreCategoricalScopedBuilderOptions = {}
    ) {
        this.options = Object.freeze({ ...options });
    }

    private nodeProvenance(
        detail: string,
        supplied?: Provenance
    ): Provenance {
        return supplied ?? provenance(
            'derived',
            detail,
            this.defaultProvenance.span
        );
    }

    private fail(
        code: CoreCategoricalFrontendErrorCode,
        nodeProvenance: Provenance,
        message: string,
        underlying?: Error
    ): never {
        throw new CoreCategoricalFrontendError(
            code,
            nodeProvenance,
            message,
            underlying
        );
    }

    private makeTerm(
        node: TemporaryCategoricalNode,
        type: InternalCoreCategoricalClassifier,
        usage: InternalCategoricalUsage,
        closed?: ElaboratedSurfaceTerm,
        abstractions:
            readonly CoreCategoricalAbstractionEvidence[] = [],
        slotToken = false,
        metadata: InternalCoreCategoricalTermMetadata = {}
    ): InternalCoreCategoricalTerm {
        const term = {
            [CORE_CATEGORICAL_TERM]: true as const,
            ...(slotToken
                ? { [CORE_CATEGORICAL_SLOT]: true as const }
                : {}),
            builderIdentity: this.builderIdentity,
            node: Object.freeze(node),
            type: deepFreeze(copyInternalClassifier(type)),
            usage: Object.freeze([...usage]),
            closed: closed === undefined
                ? undefined
                : deepFreeze({
                    term: closed.term,
                    type: copyCoreType(closed.type),
                    sourceSpan: closed.sourceSpan,
                    recovered: [...closed.recovered]
                }),
            abstractions: deepFreeze([...abstractions]),
            ...(metadata.displayedSectionWeakening === undefined
                ? {}
                : {
                    displayedSectionWeakening: Object.freeze({
                        section:
                            metadata.displayedSectionWeakening.section
                    })
                }),
            ...(metadata.displayedWeakeningFibre === undefined
                ? {}
                : {
                    displayedWeakeningFibre: Object.freeze({
                        section:
                            metadata.displayedWeakeningFibre.section,
                        basePoint:
                            metadata.displayedWeakeningFibre.basePoint
                    })
                })
        };
        return Object.freeze(term);
    }

    private assertUsageActive(
        usage: InternalCategoricalUsage,
        nodeProvenance: Provenance
    ): void {
        for (const [ordinal] of usage) {
            if (!this.activeTokenOrdinals.includes(ordinal)) {
                this.fail(
                    'ESCAPED_SLOT',
                    nodeProvenance,
                    `Categorical slot #${ordinal} escaped its callback body`
                );
            }
        }
    }

    private requireTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalTerm {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreCategoricalTerm)[
                CORE_CATEGORICAL_TERM
            ] !== true
        ) {
            this.fail(
                'INVALID_TERM',
                nodeProvenance,
                'Categorical surface constructor received an invalid term'
            );
        }
        const term = value as InternalCoreCategoricalTerm;
        if (term.builderIdentity !== this.builderIdentity) {
            this.fail(
                'FOREIGN_TERM',
                nodeProvenance,
                'Categorical term belongs to another scoped builder'
            );
        }
        this.assertUsageActive(term.usage, nodeProvenance);
        return term;
    }

    private requireBoundary(
        value: CoreCategoricalHomBoundary,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalHomBoundary {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
        ) {
            this.fail(
                'INVALID_TERM',
                nodeProvenance,
                'Categorical application received an invalid Hom boundary'
            );
        }
        const boundary = value as InternalCoreCategoricalHomBoundary;
        if (boundary.builderIdentity !== this.builderIdentity) {
            this.fail(
                'FOREIGN_TERM',
                nodeProvenance,
                'Hom boundary belongs to another scoped builder'
            );
        }
        this.assertUsageActive(boundary.usage, nodeProvenance);
        return boundary;
    }

    private spanFor(
        nodeProvenance: Provenance,
        fallback?: SourceSpan
    ): SourceSpan {
        return nodeProvenance.span ??
            fallback ??
            this.defaultProvenance.span ??
            DEFAULT_CATEGORICAL_SPAN;
    }

    private structuralCall(
        prerequisite: CoreCategoricalStructuralPrerequisiteId,
        arguments_: readonly {
            readonly plicity: Plicity;
            readonly value: KernelExpression;
        }[],
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName(prerequisite),
                nodeProvenance
            ),
            arguments_,
            nodeProvenance
        );
    }

    private dependentCall(
        prerequisite: CoreCategoricalDependentPrerequisiteId,
        arguments_: readonly {
            readonly plicity: Plicity;
            readonly value: KernelExpression;
        }[],
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalDependentCoreName(prerequisite),
                nodeProvenance
            ),
            arguments_,
            nodeProvenance
        );
    }

    private dependentCompositionCall(
        arguments_: readonly {
            readonly plicity: Plicity;
            readonly value: KernelExpression;
        }[],
        nodeProvenance: Provenance
    ): KernelExpression {
        if (
            this.options.dependentSectionComposition !== true &&
            this.options.displayedFunctorAbstraction !== true
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Generic displayed composition requires an approved ' +
                'dependent-section or displayed-functor capability'
            );
        }
        return kernelCall(
            kernelFree(
                coreCategoricalDependentCompositionCoreName(
                    'generic-category-composition'
                ),
                nodeProvenance
            ),
            arguments_,
            nodeProvenance
        );
    }

    private fibredTransfdCall(
        id:
            | 'displayed-component'
            | 'transport-lhs'
            | 'transport-rhs'
            | 'higher-cell',
        arguments_: readonly {
            readonly plicity: Plicity;
            readonly value: KernelExpression;
        }[],
        nodeProvenance: Provenance
    ): KernelExpression {
        if (this.options.displayedTransforAbstraction !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed-transfor projection requires the ' +
                'FIBRED-TRANSFD-1 capability'
            );
        }
        return kernelCall(
            kernelFree(
                coreCategoricalFibredTransfdCoreName(id),
                nodeProvenance
            ),
            arguments_,
            nodeProvenance
        );
    }

    private terminalCategory(
        nodeProvenance: Provenance
    ): KernelExpression {
        if (this.options.dependentSectionComposition !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Terminal displayed source requires the approved ' +
                'USABILITY-DEPENDENT-1A capability'
            );
        }
        return kernelFree(
            coreCategoricalDependentCompositionCoreName(
                'terminal-category'
            ),
            nodeProvenance
        );
    }

    private displayedCategoryCategory(
        baseCategory: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'displayed-category-category',
            [{ value: baseCategory }],
            nodeProvenance
        );
    }

    private displayedFunctorCategory(
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                    'displayed-functor-category'
                ],
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: sourceFamily },
                { plicity: 'explicit', value: targetFamily }
            ],
            nodeProvenance
        );
    }

    private displayedTransforCategory(
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        sourceFunctor: KernelExpression,
        targetFunctor: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalFibredTransfdCoreName(
                    'displayed-transformation-category'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'implicit', value: sourceFamily },
                { plicity: 'implicit', value: targetFamily },
                { plicity: 'explicit', value: sourceFunctor },
                { plicity: 'explicit', value: targetFunctor }
            ],
            nodeProvenance
        );
    }

    private constantDisplayedFamily(
        baseCategory: KernelExpression,
        fibreCategory: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'constant-displayed-family',
            [
                { value: baseCategory },
                { value: fibreCategory }
            ],
            nodeProvenance
        );
    }

    private oppositeCategory(
        category: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                    .oppositeCategory,
                nodeProvenance
            ),
            [{
                plicity: 'explicit',
                value: category
            }],
            nodeProvenance
        );
    }

    /**
     * Recognize only the canonical internal mixed family
     * `Functor_catd(K,A,B)`.  This is a construction-time rich view of the
     * same kernel classifier, not a coercion or a pointwise naturality claim.
     */
    private mixedFunctorFamilyShape(
        family: KernelExpression,
        baseCategory: KernelExpression
    ): CoreCategoricalMixedFunctorFamilyShape | undefined {
        if (
            family.tag !== 'call' ||
            family.callee.tag !== 'reference' ||
            family.callee.namespace !== 'free' ||
            family.callee.name !==
                coreCategoricalDisplayedEvaluationCoreName(
                    'stableFunctorFamily'
                ) ||
            family.arguments.length !== 3 ||
            family.arguments[0].plicity !== 'implicit' ||
            family.arguments[1].plicity !== 'explicit' ||
            family.arguments[2].plicity !== 'explicit' ||
            !kernelExpressionEquals(
                family.arguments[0].value,
                baseCategory
            )
        ) {
            return undefined;
        }
        return {
            sourceFamily: family.arguments[1].value,
            targetFamily: family.arguments[2].value
        };
    }

    private mixedFunctorFamily(
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalDisplayedEvaluationCoreName(
                    'stableFunctorFamily'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: sourceFamily },
                { plicity: 'explicit', value: targetFamily }
            ],
            nodeProvenance
        );
    }

    private mixedTargetAction(
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        sourceTargetFamily: KernelExpression,
        targetTargetFamily: KernelExpression,
        displayedFunctor: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const capability = this.options.directMixedIntroduction;
        if (capability === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Mixed target-family action requires the reviewed direct ' +
                    'mixed-introduction capability'
            );
        }
        const displayedCategories = this.displayedCategoryCategory(
            baseCategory,
            nodeProvenance
        );
        const partialConstructor = kernelCall(
            kernelFree(
                capability.mixedFunctorFamilyPartialCoreName,
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: sourceFamily }
            ],
            nodeProvenance
        );
        return kernelApplication(
            'functor-hom-capped',
            [
                { value: displayedCategories },
                { value: displayedCategories },
                { value: partialConstructor },
                { value: sourceTargetFamily },
                { value: targetTargetFamily },
                { value: displayedFunctor }
            ],
            nodeProvenance
        );
    }

    private mixedSourceAction(
        baseCategory: KernelExpression,
        sourceSourceFamily: KernelExpression,
        targetSourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        displayedFunctor: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const capability = this.options.directMixedIntroduction;
        if (capability === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Mixed source-family action requires the reviewed direct ' +
                    'mixed-introduction capability'
            );
        }
        const oppositeBase = this.oppositeCategory(
            baseCategory,
            nodeProvenance
        );
        const displayedCategories = this.displayedCategoryCategory(
            baseCategory,
            nodeProvenance
        );
        const oppositeDisplayedCategories = this.oppositeCategory(
            this.displayedCategoryCategory(
                oppositeBase,
                nodeProvenance
            ),
            nodeProvenance
        );
        const constructorTarget = this.functorCategory(
            displayedCategories,
            displayedCategories,
            nodeProvenance
        );
        const constructorAction = kernelApplication(
            'functor-hom-capped',
            [
                { value: oppositeDisplayedCategories },
                { value: constructorTarget },
                {
                    value: kernelCall(
                        kernelFree(
                            capability.mixedFunctorFamilyCoreName,
                            nodeProvenance
                        ),
                        [{
                            plicity: 'explicit',
                            value: baseCategory
                        }],
                        nodeProvenance
                    )
                },
                { value: targetSourceFamily },
                { value: sourceSourceFamily },
                { value: displayedFunctor }
            ],
            nodeProvenance
        );
        const partial = (
            sourceFamily: KernelExpression
        ): KernelExpression => kernelCall(
            kernelFree(
                capability.mixedFunctorFamilyPartialCoreName,
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: sourceFamily }
            ],
            nodeProvenance
        );
        return kernelApplication(
            'transfor-component-capped',
            [
                { value: displayedCategories },
                { value: displayedCategories },
                { value: partial(targetSourceFamily) },
                { value: partial(sourceSourceFamily) },
                { value: targetFamily },
                { value: constructorAction }
            ],
            nodeProvenance
        );
    }

    /**
     * Recognize only the canonical nested displayed-functor classifier
     *
     *   Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar).
     *
     * The result carries internal owners, not pointwise endpoint families or
     * external variance evidence.
     */
    private mixedNestedDisplayedFunctorShape(
        family: KernelExpression,
        outerBaseCategory: KernelExpression
    ): CoreCategoricalMixedNestedFunctorShape | undefined {
        if (
            family.tag !== 'call' ||
            family.callee.tag !== 'reference' ||
            family.callee.namespace !== 'free' ||
            family.callee.name !==
                coreCategoricalMixedModeCoreName(
                    'displayedHomFamily'
                ) ||
            family.arguments.length !== 4 ||
            family.arguments[0].plicity !== 'implicit' ||
            family.arguments[1].plicity !== 'explicit' ||
            family.arguments[2].plicity !== 'explicit' ||
            family.arguments[3].plicity !== 'explicit' ||
            !kernelExpressionEquals(
                family.arguments[0].value,
                outerBaseCategory
            )
        ) {
            return undefined;
        }
        const classifierFamily = family.arguments[1].value;
        if (
            classifierFamily.tag !== 'application' ||
            classifierFamily.owner !== 'constant-displayed-family' ||
            classifierFamily.arguments.length !== 2 ||
            !kernelExpressionEquals(
                classifierFamily.arguments[0].value,
                outerBaseCategory
            )
        ) {
            return undefined;
        }
        const displayedCategory =
            classifierFamily.arguments[1].value;
        if (
            displayedCategory.tag !== 'application' ||
            displayedCategory.owner !==
                'displayed-category-category' ||
            displayedCategory.arguments.length !== 1
        ) {
            return undefined;
        }
        return {
            outerBaseCategory,
            innerBaseCategory:
                displayedCategory.arguments[0].value,
            classifierFamily,
            sourceSection: family.arguments[2].value,
            targetSection: family.arguments[3].value
        };
    }

    /**
     * Recover a rich view of a category-valued result through the optional
     * reviewed runtime reifier. The result term is unchanged and the final
     * checker must validate the same active runtime conversion. Direct
     * builders without that capability retain only the former exact fallback.
     */
    private mixedNestedFibreRichType(
        category: KernelExpression,
        nodeProvenance: Provenance,
        detail = 'mixed nested category-object result'
    ): CoreType | undefined {
        const reifier = this.options.categoryObjectReifier;
        if (reifier !== undefined) {
            const result = reifier.reify(
                category,
                nodeProvenance,
                detail
            );
            if (result.status === 'step-limit-exceeded') {
                this.fail(
                    'INVALID_TERM',
                    nodeProvenance,
                    `Canonical classifier normalization exceeded its ` +
                        `${reifier.stepLimit}-step bound`
                );
            }
            if (result.status === 'stuck') {
                this.fail(
                    'INVALID_TERM',
                    nodeProvenance,
                    'Canonical classifier normalization became stuck on ' +
                        result.reason
                );
            }
            if (result.canonicalHead !== 'plain-object') {
                return result.type;
            }
        }

        // Preserve the exact pre-REFLECT-1A construction-only fallback for
        // direct builders that have no reviewed runtime capability. The
        // mixed program profile uses the runtime path above.
        if (
            this.options.mixedNestedFactorization !== true ||
            category.tag !== 'application' ||
            category.owner !== 'functor-object' ||
            category.arguments.length !== 4 ||
            category.arguments[0].plicity !== 'implicit' ||
            category.arguments[1].plicity !== 'implicit' ||
            category.arguments[2].plicity !== 'explicit' ||
            category.arguments[3].plicity !== 'explicit' ||
            !kernelExpressionEquals(
                category.arguments[1].value,
                this.categoryOfCategories(nodeProvenance)
            )
        ) {
            return undefined;
        }
        const outerBaseCategory = category.arguments[0].value;
        const family = category.arguments[2].value;
        const point = category.arguments[3].value;
        const shape = this.mixedNestedDisplayedFunctorShape(
            family,
            outerBaseCategory
        );
        if (shape === undefined) return undefined;

        const oppositeClassifier = kernelCall(
            kernelFree(
                coreCategoricalDisplayedNdHigherFoundationCoreName(
                    'displayedOpposite'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: outerBaseCategory
                },
                {
                    plicity: 'explicit',
                    value: shape.classifierFamily
                }
            ],
            nodeProvenance
        );
        const sectionAt = (
            sectionFamily: KernelExpression,
            section: KernelExpression
        ): KernelExpression => kernelCall(
            kernelFree(
                CORE_DIRECTED_1C_PRIMITIVE_NAMES[
                    'section-object-evaluation'
                ],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: outerBaseCategory
                },
                {
                    plicity: 'implicit',
                    value: sectionFamily
                },
                {
                    plicity: 'explicit',
                    value: section
                },
                {
                    plicity: 'explicit',
                    value: point
                }
            ],
            nodeProvenance
        );
        const sourceFamily = sectionAt(
            oppositeClassifier,
            shape.sourceSection
        );
        const targetFamily = sectionAt(
            shape.classifierFamily,
            shape.targetSection
        );
        return {
            tag: 'displayed-functor',
            category: this.displayedFunctorCategory(
                shape.innerBaseCategory,
                sourceFamily,
                targetFamily,
                nodeProvenance
            ),
            baseCategory: shape.innerBaseCategory,
            sourceFamily,
            targetFamily
        };
    }

    private displayedEvaluationFamilyShape(
        family: KernelExpression,
        baseCategory: KernelExpression,
        nodeProvenance: Provenance
    ): {
        readonly domainCategory: KernelExpression;
        readonly targetFamily: KernelExpression;
    } | undefined {
        if (
            family.tag !== 'call' ||
            family.callee.tag !== 'reference' ||
            family.callee.namespace !== 'free' ||
            family.callee.name !==
                coreCategoricalDisplayedEvaluationCoreName(
                    'stableFunctorFamily'
                ) ||
            family.arguments.length !== 3 ||
            family.arguments[0].plicity !== 'implicit' ||
            family.arguments[1].plicity !== 'explicit' ||
            family.arguments[2].plicity !== 'explicit' ||
            !kernelExpressionEquals(
                family.arguments[0].value,
                baseCategory
            )
        ) {
            return undefined;
        }
        const domainFamily = family.arguments[1].value;
        if (
            domainFamily.tag !== 'application' ||
            domainFamily.owner !== 'constant-displayed-family' ||
            domainFamily.arguments.length !== 2 ||
            !kernelExpressionEquals(
                domainFamily.arguments[0].value,
                this.oppositeCategory(
                    baseCategory,
                    nodeProvenance
                )
            )
        ) {
            return undefined;
        }
        return {
            domainCategory: domainFamily.arguments[1].value,
            targetFamily: family.arguments[2].value
        };
    }

    private displayedEvaluationTerm(
        baseCategory: KernelExpression,
        domainCategory: KernelExpression,
        targetFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalDisplayedEvaluationCoreName(
                    'displayedEvaluation'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'implicit',
                    value: domainCategory
                },
                {
                    plicity: 'explicit',
                    value: targetFamily
                }
            ],
            nodeProvenance
        );
    }

    private displayedTerminalTerm(
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalDisplayedEvaluationCoreName(
                    'displayedTerminal'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'explicit',
                    value: sourceFamily
                }
            ],
            nodeProvenance
        );
    }

    private constantSectionTerm(
        baseCategory: KernelExpression,
        domainCategory: KernelExpression,
        object: InternalCoreCategoricalTerm,
        nodeProvenance: Provenance
    ): KernelExpression {
        if (object.closed === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'A fixed displayed-evaluation argument must be closed'
            );
        }
        const constantFamily = this.constantDisplayedFamily(
            baseCategory,
            domainCategory,
            nodeProvenance
        );
        return this.functorObject(
            domainCategory,
            this.sectionCategory(
                baseCategory,
                constantFamily,
                nodeProvenance
            ),
            kernelCall(
                kernelFree(
                    coreCategoricalDisplayedEvaluationCoreName(
                        'constantSectionFunctor'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'explicit',
                        value: baseCategory
                    },
                    {
                        plicity: 'explicit',
                        value: domainCategory
                    }
                ],
                nodeProvenance
            ),
            object.closed.term,
            nodeProvenance
        );
    }

    private sectionCategory(
        baseCategory: KernelExpression,
        family: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'section-category',
            [
                { value: baseCategory },
                { value: family }
            ],
            nodeProvenance
        );
    }

    private categoryOfCategories(
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'category-of-categories',
            [],
            nodeProvenance
        );
    }

    private functorCategory(
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalStructuralSymbolCoreName(
                    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'explicit',
                    value: sourceCategory
                },
                {
                    plicity: 'explicit',
                    value: targetCategory
                }
            ],
            nodeProvenance
        );
    }

    private productCategory(
        left: KernelExpression,
        right: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.structuralCall(
            'product-category',
            [
                { plicity: 'explicit', value: left },
                { plicity: 'explicit', value: right }
            ],
            nodeProvenance
        );
    }

    private functorObject(
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        functor: KernelExpression,
        object: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'functor-object',
            [
                { value: sourceCategory },
                { value: targetCategory },
                { value: functor },
                { value: object }
            ],
            nodeProvenance
        );
    }

    /**
     * Transparent product of two Cat-valued displayed families.
     *
     * This is the already-reviewed
     * `uncurry(Product_cat_func) o Product_pair(B,C)` construction. It does
     * not introduce a `Product_catd` owner.
     */
    private displayedProductFamily(
        baseCategory: KernelExpression,
        left: KernelExpression,
        right: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const cat = this.categoryOfCategories(nodeProvenance);
        const catProduct = this.productCategory(
            cat,
            cat,
            nodeProvenance
        );
        const catEndofunctors = this.functorCategory(
            cat,
            cat,
            nodeProvenance
        );
        const uncurriedProduct = this.functorObject(
            this.functorCategory(
                cat,
                catEndofunctors,
                nodeProvenance
            ),
            this.functorCategory(
                catProduct,
                cat,
                nodeProvenance
            ),
            this.structuralCall(
                'uncurry-package',
                [
                    { plicity: 'implicit', value: cat },
                    { plicity: 'implicit', value: cat },
                    { plicity: 'implicit', value: cat }
                ],
                nodeProvenance
            ),
            kernelFree(
                coreCategoricalFibredProductCoreName(
                    'internal-product-functor'
                ),
                nodeProvenance
            ),
            nodeProvenance
        );
        const familyCategory = this.functorCategory(
            baseCategory,
            cat,
            nodeProvenance
        );
        const pairedFamilies = this.structuralCall(
            'product-pair',
            [
                {
                    plicity: 'implicit',
                    value: familyCategory
                },
                {
                    plicity: 'implicit',
                    value: familyCategory
                },
                { plicity: 'explicit', value: left },
                { plicity: 'explicit', value: right }
            ],
            nodeProvenance
        );
        return this.composeFunctors(
            baseCategory,
            catProduct,
            cat,
            uncurriedProduct,
            pairedFamilies,
            nodeProvenance
        );
    }

    private categoricalObjectCategory(
        type: InternalCoreCategoricalClassifier,
        nodeProvenance: Provenance,
        detail: string
    ): KernelExpression | undefined {
        if (
            type.tag === 'indexed-object' ||
            type.tag === 'indexed-functor' ||
            type.tag === 'indexed-transfor' ||
            type.tag === 'nested-indexed-object'
        ) {
            return undefined;
        }
        if (type.tag === 'functor') {
            return this.functorCategory(
                type.sourceCategory,
                type.targetCategory,
                nodeProvenance
            );
        }
        return coreTypeObjectCategory(
            type,
            this.spanFor(nodeProvenance),
            detail
        );
    }

    private categoricalTypeForCategoryObject(
        category: KernelExpression,
        nodeProvenance: Provenance,
        detail: string
    ): CoreType {
        const mixedNestedType =
            this.mixedNestedFibreRichType(
                category,
                nodeProvenance,
                detail
            );
        if (mixedNestedType !== undefined) return mixedNestedType;
        if (
            category.tag === 'call' &&
            category.callee.tag === 'reference' &&
            category.callee.name ===
                coreCategoricalStructuralSymbolCoreName(
                    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
                ) &&
            category.arguments.length === 2
        ) {
            return {
                tag: 'functor',
                sourceCategory: category.arguments[0].value,
                targetCategory: category.arguments[1].value
            };
        }
        return coreTypeForCategoryObject(
            category,
            this.spanFor(nodeProvenance),
            detail
        );
    }

    fromElaborated(
        elaborated: ElaboratedSurfaceTerm
    ): CoreCategoricalTerm {
        kernelAssertScoped(elaborated.term);
        const nodeProvenance = elaborated.term.provenance;
        return this.makeTerm(
            {
                tag: 'explicit-core-term',
                term: elaborated.term,
                provenance: nodeProvenance
            },
            elaborated.type,
            [],
            elaborated
        );
    }

    private slot(
        name: string,
        sourceCategory: KernelExpression,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalTerm {
        const ordinal = this.nextTokenOrdinal++;
        const token = this.makeTerm(
            {
                tag: 'slot-token',
                ordinal,
                hint: name,
                provenance: nodeProvenance
            },
            { tag: 'object', category: sourceCategory },
            [Object.freeze([ordinal, 1] as const)],
            undefined,
            [],
            true
        );
        return token;
    }

    /**
     * Bind an indexed object. An explicitly requested canonical functor view
     * enriches, rather than replaces, its exact object-family membership.
     */
    private indexedObjectSlot(
        name: string,
        baseCategory: KernelExpression,
        family: KernelExpression,
        indexOrdinal: number,
        nodeProvenance: Provenance,
        retainCanonicalFunctorView = false,
        familyBaseCategory = baseCategory
    ): InternalCoreCategoricalTerm {
        const shape = retainCanonicalFunctorView
            ? this.mixedFunctorFamilyShape(family, baseCategory)
            : undefined;
        const ordinal = this.nextTokenOrdinal++;
        return this.makeTerm(
            {
                tag: 'slot-token',
                ordinal,
                hint: name,
                provenance: nodeProvenance
            },
            shape === undefined
                ? {
                    tag: 'indexed-object',
                    baseCategory,
                    ...(kernelExpressionEquals(
                        familyBaseCategory,
                        baseCategory
                    )
                        ? {}
                        : { familyBaseCategory }),
                    family,
                    indexOrdinal
                }
                : {
                    tag: 'indexed-functor',
                    baseCategory,
                    sourceFamilyBaseCategory: this.oppositeCategory(
                        baseCategory,
                        nodeProvenance
                    ),
                    targetFamilyBaseCategory: baseCategory,
                    sourceFamily: shape.sourceFamily,
                    targetFamily: shape.targetFamily,
                    indexOrdinal,
                    underlyingObjectFamily: family,
                    underlyingObjectFamilyBaseCategory:
                        familyBaseCategory
                },
            [Object.freeze([ordinal, 1] as const)],
            undefined,
            [],
            true
        );
    }

    private nestedIndexedObjectSlot(
        name: string,
        shape: CoreCategoricalMixedNestedFunctorShape,
        outerIndexOrdinal: number,
        innerIndexOrdinal: number,
        endpoint: 'source' | 'target',
        nodeProvenance: Provenance
    ): InternalCoreCategoricalTerm {
        const ordinal = this.nextTokenOrdinal++;
        return this.makeTerm(
            {
                tag: 'slot-token',
                ordinal,
                hint: name,
                provenance: nodeProvenance
            },
            {
                tag: 'nested-indexed-object',
                outerBaseCategory: shape.outerBaseCategory,
                outerIndexOrdinal,
                innerBaseCategory: shape.innerBaseCategory,
                innerIndexOrdinal,
                classifierFamily: shape.classifierFamily,
                sourceSection: shape.sourceSection,
                targetSection: shape.targetSection,
                endpoint
            },
            [Object.freeze([ordinal, 1] as const)],
            undefined,
            [],
            true
        );
    }

    /**
     * Recover the hidden natural base index of an active displayed object.
     *
     * This is contextual construction metadata only: it emits no Core node
     * and cannot escape the callback that owns the displayed slot.
     */
    indexOf(
        value: CoreCategoricalTerm,
        suppliedProvenance?: Provenance
    ): CoreCategoricalTerm {
        const nodeProvenance = this.nodeProvenance(
            'displayed contextual index',
            suppliedProvenance
        );
        if (this.options.displayedWeakeningReindexing !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Contextual displayed indices require the ' +
                    'FIBRED-WEAKEN-REINDEX-1 capability'
            );
        }
        const indexed = this.requireTerm(value, nodeProvenance);
        if (
            indexed.type.tag !== 'indexed-object' ||
            indexed.node.tag !== 'slot-token'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'indexOf expects the active displayed object token'
            );
        }
        const base =
            this.activeDisplayedBases.get(indexed.type.indexOrdinal);
        if (base === undefined || base.node.tag !== 'slot-token') {
            this.fail(
                'ESCAPED_SLOT',
                nodeProvenance,
                'The displayed object has no active hidden base index'
            );
        }
        return base;
    }

    /**
     * First-order pair of two fibre objects over one hidden base index.
     *
     * The node remains construction IR until `displayedContextLambda`
     * compiles it through the existing displayed pairing owner.
     */
    fibrePair(
        leftValue: CoreCategoricalTerm,
        rightValue: CoreCategoricalTerm,
        suppliedProvenance?: Provenance
    ): CoreCategoricalTerm {
        const nodeProvenance = this.nodeProvenance(
            'typed displayed fibre pair',
            suppliedProvenance
        );
        if (this.options.displayedContextualAbstraction !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Typed fibre pairs require the reviewed ' +
                    'DISPLAYED-BRACKET-1A capability'
            );
        }
        const left = this.requireTerm(leftValue, nodeProvenance);
        const right = this.requireTerm(rightValue, nodeProvenance);
        if (
            left.type.tag !== 'indexed-object' ||
            right.type.tag !== 'indexed-object' ||
            left.type.indexOrdinal !== right.type.indexOrdinal ||
            !kernelExpressionEquals(
                left.type.baseCategory,
                right.type.baseCategory
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'A typed fibre pair requires two indexed objects over the ' +
                    'same hidden base slot'
            );
        }
        return this.makeTerm(
            {
                tag: 'typed-pair',
                left,
                right,
                provenance: nodeProvenance
            },
            {
                tag: 'indexed-object',
                baseCategory: left.type.baseCategory,
                family: this.displayedProductFamily(
                    left.type.baseCategory,
                    left.type.family,
                    right.type.family,
                    nodeProvenance
                ),
                indexOrdinal: left.type.indexOrdinal
            },
            mergeUsage(left.usage, right.usage),
            undefined,
            [...left.abstractions, ...right.abstractions]
        );
    }

    /**
     * Compose two typed categorical cells inside one contextual callback.
     *
     * DISPLAYED-ND-1A deliberately accepts only `indexed-transfor` first.
     * The generic node records typed recursive syntax; the enclosing
     * displayed-transfor abstraction is responsible for factoring it into
     * a genuine coherence-carrying outer term.
     */
    composeCells(
        outerValue: CoreCategoricalTerm,
        innerValue: CoreCategoricalTerm,
        suppliedProvenance?: Provenance
    ): CoreCategoricalTerm {
        const nodeProvenance = this.nodeProvenance(
            'typed categorical cell composition',
            suppliedProvenance
        );
        if (this.options.displayedTransforAbstraction !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Typed indexed cell composition requires the reviewed ' +
                    'DISPLAYED-ND-1A capability'
            );
        }
        const outer = this.requireTerm(
            outerValue,
            nodeProvenance
        );
        const inner = this.requireTerm(
            innerValue,
            nodeProvenance
        );
        if (
            outer.type.tag !== 'indexed-transfor' ||
            inner.type.tag !== 'indexed-transfor' ||
            outer.type.indexOrdinal !== inner.type.indexOrdinal ||
            !kernelExpressionEquals(
                outer.type.baseCategory,
                inner.type.baseCategory
            ) ||
            !kernelExpressionEquals(
                outer.type.sourceFamily,
                inner.type.sourceFamily
            ) ||
            !kernelExpressionEquals(
                outer.type.targetFamily,
                inner.type.targetFamily
            ) ||
            !kernelExpressionEquals(
                inner.type.targetFunctor,
                outer.type.sourceFunctor
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Typed cell composition requires indexed transformations ' +
                    'at the same contextual base and families with adjacent ' +
                    'endpoints'
            );
        }
        return this.makeTerm(
            {
                tag: 'typed-cell-composition',
                outer,
                inner,
                provenance: nodeProvenance
            },
            {
                tag: 'indexed-transfor',
                baseCategory: inner.type.baseCategory,
                sourceFamily: inner.type.sourceFamily,
                targetFamily: inner.type.targetFamily,
                sourceFunctor: inner.type.sourceFunctor,
                targetFunctor: outer.type.targetFunctor,
                indexOrdinal: inner.type.indexOrdinal
            },
            mergeUsage(outer.usage, inner.usage),
            undefined,
            [...outer.abstractions, ...inner.abstractions]
        );
    }

    homBoundary(
        category: KernelExpression,
        sourceEndpoint: CoreCategoricalTerm,
        targetEndpoint: CoreCategoricalTerm,
        suppliedProvenance?: Provenance
    ): CoreCategoricalHomBoundary {
        const nodeProvenance = this.nodeProvenance(
            'categorical whole Hom-action boundary',
            suppliedProvenance
        );
        const source = this.requireTerm(sourceEndpoint, nodeProvenance);
        const target = this.requireTerm(targetEndpoint, nodeProvenance);
        for (const [label, endpoint] of [
            ['source', source],
            ['target', target]
        ] as const) {
            if (
                endpoint.type.tag === 'indexed-object' ||
                endpoint.type.tag === 'indexed-functor' ||
                endpoint.type.tag === 'indexed-transfor' ||
                endpoint.type.tag === 'nested-indexed-object'
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `${label} Hom-boundary endpoint is an open indexed ` +
                    'fibre value, not a closed category object'
                );
            }
            const endpointCategory = coreTypeObjectCategory(
                endpoint.type,
                this.spanFor(nodeProvenance),
                `${label} Hom-boundary endpoint`
            );
            if (
                endpointCategory === undefined ||
                !coreObjectCategoryEquals(endpointCategory, category)
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `${label} Hom-boundary endpoint is not an object of the ` +
                    'requested category'
                );
            }
        }

        const boundary: InternalCoreCategoricalHomBoundary = {
            [CORE_CATEGORICAL_BOUNDARY]: true,
            builderIdentity: this.builderIdentity,
            category,
            sourceEndpoint: source,
            targetEndpoint: target,
            usage: mergeUsage(source.usage, target.usage),
            provenance: nodeProvenance
        };
        return Object.freeze(boundary);
    }

    private operation(
        operation:
            | 'functor.object'
            | 'functor.hom.full'
            | 'functor.hom.capped'
            | 'transfor.component.capped',
        operands: readonly InternalCoreCategoricalTerm[],
        nodeProvenance: Provenance
    ): ElaboratedSurfaceTerm {
        if (operands.some(operand => operand.closed === undefined)) {
            this.fail(
                'UNLOWERED_CONTEXT',
                nodeProvenance,
                `Operation ${operation} still depends on a categorical slot`
            );
        }
        try {
            return elaborateSurfaceOperationFromOperands(
                operation,
                operands.map(operand =>
                    operand.closed as ElaboratedSurfaceTerm
                ),
                this.spanFor(
                    nodeProvenance,
                    operands[0]?.closed?.sourceSpan
                )
            );
        } catch (error: unknown) {
            if (error instanceof V32ElaborationError) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    error.message,
                    error
                );
            }
            throw error;
        }
    }

    private selectTermApplication(
        subject: InternalCoreCategoricalTerm,
        argument: InternalCoreCategoricalTerm,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): {
        readonly judgment: CoreCategoricalApplicationJudgment;
        readonly operation:
            | 'functor.object'
            | 'functor.hom.capped';
    } {
        if (subject.type.tag !== 'functor') {
            this.fail(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                'Categorical application expects an ordinary functor subject'
            );
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'object-value' &&
            expectedShape !== 'arrow-value'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `A concrete ordinary argument cannot produce expected ` +
                `shape '${expectedShape}'`
            );
        }

        const objectCategory = this.categoricalObjectCategory(
            argument.type,
            nodeProvenance,
            'categorical application object view'
        );
        const matchesObject =
            objectCategory !== undefined &&
            coreObjectCategoryEquals(
                subject.type.sourceCategory,
                objectCategory
            );
        const matchesArrow =
            argument.type.tag === 'hom' &&
            kernelExpressionEquals(
                subject.type.sourceCategory,
                argument.type.category
            );

        let dimension: 'object' | 'arrow';
        let selectedShape: 'object-value' | 'arrow-value';
        if (
            expectedShape === 'object-value' ||
            expectedShape === 'arrow-value'
        ) {
            dimension = expectedShape === 'object-value'
                ? 'object'
                : 'arrow';
            selectedShape = expectedShape;
            if (
                (dimension === 'object' && !matchesObject) ||
                (dimension === 'arrow' && !matchesArrow)
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Expected ${expectedShape}, but the argument classifier ` +
                    'does not support that functor action'
                );
            }
        } else if (matchesObject && matchesArrow) {
            this.fail(
                'MISSING_EXPECTED_ACTION_SHAPE',
                nodeProvenance,
                'Argument can be viewed both as a source object and a source ' +
                'arrow; supply object-value or arrow-value expectation'
            );
        } else if (matchesObject) {
            dimension = 'object';
            selectedShape = 'object-value';
        } else if (matchesArrow) {
            dimension = 'arrow';
            selectedShape = 'arrow-value';
        } else {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Argument is neither an object nor an arrow of the functor ' +
                'source category'
            );
        }

        const judgment = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-functor',
            subjectForm: 'term',
            argumentDimension: dimension,
            expectedShape: selectedShape,
            dependency: 'ordinary'
        });
        return {
            judgment,
            operation: dimension === 'object'
                ? 'functor.object'
                : 'functor.hom.capped'
        };
    }

    private closedDependentApplication(
        subject: InternalCoreCategoricalTerm,
        argument: InternalCoreCategoricalTerm,
        judgment: CoreCategoricalApplicationJudgment,
        type: CoreType,
        term: KernelExpression,
        nodeProvenance: Provenance,
        metadata: InternalCoreCategoricalTermMetadata = {}
    ): CoreCategoricalTerm {
        if (
            subject.closed === undefined ||
            argument.closed === undefined
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Open indexed application requires the first-order ' +
                'dependent contextual classifier staged for USABILITY-2A1'
            );
        }
        const closed = deepFreeze({
            term,
            type: copyCoreType(type),
            sourceSpan: this.spanFor(nodeProvenance),
            recovered: [
                ...subject.closed.recovered,
                ...argument.closed.recovered
            ]
        });
        return this.makeTerm(
            {
                tag: 'typed-application',
                judgment,
                subject,
                argument,
                provenance: nodeProvenance
            },
            type,
            mergeUsage(subject.usage, argument.usage),
            closed,
            [
                ...subject.abstractions,
                ...argument.abstractions
            ],
            false,
            metadata
        );
    }

    private applyDependentSection(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        if (subject.type.tag !== 'dependent-section') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Internal dependent section classifier was lost'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'UNAVAILABLE_DEPENDENT_ACTION',
                nodeProvenance,
                'Whole section Hom-action requires the active piapp1_func ' +
                'transfer after USABILITY-2A1'
            );
        }
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        if (argument.type.tag === 'hom') {
            if (
                kernelExpressionEquals(
                    argument.type.category,
                    subject.type.baseCategory
                )
            ) {
                this.fail(
                    'UNAVAILABLE_DEPENDENT_ACTION',
                    nodeProvenance,
                    'Section base-arrow action requires the active ' +
                    'piapp1_fapp0 transfer after USABILITY-2A1'
                );
            }
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'dependent-object'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Dependent section application cannot produce expected ` +
                `shape '${expectedShape}' in USABILITY-2A1`
            );
        }
        const argumentCategory = this.categoricalObjectCategory(
            argument.type,
            nodeProvenance,
            'dependent section base object'
        );
        if (
            argumentCategory === undefined ||
            !coreObjectCategoryEquals(
                argumentCategory,
                subject.type.baseCategory
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Dependent section argument is not an object of its base ' +
                'category'
            );
        }
        if (subject.closed === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'An open dependent-section subject has no qualified ' +
                'contextual lowering'
            );
        }
        const judgment = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'dependent-section',
            subjectForm: 'term',
            argumentDimension: 'object',
            expectedShape: 'dependent-object',
            dependency: 'displayed'
        });
        if (argument.closed === undefined) {
            if (argument.node.tag !== 'slot-token') {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'USABILITY-2A1 indexes a section only by one direct ' +
                    'first-order contextual slot'
                );
            }
            return this.makeTerm(
                {
                    tag: 'typed-application',
                    judgment,
                    subject,
                    argument,
                    provenance: nodeProvenance
                },
                {
                    tag: 'indexed-object',
                    baseCategory: subject.type.baseCategory,
                    family: subject.type.family,
                    indexOrdinal: argument.node.ordinal
                },
                mergeUsage(subject.usage, argument.usage),
                undefined,
                [
                    ...subject.abstractions,
                    ...argument.abstractions
                ]
            );
        }

        const point = argument.closed.term;
        const fibre = this.functorObject(
            subject.type.baseCategory,
            this.categoryOfCategories(nodeProvenance),
            subject.type.family,
            point,
            nodeProvenance
        );
        const resultType = this.categoricalTypeForCategoryObject(
            fibre,
            nodeProvenance,
            'closed dependent-section object result'
        );
        const result = kernelCall(
            kernelFree(
                CORE_DIRECTED_1C_PRIMITIVE_NAMES[
                    'section-object-evaluation'
                ],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: subject.type.baseCategory
                },
                {
                    plicity: 'implicit',
                    value: subject.type.family
                },
                {
                    plicity: 'explicit',
                    value: subject.closed.term
                },
                {
                    plicity: 'explicit',
                    value: point
                }
            ],
            nodeProvenance
        );
        return this.closedDependentApplication(
            subject,
            argument,
            judgment,
            resultType,
            result,
            nodeProvenance
        );
    }

    /**
     * Re-view one hidden contextual base slot at its exact displayed-family
     * domain. `Obj(Op K)` computes to `Obj K` in the active kernel, so the
     * opposite view changes only construction typing metadata and emits no
     * coercion or equality evidence.
     */
    private orientedContextualBaseToken(
        token: InternalCoreCategoricalTerm,
        scopeBaseCategory: KernelExpression,
        familyBaseCategory: KernelExpression,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalTerm {
        if (
            token.node.tag !== 'slot-token' ||
            token.type.tag !== 'object' ||
            !kernelExpressionEquals(
                token.type.category,
                scopeBaseCategory
            )
        ) {
            this.fail(
                'ESCAPED_SLOT',
                nodeProvenance,
                'Displayed-family application lost its shared hidden base '
                    + 'slot'
            );
        }
        if (
            !kernelExpressionEquals(
                familyBaseCategory,
                scopeBaseCategory
            ) &&
            !kernelExpressionEquals(
                familyBaseCategory,
                this.oppositeCategory(
                    scopeBaseCategory,
                    nodeProvenance
                )
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'An indexed family domain must be the exact shared scope ' +
                    'base or its exact opposite'
            );
        }
        if (
            kernelExpressionEquals(
                familyBaseCategory,
                scopeBaseCategory
            )
        ) {
            return token;
        }
        return this.makeTerm(
            token.node,
            {
                tag: 'object',
                category: familyBaseCategory
            },
            token.usage,
            undefined,
            token.abstractions,
            true
        );
    }

    private applyDisplayedFunctor(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance,
        contextualScopeBaseCategory?: KernelExpression
    ): CoreCategoricalTerm {
        if (subject.type.tag !== 'displayed-functor') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Internal displayed functor classifier was lost'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'A displayed functor has no active whole laxity transfor; ' +
                'only component-level cells are active'
            );
        }
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        if (
            expectedShape === 'whole-laxity-transfor'
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'functord_laxity_transf is deliberately inactive in the ' +
                'active kernel; TypeScript cannot synthesize it'
            );
        }
        const base = subject.type.baseCategory;
        const sourceFamily = subject.type.sourceFamily;
        const targetFamily = subject.type.targetFamily;
        if (argument.closed === undefined) {
            if (
                (
                    this.options.dependentSectionComposition !== true &&
                    this.options.displayedFunctorAbstraction !== true
                ) ||
                subject.closed === undefined ||
                argument.node.tag !== 'slot-token'
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'The USABILITY-2A1 eta envelope does not expose open ' +
                    'displayed-functor projection; it requires the direct ' +
                    'indexed slot and an approved dependent-section or ' +
                    'displayed-functor capability'
                );
            }
            if (
                expectedShape !== undefined &&
                expectedShape !== 'fibre-functor'
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Open displayed base-object application cannot produce ` +
                    `expected shape '${expectedShape}'`
                );
            }
            const argumentCategory = this.categoricalObjectCategory(
                argument.type,
                nodeProvenance,
                'open displayed functor base object'
            );
            if (
                argumentCategory === undefined ||
                !coreObjectCategoryEquals(argumentCategory, base)
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Open displayed functor argument is not an object of its ' +
                    'base category'
                );
            }
            const judgment = selectCoreCategoricalApplication({
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'object',
                expectedShape: 'fibre-functor',
                dependency: 'displayed'
            }, dependentApplicationQualification);
            return this.makeTerm(
                {
                    tag: 'typed-application',
                    judgment,
                    subject,
                    argument,
                    provenance: nodeProvenance
                },
                {
                    tag: 'indexed-functor',
                    baseCategory:
                        contextualScopeBaseCategory ?? base,
                    ...(kernelExpressionEquals(
                        contextualScopeBaseCategory ?? base,
                        base
                    )
                        ? {}
                        : {
                            sourceFamilyBaseCategory: base,
                            targetFamilyBaseCategory: base
                        }),
                    sourceFamily,
                    targetFamily,
                    indexOrdinal: argument.node.ordinal
                },
                mergeUsage(subject.usage, argument.usage),
                undefined,
                [
                    ...subject.abstractions,
                    ...argument.abstractions
                ],
                false,
                subject.displayedSectionWeakening === undefined
                    ? {}
                    : {
                        displayedWeakeningFibre: {
                            section:
                                subject.displayedSectionWeakening.section,
                            basePoint: argument
                        }
                    }
            );
        }
        if (subject.closed === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed-functor subject remains open after its base index ' +
                'was closed'
            );
        }

        let judgment: CoreCategoricalApplicationJudgment;
        let resultType: CoreType;
        let result: KernelExpression;
        if (argument.type.tag === 'hom') {
            if (
                expectedShape !== undefined &&
                expectedShape !== 'transport-functor'
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Displayed base-arrow application cannot produce ` +
                    `expected shape '${expectedShape}'`
                );
            }
            if (
                !kernelExpressionEquals(
                    argument.type.category,
                    base
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed functor base arrow belongs to the wrong ' +
                    'category'
                );
            }
            const sourceFibre = this.functorObject(
                base,
                this.categoryOfCategories(nodeProvenance),
                sourceFamily,
                argument.type.sourceObject,
                nodeProvenance
            );
            const targetFibre = this.functorObject(
                base,
                this.categoryOfCategories(nodeProvenance),
                targetFamily,
                argument.type.targetObject,
                nodeProvenance
            );
            resultType = {
                tag: 'functor',
                sourceCategory: sourceFibre,
                targetCategory: targetFibre
            };
            judgment = selectCoreCategoricalApplication({
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'arrow',
                expectedShape: 'transport-functor',
                dependency: 'displayed'
            }, dependentApplicationQualification);
            result = this.dependentCall(
                'displayed-functor-transport',
                [
                    { plicity: 'implicit', value: base },
                    { plicity: 'implicit', value: sourceFamily },
                    { plicity: 'implicit', value: targetFamily },
                    {
                        plicity: 'explicit',
                        value: subject.closed.term
                    },
                    {
                        plicity: 'implicit',
                        value: argument.type.sourceObject
                    },
                    {
                        plicity: 'implicit',
                        value: argument.type.targetObject
                    },
                    {
                        plicity: 'explicit',
                        value: argument.closed.term
                    }
                ],
                nodeProvenance
            );
        } else {
            if (
                expectedShape !== undefined &&
                expectedShape !== 'fibre-functor'
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Displayed base-object application cannot produce ` +
                    `expected shape '${expectedShape}'`
                );
            }
            const argumentCategory = this.categoricalObjectCategory(
                argument.type,
                nodeProvenance,
                'displayed functor base object'
            );
            if (
                argumentCategory === undefined ||
                !coreObjectCategoryEquals(argumentCategory, base)
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed functor argument is not an object of its ' +
                    'base category'
                );
            }
            const point = argument.closed.term;
            resultType = {
                tag: 'functor',
                sourceCategory: this.functorObject(
                    base,
                    this.categoryOfCategories(nodeProvenance),
                    sourceFamily,
                    point,
                    nodeProvenance
                ),
                targetCategory: this.functorObject(
                    base,
                    this.categoryOfCategories(nodeProvenance),
                    targetFamily,
                    point,
                    nodeProvenance
                )
            };
            judgment = selectCoreCategoricalApplication({
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'object',
                expectedShape: 'fibre-functor',
                dependency: 'displayed'
            }, dependentApplicationQualification);
            result = this.dependentCall(
                'displayed-functor-fibre',
                [
                    { plicity: 'implicit', value: base },
                    { plicity: 'implicit', value: sourceFamily },
                    { plicity: 'implicit', value: targetFamily },
                    {
                        plicity: 'explicit',
                        value: subject.closed.term
                    },
                    { plicity: 'explicit', value: point }
                ],
                nodeProvenance
            );
        }
        return this.closedDependentApplication(
            subject,
            argument,
            judgment,
            resultType,
            result,
            nodeProvenance,
            subject.displayedSectionWeakening === undefined ||
                argument.type.tag === 'hom'
                ? {}
                : {
                    displayedWeakeningFibre: {
                        section:
                            subject.displayedSectionWeakening.section,
                        basePoint: argument
                    }
                }
        );
    }

    private applyDisplayedTransfor(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        if (subject.type.tag !== 'displayed-transfor') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Internal displayed-transfor classifier was lost'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'FIBRED-TRANSFD-1 exposes the coherent fibre component, ' +
                'not a whole displayed higher-action evaluator'
            );
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'displayed-component'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Displayed-transfor application cannot produce expected ` +
                `shape '${expectedShape}'`
            );
        }
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        const argumentCategory = this.categoricalObjectCategory(
            argument.type,
            nodeProvenance,
            'displayed-transfor base object'
        );
        if (
            argumentCategory === undefined ||
            !coreObjectCategoryEquals(
                argumentCategory,
                subject.type.baseCategory
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed-transfor component index belongs to the wrong ' +
                'base category'
            );
        }
        const judgment = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'displayed-transfor',
            subjectForm: 'term',
            argumentDimension: 'object',
            expectedShape: 'displayed-component',
            dependency: 'displayed'
        }, dependentApplicationQualification);

        if (argument.closed === undefined) {
            if (
                this.options.displayedTransforAbstraction !== true ||
                subject.closed === undefined ||
                argument.node.tag !== 'slot-token'
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'Open displayed-transfor projection requires the direct ' +
                    'FIBRED-TRANSFD-1 base slot and a closed coherent subject'
                );
            }
            return this.makeTerm(
                {
                    tag: 'typed-application',
                    judgment,
                    subject,
                    argument,
                    provenance: nodeProvenance
                },
                {
                    tag: 'indexed-transfor',
                    baseCategory: subject.type.baseCategory,
                    sourceFamily: subject.type.sourceFamily,
                    targetFamily: subject.type.targetFamily,
                    sourceFunctor: subject.type.sourceFunctor,
                    targetFunctor: subject.type.targetFunctor,
                    indexOrdinal: argument.node.ordinal
                },
                mergeUsage(subject.usage, argument.usage),
                undefined,
                [
                    ...subject.abstractions,
                    ...argument.abstractions
                ]
            );
        }
        if (subject.closed === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed-transfor subject remains open after its base ' +
                'index was closed'
            );
        }

        const point = argument.closed.term;
        const displayedType = subject.type;
        const sourceFibre = this.functorObject(
            displayedType.baseCategory,
            this.categoryOfCategories(nodeProvenance),
            displayedType.sourceFamily,
            point,
            nodeProvenance
        );
        const targetFibre = this.functorObject(
            displayedType.baseCategory,
            this.categoryOfCategories(nodeProvenance),
            displayedType.targetFamily,
            point,
            nodeProvenance
        );
        const fibreFunctor = (
            displayedFunctor: KernelExpression
        ): KernelExpression => this.dependentCall(
            'displayed-functor-fibre',
            [
                {
                    plicity: 'implicit',
                    value: displayedType.baseCategory
                },
                {
                    plicity: 'implicit',
                    value: displayedType.sourceFamily
                },
                {
                    plicity: 'implicit',
                    value: displayedType.targetFamily
                },
                {
                    plicity: 'explicit',
                    value: displayedFunctor
                },
                { plicity: 'explicit', value: point }
            ],
            nodeProvenance
        );
        const resultType: CoreType = {
            tag: 'transfor',
            sourceCategory: sourceFibre,
            targetCategory: targetFibre,
            sourceFunctor: fibreFunctor(
                displayedType.sourceFunctor
            ),
            targetFunctor: fibreFunctor(
                displayedType.targetFunctor
            )
        };
        const result = this.fibredTransfdCall(
            'displayed-component',
            [
                {
                    plicity: 'implicit',
                    value: displayedType.baseCategory
                },
                {
                    plicity: 'implicit',
                    value: displayedType.sourceFamily
                },
                {
                    plicity: 'implicit',
                    value: displayedType.targetFamily
                },
                {
                    plicity: 'implicit',
                    value: displayedType.sourceFunctor
                },
                {
                    plicity: 'implicit',
                    value: displayedType.targetFunctor
                },
                { plicity: 'explicit', value: point },
                {
                    plicity: 'explicit',
                    value: subject.closed.term
                }
            ],
            nodeProvenance
        );
        return this.closedDependentApplication(
            subject,
            argument,
            judgment,
            resultType,
            result,
            nodeProvenance
        );
    }

    private applyOrdinaryTransfor(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        if (subject.type.tag !== 'transfor') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Internal ordinary-transfor classifier was lost'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'RESERVED_NATURALITY_ACTION',
                nodeProvenance,
                'Whole ordinary transfor Hom-action remains behind its ' +
                'separate naturality gate'
            );
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'point-component'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Ordinary transfor application cannot produce expected ` +
                `shape '${expectedShape}'`
            );
        }
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        const argumentCategory = this.categoricalObjectCategory(
            argument.type,
            nodeProvenance,
            'ordinary transfor component index'
        );
        if (
            argumentCategory === undefined ||
            !coreObjectCategoryEquals(
                argumentCategory,
                subject.type.sourceCategory
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Ordinary transfor component index belongs to the wrong ' +
                'source category'
            );
        }
        if (
            subject.closed === undefined ||
            argument.closed === undefined
        ) {
            this.fail(
                'MISSING_STRUCTURAL_OWNER',
                nodeProvenance,
                'Open ordinary transfor components require later ' +
                'contextual naturality lowering'
            );
        }
        const judgment = selectCoreCategoricalApplication({
            layer: 'categorical',
            subjectClassifier: 'ordinary-transfor',
            subjectForm: 'term',
            argumentDimension: 'object',
            expectedShape: 'point-component',
            dependency: 'ordinary'
        });
        const closed = this.operation(
            'transfor.component.capped',
            [subject, argument],
            nodeProvenance
        );
        return this.makeTerm(
            {
                tag: 'typed-application',
                judgment,
                subject,
                argument,
                provenance: nodeProvenance
            },
            closed.type,
            mergeUsage(subject.usage, argument.usage),
            closed,
            [...subject.abstractions, ...argument.abstractions]
        );
    }

    private applyIndexedFibreFunctor(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        if (
            (
                this.options.dependentSectionComposition !== true &&
                this.options.displayedFunctorAbstraction !== true
            ) ||
            subject.type.tag !== 'indexed-functor'
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Indexed fibre-functor application requires an approved ' +
                'dependent-section or displayed-functor capability'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'An indexed fibre functor expects an indexed object, not a ' +
                'whole Hom boundary'
            );
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'object-value'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Indexed fibre-functor application cannot produce expected ` +
                `shape '${expectedShape}'`
            );
        }
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        const argumentObject = indexedObjectView(argument.type);
        if (
            argumentObject === undefined ||
            argumentObject.indexOrdinal !==
                subject.type.indexOrdinal ||
            !kernelExpressionEquals(
                argumentObject.baseCategory,
                subject.type.baseCategory
            ) ||
            !kernelExpressionEquals(
                argumentObject.familyBaseCategory,
                indexedFunctorSourceBase(subject.type)
            ) ||
            !kernelExpressionEquals(
                argumentObject.family,
                subject.type.sourceFamily
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Indexed fibre functor and object must share the same base ' +
                'slot and the functor source family'
            );
        }
        if (subject.displayedWeakeningFibre !== undefined) {
            return this.applyDependentSection(
                subject.displayedWeakeningFibre.section,
                subject.displayedWeakeningFibre.basePoint,
                'dependent-object',
                nodeProvenance
            );
        }
        const mixedTarget =
            this.options.directMixedIntroduction === undefined ||
            !kernelExpressionEquals(
                indexedFunctorTargetBase(subject.type),
                subject.type.baseCategory
            )
                ? undefined
                : this.mixedFunctorFamilyShape(
                    subject.type.targetFamily,
                    subject.type.baseCategory
                );
        const resultType: InternalCoreCategoricalClassifier =
            mixedTarget === undefined
                ? {
                    tag: 'indexed-object',
                    baseCategory: subject.type.baseCategory,
                    ...(kernelExpressionEquals(
                        indexedFunctorTargetBase(subject.type),
                        subject.type.baseCategory
                    )
                        ? {}
                        : {
                            familyBaseCategory:
                                indexedFunctorTargetBase(subject.type)
                        }),
                    family: subject.type.targetFamily,
                    indexOrdinal: subject.type.indexOrdinal
                }
                : {
                    tag: 'indexed-functor',
                    baseCategory: subject.type.baseCategory,
                    sourceFamilyBaseCategory: this.oppositeCategory(
                        subject.type.baseCategory,
                        nodeProvenance
                    ),
                    targetFamilyBaseCategory: subject.type.baseCategory,
                    sourceFamily: mixedTarget.sourceFamily,
                    targetFamily: mixedTarget.targetFamily,
                    indexOrdinal: subject.type.indexOrdinal,
                    underlyingObjectFamily:
                        subject.type.targetFamily,
                    underlyingObjectFamilyBaseCategory:
                        indexedFunctorTargetBase(subject.type)
                };
        return this.makeTerm(
            {
                tag: 'typed-application',
                judgment:
                    CORE_CATEGORICAL_DEPENDENT_CONTINUATION_APPLICATION,
                subject,
                argument,
                provenance: nodeProvenance
            },
            resultType,
            mergeUsage(subject.usage, argument.usage),
            undefined,
            [
                ...subject.abstractions,
                ...argument.abstractions
            ]
        );
    }

    private applyNestedDisplayedFunctor(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        if (
            this.options.mixedNestedFactorization !== true ||
            subject.type.tag !== 'indexed-object'
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Nested displayed application requires the reviewed ' +
                    'MIXED-NEST-1A factorization capability'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'A nested displayed functor expects its scoped fibre ' +
                    'object, not a whole Hom boundary'
            );
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'object-value'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Nested displayed application cannot produce expected ` +
                    `shape '${expectedShape}'`
            );
        }
        const shape = this.mixedNestedDisplayedFunctorShape(
            subject.type.family,
            subject.type.baseCategory
        );
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        if (
            shape === undefined ||
            argument.type.tag !== 'nested-indexed-object' ||
            argument.type.endpoint !== 'source' ||
            argument.type.outerIndexOrdinal !==
                subject.type.indexOrdinal ||
            !kernelExpressionEquals(
                argument.type.outerBaseCategory,
                subject.type.baseCategory
            ) ||
            !kernelExpressionEquals(
                argument.type.innerBaseCategory,
                shape.innerBaseCategory
            ) ||
            !kernelExpressionEquals(
                argument.type.classifierFamily,
                shape.classifierFamily
            ) ||
            !kernelExpressionEquals(
                argument.type.sourceSection,
                shape.sourceSection
            ) ||
            !kernelExpressionEquals(
                argument.type.targetSection,
                shape.targetSection
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Nested displayed subject and fibre token do not share the ' +
                    'canonical Hom_catd classifier and contextual indices'
            );
        }
        const base = this.activeDisplayedBases.get(
            argument.type.innerIndexOrdinal
        );
        if (
            base === undefined ||
            base.node.tag !== 'slot-token' ||
            base.node.ordinal !== argument.type.innerIndexOrdinal
        ) {
            this.fail(
                'ESCAPED_SLOT',
                nodeProvenance,
                'Nested displayed application lost its hidden inner base'
            );
        }
        return this.makeTerm(
            {
                tag: 'typed-nested-displayed-application',
                subject,
                base,
                argument,
                provenance: nodeProvenance
            },
            {
                ...argument.type,
                endpoint: 'target'
            },
            mergeUsage(subject.usage, base.usage, argument.usage),
            undefined,
            [
                ...subject.abstractions,
                ...argument.abstractions
            ]
        );
    }

    private applyDisplayedEvaluation(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        if (
            this.options.displayedEvaluation !== true ||
            subject.type.tag !== 'indexed-object'
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Open displayed evaluation requires the reviewed ' +
                    'DISPLAYED-EVAL-1A capability'
            );
        }
        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed evaluation expects an object argument, not a ' +
                    'whole Hom boundary'
            );
        }
        if (
            expectedShape !== undefined &&
            expectedShape !== 'object-value'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Displayed evaluation cannot produce expected shape ` +
                    `'${expectedShape}'`
            );
        }
        const shape = this.displayedEvaluationFamilyShape(
            subject.type.family,
            subject.type.baseCategory,
            nodeProvenance
        );
        if (shape === undefined) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed evaluation requires the stable constant-domain ' +
                    'Functor_catd(Const_(Op K)(A),B) subject family'
            );
        }
        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        const coherentArgumentFamily = this.constantDisplayedFamily(
            subject.type.baseCategory,
            shape.domainCategory,
            nodeProvenance
        );
        let judgment:
            CoreCategoricalDisplayedEvaluationApplicationJudgment;
        if (argument.type.tag === 'indexed-object') {
            if (
                argument.type.indexOrdinal !==
                    subject.type.indexOrdinal ||
                !kernelExpressionEquals(
                    argument.type.baseCategory,
                    subject.type.baseCategory
                ) ||
                !kernelExpressionEquals(
                    argument.type.family,
                    coherentArgumentFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'The varying displayed-evaluation argument must be an ' +
                        'object of Const_K(A) at the subject base slot'
                );
            }
            judgment =
                CORE_CATEGORICAL_DISPLAYED_EVALUATION_VARYING_APPLICATION;
        } else {
            const argumentCategory = this.categoricalObjectCategory(
                argument.type,
                nodeProvenance,
                'fixed displayed-evaluation argument'
            );
            if (
                argument.closed === undefined ||
                argumentCategory === undefined ||
                !coreObjectCategoryEquals(
                    argumentCategory,
                    shape.domainCategory
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'The fixed displayed-evaluation argument must be a ' +
                        'closed object of the constant domain A'
                );
            }
            judgment =
                CORE_CATEGORICAL_DISPLAYED_EVALUATION_FIXED_APPLICATION;
        }
        return this.makeTerm(
            {
                tag: 'typed-application',
                judgment,
                subject,
                argument,
                provenance: nodeProvenance
            },
            {
                tag: 'indexed-object',
                baseCategory: subject.type.baseCategory,
                family: shape.targetFamily,
                indexOrdinal: subject.type.indexOrdinal
            },
            mergeUsage(subject.usage, argument.usage),
            undefined,
            [
                ...subject.abstractions,
                ...argument.abstractions
            ]
        );
    }

    apply(
        subjectValue: CoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape?: CoreCategoricalExpectedShape,
        suppliedProvenance?: Provenance
    ): CoreCategoricalTerm {
        const nodeProvenance = this.nodeProvenance(
            'typed categorical application',
            suppliedProvenance
        );
        const subject = this.requireTerm(
            subjectValue,
            nodeProvenance
        );
        if (
            subject.type.tag === 'displayed-functor' &&
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
        ) {
            const argument = this.requireTerm(
                argumentValue as CoreCategoricalTerm,
                nodeProvenance
            );
            const argumentObject = indexedObjectView(argument.type);
            if (argumentObject !== undefined) {
                if (
                    this.options.displayedFunctorAbstraction !== true
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        nodeProvenance,
                        'Direct displayed-functor application to a fibre ' +
                        'slot requires the FIBRED-BINDER-1 capability'
                    );
                }
                const baseToken = this.activeDisplayedBases.get(
                    argumentObject.indexOrdinal
                );
                if (baseToken === undefined) {
                    this.fail(
                        'ESCAPED_SLOT',
                        nodeProvenance,
                        'Direct displayed-functor application lost its ' +
                        'hidden base slot'
                    );
                }
                if (
                    !kernelExpressionEquals(
                        subject.type.baseCategory,
                        argumentObject.familyBaseCategory
                    )
                ) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        nodeProvenance,
                        'Displayed functor and indexed object must share ' +
                            'the exact displayed-family domain'
                    );
                }
                const orientedBaseToken =
                    this.orientedContextualBaseToken(
                        baseToken,
                        argumentObject.baseCategory,
                        argumentObject.familyBaseCategory,
                        nodeProvenance
                    );
                const indexedFunctor = this.applyDisplayedFunctor(
                    subject,
                    orientedBaseToken,
                    'fibre-functor',
                    nodeProvenance,
                    argumentObject.baseCategory
                );
                return this.applyIndexedFibreFunctor(
                    this.requireTerm(indexedFunctor, nodeProvenance),
                    argument,
                    expectedShape,
                    nodeProvenance
                );
            }
        }
        if (
            subject.type.tag === 'indexed-object' &&
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
        ) {
            const argument = this.requireTerm(
                argumentValue as CoreCategoricalTerm,
                nodeProvenance
            );
            if (argument.type.tag === 'nested-indexed-object') {
                return this.applyNestedDisplayedFunctor(
                    subject,
                    argument,
                    expectedShape,
                    nodeProvenance
                );
            }
        }
        if (
            subject.type.tag === 'indexed-object' &&
            this.displayedEvaluationFamilyShape(
                subject.type.family,
                subject.type.baseCategory,
                nodeProvenance
            ) !== undefined
        ) {
            return this.applyDisplayedEvaluation(
                subject,
                argumentValue,
                expectedShape,
                nodeProvenance
            );
        }
        if (subject.type.tag === 'indexed-functor') {
            return this.applyIndexedFibreFunctor(
                subject,
                argumentValue,
                expectedShape,
                nodeProvenance
            );
        }
        if (subject.type.tag === 'dependent-section') {
            return this.applyDependentSection(
                subject,
                argumentValue,
                expectedShape,
                nodeProvenance
            );
        }
        if (subject.type.tag === 'displayed-functor') {
            return this.applyDisplayedFunctor(
                subject,
                argumentValue,
                expectedShape,
                nodeProvenance
            );
        }
        if (subject.type.tag === 'displayed-transfor') {
            return this.applyDisplayedTransfor(
                subject,
                argumentValue,
                expectedShape,
                nodeProvenance
            );
        }
        if (subject.type.tag === 'transfor') {
            return this.applyOrdinaryTransfor(
                subject,
                argumentValue,
                expectedShape,
                nodeProvenance
            );
        }
        if (
            subject.type.tag === 'functor' &&
            subject.displayedWeakeningFibre !== undefined
        ) {
            if (
                typeof argumentValue === 'object' &&
                argumentValue !== null &&
                (argumentValue as InternalCoreCategoricalHomBoundary)[
                    CORE_CATEGORICAL_BOUNDARY
                ] === true
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'A weakened displayed fibre functor expects an object'
                );
            }
            const argument = this.requireTerm(
                argumentValue as CoreCategoricalTerm,
                nodeProvenance
            );
            const argumentCategory = this.categoricalObjectCategory(
                argument.type,
                nodeProvenance,
                'weakened displayed fibre argument'
            );
            if (
                argumentCategory === undefined ||
                !coreObjectCategoryEquals(
                    argumentCategory,
                    subject.type.sourceCategory
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Weakened displayed fibre argument belongs to the ' +
                        'wrong source fibre'
                );
            }
            if (
                expectedShape !== undefined &&
                expectedShape !== 'object-value'
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Weakened displayed fibre application cannot produce ` +
                        `expected shape '${expectedShape}'`
                );
            }
            return this.applyDependentSection(
                subject.displayedWeakeningFibre.section,
                subject.displayedWeakeningFibre.basePoint,
                'dependent-object',
                nodeProvenance
            );
        }
        if (subject.type.tag !== 'functor') {
            this.fail(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                'Categorical application expects an ordinary functor subject'
            );
        }

        if (
            typeof argumentValue === 'object' &&
            argumentValue !== null &&
            (argumentValue as InternalCoreCategoricalHomBoundary)[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            const boundary = this.requireBoundary(
                argumentValue as CoreCategoricalHomBoundary,
                nodeProvenance
            );
            if (
                !kernelExpressionEquals(
                    subject.type.sourceCategory,
                    boundary.category
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Hom boundary belongs to the wrong functor source category'
                );
            }
            if (
                expectedShape !== undefined &&
                expectedShape !== 'whole-hom-action'
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'A Hom boundary requires whole-hom-action expectation'
                );
            }
            const judgment = selectCoreCategoricalApplication({
                layer: 'categorical',
                subjectClassifier: 'ordinary-functor',
                subjectForm: 'term',
                argumentDimension: 'hom-boundary',
                expectedShape: 'whole-hom-action',
                dependency: 'ordinary'
            });
            const usage = mergeUsage(subject.usage, boundary.usage);
            const allClosed =
                subject.closed !== undefined &&
                boundary.sourceEndpoint.closed !== undefined &&
                boundary.targetEndpoint.closed !== undefined;
            const closed = allClosed
                ? this.operation(
                    'functor.hom.full',
                    [
                        subject,
                        boundary.sourceEndpoint,
                        boundary.targetEndpoint
                    ],
                    nodeProvenance
                )
                : undefined;
            if (!allClosed) {
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    'Open whole Hom-action boundaries require later ' +
                    'contextual structural lowering'
                );
            }
            return this.makeTerm(
                {
                    tag: 'typed-application',
                    judgment,
                    subject,
                    argument: boundary,
                    provenance: nodeProvenance
                },
                (closed as ElaboratedSurfaceTerm).type,
                usage,
                closed,
                [
                    ...subject.abstractions,
                    ...boundary.sourceEndpoint.abstractions,
                    ...boundary.targetEndpoint.abstractions
                ]
            );
        }

        const argument = this.requireTerm(
            argumentValue as CoreCategoricalTerm,
            nodeProvenance
        );
        const selection = this.selectTermApplication(
            subject,
            argument,
            expectedShape,
            nodeProvenance
        );
        const usage = mergeUsage(subject.usage, argument.usage);
        let type: CoreType;
        let closed: ElaboratedSurfaceTerm | undefined;
        if (
            subject.closed !== undefined &&
            argument.closed !== undefined
        ) {
            closed = this.operation(
                selection.operation,
                [subject, argument],
                nodeProvenance
            );
            const mixedNestedType =
                selection.operation === 'functor.object' &&
                subject.type.tag === 'functor'
                    ? this.mixedNestedFibreRichType(
                        subject.type.targetCategory,
                        nodeProvenance,
                        'closed categorical object application result'
                    )
                    : undefined;
            if (mixedNestedType === undefined) {
                type = closed.type;
            } else {
                type = mixedNestedType;
                closed = deepFreeze({
                    term: closed.term,
                    type: copyCoreType(mixedNestedType),
                    sourceSpan: closed.sourceSpan,
                    recovered: [...closed.recovered]
                });
            }
        } else if (selection.operation === 'functor.object') {
            type = this.categoricalTypeForCategoryObject(
                subject.type.targetCategory,
                nodeProvenance,
                'open categorical object application result'
            );
        } else {
            this.fail(
                'MISSING_STRUCTURAL_OWNER',
                nodeProvenance,
                'This open categorical application requires evaluation and ' +
                'contextual structural lowering from USABILITY-1C'
            );
        }

        return this.makeTerm(
            {
                tag: 'typed-application',
                judgment: selection.judgment,
                subject,
                argument,
                provenance: nodeProvenance
            },
            type,
            usage,
            closed,
            [...subject.abstractions, ...argument.abstractions]
        );
    }

    private normalizeBoundary(
        boundary: InternalCoreCategoricalHomBoundary,
        scope: readonly number[]
    ): CoreCategoricalHomBoundaryIr {
        return deepFreeze({
            tag: 'hom-boundary',
            category: boundary.category,
            sourceEndpoint: this.normalizeNode(
                boundary.sourceEndpoint,
                scope
            ),
            targetEndpoint: this.normalizeNode(
                boundary.targetEndpoint,
                scope
            ),
            provenance: boundary.provenance
        });
    }

    private normalizeClassifier(
        classifier: InternalCoreCategoricalClassifier,
        scope: readonly number[],
        nodeProvenance: Provenance
    ): CoreCategoricalClassifier {
        if (
            classifier.tag !== 'indexed-object' &&
            classifier.tag !== 'indexed-functor' &&
            classifier.tag !== 'indexed-transfor' &&
            classifier.tag !== 'nested-indexed-object'
        ) {
            return copyCoreType(classifier);
        }
        if (classifier.tag === 'nested-indexed-object') {
            const outerIndex = scope.indexOf(
                classifier.outerIndexOrdinal
            );
            const innerIndex = scope.indexOf(
                classifier.innerIndexOrdinal
            );
            if (outerIndex < 0 || innerIndex < 0) {
                this.fail(
                    'ESCAPED_SLOT',
                    nodeProvenance,
                    'Nested indexed classifier refers to an escaped outer ' +
                        'or inner base slot'
                );
            }
            return {
                tag: 'nested-indexed-object',
                outerBaseCategory: classifier.outerBaseCategory,
                outerIndex,
                innerBaseCategory: classifier.innerBaseCategory,
                innerIndex,
                classifierFamily: classifier.classifierFamily,
                sourceSection: classifier.sourceSection,
                targetSection: classifier.targetSection,
                endpoint: classifier.endpoint
            };
        }
        const index = scope.indexOf(classifier.indexOrdinal);
        if (index < 0) {
            this.fail(
                'ESCAPED_SLOT',
                nodeProvenance,
                `Indexed fibre classifier refers to escaped slot ` +
                `#${classifier.indexOrdinal}`
            );
        }
        if (classifier.tag === 'indexed-object') {
            return {
                tag: 'indexed-object',
                baseCategory: classifier.baseCategory,
                ...(classifier.familyBaseCategory === undefined
                    ? {}
                    : {
                        familyBaseCategory:
                            classifier.familyBaseCategory
                    }),
                family: classifier.family,
                index
            };
        }
        if (classifier.tag === 'indexed-functor') {
            return {
                tag: 'indexed-functor',
                baseCategory: classifier.baseCategory,
                ...(classifier.sourceFamilyBaseCategory === undefined
                    ? {}
                    : {
                        sourceFamilyBaseCategory:
                            classifier.sourceFamilyBaseCategory
                    }),
                ...(classifier.targetFamilyBaseCategory === undefined
                    ? {}
                    : {
                        targetFamilyBaseCategory:
                            classifier.targetFamilyBaseCategory
                    }),
                sourceFamily: classifier.sourceFamily,
                targetFamily: classifier.targetFamily,
                index,
                ...(classifier.underlyingObjectFamily === undefined
                    ? {}
                    : {
                        underlyingObjectFamily:
                            classifier.underlyingObjectFamily
                    }),
                ...(
                    classifier
                        .underlyingObjectFamilyBaseCategory === undefined
                        ? {}
                        : {
                            underlyingObjectFamilyBaseCategory:
                                classifier
                                    .underlyingObjectFamilyBaseCategory
                        }
                )
            };
        }
        return {
            tag: 'indexed-transfor',
            baseCategory: classifier.baseCategory,
            sourceFamily: classifier.sourceFamily,
            targetFamily: classifier.targetFamily,
            sourceFunctor: classifier.sourceFunctor,
            targetFunctor: classifier.targetFunctor,
            index
        };
    }

    private normalizeNode(
        term: InternalCoreCategoricalTerm,
        scope: readonly number[]
    ): CoreCategoricalContextualIr {
        switch (term.node.tag) {
            case 'explicit-core-term':
                return deepFreeze({
                    tag: 'explicit-core-term',
                    term: term.node.term,
                    type: this.normalizeClassifier(
                        term.type,
                        scope,
                        term.node.provenance
                    ),
                    provenance: term.node.provenance
                });
            case 'slot-token': {
                const index = scope.indexOf(term.node.ordinal);
                if (index < 0) {
                    this.fail(
                        'ESCAPED_SLOT',
                        term.node.provenance,
                        `Categorical slot '${term.node.hint}' ` +
                        `#${term.node.ordinal} escaped its callback body`
                    );
                }
                return deepFreeze({
                    tag: 'slot-reference',
                    index,
                    hint: term.node.hint,
                    type: this.normalizeClassifier(
                        term.type,
                        scope,
                        term.node.provenance
                    ),
                    provenance: term.node.provenance
                });
            }
            case 'typed-application':
                return deepFreeze({
                    tag: 'typed-application',
                    judgmentId: term.node.judgment.id,
                    target: term.node.judgment.target,
                    subject: this.normalizeNode(
                        term.node.subject,
                        scope
                    ),
                    argument:
                        term.node.argument[
                            CORE_CATEGORICAL_BOUNDARY
                        ] === true
                            ? this.normalizeBoundary(
                                term.node.argument as
                                    InternalCoreCategoricalHomBoundary,
                                scope
                            )
                            : this.normalizeNode(
                                term.node.argument as
                                    InternalCoreCategoricalTerm,
                                scope
                            ),
                    type: this.normalizeClassifier(
                        term.type,
                        scope,
                        term.node.provenance
                    ),
                    provenance: term.node.provenance
                });
            case 'typed-cell-composition': {
                const type = this.normalizeClassifier(
                    term.type,
                    scope,
                    term.node.provenance
                );
                if (type.tag !== 'indexed-transfor') {
                    throw new Error(
                        'Typed cell composition lost its indexed-transfor ' +
                            'classifier'
                    );
                }
                return deepFreeze({
                    tag: 'typed-cell-composition',
                    outer: this.normalizeNode(
                        term.node.outer,
                        scope
                    ),
                    inner: this.normalizeNode(
                        term.node.inner,
                        scope
                    ),
                    type,
                    provenance: term.node.provenance
                });
            }
            case 'typed-pair': {
                const type = this.normalizeClassifier(
                    term.type,
                    scope,
                    term.node.provenance
                );
                if (type.tag !== 'indexed-object') {
                    throw new Error(
                        'Typed pair lost its indexed-object classifier'
                    );
                }
                return deepFreeze({
                    tag: 'typed-pair',
                    left: this.normalizeNode(
                        term.node.left,
                        scope
                    ),
                    right: this.normalizeNode(
                        term.node.right,
                        scope
                    ),
                    type,
                    provenance: term.node.provenance
                });
            }
            case 'typed-nested-displayed-application': {
                const type = this.normalizeClassifier(
                    term.type,
                    scope,
                    term.node.provenance
                );
                if (type.tag !== 'nested-indexed-object') {
                    throw new Error(
                        'Typed nested displayed application lost its ' +
                            'nested indexed-object classifier'
                    );
                }
                return deepFreeze({
                    tag: 'typed-nested-displayed-application',
                    subject: this.normalizeNode(
                        term.node.subject,
                        scope
                    ),
                    base: this.normalizeNode(
                        term.node.base,
                        scope
                    ),
                    argument: this.normalizeNode(
                        term.node.argument,
                        scope
                    ),
                    type,
                    provenance: term.node.provenance
                });
            }
            case 'nested-displayed-abstraction': {
                const type = this.normalizeClassifier(
                    term.type,
                    scope,
                    term.node.provenance
                );
                if (type.tag !== 'indexed-object') {
                    throw new Error(
                        'Nested displayed abstraction lost its outer ' +
                            'indexed-object classifier'
                    );
                }
                return deepFreeze({
                    tag: 'nested-displayed-abstraction',
                    name: term.node.name,
                    innerBaseCategory:
                        term.node.innerBaseCategory,
                    subject: this.normalizeNode(
                        term.node.subject,
                        scope
                    ),
                    body: this.normalizeNode(
                        term.node.body,
                        [
                            term.node.fibreOrdinal,
                            term.node.baseOrdinal,
                            ...scope
                        ]
                    ),
                    type,
                    provenance: term.node.provenance
                });
            }
            case 'categorical-abstraction':
                return deepFreeze({
                    tag: 'categorical-abstraction',
                    name: term.node.name,
                    sourceCategory: term.node.sourceCategory,
                    targetCategory: term.node.targetCategory,
                    body: this.normalizeNode(
                        term.node.body,
                        [term.node.ordinal, ...scope]
                    ),
                    type: this.normalizeClassifier(
                        term.type,
                        scope,
                        term.node.provenance
                    ),
                    provenance: term.node.provenance
                });
            default: {
                const exhaustive: never = term.node;
                return exhaustive;
            }
        }
    }

    private identityFunctor(
        category: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation {
        return {
            term: this.structuralCall(
                'identity-functor',
                [{ plicity: 'implicit', value: category }],
                nodeProvenance
            ),
            targetCategory: category,
            structuralPrerequisites: Object.freeze([
                'identity-functor'
            ])
        };
    }

    private composeFunctors(
        sourceCategory: KernelExpression,
        middleCategory: KernelExpression,
        targetCategory: KernelExpression,
        outer: KernelExpression,
        inner: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.structuralCall(
            'functor-composition',
            [
                {
                    plicity: 'implicit',
                    value: sourceCategory
                },
                {
                    plicity: 'implicit',
                    value: middleCategory
                },
                {
                    plicity: 'implicit',
                    value: targetCategory
                },
                { plicity: 'explicit', value: outer },
                { plicity: 'explicit', value: inner }
            ],
            nodeProvenance
        );
    }

    private constantCompilation(
        baseCategory: KernelExpression,
        targetCategory: KernelExpression,
        object: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation {
        const functorCategory = this.functorCategory(
            baseCategory,
            targetCategory,
            nodeProvenance
        );
        const constantAbstraction = this.structuralCall(
            'constant-functor-abstraction',
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'implicit',
                    value: targetCategory
                }
            ],
            nodeProvenance
        );
        return {
            term: this.functorObject(
                targetCategory,
                functorCategory,
                constantAbstraction,
                object,
                nodeProvenance
            ),
            targetCategory,
            structuralPrerequisites: Object.freeze([
                'constant-functor-abstraction'
            ])
        };
    }

    private compileApplicationContext(
        term: InternalCoreCategoricalTerm,
        baseCategory: KernelExpression,
        wiring: CoreCategoricalWiring,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation {
        if (
            term.node.tag !== 'typed-application' ||
            term.node.judgment.target !== 'functor-object' ||
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            this.fail(
                'MISSING_STRUCTURAL_OWNER',
                nodeProvenance,
                'USABILITY-1C bracket lowering currently supports open ' +
                    'ordinary object application only'
            );
        }
        const subject = term.node.subject;
        const argument = term.node.argument as
            InternalCoreCategoricalTerm;
        if (subject.type.tag !== 'functor') {
            this.fail(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                'Contextual application subject is not a functor'
            );
        }
        const sourceCategory = subject.type.sourceCategory;
        const targetCategory = subject.type.targetCategory;
        const argumentCompilation = this.compileContextual(
            argument,
            baseCategory,
            wiring,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                argumentCompilation.targetCategory,
                sourceCategory
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Contextual application argument compiled to the wrong ' +
                    'source category'
            );
        }

        const activeOrdinals = new Set(wiring.keys());
        if (
            subject.closed !== undefined &&
            !usageIntersects(subject.usage, activeOrdinals)
        ) {
            return {
                term: this.composeFunctors(
                    baseCategory,
                    sourceCategory,
                    targetCategory,
                    subject.closed.term,
                    argumentCompilation.term,
                    nodeProvenance
                ),
                targetCategory,
                structuralPrerequisites: mergePrerequisites(
                    argumentCompilation.structuralPrerequisites,
                    ['functor-composition']
                )
            };
        }

        const subjectCompilation = this.compileContextual(
            subject,
            baseCategory,
            wiring,
            nodeProvenance
        );
        const expectedSubjectTarget = this.functorCategory(
            sourceCategory,
            targetCategory,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                subjectCompilation.targetCategory,
                expectedSubjectTarget
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Contextual application subject compiled to the wrong ' +
                    'functor category'
            );
        }

        const evaluationInput = this.productCategory(
            expectedSubjectTarget,
            sourceCategory,
            nodeProvenance
        );
        const subjectFunctorCategory = this.functorCategory(
            baseCategory,
            expectedSubjectTarget,
            nodeProvenance
        );
        const argumentFunctorCategory = this.functorCategory(
            baseCategory,
            sourceCategory,
            nodeProvenance
        );
        const paired = this.structuralCall(
            'product-pair',
            [
                {
                    plicity: 'implicit',
                    value: subjectFunctorCategory
                },
                {
                    plicity: 'implicit',
                    value: argumentFunctorCategory
                },
                {
                    plicity: 'explicit',
                    value: subjectCompilation.term
                },
                {
                    plicity: 'explicit',
                    value: argumentCompilation.term
                }
            ],
            nodeProvenance
        );
        const evaluation = this.structuralCall(
            'evaluation-functor',
            [
                {
                    plicity: 'implicit',
                    value: sourceCategory
                },
                {
                    plicity: 'implicit',
                    value: targetCategory
                }
            ],
            nodeProvenance
        );
        return {
            term: this.composeFunctors(
            baseCategory,
            evaluationInput,
            targetCategory,
            evaluation,
            paired,
            nodeProvenance
            ),
            targetCategory,
            structuralPrerequisites: mergePrerequisites(
                subjectCompilation.structuralPrerequisites,
                argumentCompilation.structuralPrerequisites,
                [
                    'product-category',
                    'product-pair',
                    'evaluation-functor',
                    'functor-composition'
                ]
            )
        };
    }

    private directDiagonal(
        term: InternalCoreCategoricalTerm,
        ordinal: number,
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation | undefined {
        if (
            term.node.tag !== 'typed-application' ||
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            return undefined;
        }
        const finalArgument = term.node.argument as
            InternalCoreCategoricalTerm;
        const firstApplication = term.node.subject;
        if (
            finalArgument.node.tag !== 'slot-token' ||
            finalArgument.node.ordinal !== ordinal ||
            firstApplication.node.tag !== 'typed-application' ||
            firstApplication.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            return undefined;
        }
        const firstArgument = firstApplication.node.argument as
            InternalCoreCategoricalTerm;
        const original = firstApplication.node.subject;
        const expectedOriginalTarget = this.functorCategory(
            sourceCategory,
            targetCategory,
            nodeProvenance
        );
        if (
            firstArgument.node.tag !== 'slot-token' ||
            firstArgument.node.ordinal !== ordinal ||
            original.closed === undefined ||
            original.type.tag !== 'functor' ||
            !kernelExpressionEquals(
                original.type.sourceCategory,
                sourceCategory
            ) ||
            !kernelExpressionEquals(
                original.type.targetCategory,
                expectedOriginalTarget
            )
        ) {
            return undefined;
        }

        const diagonalSource = this.functorCategory(
            sourceCategory,
            expectedOriginalTarget,
            nodeProvenance
        );
        const diagonalTarget = expectedOriginalTarget;
        const diagonal = this.structuralCall(
            'diagonal-functor-abstraction',
            [
                {
                    plicity: 'implicit',
                    value: sourceCategory
                },
                {
                    plicity: 'implicit',
                    value: targetCategory
                }
            ],
            nodeProvenance
        );
        return {
            term: this.functorObject(
                diagonalSource,
                diagonalTarget,
                diagonal,
                original.closed.term,
                nodeProvenance
            ),
            targetCategory,
            structuralPrerequisites: Object.freeze([
                'diagonal-functor-abstraction'
            ])
        };
    }

    private exchangedNestedEta(
        term: InternalCoreCategoricalTerm,
        baseCategory: KernelExpression,
        wiring: CoreCategoricalWiring,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation | undefined {
        if (
            term.node.tag !== 'categorical-abstraction' ||
            wiring.size !== 1 ||
            term.node.body.node.tag !== 'typed-application' ||
            term.node.body.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            return undefined;
        }
        const [outerOrdinal] = wiring.keys();
        const finalArgument = term.node.body.node.argument as
            InternalCoreCategoricalTerm;
        const firstApplication = term.node.body.node.subject;
        if (
            finalArgument.node.tag !== 'slot-token' ||
            finalArgument.node.ordinal !== outerOrdinal ||
            firstApplication.node.tag !== 'typed-application' ||
            firstApplication.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            return undefined;
        }
        const firstArgument = firstApplication.node.argument as
            InternalCoreCategoricalTerm;
        const original = firstApplication.node.subject;
        if (
            firstArgument.node.tag !== 'slot-token' ||
            firstArgument.node.ordinal !== term.node.ordinal ||
            original.closed === undefined ||
            original.type.tag !== 'functor'
        ) {
            return undefined;
        }

        const innerFunctorCategory = this.functorCategory(
            baseCategory,
            term.node.targetCategory,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                original.type.sourceCategory,
                term.node.sourceCategory
            ) ||
            !kernelExpressionEquals(
                original.type.targetCategory,
                innerFunctorCategory
            )
        ) {
            return undefined;
        }

        const exchangeSource = this.functorCategory(
            term.node.sourceCategory,
            innerFunctorCategory,
            nodeProvenance
        );
        const exchangeTarget = this.functorCategory(
            baseCategory,
            this.functorCategory(
                term.node.sourceCategory,
                term.node.targetCategory,
                nodeProvenance
            ),
            nodeProvenance
        );
        const exchange = this.structuralCall(
            'exchange-functor-abstraction',
            [
                {
                    plicity: 'implicit',
                    value: term.node.sourceCategory
                },
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'implicit',
                    value: term.node.targetCategory
                }
            ],
            nodeProvenance
        );
        return {
            term: this.functorObject(
                exchangeSource,
                exchangeTarget,
                exchange,
                original.closed.term,
                nodeProvenance
            ),
            targetCategory: this.functorCategory(
                term.node.sourceCategory,
                term.node.targetCategory,
                nodeProvenance
            ),
            structuralPrerequisites: Object.freeze([
                'exchange-functor-abstraction'
            ])
        };
    }

    private compileNestedAbstractionContext(
        term: InternalCoreCategoricalTerm,
        baseCategory: KernelExpression,
        wiring: CoreCategoricalWiring,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation {
        if (term.node.tag !== 'categorical-abstraction') {
            throw new Error('Expected a categorical abstraction node');
        }
        const exchanged = this.exchangedNestedEta(
            term,
            baseCategory,
            wiring,
            nodeProvenance
        );
        if (exchanged !== undefined) return exchanged;

        const extendedBase = this.productCategory(
            baseCategory,
            term.node.sourceCategory,
            nodeProvenance
        );
        const leftProjection = this.structuralCall(
            'product-left-projection',
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'implicit',
                    value: term.node.sourceCategory
                }
            ],
            nodeProvenance
        );
        const rightProjection = this.structuralCall(
            'product-right-projection',
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'implicit',
                    value: term.node.sourceCategory
                }
            ],
            nodeProvenance
        );
        const extendedWiring = new Map<
            number,
            CoreCategoricalContextualCompilation
        >();
        for (const [ordinal, compilation] of wiring) {
            extendedWiring.set(ordinal, {
                term: this.composeFunctors(
                    extendedBase,
                    baseCategory,
                    compilation.targetCategory,
                    compilation.term,
                    leftProjection,
                    nodeProvenance
                ),
                targetCategory: compilation.targetCategory,
                structuralPrerequisites: mergePrerequisites(
                    compilation.structuralPrerequisites,
                    [
                        'product-category',
                        'product-left-projection',
                        'functor-composition'
                    ]
                )
            });
        }
        extendedWiring.set(term.node.ordinal, {
            term: rightProjection,
            targetCategory: term.node.sourceCategory,
            structuralPrerequisites: Object.freeze([
                'product-category',
                'product-right-projection'
            ])
        });

        const body = this.compileContextual(
            term.node.body,
            extendedBase,
            extendedWiring,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                body.targetCategory,
                term.node.targetCategory
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Nested categorical abstraction '${term.node.name}' ` +
                    'compiled to the wrong target category'
            );
        }

        const uncurriedCategory = this.functorCategory(
            extendedBase,
            term.node.targetCategory,
            nodeProvenance
        );
        const curriedCategory = this.functorCategory(
            baseCategory,
            this.functorCategory(
                term.node.sourceCategory,
                term.node.targetCategory,
                nodeProvenance
            ),
            nodeProvenance
        );
        const curry = this.structuralCall(
            'curry-package',
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'implicit',
                    value: term.node.sourceCategory
                },
                {
                    plicity: 'implicit',
                    value: term.node.targetCategory
                }
            ],
            nodeProvenance
        );
        return {
            term: this.functorObject(
                uncurriedCategory,
                curriedCategory,
                curry,
                body.term,
                nodeProvenance
            ),
            targetCategory: this.functorCategory(
                term.node.sourceCategory,
                term.node.targetCategory,
                nodeProvenance
            ),
            structuralPrerequisites: mergePrerequisites(
                body.structuralPrerequisites,
                ['product-category', 'curry-package']
            )
        };
    }

    private compileContextual(
        term: InternalCoreCategoricalTerm,
        baseCategory: KernelExpression,
        wiring: CoreCategoricalWiring,
        nodeProvenance: Provenance
    ): CoreCategoricalContextualCompilation {
        switch (term.node.tag) {
            case 'slot-token': {
                const compilation = wiring.get(term.node.ordinal);
                if (compilation === undefined) {
                    this.fail(
                        'ESCAPED_SLOT',
                        term.node.provenance,
                        `Categorical slot '${term.node.hint}' has no ` +
                            'contextual wiring'
                    );
                }
                return compilation;
            }
            case 'explicit-core-term': {
                const targetCategory = this.categoricalObjectCategory(
                    term.type,
                    nodeProvenance,
                    'constant bracket target'
                );
                if (targetCategory === undefined) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        nodeProvenance,
                        'Categorical bracket body is not an object of a ' +
                            'supported category'
                    );
                }
                return this.constantCompilation(
                    baseCategory,
                    targetCategory,
                    term.node.term,
                    nodeProvenance
                );
            }
            case 'typed-application':
                return this.compileApplicationContext(
                    term,
                    baseCategory,
                    wiring,
                    nodeProvenance
                );
            case 'typed-cell-composition':
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    'Typed cell composition lowers only inside the ' +
                        'reviewed displayed-transfor abstraction'
                );
            case 'typed-pair':
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    'Typed fibre pairs lower only inside the reviewed ' +
                        'displayed contextual bracket'
                );
            case 'typed-nested-displayed-application':
            case 'nested-displayed-abstraction':
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    'Mixed nested displayed syntax lowers only inside the ' +
                        'reviewed displayed contextual bracket'
                );
            case 'categorical-abstraction':
                return this.compileNestedAbstractionContext(
                    term,
                    baseCategory,
                    wiring,
                    nodeProvenance
                );
            default: {
                const exhaustive: never = term.node;
                return exhaustive;
            }
        }
    }

    private lowerDependentSectionComposition(
        body: InternalCoreCategoricalTerm,
        name: string,
        ordinal: number,
        outerScope: readonly number[],
        baseCategory: KernelExpression,
        targetFamily: KernelExpression,
        plicity: Plicity,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm | undefined {
        if (
            body.node.tag !== 'typed-application' ||
            body.node.judgment.target !==
                'indexed-fibre-functor-object'
        ) {
            return undefined;
        }
        if (
            body.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Dependent section composition received an impossible Hom ' +
                'boundary as its indexed object'
            );
        }
        const indexedFunctor = body.node.subject;
        const indexedObject = body.node.argument as
            InternalCoreCategoricalTerm;
        const fibreApplication =
            indexedFunctor.node.tag === 'typed-application' &&
            indexedFunctor.node.judgment.target ===
                'displayed-functor-fibre' &&
            indexedFunctor.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
                ? indexedFunctor.node
                : undefined;
        const sectionApplication =
            indexedObject.node.tag === 'typed-application' &&
            indexedObject.node.judgment.target ===
                'section-object-evaluation' &&
            indexedObject.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
                ? indexedObject.node
                : undefined;
        const fibreIndex = fibreApplication?.argument as
            InternalCoreCategoricalTerm | undefined;
        const sectionIndex = sectionApplication?.argument as
            InternalCoreCategoricalTerm | undefined;
        const displayedFunctor = fibreApplication?.subject;
        const section = sectionApplication?.subject;

        if (
            this.options.dependentSectionComposition !== true ||
            indexedFunctor.type.tag !== 'indexed-functor' ||
            indexedObject.type.tag !== 'indexed-object' ||
            fibreIndex?.node.tag !== 'slot-token' ||
            sectionIndex?.node.tag !== 'slot-token' ||
            fibreIndex.node.ordinal !== ordinal ||
            sectionIndex.node.ordinal !== ordinal ||
            displayedFunctor === undefined ||
            displayedFunctor.type.tag !== 'displayed-functor' ||
            section === undefined ||
            section.type.tag !== 'dependent-section' ||
            displayedFunctor.closed === undefined ||
            section.closed === undefined ||
            usageCount(displayedFunctor.usage, ordinal) !== 0 ||
            usageCount(section.usage, ordinal) !== 0 ||
            usageCount(body.usage, ordinal) !== 2 ||
            !kernelExpressionEquals(
                indexedFunctor.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                indexedFunctor.type.sourceFamily,
                section.type.family
            ) ||
            !kernelExpressionEquals(
                indexedFunctor.type.targetFamily,
                targetFamily
            ) ||
            !kernelExpressionEquals(
                indexedObject.type.family,
                section.type.family
            ) ||
            !kernelExpressionEquals(
                displayedFunctor.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                displayedFunctor.type.sourceFamily,
                section.type.family
            ) ||
            !kernelExpressionEquals(
                displayedFunctor.type.targetFamily,
                targetFamily
            ) ||
            !kernelExpressionEquals(
                section.type.baseCategory,
                baseCategory
            )
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'USABILITY-DEPENDENT-1A accepts only the exact scoped ' +
                'section-composition body FF[k](s[k]) with a rigid ' +
                'displayed functor and section'
            );
        }

        const sourceFamily = section.type.family;
        const terminal = this.terminalCategory(nodeProvenance);
        const terminalFamily = this.constantDisplayedFamily(
            baseCategory,
            terminal,
            nodeProvenance
        );
        const resultExpression = this.dependentCompositionCall(
            [
                {
                    plicity: 'implicit',
                    value: this.displayedCategoryCategory(
                        baseCategory,
                        nodeProvenance
                    )
                },
                {
                    plicity: 'implicit',
                    value: terminalFamily
                },
                {
                    plicity: 'implicit',
                    value: sourceFamily
                },
                {
                    plicity: 'implicit',
                    value: targetFamily
                },
                {
                    plicity: 'explicit',
                    value: displayedFunctor.closed.term
                },
                {
                    plicity: 'explicit',
                    value: section.closed.term
                }
            ],
            nodeProvenance
        );
        const resultType: CoreType = {
            tag: 'dependent-section',
            category: this.sectionCategory(
                baseCategory,
                targetFamily,
                nodeProvenance
            ),
            baseCategory,
            family: targetFamily
        };
        const resultNode: TemporaryCategoricalNode = Object.freeze({
            tag: 'explicit-core-term' as const,
            term: resultExpression,
            provenance: nodeProvenance
        });
        const remainingUsage = removeUsage(body.usage, ordinal);
        const closed = deepFreeze({
            term: resultExpression,
            type: copyCoreType(resultType),
            sourceSpan: this.spanFor(nodeProvenance),
            recovered: [
                ...displayedFunctor.closed.recovered,
                ...section.closed.recovered
            ]
        });
        const provisional = this.makeTerm(
            resultNode,
            resultType,
            remainingUsage,
            closed,
            body.abstractions
        );
        const evidence = deepFreeze({
            rule:
                'categorical.dependent-section-composition' as const,
            name,
            plicity,
            variation: 'natural' as const,
            polarity: 'covariant' as const,
            cellLevel: 'object' as const,
            dependency: 'displayed' as const,
            sourceCategory: baseCategory,
            targetFamily,
            body: this.normalizeNode(
                body,
                [ordinal, ...outerScope]
            ),
            result: this.normalizeNode(provisional, outerScope),
            structuralPrerequisites: Object.freeze([]),
            dependentPrerequisites: Object.freeze([
                'displayed-functor-fibre' as const,
                'section-object-evaluation' as const,
                'generic-category-composition' as const,
                'terminal-category' as const,
                'displayed-hom-classifier-reduction' as const,
                'section-object-classifier-reduction' as const
            ]),
            provenance: nodeProvenance
        });
        return this.makeTerm(
            resultNode,
            resultType,
            remainingUsage,
            closed,
            [...body.abstractions, evidence]
        );
    }

    /**
     * Factor a finite contravariant source argument
     *
     *   a | L(source-argument)
     *
     * where each closed coherent L is displayed over exact `Op K` while the
     * locally nameless object index remains the shared `k : Obj K`.
     */
    private directMixedSourceFactorization(
        term: InternalCoreCategoricalTerm,
        innerOrdinal: number,
        baseOrdinal: number,
        baseCategory: KernelExpression,
        initialSourceFamily: KernelExpression
    ): CoreCategoricalDirectMixedSourceFactorization | undefined {
        const termObject = indexedObjectView(term.type);
        const oppositeBase = this.oppositeCategory(
            baseCategory,
            term.node.provenance
        );
        if (
            term.node.tag === 'slot-token' &&
            term.node.ordinal === innerOrdinal &&
            termObject !== undefined &&
            termObject.indexOrdinal === baseOrdinal &&
            kernelExpressionEquals(
                termObject.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                termObject.familyBaseCategory,
                oppositeBase
            ) &&
            kernelExpressionEquals(
                termObject.family,
                initialSourceFamily
            )
        ) {
            return Object.freeze({
                rootSourceFamily: initialSourceFamily,
                sourceChain: Object.freeze([])
            });
        }
        if (
            termObject === undefined ||
            term.node.tag !== 'typed-application' ||
            term.node.judgment.target !==
                'indexed-fibre-functor-object' ||
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            return undefined;
        }
        const argument = term.node.argument as
            InternalCoreCategoricalTerm;
        const appliedFunctor = term.node.subject;
        if (
            appliedFunctor.type.tag !== 'indexed-functor' ||
            appliedFunctor.type.indexOrdinal !== baseOrdinal ||
            !kernelExpressionEquals(
                appliedFunctor.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                indexedFunctorSourceBase(appliedFunctor.type),
                oppositeBase
            ) ||
            !kernelExpressionEquals(
                indexedFunctorTargetBase(appliedFunctor.type),
                oppositeBase
            ) ||
            appliedFunctor.node.tag !== 'typed-application' ||
            appliedFunctor.node.judgment.target !==
                'displayed-functor-fibre' ||
            appliedFunctor.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            return undefined;
        }
        const orientedBase = appliedFunctor.node.argument as
            InternalCoreCategoricalTerm;
        const mapper = appliedFunctor.node.subject;
        if (
            orientedBase.node.tag !== 'slot-token' ||
            orientedBase.node.ordinal !== baseOrdinal ||
            orientedBase.type.tag !== 'object' ||
            !kernelExpressionEquals(
                orientedBase.type.category,
                oppositeBase
            ) ||
            mapper.type.tag !== 'displayed-functor' ||
            mapper.closed === undefined ||
            mapper.usage.length !== 0 ||
            !kernelExpressionEquals(
                mapper.type.baseCategory,
                oppositeBase
            ) ||
            !kernelExpressionEquals(
                mapper.type.sourceFamily,
                appliedFunctor.type.sourceFamily
            ) ||
            !kernelExpressionEquals(
                mapper.type.targetFamily,
                appliedFunctor.type.targetFamily
            ) ||
            !kernelExpressionEquals(
                termObject.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                termObject.familyBaseCategory,
                oppositeBase
            ) ||
            !kernelExpressionEquals(
                termObject.family,
                mapper.type.targetFamily
            )
        ) {
            return undefined;
        }
        const prefix = this.directMixedSourceFactorization(
            argument,
            innerOrdinal,
            baseOrdinal,
            baseCategory,
            initialSourceFamily
        );
        const argumentObject = indexedObjectView(argument.type);
        if (
            prefix === undefined ||
            argumentObject === undefined ||
            !kernelExpressionEquals(
                argumentObject.familyBaseCategory,
                oppositeBase
            ) ||
            !kernelExpressionEquals(
                argumentObject.family,
                prefix.rootSourceFamily
            ) ||
            !kernelExpressionEquals(
                appliedFunctor.type.sourceFamily,
                prefix.rootSourceFamily
            )
        ) {
            return undefined;
        }
        return Object.freeze({
            rootSourceFamily: mapper.type.targetFamily,
            sourceChain: Object.freeze([
                ...prefix.sourceChain,
                mapper
            ])
        });
    }

    /**
     * Factor the direct mixed body grammar
     *
     *   c(source-argument)
     *   | F[c](source-argument)
     *   | G(mixed-body)
     *   | (mixed-body, mixed-body)
     *
     * back to either the displayed identity or its already-coherent `F`, plus
     * a finite covariant target chain. No pointwise function or external
     * naturality witness is accepted.
     */
    private directMixedFactorization(
        term: InternalCoreCategoricalTerm,
        outerOrdinal: number,
        innerOrdinal: number,
        baseOrdinal: number,
        baseCategory: KernelExpression,
        outerSourceFamily: KernelExpression,
        innerSourceFamily: KernelExpression
    ): CoreCategoricalDirectMixedFactorization | undefined {
        const termObject = indexedObjectView(term.type);
        if (term.node.tag === 'typed-pair') {
            const left = this.directMixedFactorization(
                term.node.left,
                outerOrdinal,
                innerOrdinal,
                baseOrdinal,
                baseCategory,
                outerSourceFamily,
                innerSourceFamily
            );
            const right = this.directMixedFactorization(
                term.node.right,
                outerOrdinal,
                innerOrdinal,
                baseOrdinal,
                baseCategory,
                outerSourceFamily,
                innerSourceFamily
            );
            if (
                left === undefined ||
                right === undefined ||
                termObject === undefined ||
                termObject.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    termObject.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    termObject.familyBaseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    termObject.family,
                    this.displayedProductFamily(
                        baseCategory,
                        left.targetFamily,
                        right.targetFamily,
                        term.node.provenance
                    )
                )
            ) {
                return undefined;
            }
            return Object.freeze({
                tag: 'pair' as const,
                left,
                right,
                targetFamily: termObject.family
            });
        }
        if (
            term.node.tag !== 'typed-application' ||
            term.node.judgment.target !==
                'indexed-fibre-functor-object' ||
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            return undefined;
        }
        const argument = term.node.argument as
            InternalCoreCategoricalTerm;
        const appliedFunctor = term.node.subject;
        const sourceFactorization =
            this.directMixedSourceFactorization(
                argument,
                innerOrdinal,
                baseOrdinal,
                baseCategory,
                innerSourceFamily
            );
        const oppositeBase = this.oppositeCategory(
            baseCategory,
            term.node.provenance
        );

        // Direct outer-value weakening leaf: H[c], with H : C -> B.
        // The inner `a : A` is structurally unused; compilation composes the
        // coherent H with Functor_catd_const_funcd(A,B). This is a direct
        // nested-binder rule, not a total-context section or curry route.
        const outerArgumentObject = indexedObjectView(argument.type);
        if (
            argument.node.tag === 'slot-token' &&
            argument.node.ordinal === outerOrdinal &&
            outerArgumentObject !== undefined &&
            outerArgumentObject.indexOrdinal === baseOrdinal &&
            kernelExpressionEquals(
                outerArgumentObject.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                outerArgumentObject.familyBaseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                outerArgumentObject.family,
                outerSourceFamily
            ) &&
            appliedFunctor.type.tag === 'indexed-functor' &&
            appliedFunctor.type.indexOrdinal === baseOrdinal &&
            kernelExpressionEquals(
                appliedFunctor.type.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                indexedFunctorSourceBase(appliedFunctor.type),
                baseCategory
            ) &&
            kernelExpressionEquals(
                indexedFunctorTargetBase(appliedFunctor.type),
                baseCategory
            ) &&
            kernelExpressionEquals(
                appliedFunctor.type.sourceFamily,
                outerSourceFamily
            ) &&
            appliedFunctor.node.tag === 'typed-application' &&
            appliedFunctor.node.judgment.target ===
                'displayed-functor-fibre' &&
            appliedFunctor.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
        ) {
            const base = appliedFunctor.node.argument as
                InternalCoreCategoricalTerm;
            const subject = appliedFunctor.node.subject;
            if (
                base.node.tag === 'slot-token' &&
                base.node.ordinal === baseOrdinal &&
                subject.type.tag === 'displayed-functor' &&
                subject.closed !== undefined &&
                subject.usage.length === 0 &&
                kernelExpressionEquals(
                    subject.type.baseCategory,
                    baseCategory
                ) &&
                kernelExpressionEquals(
                    subject.type.sourceFamily,
                    outerSourceFamily
                ) &&
                kernelExpressionEquals(
                    subject.type.targetFamily,
                    appliedFunctor.type.targetFamily
                ) &&
                termObject !== undefined &&
                termObject.indexOrdinal === baseOrdinal &&
                kernelExpressionEquals(
                    termObject.baseCategory,
                    baseCategory
                ) &&
                kernelExpressionEquals(
                    termObject.familyBaseCategory,
                    baseCategory
                ) &&
                kernelExpressionEquals(
                    termObject.family,
                    subject.type.targetFamily
                )
            ) {
                return Object.freeze({
                    tag: 'leaf' as const,
                    rootExpression: subject.closed.term,
                    rootRecovered: Object.freeze([
                        ...subject.closed.recovered
                    ]),
                    rootKind: 'outer-value-weakening' as const,
                    rootBaseUsageCount: 1 as const,
                    rootSourceFamily: innerSourceFamily,
                    sourceChain: Object.freeze([]),
                    initialTargetFamily: subject.type.targetFamily,
                    targetFamily: subject.type.targetFamily
                });
            }
        }

        // Exact bound-outer identity leaf: c(a), with
        // C = Functor_catd(A,B).
        const outerShape = this.mixedFunctorFamilyShape(
            outerSourceFamily,
            baseCategory
        );
        if (
            outerShape !== undefined &&
            sourceFactorization !== undefined &&
            appliedFunctor.node.tag === 'slot-token' &&
            appliedFunctor.node.ordinal === outerOrdinal &&
            appliedFunctor.type.tag === 'indexed-functor' &&
            appliedFunctor.type.indexOrdinal === baseOrdinal &&
            appliedFunctor.type.underlyingObjectFamily !== undefined &&
            kernelExpressionEquals(
                appliedFunctor.type.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                appliedFunctor.type.underlyingObjectFamily,
                outerSourceFamily
            ) &&
            kernelExpressionEquals(
                appliedFunctor.type
                    .underlyingObjectFamilyBaseCategory ?? baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                appliedFunctor.type.sourceFamily,
                outerShape.sourceFamily
            ) &&
            kernelExpressionEquals(
                indexedFunctorSourceBase(appliedFunctor.type),
                oppositeBase
            ) &&
            kernelExpressionEquals(
                indexedFunctorTargetBase(appliedFunctor.type),
                baseCategory
            ) &&
            kernelExpressionEquals(
                appliedFunctor.type.targetFamily,
                outerShape.targetFamily
            ) &&
            kernelExpressionEquals(
                outerShape.sourceFamily,
                sourceFactorization.rootSourceFamily
            ) &&
            termObject !== undefined &&
            termObject.indexOrdinal === baseOrdinal &&
            kernelExpressionEquals(
                termObject.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                termObject.familyBaseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                termObject.family,
                outerShape.targetFamily
            )
        ) {
            const identity = this.displayedIdentityCompilation(
                baseCategory,
                outerSourceFamily,
                term.node.provenance
            );
            return Object.freeze({
                tag: 'leaf' as const,
                rootExpression: identity.term,
                rootRecovered: Object.freeze([]),
                rootKind: 'bound-outer-identity' as const,
                rootBaseUsageCount: 0 as const,
                rootSourceFamily:
                    sourceFactorization.rootSourceFamily,
                sourceChain: sourceFactorization.sourceChain,
                initialTargetFamily: outerShape.targetFamily,
                targetFamily: outerShape.targetFamily
            });
        }

        // Exact eta leaf: F[k](c)(a).
        if (
            sourceFactorization !== undefined &&
            appliedFunctor.type.tag === 'indexed-functor' &&
            appliedFunctor.type.indexOrdinal === baseOrdinal &&
            kernelExpressionEquals(
                appliedFunctor.type.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(
                appliedFunctor.type.sourceFamily,
                sourceFactorization.rootSourceFamily
            ) &&
            kernelExpressionEquals(
                indexedFunctorSourceBase(appliedFunctor.type),
                oppositeBase
            ) &&
            kernelExpressionEquals(
                indexedFunctorTargetBase(appliedFunctor.type),
                baseCategory
            ) &&
            appliedFunctor.node.tag === 'typed-application' &&
            appliedFunctor.node.judgment.target ===
                'indexed-fibre-functor-object' &&
            appliedFunctor.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] !== true
        ) {
            const outerArgument = appliedFunctor.node.argument as
                InternalCoreCategoricalTerm;
            const outerObject = indexedObjectView(outerArgument.type);
            const projectedOuterFunctor =
                appliedFunctor.node.subject;
            if (
                outerArgument.node.tag === 'slot-token' &&
                outerArgument.node.ordinal === outerOrdinal &&
                outerObject !== undefined &&
                outerObject.indexOrdinal === baseOrdinal &&
                kernelExpressionEquals(
                    outerObject.baseCategory,
                    baseCategory
                ) &&
                kernelExpressionEquals(
                    outerObject.familyBaseCategory,
                    baseCategory
                ) &&
                kernelExpressionEquals(
                    outerObject.family,
                    outerSourceFamily
                ) &&
                projectedOuterFunctor.type.tag === 'indexed-functor' &&
                projectedOuterFunctor.type.indexOrdinal === baseOrdinal &&
                projectedOuterFunctor.node.tag ===
                    'typed-application' &&
                projectedOuterFunctor.node.judgment.target ===
                    'displayed-functor-fibre' &&
                projectedOuterFunctor.node.argument[
                    CORE_CATEGORICAL_BOUNDARY
                ] !== true
            ) {
                const base = projectedOuterFunctor.node.argument as
                    InternalCoreCategoricalTerm;
                const subject = projectedOuterFunctor.node.subject;
                const shape = subject.type.tag === 'displayed-functor'
                    ? this.mixedFunctorFamilyShape(
                        subject.type.targetFamily,
                        baseCategory
                    )
                    : undefined;
                if (
                    base.node.tag === 'slot-token' &&
                    base.node.ordinal === baseOrdinal &&
                    subject.type.tag === 'displayed-functor' &&
                    subject.closed !== undefined &&
                    subject.usage.length === 0 &&
                    kernelExpressionEquals(
                        subject.type.baseCategory,
                        baseCategory
                    ) &&
                    kernelExpressionEquals(
                        subject.type.sourceFamily,
                        outerSourceFamily
                    ) &&
                    shape !== undefined &&
                    kernelExpressionEquals(
                        shape.sourceFamily,
                        sourceFactorization.rootSourceFamily
                    ) &&
                    kernelExpressionEquals(
                        shape.targetFamily,
                        appliedFunctor.type.targetFamily
                    ) &&
                    appliedFunctor.type.underlyingObjectFamily !== undefined &&
                    kernelExpressionEquals(
                        appliedFunctor.type.underlyingObjectFamily,
                        subject.type.targetFamily
                    ) &&
                    kernelExpressionEquals(
                        appliedFunctor.type
                            .underlyingObjectFamilyBaseCategory ??
                            baseCategory,
                        baseCategory
                    ) &&
                    termObject !== undefined &&
                    termObject.indexOrdinal === baseOrdinal &&
                    kernelExpressionEquals(
                        termObject.baseCategory,
                        baseCategory
                    ) &&
                    kernelExpressionEquals(
                        termObject.familyBaseCategory,
                        baseCategory
                    ) &&
                    kernelExpressionEquals(
                        termObject.family,
                        shape.targetFamily
                    )
                ) {
                    return Object.freeze({
                        tag: 'leaf' as const,
                        rootExpression: subject.closed.term,
                        rootRecovered: Object.freeze([
                            ...subject.closed.recovered
                        ]),
                        rootKind:
                            'closed-coherent-subject' as const,
                        rootBaseUsageCount: 1 as const,
                        rootSourceFamily:
                            sourceFactorization.rootSourceFamily,
                        sourceChain:
                            sourceFactorization.sourceChain,
                        initialTargetFamily: shape.targetFamily,
                        targetFamily: shape.targetFamily
                    });
                }
            }
        }

        // Recursive target mapping: G[k](mixed-body).
        if (
            termObject === undefined ||
            appliedFunctor.type.tag !== 'indexed-functor' ||
            appliedFunctor.type.indexOrdinal !== baseOrdinal ||
            !kernelExpressionEquals(
                appliedFunctor.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                indexedFunctorSourceBase(appliedFunctor.type),
                baseCategory
            ) ||
            !kernelExpressionEquals(
                indexedFunctorTargetBase(appliedFunctor.type),
                baseCategory
            ) ||
            appliedFunctor.node.tag !== 'typed-application' ||
            appliedFunctor.node.judgment.target !==
                'displayed-functor-fibre' ||
            appliedFunctor.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] === true
        ) {
            return undefined;
        }
        const base = appliedFunctor.node.argument as
            InternalCoreCategoricalTerm;
        const mapper = appliedFunctor.node.subject;
        if (
            base.node.tag !== 'slot-token' ||
            base.node.ordinal !== baseOrdinal ||
            mapper.type.tag !== 'displayed-functor' ||
            mapper.closed === undefined ||
            mapper.usage.length !== 0 ||
            !kernelExpressionEquals(
                mapper.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                mapper.type.sourceFamily,
                appliedFunctor.type.sourceFamily
            ) ||
            !kernelExpressionEquals(
                mapper.type.targetFamily,
                appliedFunctor.type.targetFamily
            )
        ) {
            return undefined;
        }
        const prefix = this.directMixedFactorization(
            argument,
            outerOrdinal,
            innerOrdinal,
            baseOrdinal,
            baseCategory,
            outerSourceFamily,
            innerSourceFamily
        );
        const recursiveArgumentObject = indexedObjectView(argument.type);
        if (
            prefix === undefined ||
            recursiveArgumentObject === undefined ||
            !kernelExpressionEquals(
                recursiveArgumentObject.family,
                prefix.targetFamily
            ) ||
            !kernelExpressionEquals(
                recursiveArgumentObject.familyBaseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                mapper.type.sourceFamily,
                prefix.targetFamily
            ) ||
            !kernelExpressionEquals(
                termObject.family,
                mapper.type.targetFamily
            ) ||
            !kernelExpressionEquals(
                termObject.familyBaseCategory,
                baseCategory
            )
        ) {
            return undefined;
        }
        return Object.freeze({
            tag: 'target-map' as const,
            child: prefix,
            mapper,
            targetFamily: mapper.type.targetFamily
        });
    }

    /**
     * Compile the recursive direct-mixed body tree into one genuine
     * `Functord` term. Every leaf is an existing direct introduction; target
     * nodes use the existing covariant action; pair nodes first use
     * `Product_pair_funcd` and then the reviewed internal product
     * distributor. No contextual curry or pointwise coherence witness occurs
     * in this recursion.
     */
    private compileDirectMixedFactorization(
        factorization: CoreCategoricalDirectMixedFactorization,
        baseCategory: KernelExpression,
        outerSourceFamily: KernelExpression,
        innerSourceFamily: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalCompiledDirectMixedFactorization {
        if (factorization.tag === 'leaf') {
            let currentSource = factorization.rootSourceFamily;
            const currentTarget = factorization.initialTargetFamily;
            let resultFamily = this.mixedFunctorFamily(
                baseCategory,
                currentSource,
                currentTarget,
                nodeProvenance
            );
            let compilation:
                CoreCategoricalDisplayedContextualCompilation;
            if (factorization.rootKind === 'outer-value-weakening') {
                const capability = this.options.directMixedIntroduction;
                if (
                    capability === undefined ||
                    factorization.sourceChain.length !== 0
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        nodeProvenance,
                        'Direct mixed outer-value weakening requires the ' +
                            'reviewed weakening owner and no inner source ' +
                            'chain'
                    );
                }
                const root: CoreCategoricalDisplayedContextualCompilation = {
                    term: factorization.rootExpression,
                    sourceFamily: outerSourceFamily,
                    targetFamily: currentTarget,
                    identity: false,
                    structuralPrerequisites: Object.freeze([]),
                    dependentPrerequisites: Object.freeze([])
                };
                const weakening:
                    CoreCategoricalDisplayedContextualCompilation = {
                        term: kernelCall(
                            kernelFree(
                                capability.mixedConstantWeakeningCoreName,
                                nodeProvenance
                            ),
                            [
                                {
                                    plicity: 'implicit',
                                    value: baseCategory
                                },
                                {
                                    plicity: 'implicit',
                                    value: currentSource
                                },
                                {
                                    plicity: 'implicit',
                                    value: currentTarget
                                }
                            ],
                            nodeProvenance
                        ),
                        sourceFamily: currentTarget,
                        targetFamily: resultFamily,
                        identity: false,
                        structuralPrerequisites: Object.freeze([]),
                        dependentPrerequisites: Object.freeze([
                            'stable-functor-family',
                            'mixed-functor-weakening'
                        ])
                    };
                compilation = this.composeDisplayedCompilations(
                    baseCategory,
                    weakening,
                    root,
                    nodeProvenance
                );
            } else {
                compilation = {
                    term: factorization.rootExpression,
                    sourceFamily: outerSourceFamily,
                    targetFamily: resultFamily,
                    // Keep action composition explicit even when the leaf
                    // term itself is an identity. This preserves the stable
                    // direct-binder Core shape; only the no-action leaf emits
                    // the identity by itself.
                    identity: false,
                    structuralPrerequisites: Object.freeze([]),
                    dependentPrerequisites: Object.freeze([
                        'stable-functor-family',
                        ...(factorization.rootKind ===
                            'bound-outer-identity'
                            ? ['displayed-identity' as const]
                            : [])
                    ])
                };
            }
            if (
                factorization.rootKind === 'bound-outer-identity' &&
                !kernelExpressionEquals(
                    compilation.sourceFamily,
                    compilation.targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Bound-outer direct mixed identity has unequal source ' +
                        'and target families'
                );
            }
            for (
                const mapper of [...factorization.sourceChain].reverse()
            ) {
                if (
                    mapper.type.tag !== 'displayed-functor' ||
                    mapper.closed === undefined ||
                    !kernelExpressionEquals(
                        mapper.type.baseCategory,
                        this.oppositeCategory(
                            baseCategory,
                            nodeProvenance
                        )
                    ) ||
                    !kernelExpressionEquals(
                        mapper.type.targetFamily,
                        currentSource
                    )
                ) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        nodeProvenance,
                        'Direct mixed source chain has incompatible ' +
                            'adjacent families or orientation'
                    );
                }
                const nextSource = mapper.type.sourceFamily;
                const nextResultFamily = this.mixedFunctorFamily(
                    baseCategory,
                    nextSource,
                    currentTarget,
                    nodeProvenance
                );
                const action:
                    CoreCategoricalDisplayedContextualCompilation = {
                        term: this.mixedSourceAction(
                            baseCategory,
                            nextSource,
                            currentSource,
                            currentTarget,
                            mapper.closed.term,
                            nodeProvenance
                        ),
                        sourceFamily: resultFamily,
                        targetFamily: nextResultFamily,
                        identity: false,
                        structuralPrerequisites: Object.freeze([]),
                        dependentPrerequisites: Object.freeze([
                            'stable-functor-family',
                            'mixed-functor-source-action'
                        ])
                    };
                compilation = this.composeDisplayedCompilations(
                    baseCategory,
                    action,
                    compilation,
                    nodeProvenance
                );
                currentSource = nextSource;
                resultFamily = nextResultFamily;
            }
            if (!kernelExpressionEquals(currentSource, innerSourceFamily)) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Direct mixed source chain does not end at the bound ' +
                        'inner source family'
                );
            }
            return {
                compilation,
                recovered: Object.freeze([
                    ...factorization.rootRecovered,
                    ...factorization.sourceChain.flatMap(term =>
                        term.closed === undefined
                            ? []
                            : [...term.closed.recovered]
                    )
                ]),
                leafCount: 1,
                outerUsageCount: 1,
                innerUsageCount: factorization.rootKind ===
                    'outer-value-weakening'
                    ? 0
                    : 1,
                baseUsageCount:
                    factorization.rootBaseUsageCount +
                    factorization.sourceChain.length,
                sourceChainLength: factorization.sourceChain.length,
                targetChainLength: 0,
                pairNodeCount: 0,
                pairDepth: 0,
                rootKinds: Object.freeze([factorization.rootKind]),
                rootSourceFamilies: Object.freeze([
                    factorization.rootSourceFamily
                ]),
                initialTargetFamilies: Object.freeze([
                    factorization.initialTargetFamily
                ])
            };
        }

        if (factorization.tag === 'target-map') {
            const child = this.compileDirectMixedFactorization(
                factorization.child,
                baseCategory,
                outerSourceFamily,
                innerSourceFamily,
                nodeProvenance
            );
            const mapper = factorization.mapper;
            if (
                mapper.type.tag !== 'displayed-functor' ||
                mapper.closed === undefined ||
                !kernelExpressionEquals(
                    mapper.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    mapper.type.sourceFamily,
                    factorization.child.targetFamily
                ) ||
                !kernelExpressionEquals(
                    mapper.type.targetFamily,
                    factorization.targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Direct mixed target map has incompatible adjacent ' +
                        'families'
                );
            }
            const nextResultFamily = this.mixedFunctorFamily(
                baseCategory,
                innerSourceFamily,
                factorization.targetFamily,
                nodeProvenance
            );
            const action: CoreCategoricalDisplayedContextualCompilation = {
                term: this.mixedTargetAction(
                    baseCategory,
                    innerSourceFamily,
                    factorization.child.targetFamily,
                    factorization.targetFamily,
                    mapper.closed.term,
                    nodeProvenance
                ),
                sourceFamily: child.compilation.targetFamily,
                targetFamily: nextResultFamily,
                identity: false,
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites: Object.freeze([
                    'stable-functor-family',
                    'mixed-functor-target-action'
                ])
            };
            return {
                ...child,
                compilation: this.composeDisplayedCompilations(
                    baseCategory,
                    action,
                    child.compilation,
                    nodeProvenance
                ),
                recovered: Object.freeze([
                    ...child.recovered,
                    ...mapper.closed.recovered
                ]),
                baseUsageCount: child.baseUsageCount + 1,
                targetChainLength: child.targetChainLength + 1
            };
        }

        const left = this.compileDirectMixedFactorization(
            factorization.left,
            baseCategory,
            outerSourceFamily,
            innerSourceFamily,
            nodeProvenance
        );
        const right = this.compileDirectMixedFactorization(
            factorization.right,
            baseCategory,
            outerSourceFamily,
            innerSourceFamily,
            nodeProvenance
        );
        const paired = this.pairDisplayedCompilations(
            baseCategory,
            left.compilation,
            right.compilation,
            nodeProvenance
        );
        const capability = this.options.directMixedIntroduction;
        if (capability === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Recursive direct mixed pairs require the reviewed product ' +
                    'distributor capability'
            );
        }
        const distributedTarget = this.mixedFunctorFamily(
            baseCategory,
            innerSourceFamily,
            factorization.targetFamily,
            nodeProvenance
        );
        const distributor:
            CoreCategoricalDisplayedContextualCompilation = {
                term: kernelCall(
                    kernelFree(
                        capability.mixedProductDistributorCoreName,
                        nodeProvenance
                    ),
                    [
                        { plicity: 'implicit', value: baseCategory },
                        { plicity: 'implicit', value: innerSourceFamily },
                        {
                            plicity: 'implicit',
                            value: factorization.left.targetFamily
                        },
                        {
                            plicity: 'implicit',
                            value: factorization.right.targetFamily
                        }
                    ],
                    nodeProvenance
                ),
                sourceFamily: paired.targetFamily,
                targetFamily: distributedTarget,
                identity: false,
                structuralPrerequisites: Object.freeze([
                    'product-category',
                    'product-pair',
                    'functor-composition',
                    'uncurry-package'
                ]),
                dependentPrerequisites: Object.freeze([
                    'internal-product-functor',
                    'stable-functor-family',
                    'mixed-functor-product-distributor'
                ])
            };
        return {
            compilation: this.composeDisplayedCompilations(
                baseCategory,
                distributor,
                paired,
                nodeProvenance
            ),
            recovered: Object.freeze([
                ...left.recovered,
                ...right.recovered
            ]),
            leafCount: left.leafCount + right.leafCount,
            outerUsageCount:
                left.outerUsageCount + right.outerUsageCount,
            innerUsageCount:
                left.innerUsageCount + right.innerUsageCount,
            baseUsageCount:
                left.baseUsageCount + right.baseUsageCount,
            sourceChainLength:
                left.sourceChainLength + right.sourceChainLength,
            targetChainLength:
                left.targetChainLength + right.targetChainLength,
            pairNodeCount:
                left.pairNodeCount + right.pairNodeCount + 1,
            pairDepth: Math.max(left.pairDepth, right.pairDepth) + 1,
            rootKinds: Object.freeze([
                ...left.rootKinds,
                ...right.rootKinds
            ]),
            rootSourceFamilies: Object.freeze([
                ...left.rootSourceFamilies,
                ...right.rootSourceFamilies
            ]),
            initialTargetFamilies: Object.freeze([
                ...left.initialTargetFamilies,
                ...right.initialTargetFamilies
            ])
        };
    }

    private directDisplayedFunctorChain(
        term: InternalCoreCategoricalTerm,
        fibreOrdinal: number,
        baseOrdinal: number,
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression
    ): readonly InternalCoreCategoricalTerm[] | undefined {
        if (
            term.node.tag === 'slot-token' &&
            term.node.ordinal === fibreOrdinal &&
            term.type.tag === 'indexed-object' &&
            term.type.indexOrdinal === baseOrdinal &&
            kernelExpressionEquals(
                term.type.baseCategory,
                baseCategory
            ) &&
            kernelExpressionEquals(term.type.family, sourceFamily)
        ) {
            return Object.freeze([]);
        }
        if (
            term.node.tag !== 'typed-application' ||
            term.node.judgment.target !==
                'indexed-fibre-functor-object' ||
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            return undefined;
        }
        const indexedFunctor = term.node.subject;
        const argument = term.node.argument as
            InternalCoreCategoricalTerm;
        if (
            indexedFunctor.node.tag !== 'typed-application' ||
            indexedFunctor.node.judgment.target !==
                'displayed-functor-fibre' ||
            indexedFunctor.node.argument[
                CORE_CATEGORICAL_BOUNDARY
            ] === true ||
            indexedFunctor.type.tag !== 'indexed-functor' ||
            indexedFunctor.type.indexOrdinal !== baseOrdinal ||
            !kernelExpressionEquals(
                indexedFunctor.type.baseCategory,
                baseCategory
            )
        ) {
            return undefined;
        }
        const baseToken = indexedFunctor.node.argument as
            InternalCoreCategoricalTerm;
        const displayedFunctor = indexedFunctor.node.subject;
        if (
            baseToken.node.tag !== 'slot-token' ||
            baseToken.node.ordinal !== baseOrdinal ||
            displayedFunctor.type.tag !== 'displayed-functor' ||
            displayedFunctor.closed === undefined ||
            usageCount(displayedFunctor.usage, baseOrdinal) !== 0 ||
            usageCount(displayedFunctor.usage, fibreOrdinal) !== 0 ||
            !kernelExpressionEquals(
                displayedFunctor.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                displayedFunctor.type.sourceFamily,
                indexedFunctor.type.sourceFamily
            ) ||
            !kernelExpressionEquals(
                displayedFunctor.type.targetFamily,
                indexedFunctor.type.targetFamily
            )
        ) {
            return undefined;
        }
        const prefix = this.directDisplayedFunctorChain(
            argument,
            fibreOrdinal,
            baseOrdinal,
            baseCategory,
            sourceFamily
        );
        if (
            prefix === undefined ||
            argument.type.tag !== 'indexed-object' ||
            !kernelExpressionEquals(
                argument.type.family,
                displayedFunctor.type.sourceFamily
            ) ||
            term.type.tag !== 'indexed-object' ||
            !kernelExpressionEquals(
                term.type.family,
                displayedFunctor.type.targetFamily
            )
        ) {
            return undefined;
        }
        return Object.freeze([...prefix, displayedFunctor]);
    }

    private displayedSectionWeakeningBody(
        body: InternalCoreCategoricalTerm,
        fibreOrdinal: number,
        baseOrdinal: number,
        baseCategory: KernelExpression,
        targetFamily: KernelExpression
    ): InternalCoreCategoricalTerm | undefined {
        if (
            this.options.displayedWeakeningReindexing !== true ||
            body.node.tag !== 'typed-application' ||
            body.node.judgment.target !==
                'section-object-evaluation' ||
            body.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
        ) {
            return undefined;
        }
        const index = body.node.argument as
            InternalCoreCategoricalTerm;
        const section = body.node.subject;
        if (
            index.node.tag !== 'slot-token' ||
            index.node.ordinal !== baseOrdinal ||
            section.type.tag !== 'dependent-section' ||
            section.closed === undefined ||
            !kernelExpressionEquals(
                section.type.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                section.type.family,
                targetFamily
            ) ||
            usageCount(section.usage, fibreOrdinal) !== 0 ||
            usageCount(section.usage, baseOrdinal) !== 0 ||
            usageCount(body.usage, fibreOrdinal) !== 0 ||
            usageCount(body.usage, baseOrdinal) !== 1
        ) {
            return undefined;
        }
        return section;
    }

    private lowerDisplayedSectionWeakening(
        section: InternalCoreCategoricalTerm,
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        if (
            this.options.displayedWeakeningReindexing !== true ||
            section.type.tag !== 'dependent-section' ||
            section.closed === undefined
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed section weakening lost its qualified section'
            );
        }
        return this.lowerDisplayedSectionWeakeningTerm(
            section.closed.term,
            baseCategory,
            sourceFamily,
            targetFamily,
            nodeProvenance
        );
    }

    private lowerDisplayedSectionWeakeningTerm(
        sectionTerm: KernelExpression,
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const totalCategory = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: sourceFamily }
            ],
            nodeProvenance
        );
        const projection = kernelCall(
            kernelFree(
                CORE_DIRECTED_1B_PRIMITIVE_NAMES[
                    'sigma-first-projection'
                ],
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: sourceFamily }
            ],
            nodeProvenance
        );
        const pulledTarget = kernelApplication(
            'displayed-pullback',
            [
                { value: totalCategory },
                { value: baseCategory },
                { value: targetFamily },
                { value: projection }
            ],
            nodeProvenance
        );
        const pullbackFunctor = kernelCall(
            kernelFree(
                coreCategoricalFibredWeakenReindexCoreName(
                    'sectionPullback'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: totalCategory },
                { plicity: 'implicit', value: baseCategory },
                { plicity: 'explicit', value: projection },
                { plicity: 'explicit', value: targetFamily }
            ],
            nodeProvenance
        );
        const sourceSectionCategory = this.displayedFunctorCategory(
            baseCategory,
            this.constantDisplayedFamily(
                baseCategory,
                this.terminalCategory(nodeProvenance),
                nodeProvenance
            ),
            targetFamily,
            nodeProvenance
        );
        const targetSectionCategory = this.displayedFunctorCategory(
            totalCategory,
            this.constantDisplayedFamily(
                totalCategory,
                this.terminalCategory(nodeProvenance),
                nodeProvenance
            ),
            pulledTarget,
            nodeProvenance
        );
        return kernelApplication(
            'functor-object',
            [
                { value: sourceSectionCategory },
                { value: targetSectionCategory },
                { value: pullbackFunctor },
                { value: sectionTerm }
            ],
            nodeProvenance
        );
    }

    /**
     * Carry an already compiled displayed map through one later dependent
     * context level.
     *
     * If `compiled : R -> T` lies over K and `S` lies over Sigma_K(R),
     * first reinterpret `compiled` as its Sigma section and then pull that
     * section through S. The result is the canonical displayed map
     *
     *   S -> (Sigma_proj1 R)^* T
     *
     * over Sigma_K(R). Repeating this operation is the context-presentation
     * recursion used by DISPLAYED-CHAIN-2A; it introduces no owner-specific
     * checker or evaluator branch.
     */
    private liftDisplayedCompilationThroughNextFamily(
        baseCategory: KernelExpression,
        compiled:
            CoreCategoricalDisplayedContextualCompilation,
        nextFamily: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        const totalBaseCategory = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                {
                    plicity: 'explicit',
                    value: compiled.sourceFamily
                }
            ],
            nodeProvenance
        );
        const projection = kernelCall(
            kernelFree(
                CORE_DIRECTED_1B_PRIMITIVE_NAMES[
                    'sigma-first-projection'
                ],
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                {
                    plicity: 'explicit',
                    value: compiled.sourceFamily
                }
            ],
            nodeProvenance
        );
        const liftedTargetFamily = kernelApplication(
            'displayed-pullback',
            [
                { value: totalBaseCategory },
                { value: baseCategory },
                { value: compiled.targetFamily },
                { value: projection }
            ],
            nodeProvenance
        );
        const sigmaSection = kernelCall(
            kernelFree(
                coreCategoricalDisplayedChainCoreName(
                    'sigmaFunctordSection'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: baseCategory },
                {
                    plicity: 'implicit',
                    value: compiled.sourceFamily
                },
                {
                    plicity: 'implicit',
                    value: compiled.targetFamily
                },
                { plicity: 'explicit', value: compiled.term }
            ],
            nodeProvenance
        );
        return {
            term: this.lowerDisplayedSectionWeakeningTerm(
                sigmaSection,
                totalBaseCategory,
                nextFamily,
                liftedTargetFamily,
                nodeProvenance
            ),
            sourceFamily: nextFamily,
            targetFamily: liftedTargetFamily,
            identity: false,
            structuralPrerequisites:
                compiled.structuralPrerequisites,
            dependentPrerequisites:
                mergeDependentPrerequisites(
                    compiled.dependentPrerequisites,
                    [
                        'sigma-functord-section',
                        'sigma-projection-pullback',
                        'sigma-pi-uncurrying-proof',
                        'sigma-first-projection',
                        'section-pullback-functor',
                        'constant-displayed-family-object'
                    ]
                )
        };
    }

    private displayedIdentityCompilation(
        baseCategory: KernelExpression,
        family: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        return {
            term: kernelCall(
                kernelFree(
                    coreCategoricalFibredStructureCoreName(
                        'displayed-identity'
                    ),
                    nodeProvenance
                ),
                [
                    { plicity: 'implicit', value: baseCategory },
                    { plicity: 'implicit', value: family }
                ],
                nodeProvenance
            ),
            sourceFamily: family,
            targetFamily: family,
            identity: true,
            structuralPrerequisites: Object.freeze([]),
            dependentPrerequisites: Object.freeze([
                'displayed-identity'
            ])
        };
    }

    private displayedProjectionCompilation(
        side: 'left' | 'right',
        baseCategory: KernelExpression,
        leftFamily: KernelExpression,
        rightFamily: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        const sourceFamily = this.displayedProductFamily(
            baseCategory,
            leftFamily,
            rightFamily,
            nodeProvenance
        );
        return {
            term: kernelCall(
                kernelFree(
                    coreCategoricalFibredStructureCoreName(
                        side === 'left'
                            ? 'displayed-product-left-projection'
                            : 'displayed-product-right-projection'
                    ),
                    nodeProvenance
                ),
                [
                    { plicity: 'implicit', value: baseCategory },
                    { plicity: 'explicit', value: leftFamily },
                    { plicity: 'explicit', value: rightFamily }
                ],
                nodeProvenance
            ),
            sourceFamily,
            targetFamily: side === 'left'
                ? leftFamily
                : rightFamily,
            identity: false,
            structuralPrerequisites: Object.freeze([
                'product-category',
                'product-pair',
                'functor-composition',
                'uncurry-package'
            ]),
            dependentPrerequisites: Object.freeze([
                'internal-product-functor',
                side === 'left'
                    ? 'displayed-product-left-projection'
                    : 'displayed-product-right-projection'
            ])
        };
    }

    private composeDisplayedCompilations(
        baseCategory: KernelExpression,
        after:
            CoreCategoricalDisplayedContextualCompilation,
        before:
            CoreCategoricalDisplayedContextualCompilation,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        if (!kernelExpressionEquals(
            before.targetFamily,
            after.sourceFamily
        )) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed contextual composition has incompatible ' +
                    'intermediate families'
            );
        }
        if (before.identity) {
            return {
                ...after,
                sourceFamily: before.sourceFamily
            };
        }
        if (after.identity) {
            return {
                ...before,
                targetFamily: after.targetFamily
            };
        }
        return {
            term: this.dependentCompositionCall(
                [
                    {
                        plicity: 'implicit',
                        value: this.displayedCategoryCategory(
                            baseCategory,
                            nodeProvenance
                        )
                    },
                    {
                        plicity: 'implicit',
                        value: before.sourceFamily
                    },
                    {
                        plicity: 'implicit',
                        value: before.targetFamily
                    },
                    {
                        plicity: 'implicit',
                        value: after.targetFamily
                    },
                    { plicity: 'explicit', value: after.term },
                    { plicity: 'explicit', value: before.term }
                ],
                nodeProvenance
            ),
            sourceFamily: before.sourceFamily,
            targetFamily: after.targetFamily,
            identity: false,
            structuralPrerequisites: mergePrerequisites(
                before.structuralPrerequisites,
                after.structuralPrerequisites
            ),
            dependentPrerequisites:
                mergeDependentPrerequisites(
                    before.dependentPrerequisites,
                    after.dependentPrerequisites,
                    [
                        'generic-category-composition',
                        'displayed-hom-classifier-reduction'
                    ]
                )
        };
    }

    private pairDisplayedCompilations(
        baseCategory: KernelExpression,
        left:
            CoreCategoricalDisplayedContextualCompilation,
        right:
            CoreCategoricalDisplayedContextualCompilation,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        if (!kernelExpressionEquals(
            left.sourceFamily,
            right.sourceFamily
        )) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed contextual pair branches do not have one ' +
                    'literal source family'
            );
        }
        const targetFamily = this.displayedProductFamily(
            baseCategory,
            left.targetFamily,
            right.targetFamily,
            nodeProvenance
        );
        return {
            term: kernelCall(
                kernelFree(
                    coreCategoricalFibredStructureCoreName(
                        'displayed-product-pair'
                    ),
                    nodeProvenance
                ),
                [
                    { plicity: 'implicit', value: baseCategory },
                    {
                        plicity: 'implicit',
                        value: left.sourceFamily
                    },
                    {
                        plicity: 'implicit',
                        value: left.targetFamily
                    },
                    {
                        plicity: 'implicit',
                        value: right.targetFamily
                    },
                    { plicity: 'explicit', value: left.term },
                    { plicity: 'explicit', value: right.term }
                ],
                nodeProvenance
            ),
            sourceFamily: left.sourceFamily,
            targetFamily,
            identity: false,
            structuralPrerequisites: mergePrerequisites(
                left.structuralPrerequisites,
                right.structuralPrerequisites,
                [
                    'product-category',
                    'product-pair',
                    'functor-composition',
                    'uncurry-package'
                ]
            ),
            dependentPrerequisites:
                mergeDependentPrerequisites(
                    left.dependentPrerequisites,
                    right.dependentPrerequisites,
                    [
                        'internal-product-functor',
                        'displayed-product-pair'
                    ]
                )
        };
    }

    private displayedFamilyTree(
        bindings: readonly {
            readonly ordinal: number;
            readonly family: KernelExpression;
        }[],
        baseCategory: KernelExpression,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedFamilyTree {
        let tree: CoreCategoricalDisplayedFamilyTree = {
            family: bindings[0].family,
            ordinal: bindings[0].ordinal
        };
        for (const binding of bindings.slice(1)) {
            const right: CoreCategoricalDisplayedFamilyTree = {
                family: binding.family,
                ordinal: binding.ordinal
            };
            tree = {
                family: this.displayedProductFamily(
                    baseCategory,
                    tree.family,
                    right.family,
                    nodeProvenance
                ),
                left: tree,
                right
            };
        }
        return tree;
    }

    private displayedProjectionWiring(
        baseCategory: KernelExpression,
        tree: CoreCategoricalDisplayedFamilyTree,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedWiring {
        const wiring = new Map<
            number,
            CoreCategoricalDisplayedContextualCompilation
        >();
        const visit = (
            node: CoreCategoricalDisplayedFamilyTree,
            current:
                CoreCategoricalDisplayedContextualCompilation
        ): void => {
            if (node.ordinal !== undefined) {
                wiring.set(node.ordinal, current);
                return;
            }
            if (node.left === undefined || node.right === undefined) {
                throw new Error(
                    'Displayed family product tree lost a factor'
                );
            }
            const leftProjection =
                this.displayedProjectionCompilation(
                    'left',
                    baseCategory,
                    node.left.family,
                    node.right.family,
                    nodeProvenance
                );
            const rightProjection =
                this.displayedProjectionCompilation(
                    'right',
                    baseCategory,
                    node.left.family,
                    node.right.family,
                    nodeProvenance
                );
            visit(
                node.left,
                this.composeDisplayedCompilations(
                    baseCategory,
                    leftProjection,
                    current,
                    nodeProvenance
                )
            );
            visit(
                node.right,
                this.composeDisplayedCompilations(
                    baseCategory,
                    rightProjection,
                    current,
                    nodeProvenance
                )
            );
        };
        visit(
            tree,
            this.displayedIdentityCompilation(
                baseCategory,
                tree.family,
                nodeProvenance
            )
        );
        return wiring;
    }

    private compileDisplayedEvaluationApplication(
        term: InternalCoreCategoricalTerm,
        baseOrdinal: number,
        baseCategory: KernelExpression,
        wiring: CoreCategoricalDisplayedWiring,
        activeOrdinals: ReadonlySet<number>,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        if (
            this.options.displayedEvaluation !== true ||
            term.node.tag !== 'typed-application' ||
            (
                term.node.judgment.target !==
                    'displayed-evaluation-varying-object' &&
                term.node.judgment.target !==
                    'displayed-evaluation-fixed-object'
            ) ||
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true ||
            term.node.subject.type.tag !== 'indexed-object' ||
            term.node.subject.type.indexOrdinal !== baseOrdinal ||
            term.type.tag !== 'indexed-object' ||
            term.type.indexOrdinal !== baseOrdinal
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                term.node.provenance,
                'Displayed contextual evaluation lost its reviewed typed ' +
                    'application judgment'
            );
        }
        const subject = term.node.subject;
        const argument = term.node.argument as
            InternalCoreCategoricalTerm;
        if (
            subject.type.tag !== 'indexed-object' ||
            term.type.tag !== 'indexed-object'
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                term.node.provenance,
                'Displayed evaluation lost its indexed-object classifier'
            );
        }
        const subjectType = subject.type;
        const resultType = term.type;
        const shape = this.displayedEvaluationFamilyShape(
            subjectType.family,
            baseCategory,
            term.node.provenance
        );
        if (
            shape === undefined ||
            !kernelExpressionEquals(
                subjectType.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                resultType.baseCategory,
                baseCategory
            ) ||
            !kernelExpressionEquals(
                resultType.family,
                shape.targetFamily
            )
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                term.node.provenance,
                'Displayed evaluation classifier drifted from its stable ' +
                    'constant-domain source or target family'
            );
        }
        const subjectCompilation = this.compileDisplayedContextual(
            subject,
            baseOrdinal,
            baseCategory,
            wiring,
            activeOrdinals,
            nodeProvenance
        );
        if (!kernelExpressionEquals(
            subjectCompilation.targetFamily,
            subjectType.family
        )) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                term.node.provenance,
                'Recursively compiled displayed-evaluation subject has the ' +
                    'wrong target family'
            );
        }
        const coherentArgumentFamily = this.constantDisplayedFamily(
            baseCategory,
            shape.domainCategory,
            term.node.provenance
        );
        let argumentCompilation:
            CoreCategoricalDisplayedContextualCompilation;
        if (
            term.node.judgment.target ===
                'displayed-evaluation-varying-object'
        ) {
            if (
                argument.type.tag !== 'indexed-object' ||
                argument.type.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    argument.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    argument.type.family,
                    coherentArgumentFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    term.node.provenance,
                    'The recursively varying evaluation argument must have ' +
                        'the constant family Const_K(A)'
                );
            }
            argumentCompilation = this.compileDisplayedContextual(
                argument,
                baseOrdinal,
                baseCategory,
                wiring,
                activeOrdinals,
                nodeProvenance
            );
        } else {
            const argumentCategory = this.categoricalObjectCategory(
                argument.type,
                term.node.provenance,
                'fixed displayed-evaluation argument'
            );
            if (
                argument.closed === undefined ||
                argumentCategory === undefined ||
                !coreObjectCategoryEquals(
                    argumentCategory,
                    shape.domainCategory
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    term.node.provenance,
                    'The fixed displayed-evaluation argument must remain a ' +
                        'closed object of A'
                );
            }
            const sourceFamily = subjectCompilation.sourceFamily;
            const terminalFamily = this.constantDisplayedFamily(
                baseCategory,
                this.terminalCategory(term.node.provenance),
                term.node.provenance
            );
            const terminalCompilation:
            CoreCategoricalDisplayedContextualCompilation = {
                term: this.displayedTerminalTerm(
                    baseCategory,
                    sourceFamily,
                    term.node.provenance
                ),
                sourceFamily,
                targetFamily: terminalFamily,
                identity: false,
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites: Object.freeze([
                    'displayed-terminal'
                ])
            };
            const constantSectionCompilation:
            CoreCategoricalDisplayedContextualCompilation = {
                term: this.constantSectionTerm(
                    baseCategory,
                    shape.domainCategory,
                    argument,
                    term.node.provenance
                ),
                sourceFamily: terminalFamily,
                targetFamily: coherentArgumentFamily,
                identity: false,
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites: Object.freeze([
                    'constant-section-functor',
                    'section-object-classifier-reduction'
                ])
            };
            argumentCompilation =
                this.composeDisplayedCompilations(
                    baseCategory,
                    constantSectionCompilation,
                    terminalCompilation,
                    term.node.provenance
                );
        }
        if (!kernelExpressionEquals(
            argumentCompilation.targetFamily,
            coherentArgumentFamily
        )) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                term.node.provenance,
                'Compiled displayed-evaluation argument has the wrong ' +
                    'constant family'
            );
        }
        const paired = this.pairDisplayedCompilations(
            baseCategory,
            subjectCompilation,
            argumentCompilation,
            term.node.provenance
        );
        const evaluator:
        CoreCategoricalDisplayedContextualCompilation = {
            term: this.displayedEvaluationTerm(
                baseCategory,
                shape.domainCategory,
                shape.targetFamily,
                term.node.provenance
            ),
            sourceFamily: this.displayedProductFamily(
                baseCategory,
                subjectType.family,
                coherentArgumentFamily,
                term.node.provenance
            ),
            targetFamily: shape.targetFamily,
            identity: false,
            structuralPrerequisites: Object.freeze([
                'product-category',
                'product-pair',
                'functor-composition',
                'uncurry-package'
            ]),
            dependentPrerequisites: Object.freeze([
                'stable-functor-family',
                'displayed-evaluation'
            ])
        };
        return this.composeDisplayedCompilations(
            baseCategory,
            evaluator,
            paired,
            term.node.provenance
        );
    }

    private compileDisplayedContextual(
        term: InternalCoreCategoricalTerm,
        baseOrdinal: number,
        baseCategory: KernelExpression,
        wiring: CoreCategoricalDisplayedWiring,
        activeOrdinals: ReadonlySet<number>,
        nodeProvenance: Provenance
    ): CoreCategoricalDisplayedContextualCompilation {
        switch (term.node.tag) {
            case 'slot-token': {
                const compilation = wiring.get(term.node.ordinal);
                if (
                    compilation === undefined ||
                    term.type.tag !== 'indexed-object' ||
                    term.type.indexOrdinal !== baseOrdinal ||
                    !kernelExpressionEquals(
                        term.type.baseCategory,
                        baseCategory
                    ) ||
                    !kernelExpressionEquals(
                        term.type.family,
                        compilation.targetFamily
                    )
                ) {
                    this.fail(
                        'ESCAPED_SLOT',
                        term.node.provenance,
                        `Displayed slot '${term.node.hint}' has no valid ` +
                            'projection wiring'
                    );
                }
                return compilation;
            }
            case 'typed-pair': {
                const left = this.compileDisplayedContextual(
                    term.node.left,
                    baseOrdinal,
                    baseCategory,
                    wiring,
                    activeOrdinals,
                    nodeProvenance
                );
                const right = this.compileDisplayedContextual(
                    term.node.right,
                    baseOrdinal,
                    baseCategory,
                    wiring,
                    activeOrdinals,
                    nodeProvenance
                );
                const paired = this.pairDisplayedCompilations(
                    baseCategory,
                    left,
                    right,
                    term.node.provenance
                );
                if (
                    term.type.tag !== 'indexed-object' ||
                    !kernelExpressionEquals(
                        term.type.family,
                        paired.targetFamily
                    )
                ) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        term.node.provenance,
                        'Typed fibre-pair classifier drifted from its ' +
                            'compiled target family'
                    );
                }
                return paired;
            }
            case 'nested-displayed-abstraction': {
                if (
                    this.options.mixedNestedFactorization !== true ||
                    term.type.tag !== 'indexed-object' ||
                    term.node.subject.type.tag !== 'indexed-object' ||
                    term.type.indexOrdinal !== baseOrdinal ||
                    term.node.subject.type.indexOrdinal !== baseOrdinal ||
                    !kernelExpressionEquals(
                        term.type.baseCategory,
                        baseCategory
                    ) ||
                    !kernelExpressionEquals(
                        term.node.subject.type.baseCategory,
                        baseCategory
                    ) ||
                    !kernelExpressionEquals(
                        term.type.family,
                        term.node.subject.type.family
                    ) ||
                    this.mixedNestedDisplayedFunctorShape(
                        term.type.family,
                        baseCategory
                    ) === undefined
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        term.node.provenance,
                        'Nested displayed abstraction lost its canonical ' +
                            'Hom_catd classifier or outer contextual index'
                    );
                }
                const compilation = this.compileDisplayedContextual(
                    term.node.subject,
                    baseOrdinal,
                    baseCategory,
                    wiring,
                    activeOrdinals,
                    nodeProvenance
                );
                if (!kernelExpressionEquals(
                    compilation.targetFamily,
                    term.type.family
                )) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        term.node.provenance,
                        'Factored nested displayed subject compiled to the ' +
                            'wrong outer target family'
                    );
                }
                return compilation;
            }
            case 'typed-nested-displayed-application':
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    term.node.provenance,
                    'A nested displayed application must be eliminated by ' +
                        'its enclosing exact-eta abstraction'
                );
            case 'typed-cell-composition':
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    term.node.provenance,
                    'Typed cell composition lowers only inside the ' +
                        'reviewed displayed-transfor abstraction'
                );
            case 'typed-application': {
                if (
                    term.node.judgment.target ===
                        'displayed-evaluation-varying-object' ||
                    term.node.judgment.target ===
                        'displayed-evaluation-fixed-object'
                ) {
                    return this.compileDisplayedEvaluationApplication(
                        term,
                        baseOrdinal,
                        baseCategory,
                        wiring,
                        activeOrdinals,
                        nodeProvenance
                    );
                }
                if (
                    term.node.judgment.target !==
                        'indexed-fibre-functor-object' ||
                    term.node.argument[CORE_CATEGORICAL_BOUNDARY] === true
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        term.node.provenance,
                        'The displayed contextual body supports only a ' +
                            'closed displayed functor applied to a compiled ' +
                            'fibre argument'
                    );
                }
                const indexedFunctor = term.node.subject;
                const argument = term.node.argument as
                    InternalCoreCategoricalTerm;
                if (
                    indexedFunctor.node.tag !== 'typed-application' ||
                    indexedFunctor.node.judgment.target !==
                        'displayed-functor-fibre' ||
                    indexedFunctor.node.argument[
                        CORE_CATEGORICAL_BOUNDARY
                    ] === true ||
                    indexedFunctor.type.tag !== 'indexed-functor'
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        term.node.provenance,
                        'Displayed contextual application lost its closed ' +
                            'fibre-functor projection'
                    );
                }
                const baseToken = indexedFunctor.node.argument as
                    InternalCoreCategoricalTerm;
                const displayedFunctor = indexedFunctor.node.subject;
                if (
                    baseToken.node.tag !== 'slot-token' ||
                    baseToken.node.ordinal !== baseOrdinal ||
                    displayedFunctor.type.tag !== 'displayed-functor' ||
                    displayedFunctor.closed === undefined ||
                    usageIntersects(
                        displayedFunctor.usage,
                        activeOrdinals
                    ) ||
                    !kernelExpressionEquals(
                        displayedFunctor.type.baseCategory,
                        baseCategory
                    ) ||
                    !kernelExpressionEquals(
                        displayedFunctor.type.sourceFamily,
                        indexedFunctor.type.sourceFamily
                    ) ||
                    !kernelExpressionEquals(
                        displayedFunctor.type.targetFamily,
                        indexedFunctor.type.targetFamily
                    )
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        term.node.provenance,
                        'Displayed contextual functor subjects must be ' +
                            'closed and share the bracket base'
                    );
                }
                const argumentCompilation =
                    this.compileDisplayedContextual(
                        argument,
                        baseOrdinal,
                        baseCategory,
                        wiring,
                        activeOrdinals,
                        nodeProvenance
                    );
                if (
                    argument.type.tag !== 'indexed-object' ||
                    term.type.tag !== 'indexed-object' ||
                    !kernelExpressionEquals(
                        argumentCompilation.targetFamily,
                        displayedFunctor.type.sourceFamily
                    ) ||
                    !kernelExpressionEquals(
                        term.type.family,
                        displayedFunctor.type.targetFamily
                    )
                ) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        term.node.provenance,
                        'Displayed contextual application has incompatible ' +
                            'source or target families'
                    );
                }
                return this.composeDisplayedCompilations(
                    baseCategory,
                    {
                        term: displayedFunctor.closed.term,
                        sourceFamily:
                            displayedFunctor.type.sourceFamily,
                        targetFamily:
                            displayedFunctor.type.targetFamily,
                        identity: false,
                        structuralPrerequisites: Object.freeze([]),
                        dependentPrerequisites: Object.freeze([])
                    },
                    argumentCompilation,
                    term.node.provenance
                );
            }
            case 'explicit-core-term':
            case 'categorical-abstraction':
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    term.node.provenance,
                    'DISPLAYED-BRACKET-1A supports displayed slots, closed ' +
                        'displayed-functor application, and typed fibre ' +
                        'pairs only'
                );
            default: {
                const exhaustive: never = term.node;
                return exhaustive;
            }
        }
    }

    /**
     * Generic first-order bracket for a finite independent displayed
     * sibling block over one hidden base.
     */
    displayedContextLambda(
        bindings: readonly {
            readonly name: string;
            readonly family: KernelExpression;
        }[],
        baseCategory: KernelExpression,
        targetFamily: KernelExpression,
        bodyBuilder: (
            tokens: readonly CoreCategoricalSlotToken[]
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        kernelAssertScoped(baseCategory);
        kernelAssertScoped(targetFamily);
        const nodeProvenance = this.nodeProvenance(
            'displayed contextual abstraction',
            options.provenance
        );
        if (this.options.displayedContextualAbstraction !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed contextual abstraction requires the reviewed ' +
                    'DISPLAYED-BRACKET-1A capability'
            );
        }
        if (bindings.length === 0) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed contextual abstraction requires at least one ' +
                    'sibling binding'
            );
        }
        const names = new Set<string>();
        for (const binding of bindings) {
            assertSafeIdentifier(
                binding.name,
                'Displayed contextual binder hint'
            );
            kernelAssertScoped(binding.family);
            if (names.has(binding.name)) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Duplicate displayed contextual binder ` +
                        `'${binding.name}'`
                );
            }
            names.add(binding.name);
        }
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (variation !== 'functorial' || dependency !== 'displayed') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed contextual abstraction requires functorial ' +
                    'variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                'Displayed contextual abstraction is covariant'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'DISPLAYED-BRACKET-1A abstracts displayed objects'
            );
        }

        const baseToken = this.slot(
            `${bindings[0].name}ContextBase`,
            baseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const fibreTokens = bindings.map(binding =>
            this.indexedObjectSlot(
                binding.name,
                baseCategory,
                binding.family,
                baseOrdinal,
                nodeProvenance
            )
        );
        const fibreOrdinals = fibreTokens.map(token =>
            token.node.tag === 'slot-token'
                ? token.node.ordinal
                : -1
        );
        const tree = this.displayedFamilyTree(
            bindings.map((binding, index) => ({
                ordinal: fibreOrdinals[index],
                family: binding.family
            })),
            baseCategory,
            nodeProvenance
        );
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        for (const ordinal of fibreOrdinals) {
            this.activeTokenOrdinals.unshift(ordinal);
        }
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(Object.freeze(
                    fibreTokens.map(token =>
                        token as CoreCategoricalSlotToken
                    )
                )),
                nodeProvenance
            );
            const localOrdinals = new Set([
                baseOrdinal,
                ...fibreOrdinals
            ]);
            if (usageIntersects(body.usage, new Set(outerScope))) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'DISPLAYED-BRACKET-1A does not admit an open displayed ' +
                        'functor subject or capture an outer context'
                );
            }
            if (
                body.type.tag !== 'indexed-object' ||
                body.type.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    body.type.family,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed contextual body is not an object of the ' +
                        'requested target family over its hidden base'
                );
            }

            const weakeningSection = bindings.length === 1
                ? this.displayedSectionWeakeningBody(
                    body,
                    fibreOrdinals[0],
                    baseOrdinal,
                    baseCategory,
                    targetFamily
                )
                : undefined;
            let resultExpression: KernelExpression;
            let structuralPrerequisites:
                readonly CoreCategoricalStructuralPrerequisiteId[];
            let dependentPrerequisites:
                readonly CoreCategoricalDependentApplicationPrerequisiteId[];
            if (weakeningSection !== undefined) {
                resultExpression = this.lowerDisplayedSectionWeakening(
                    weakeningSection,
                    baseCategory,
                    tree.family,
                    targetFamily,
                    nodeProvenance
                );
                structuralPrerequisites = Object.freeze([]);
                dependentPrerequisites = Object.freeze([
                    'sigma-projection-pullback',
                    'sigma-pi-uncurrying-proof',
                    'sigma-first-projection',
                    'section-pullback-functor',
                    'constant-displayed-family-object'
                ]);
            } else {
                const wiring = this.displayedProjectionWiring(
                    baseCategory,
                    tree,
                    nodeProvenance
                );
                const compilation = this.compileDisplayedContextual(
                    body,
                    baseOrdinal,
                    baseCategory,
                    wiring,
                    localOrdinals,
                    nodeProvenance
                );
                if (
                    !kernelExpressionEquals(
                        compilation.sourceFamily,
                        tree.family
                    ) ||
                    !kernelExpressionEquals(
                        compilation.targetFamily,
                        targetFamily
                    )
                ) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        nodeProvenance,
                        'Displayed contextual compilation produced the ' +
                            'wrong source or target family'
                    );
                }
                resultExpression = compilation.term;
                structuralPrerequisites =
                    compilation.structuralPrerequisites;
                dependentPrerequisites =
                    mergeDependentPrerequisites(
                        [
                            'sigma-projection-pullback',
                            'sigma-pi-uncurrying-proof'
                        ],
                        compilation.dependentPrerequisites
                    );
            }

            const resultType: CoreType = {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategory(
                    baseCategory,
                    tree.family,
                    targetFamily,
                    nodeProvenance
                ),
                baseCategory,
                sourceFamily: tree.family,
                targetFamily
            };
            const resultNode: TemporaryCategoricalNode = {
                tag: 'explicit-core-term',
                term: resultExpression,
                provenance: nodeProvenance
            };
            let remainingUsage = body.usage;
            for (const ordinal of [
                baseOrdinal,
                ...fibreOrdinals
            ]) {
                remainingUsage = removeUsage(
                    remainingUsage,
                    ordinal
                );
            }
            const closed = deepFreeze({
                term: resultExpression,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: body.closed === undefined
                    ? []
                    : [...body.closed.recovered]
            });
            const provisional = this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                body.abstractions
            );
            const bodyScope = [
                ...[...fibreOrdinals].reverse(),
                baseOrdinal,
                ...outerScope
            ];
            const evidence = deepFreeze({
                rule:
                    'categorical.displayed-context-bracket' as const,
                name: bindings.map(binding => binding.name).join(','),
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: baseCategory,
                bindingNames: bindings.map(binding => binding.name),
                sourceFamilies:
                    bindings.map(binding => binding.family),
                sourceFamily: tree.family,
                targetFamily,
                contextSize: bindings.length,
                contextRelation:
                    'shared-minimal-base-siblings' as const,
                body: this.normalizeNode(body, bodyScope),
                result: this.normalizeNode(provisional, outerScope),
                structuralPrerequisites,
                dependentPrerequisites,
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence],
                false,
                weakeningSection === undefined
                    ? {}
                    : {
                        displayedSectionWeakening: {
                            section: weakeningSection
                        }
                    }
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            for (let index = 0;
                index < fibreOrdinals.length + 1;
                index += 1
            ) {
                this.activeTokenOrdinals.shift();
            }
        }
    }

    /**
     * D-DTTLF-USABILITY-026 arbitrary finite canonical layer fold.
     *
     * Consecutive families over one literal base form a sibling layer. Each
     * following layer must be based on the Sigma total of the preceding
     * layer's left-associated product. Every factor projection is then
     * lifted through all later layers by the existing one-level helper.
     */
    private displayedGenericDependentContextLambda(
        bindings: readonly {
            readonly name: string;
            readonly family: KernelExpression;
            readonly baseCategory: KernelExpression;
        }[],
        contextRootCategory: KernelExpression,
        targetFamily: KernelExpression,
        bodyBuilder: (
            tokens: readonly CoreCategoricalSlotToken[]
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions
    ): CoreCategoricalTerm {
        kernelAssertScoped(contextRootCategory);
        kernelAssertScoped(targetFamily);
        const nodeProvenance = this.nodeProvenance(
            'displayed generic dependent contextual abstraction',
            options.provenance
        );
        if (this.options.displayedGenericTelescope !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Generic displayed telescope abstraction requires the ' +
                    'reviewed DISPLAYED-TELESCOPE-GENERIC-1 capability'
            );
        }
        if (bindings.length < 2) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Generic displayed dependent abstraction requires at ' +
                    'least two bindings in at least two layers'
            );
        }
        const names = new Set<string>();
        for (const binding of bindings) {
            assertSafeIdentifier(
                binding.name,
                'Generic displayed telescope binder hint'
            );
            kernelAssertScoped(binding.family);
            kernelAssertScoped(binding.baseCategory);
            if (names.has(binding.name)) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Duplicate generic displayed telescope binder ` +
                        `'${binding.name}'`
                );
            }
            names.add(binding.name);
        }
        if (!kernelExpressionEquals(
            bindings[0].baseCategory,
            contextRootCategory
        )) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Generic displayed telescope root does not match the first ' +
                    'family base'
            );
        }

        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (variation !== 'functorial' || dependency !== 'displayed') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Generic displayed telescope abstraction requires ' +
                    'functorial variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                'Generic displayed telescope abstraction is covariant'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Generic displayed telescope abstraction binds displayed ' +
                    'objects'
            );
        }

        interface Layer {
            readonly baseCategory: KernelExpression;
            readonly bindingIndices: readonly number[];
            readonly tree: CoreCategoricalDisplayedFamilyTree;
        }
        const layers: Layer[] = [];
        let currentBaseCategory = bindings[0].baseCategory;
        let currentBindingIndices: number[] = [];
        for (let index = 0; index < bindings.length; index += 1) {
            const binding = bindings[index];
            if (kernelExpressionEquals(
                binding.baseCategory,
                currentBaseCategory
            )) {
                currentBindingIndices.push(index);
                continue;
            }
            const tree = this.displayedFamilyTree(
                currentBindingIndices.map(bindingIndex => ({
                    ordinal: bindingIndex,
                    family: bindings[bindingIndex].family
                })),
                currentBaseCategory,
                nodeProvenance
            );
            const expectedNextBase = kernelCall(
                kernelFree(
                    CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                        'sigma-category'
                    ],
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: currentBaseCategory
                    },
                    {
                        plicity: 'explicit',
                        value: tree.family
                    }
                ],
                nodeProvenance
            );
            if (!kernelExpressionEquals(
                binding.baseCategory,
                expectedNextBase
            )) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Displayed binding '${binding.name}' is not based on ` +
                        'the Sigma total of the preceding sibling layer'
                );
            }
            layers.push({
                baseCategory: currentBaseCategory,
                bindingIndices: Object.freeze([
                    ...currentBindingIndices
                ]),
                tree
            });
            currentBaseCategory = binding.baseCategory;
            currentBindingIndices = [index];
        }
        const finalTree = this.displayedFamilyTree(
            currentBindingIndices.map(bindingIndex => ({
                ordinal: bindingIndex,
                family: bindings[bindingIndex].family
            })),
            currentBaseCategory,
            nodeProvenance
        );
        layers.push({
            baseCategory: currentBaseCategory,
            bindingIndices: Object.freeze([
                ...currentBindingIndices
            ]),
            tree: finalTree
        });
        if (layers.length < 2) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'One independent displayed sibling layer belongs to ' +
                    'displayedContextLambda, not the dependent telescope'
            );
        }

        const liftedCompilations = new Map<
            number,
            CoreCategoricalDisplayedContextualCompilation
        >();
        for (
            let layerIndex = 0;
            layerIndex < layers.length;
            layerIndex += 1
        ) {
            const layer = layers[layerIndex];
            const projections = this.displayedProjectionWiring(
                layer.baseCategory,
                layer.tree,
                nodeProvenance
            );
            for (const bindingIndex of layer.bindingIndices) {
                let compilation = projections.get(bindingIndex);
                if (compilation === undefined) {
                    throw new Error(
                        'Generic displayed layer lost a factor projection'
                    );
                }
                let liftBaseCategory = layer.baseCategory;
                for (
                    let nextLayerIndex = layerIndex + 1;
                    nextLayerIndex < layers.length;
                    nextLayerIndex += 1
                ) {
                    const nextLayer = layers[nextLayerIndex];
                    compilation =
                        this.liftDisplayedCompilationThroughNextFamily(
                            liftBaseCategory,
                            compilation,
                            nextLayer.tree.family,
                            nodeProvenance
                        );
                    liftBaseCategory = nextLayer.baseCategory;
                }
                liftedCompilations.set(bindingIndex, compilation);
            }
        }

        const finalLayer = layers[layers.length - 1];
        const finalBaseCategory = finalLayer.baseCategory;
        const sourceFamily = finalLayer.tree.family;
        const baseToken = this.slot(
            `${bindings.map(binding => binding.name).join('')}ContextBase`,
            finalBaseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const fibreTokens = bindings.map((binding, index) => {
            const compilation = liftedCompilations.get(index);
            if (compilation === undefined) {
                throw new Error(
                    'Generic displayed telescope lost a lifted binding'
                );
            }
            return this.indexedObjectSlot(
                binding.name,
                finalBaseCategory,
                compilation.targetFamily,
                baseOrdinal,
                nodeProvenance
            );
        });
        const fibreOrdinals = fibreTokens.map(token =>
            token.node.tag === 'slot-token'
                ? token.node.ordinal
                : -1
        );
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        for (const ordinal of fibreOrdinals) {
            this.activeTokenOrdinals.unshift(ordinal);
        }
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(Object.freeze(
                    fibreTokens.map(token =>
                        token as CoreCategoricalSlotToken
                    )
                )),
                nodeProvenance
            );
            const localOrdinals = new Set([
                baseOrdinal,
                ...fibreOrdinals
            ]);
            if (usageIntersects(body.usage, new Set(outerScope))) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'Generic displayed telescope abstraction does not ' +
                        'capture an outer context'
                );
            }
            if (
                body.type.tag !== 'indexed-object' ||
                body.type.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    finalBaseCategory
                ) ||
                !kernelExpressionEquals(
                    body.type.family,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Generic displayed telescope body is not an object of ' +
                        'the target family over the final layer base'
                );
            }

            const wiring: CoreCategoricalDisplayedWiring =
                new Map(fibreOrdinals.map((ordinal, index) => {
                    const compilation = liftedCompilations.get(index);
                    if (compilation === undefined) {
                        throw new Error(
                            'Generic displayed telescope wiring lost a ' +
                                'binding'
                        );
                    }
                    return [ordinal, compilation] as const;
                }));
            const compilation = this.compileDisplayedContextual(
                body,
                baseOrdinal,
                finalBaseCategory,
                wiring,
                localOrdinals,
                nodeProvenance
            );
            if (
                !kernelExpressionEquals(
                    compilation.sourceFamily,
                    sourceFamily
                ) ||
                !kernelExpressionEquals(
                    compilation.targetFamily,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Generic displayed telescope compilation produced the ' +
                        'wrong source or target family'
                );
            }

            const resultExpression = compilation.term;
            const resultType: CoreType = {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategory(
                    finalBaseCategory,
                    sourceFamily,
                    targetFamily,
                    nodeProvenance
                ),
                baseCategory: finalBaseCategory,
                sourceFamily,
                targetFamily
            };
            const resultNode: TemporaryCategoricalNode = {
                tag: 'explicit-core-term',
                term: resultExpression,
                provenance: nodeProvenance
            };
            let remainingUsage = body.usage;
            for (const ordinal of [
                baseOrdinal,
                ...fibreOrdinals
            ]) {
                remainingUsage = removeUsage(
                    remainingUsage,
                    ordinal
                );
            }
            const closed = deepFreeze({
                term: resultExpression,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: body.closed === undefined
                    ? []
                    : [...body.closed.recovered]
            });
            const provisional = this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                body.abstractions
            );
            const bodyScope = [
                ...[...fibreOrdinals].reverse(),
                baseOrdinal,
                ...outerScope
            ];
            const liftedBindingFamilies = bindings.map(
                (_binding, index) => {
                    const lifted = liftedCompilations.get(index);
                    if (lifted === undefined) {
                        throw new Error(
                            'Generic displayed evidence lost a binding'
                        );
                    }
                    return lifted.targetFamily;
                }
            );
            const evidence = deepFreeze({
                rule: (
                    'categorical.displayed-generic-dependent-context-bracket'
                ) as const,
                name:
                    bindings.map(binding => binding.name).join(','),
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: finalBaseCategory,
                bindingNames:
                    bindings.map(binding => binding.name),
                sourceFamilies:
                    bindings.map(binding => binding.family),
                liftedBindingFamilies,
                sourceFamily,
                targetFamily,
                contextRootCategory,
                finalBaseCategory,
                layers: layers.map((layer, layerIndex) => ({
                    layerIndex,
                    baseCategory: layer.baseCategory,
                    bindingNames: layer.bindingIndices.map(
                        index => bindings[index].name
                    ),
                    sourceFamilies: layer.bindingIndices.map(
                        index => bindings[index].family
                    ),
                    sourceFamily: layer.tree.family
                })),
                contextSize: bindings.length,
                contextRelation: (
                    'arbitrary-finite-canonical-layer-fold'
                ) as const,
                body: this.normalizeNode(body, bodyScope),
                result: this.normalizeNode(provisional, outerScope),
                structuralPrerequisites:
                    compilation.structuralPrerequisites,
                dependentPrerequisites:
                    compilation.dependentPrerequisites,
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence]
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            for (
                let index = 0;
                index < fibreOrdinals.length + 1;
                index += 1
            ) {
                this.activeTokenOrdinals.shift();
            }
        }
    }

    /**
     * Frozen DISPLAYED-CHAIN-2A stress:
     *
     *   k : K;
     *   a : A[k];
     *   b : B[(k,a)], c : C[(k,a)];
     *   d : D[((k,a),(b,c))].
     *
     * B and C are grouped by the already transparent displayed product P.
     * The generic one-level lifting helper then carries the a, b, and c
     * projections through D. The body still uses the same recursive typed
     * contextual compiler as every prior displayed bracket.
     */
    private displayedMixedDependentContextLambda(
        bindings: readonly {
            readonly name: string;
            readonly family: KernelExpression;
        }[],
        contextRootCategory: KernelExpression,
        targetFamily: KernelExpression,
        bodyBuilder: (
            tokens: readonly CoreCategoricalSlotToken[]
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions
    ): CoreCategoricalTerm {
        kernelAssertScoped(contextRootCategory);
        kernelAssertScoped(targetFamily);
        const nodeProvenance = this.nodeProvenance(
            'displayed mixed dependent contextual abstraction',
            options.provenance
        );
        if (
            this.options
                .displayedDependentContextualAbstraction !== true
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed mixed dependent contextual abstraction requires ' +
                    'the reviewed DISPLAYED-CHAIN-2A capability'
            );
        }
        if (bindings.length !== 4) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'DISPLAYED-CHAIN-2A accepts exactly a prefix, two ' +
                    'independent middle siblings, and one deepest binding'
            );
        }
        const [
            prefixBinding,
            leftBinding,
            rightBinding,
            deepestBinding
        ] = bindings;
        const names = new Set<string>();
        for (const binding of bindings) {
            assertSafeIdentifier(
                binding.name,
                'Displayed mixed dependent binder hint'
            );
            kernelAssertScoped(binding.family);
            if (names.has(binding.name)) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Duplicate displayed mixed dependent binder ` +
                        `'${binding.name}'`
                );
            }
            names.add(binding.name);
        }

        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (variation !== 'functorial' || dependency !== 'displayed') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed mixed dependent contextual abstraction requires ' +
                    'functorial variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                'Displayed mixed dependent contextual abstraction is ' +
                    'covariant'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'DISPLAYED-CHAIN-2A abstracts displayed objects'
            );
        }

        const firstTotalBaseCategory = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: contextRootCategory
                },
                {
                    plicity: 'explicit',
                    value: prefixBinding.family
                }
            ],
            nodeProvenance
        );
        const groupedMiddleFamily = this.displayedProductFamily(
            firstTotalBaseCategory,
            leftBinding.family,
            rightBinding.family,
            nodeProvenance
        );
        const totalBaseCategory = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: firstTotalBaseCategory
                },
                {
                    plicity: 'explicit',
                    value: groupedMiddleFamily
                }
            ],
            nodeProvenance
        );

        const prefixAtMiddle =
            this.liftDisplayedCompilationThroughNextFamily(
                contextRootCategory,
                this.displayedIdentityCompilation(
                    contextRootCategory,
                    prefixBinding.family,
                    nodeProvenance
                ),
                groupedMiddleFamily,
                nodeProvenance
            );
        const prefixAtDeepest =
            this.liftDisplayedCompilationThroughNextFamily(
                firstTotalBaseCategory,
                prefixAtMiddle,
                deepestBinding.family,
                nodeProvenance
            );
        const leftAtDeepest =
            this.liftDisplayedCompilationThroughNextFamily(
                firstTotalBaseCategory,
                this.displayedProjectionCompilation(
                    'left',
                    firstTotalBaseCategory,
                    leftBinding.family,
                    rightBinding.family,
                    nodeProvenance
                ),
                deepestBinding.family,
                nodeProvenance
            );
        const rightAtDeepest =
            this.liftDisplayedCompilationThroughNextFamily(
                firstTotalBaseCategory,
                this.displayedProjectionCompilation(
                    'right',
                    firstTotalBaseCategory,
                    leftBinding.family,
                    rightBinding.family,
                    nodeProvenance
                ),
                deepestBinding.family,
                nodeProvenance
            );
        const deepestIdentity = this.displayedIdentityCompilation(
            totalBaseCategory,
            deepestBinding.family,
            nodeProvenance
        );
        const liftedBindingFamilies = [
            prefixAtDeepest.targetFamily,
            leftAtDeepest.targetFamily,
            rightAtDeepest.targetFamily,
            deepestBinding.family
        ] as const;

        const baseToken = this.slot(
            `${bindings.map(binding => binding.name).join('')}ContextBase`,
            totalBaseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const fibreTokens = bindings.map((binding, index) =>
            this.indexedObjectSlot(
                binding.name,
                totalBaseCategory,
                liftedBindingFamilies[index],
                baseOrdinal,
                nodeProvenance
            )
        );
        const fibreOrdinals = fibreTokens.map(token =>
            token.node.tag === 'slot-token'
                ? token.node.ordinal
                : -1
        );
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        for (const ordinal of fibreOrdinals) {
            this.activeTokenOrdinals.unshift(ordinal);
        }
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(Object.freeze(
                    fibreTokens.map(token =>
                        token as CoreCategoricalSlotToken
                    )
                )),
                nodeProvenance
            );
            const localOrdinals = new Set([
                baseOrdinal,
                ...fibreOrdinals
            ]);
            if (usageIntersects(body.usage, new Set(outerScope))) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'DISPLAYED-CHAIN-2A does not capture an outer context'
                );
            }
            if (
                body.type.tag !== 'indexed-object' ||
                body.type.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    totalBaseCategory
                ) ||
                !kernelExpressionEquals(
                    body.type.family,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed mixed dependent contextual body is not an ' +
                        'object of the target family over Sigma(P)'
                );
            }

            const wiring:
            CoreCategoricalDisplayedWiring = new Map([
                [fibreOrdinals[0], prefixAtDeepest],
                [fibreOrdinals[1], leftAtDeepest],
                [fibreOrdinals[2], rightAtDeepest],
                [fibreOrdinals[3], deepestIdentity]
            ]);
            const compilation = this.compileDisplayedContextual(
                body,
                baseOrdinal,
                totalBaseCategory,
                wiring,
                localOrdinals,
                nodeProvenance
            );
            if (
                !kernelExpressionEquals(
                    compilation.sourceFamily,
                    deepestBinding.family
                ) ||
                !kernelExpressionEquals(
                    compilation.targetFamily,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed mixed dependent contextual compilation ' +
                        'produced the wrong source or target family'
                );
            }

            const resultExpression = compilation.term;
            const resultType: CoreType = {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategory(
                    totalBaseCategory,
                    deepestBinding.family,
                    targetFamily,
                    nodeProvenance
                ),
                baseCategory: totalBaseCategory,
                sourceFamily: deepestBinding.family,
                targetFamily
            };
            const resultNode: TemporaryCategoricalNode = {
                tag: 'explicit-core-term',
                term: resultExpression,
                provenance: nodeProvenance
            };
            let remainingUsage = body.usage;
            for (const ordinal of [
                baseOrdinal,
                ...fibreOrdinals
            ]) {
                remainingUsage = removeUsage(
                    remainingUsage,
                    ordinal
                );
            }
            const closed = deepFreeze({
                term: resultExpression,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: body.closed === undefined
                    ? []
                    : [...body.closed.recovered]
            });
            const provisional = this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                body.abstractions
            );
            const bodyScope = [
                ...[...fibreOrdinals].reverse(),
                baseOrdinal,
                ...outerScope
            ];
            const evidence = deepFreeze({
                rule: (
                    'categorical.displayed-mixed-dependent-context-bracket'
                ) as const,
                name:
                    bindings.map(binding => binding.name).join(','),
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: totalBaseCategory,
                bindingNames: [
                    prefixBinding.name,
                    leftBinding.name,
                    rightBinding.name,
                    deepestBinding.name
                ] as const,
                sourceFamilies: [
                    prefixBinding.family,
                    leftBinding.family,
                    rightBinding.family,
                    deepestBinding.family
                ] as const,
                liftedBindingFamilies,
                sourceFamily: deepestBinding.family,
                targetFamily,
                contextRootCategory,
                firstTotalBaseCategory,
                groupedMiddleFamily,
                totalBaseCategory,
                contextSize: 4 as const,
                siblingGroup: [
                    leftBinding.name,
                    rightBinding.name
                ] as const,
                contextRelation: (
                    'two-dependency-transitions-with-middle-siblings'
                ) as const,
                body: this.normalizeNode(body, bodyScope),
                result: this.normalizeNode(provisional, outerScope),
                structuralPrerequisites:
                    compilation.structuralPrerequisites,
                dependentPrerequisites:
                    compilation.dependentPrerequisites,
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence]
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            for (let index = 0;
                index < fibreOrdinals.length + 1;
                index += 1
            ) {
                this.activeTokenOrdinals.shift();
            }
        }
    }

    /**
     * Recursive displayed bracket for exactly one genuine dependency edge:
     *
     *   k : K; a : A[k]; b : B[(k,a)].
     *
     * The result is a direct displayed functor from B over Sigma(A). The
     * immediate variable b uses identity wiring. The outer variable a uses
     * `sigma_functord_sec(id_funcd A)` and the existing section-pullback
     * weakening across B. The body itself is compiled by the same recursive
     * contextual occurrence compiler used for independent siblings.
     */
    displayedDependentContextLambda(
        bindings: readonly {
            readonly name: string;
            readonly family: KernelExpression;
            readonly baseCategory?: KernelExpression;
        }[],
        contextRootCategory: KernelExpression,
        targetFamily: KernelExpression,
        bodyBuilder: (
            tokens: readonly CoreCategoricalSlotToken[]
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        kernelAssertScoped(contextRootCategory);
        kernelAssertScoped(targetFamily);
        const nodeProvenance = this.nodeProvenance(
            'displayed dependent contextual abstraction',
            options.provenance
        );
        if (
            this.options
                .displayedDependentContextualAbstraction !== true
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Displayed dependent contextual abstraction requires the ' +
                'reviewed DISPLAYED-CHAIN-1A capability'
            );
        }
        if (this.options.displayedGenericTelescope === true) {
            const genericBindings = bindings.map(binding => {
                if (binding.baseCategory === undefined) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        nodeProvenance,
                        'Generic displayed telescope lowering requires the ' +
                            `literal base of '${binding.name}'`
                    );
                }
                return {
                    name: binding.name,
                    family: binding.family,
                    baseCategory: binding.baseCategory
                };
            });
            return this.displayedGenericDependentContextLambda(
                genericBindings,
                contextRootCategory,
                targetFamily,
                bodyBuilder,
                options
            );
        }
        if (bindings.length === 4) {
            return this.displayedMixedDependentContextLambda(
                bindings,
                contextRootCategory,
                targetFamily,
                bodyBuilder,
                options
            );
        }
        if (bindings.length !== 2) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'DISPLAYED-CHAIN-1A accepts exactly one prefix family and ' +
                    'one genuinely dependent next family'
            );
        }
        const [prefixBinding, nextBinding] = bindings;
        assertSafeIdentifier(
            prefixBinding.name,
            'Displayed dependent prefix binder hint'
        );
        assertSafeIdentifier(
            nextBinding.name,
            'Displayed dependent next binder hint'
        );
        kernelAssertScoped(prefixBinding.family);
        kernelAssertScoped(nextBinding.family);
        if (prefixBinding.name === nextBinding.name) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Duplicate displayed dependent binder ` +
                    `'${prefixBinding.name}'`
            );
        }

        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (variation !== 'functorial' || dependency !== 'displayed') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Displayed dependent contextual abstraction requires ' +
                    'functorial variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                'Displayed dependent contextual abstraction is covariant'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'DISPLAYED-CHAIN-1A abstracts displayed objects'
            );
        }

        const totalBaseCategory = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: contextRootCategory
                },
                {
                    plicity: 'explicit',
                    value: prefixBinding.family
                }
            ],
            nodeProvenance
        );
        const prefixProjection = kernelCall(
            kernelFree(
                CORE_DIRECTED_1B_PRIMITIVE_NAMES[
                    'sigma-first-projection'
                ],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: contextRootCategory
                },
                {
                    plicity: 'explicit',
                    value: prefixBinding.family
                }
            ],
            nodeProvenance
        );
        const liftedPrefixFamily = kernelApplication(
            'displayed-pullback',
            [
                { value: totalBaseCategory },
                { value: contextRootCategory },
                { value: prefixBinding.family },
                { value: prefixProjection }
            ],
            nodeProvenance
        );

        const baseToken = this.slot(
            `${prefixBinding.name}${nextBinding.name}ContextBase`,
            totalBaseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const prefixToken = this.indexedObjectSlot(
            prefixBinding.name,
            totalBaseCategory,
            liftedPrefixFamily,
            baseOrdinal,
            nodeProvenance
        );
        const nextToken = this.indexedObjectSlot(
            nextBinding.name,
            totalBaseCategory,
            nextBinding.family,
            baseOrdinal,
            nodeProvenance
        );
        const prefixOrdinal =
            prefixToken.node.tag === 'slot-token'
                ? prefixToken.node.ordinal
                : -1;
        const nextOrdinal =
            nextToken.node.tag === 'slot-token'
                ? nextToken.node.ordinal
                : -1;
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        this.activeTokenOrdinals.unshift(prefixOrdinal);
        this.activeTokenOrdinals.unshift(nextOrdinal);
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(Object.freeze([
                    prefixToken as CoreCategoricalSlotToken,
                    nextToken as CoreCategoricalSlotToken
                ])),
                nodeProvenance
            );
            const localOrdinals = new Set([
                baseOrdinal,
                prefixOrdinal,
                nextOrdinal
            ]);
            if (usageIntersects(body.usage, new Set(outerScope))) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'DISPLAYED-CHAIN-1A does not capture an outer context'
                );
            }
            if (
                body.type.tag !== 'indexed-object' ||
                body.type.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    totalBaseCategory
                ) ||
                !kernelExpressionEquals(
                    body.type.family,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed dependent contextual body is not an object ' +
                        'of the target family over Sigma(A)'
                );
            }

            const prefixIdentity =
                this.displayedIdentityCompilation(
                    contextRootCategory,
                    prefixBinding.family,
                    nodeProvenance
                );
            const prefixSection = kernelCall(
                kernelFree(
                    coreCategoricalDisplayedChainCoreName(
                        'sigmaFunctordSection'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: contextRootCategory
                    },
                    {
                        plicity: 'implicit',
                        value: prefixBinding.family
                    },
                    {
                        plicity: 'implicit',
                        value: prefixBinding.family
                    },
                    {
                        plicity: 'explicit',
                        value: prefixIdentity.term
                    }
                ],
                nodeProvenance
            );
            const prefixUnderNext:
            CoreCategoricalDisplayedContextualCompilation = {
                term: this.lowerDisplayedSectionWeakeningTerm(
                    prefixSection,
                    totalBaseCategory,
                    nextBinding.family,
                    liftedPrefixFamily,
                    nodeProvenance
                ),
                sourceFamily: nextBinding.family,
                targetFamily: liftedPrefixFamily,
                identity: false,
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites:
                    mergeDependentPrerequisites(
                        prefixIdentity.dependentPrerequisites,
                        [
                            'sigma-functord-section',
                            'sigma-projection-pullback',
                            'sigma-pi-uncurrying-proof',
                            'sigma-first-projection',
                            'section-pullback-functor',
                            'constant-displayed-family-object'
                        ]
                    )
            };
            const wiring:
            CoreCategoricalDisplayedWiring = new Map([
                [prefixOrdinal, prefixUnderNext],
                [
                    nextOrdinal,
                    this.displayedIdentityCompilation(
                        totalBaseCategory,
                        nextBinding.family,
                        nodeProvenance
                    )
                ]
            ]);
            const compilation = this.compileDisplayedContextual(
                body,
                baseOrdinal,
                totalBaseCategory,
                wiring,
                localOrdinals,
                nodeProvenance
            );
            if (
                !kernelExpressionEquals(
                    compilation.sourceFamily,
                    nextBinding.family
                ) ||
                !kernelExpressionEquals(
                    compilation.targetFamily,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Displayed dependent contextual compilation produced ' +
                        'the wrong source or target family'
                );
            }

            const resultExpression = compilation.term;
            const resultType: CoreType = {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategory(
                    totalBaseCategory,
                    nextBinding.family,
                    targetFamily,
                    nodeProvenance
                ),
                baseCategory: totalBaseCategory,
                sourceFamily: nextBinding.family,
                targetFamily
            };
            const resultNode: TemporaryCategoricalNode = {
                tag: 'explicit-core-term',
                term: resultExpression,
                provenance: nodeProvenance
            };
            let remainingUsage = body.usage;
            for (const ordinal of [
                baseOrdinal,
                prefixOrdinal,
                nextOrdinal
            ]) {
                remainingUsage = removeUsage(
                    remainingUsage,
                    ordinal
                );
            }
            const closed = deepFreeze({
                term: resultExpression,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: body.closed === undefined
                    ? []
                    : [...body.closed.recovered]
            });
            const provisional = this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                body.abstractions
            );
            const bodyScope = [
                nextOrdinal,
                prefixOrdinal,
                baseOrdinal,
                ...outerScope
            ];
            const evidence = deepFreeze({
                rule: (
                    'categorical.displayed-dependent-context-bracket'
                ) as const,
                name:
                    `${prefixBinding.name},${nextBinding.name}`,
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: totalBaseCategory,
                bindingNames: [
                    prefixBinding.name,
                    nextBinding.name
                ] as const,
                sourceFamilies: [
                    prefixBinding.family,
                    nextBinding.family
                ] as const,
                sourceFamily: nextBinding.family,
                targetFamily,
                contextRootCategory,
                totalBaseCategory,
                liftedPrefixFamily,
                contextSize: 2 as const,
                contextRelation:
                    'one-genuine-dependency-edge' as const,
                body: this.normalizeNode(body, bodyScope),
                result: this.normalizeNode(provisional, outerScope),
                structuralPrerequisites:
                    compilation.structuralPrerequisites,
                dependentPrerequisites:
                    compilation.dependentPrerequisites,
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence]
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            this.activeTokenOrdinals.shift();
            this.activeTokenOrdinals.shift();
            this.activeTokenOrdinals.shift();
        }
    }

    /**
     * Exact recursive eta for one already-coherent inner displayed functor.
     *
     * The subject is an open object of
     * `Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)` at an active outer
     * index. The callback sees one fibre object over a fresh hidden `z : Z`.
     * Only `subject(e)` is accepted; the result factors back to `subject`.
     */
    nestedDisplayedFunctorLambda(
        name: string,
        coherentSubjectValue: CoreCategoricalTerm,
        bodyBuilder: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        assertSafeIdentifier(name, 'Nested displayed-functor binder hint');
        const nodeProvenance = this.nodeProvenance(
            `nested displayed-functor abstraction ${name}`,
            options.provenance
        );
        if (this.options.mixedNestedFactorization !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Nested displayed-functor eta requires the reviewed ' +
                    'MIXED-NEST-1A capability'
            );
        }
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (
            variation !== 'functorial' ||
            dependency !== 'displayed'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Nested displayed-functor binder '${name}' requires ` +
                    'functorial variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                `Nested displayed-functor binder '${name}' derives its ` +
                    'negative source from Hom_catd'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'MIXED-NEST-1A abstracts one inner displayed object'
            );
        }

        const subject = this.requireTerm(
            coherentSubjectValue,
            nodeProvenance
        );
        if (
            subject.type.tag !== 'indexed-object' ||
            subject.closed !== undefined ||
            !this.activeTokenOrdinals.includes(
                subject.type.indexOrdinal
            ) ||
            !this.activeDisplayedBases.has(
                subject.type.indexOrdinal
            )
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Nested displayed-functor eta requires an open indexed ' +
                    'object at the active outer displayed base'
            );
        }
        const shape = this.mixedNestedDisplayedFunctorShape(
            subject.type.family,
            subject.type.baseCategory
        );
        if (shape === undefined) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Nested displayed-functor eta requires exactly ' +
                    'Hom_catd(Const_catd K (Catd_cat Z),Ebar,Dbar)'
            );
        }

        const baseToken = this.slot(
            `${name}NestedBase`,
            shape.innerBaseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const fibreToken = this.nestedIndexedObjectSlot(
            name,
            shape,
            subject.type.indexOrdinal,
            baseOrdinal,
            'source',
            nodeProvenance
        );
        const fibreOrdinal =
            fibreToken.node.tag === 'slot-token'
                ? fibreToken.node.ordinal
                : -1;
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        this.activeTokenOrdinals.unshift(fibreOrdinal);
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(
                    fibreToken as CoreCategoricalSlotToken
                ),
                nodeProvenance
            );
            if (
                body.node.tag !==
                    'typed-nested-displayed-application' ||
                body.node.subject !== subject ||
                body.node.base !== baseToken ||
                body.node.argument !== fibreToken ||
                body.type.tag !== 'nested-indexed-object' ||
                body.type.endpoint !== 'target' ||
                body.type.outerIndexOrdinal !==
                    subject.type.indexOrdinal ||
                body.type.innerIndexOrdinal !== baseOrdinal ||
                usageCount(body.usage, baseOrdinal) !== 1 ||
                usageCount(body.usage, fibreOrdinal) !== 1
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'The first nested displayed binder accepts only exact ' +
                        'eta of the same already-coherent inner subject'
                );
            }
            const remainingUsage = removeUsage(
                removeUsage(body.usage, fibreOrdinal),
                baseOrdinal
            );
            if (
                remainingUsage.length !== subject.usage.length ||
                remainingUsage.some(([ordinal, count]) =>
                    usageCount(subject.usage, ordinal) !== count
                )
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'Nested displayed eta changed outer contextual usage'
                );
            }
            const resultNode: TemporaryCategoricalNode = {
                tag: 'nested-displayed-abstraction',
                baseOrdinal,
                fibreOrdinal,
                name,
                innerBaseCategory: shape.innerBaseCategory,
                subject,
                body,
                provenance: nodeProvenance
            };
            const provisional = this.makeTerm(
                resultNode,
                subject.type,
                remainingUsage,
                undefined,
                body.abstractions
            );
            const evidence = deepFreeze({
                rule:
                    'categorical.mixed-nested-displayed-eta' as const,
                name,
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: shape.innerBaseCategory,
                outerBaseCategory: shape.outerBaseCategory,
                innerBaseCategory: shape.innerBaseCategory,
                classifierFamily: shape.classifierFamily,
                sourceSection: shape.sourceSection,
                targetSection: shape.targetSection,
                body: this.normalizeNode(
                    body,
                    [
                        fibreOrdinal,
                        baseOrdinal,
                        ...outerScope
                    ]
                ),
                result: this.normalizeNode(
                    provisional,
                    outerScope
                ),
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites: Object.freeze([]),
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                subject.type,
                remainingUsage,
                undefined,
                [...body.abstractions, evidence]
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            this.activeTokenOrdinals.shift();
            this.activeTokenOrdinals.shift();
        }
    }

    /**
     * Direct recursive introduction for
     *
     *   lambda^n k. lambda^f c. lambda^f a. body
     *     : Functord C (Functor_catd A B).
     *
     * The callback is accepted only when `body` is generated by the exact
     * recursive grammar
     * `source ::= a | L(source)`,
     * `body ::= c(source) | F[c](source) | H[c] | G(body) | (body, body)`.
     * Bound-outer identity
     * returns `id_funcd(Functor_catd(A,B))`; eta returns `F` directly;
     * `H[c]` composes direct displayed weakening after `H`;
     * source and target chains use the two internal actions of
     * `Functor_catd(-,-)` plus generic composition. Pairs use the existing
     * internal displayed pairing and product distributor. Contextual curry is
     * not consulted or emitted.
     */
    mixedDisplayedFunctorLambda(
        outerName: string,
        innerName: string,
        baseCategory: KernelExpression,
        outerSourceFamily: KernelExpression,
        innerSourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        bodyBuilder: (
            outerToken: CoreCategoricalSlotToken,
            innerToken: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        assertSafeIdentifier(
            outerName,
            'Direct mixed outer binder hint'
        );
        assertSafeIdentifier(
            innerName,
            'Direct mixed inner binder hint'
        );
        kernelAssertScoped(baseCategory);
        kernelAssertScoped(outerSourceFamily);
        kernelAssertScoped(innerSourceFamily);
        kernelAssertScoped(targetFamily);
        const nodeProvenance = this.nodeProvenance(
            `direct mixed abstraction ${outerName}, ${innerName}`,
            options.provenance
        );
        if (this.options.directMixedIntroduction === undefined) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Direct mixed abstraction requires the reviewed ' +
                    'DIRECT-MIXED-INTRODUCTION-1D capability'
            );
        }
        if (outerName === innerName) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Direct mixed outer and inner binders require distinct hints'
            );
        }
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (
            variation !== 'functorial' ||
            dependency !== 'displayed'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Direct mixed fibre binders require functorial variation ' +
                    'and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                'The direct mixed target-recursion slice is covariant'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'Direct mixed introduction abstracts object-level inputs'
            );
        }

        const baseName = `${outerName}Base`;
        const baseToken = this.slot(
            baseName,
            baseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const outerToken = this.indexedObjectSlot(
            outerName,
            baseCategory,
            outerSourceFamily,
            baseOrdinal,
            nodeProvenance,
            true
        );
        const outerOrdinal = outerToken.node.tag === 'slot-token'
            ? outerToken.node.ordinal
            : -1;
        const innerToken = this.indexedObjectSlot(
            innerName,
            baseCategory,
            innerSourceFamily,
            baseOrdinal,
            nodeProvenance,
            false,
            this.oppositeCategory(baseCategory, nodeProvenance)
        );
        const innerOrdinal = innerToken.node.tag === 'slot-token'
            ? innerToken.node.ordinal
            : -1;
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        this.activeTokenOrdinals.unshift(outerOrdinal);
        this.activeTokenOrdinals.unshift(innerOrdinal);
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(
                    outerToken as CoreCategoricalSlotToken,
                    innerToken as CoreCategoricalSlotToken
                ),
                nodeProvenance
            );
            const bodyObject = indexedObjectView(body.type);
            if (
                bodyObject === undefined ||
                bodyObject.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    bodyObject.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    bodyObject.familyBaseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    bodyObject.family,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Direct mixed body is not an object of the requested ' +
                        'target family over the shared hidden base'
                );
            }
            const factorization = this.directMixedFactorization(
                body,
                outerOrdinal,
                innerOrdinal,
                baseOrdinal,
                baseCategory,
                outerSourceFamily,
                innerSourceFamily
            );
            if (
                factorization === undefined ||
                !kernelExpressionEquals(
                    factorization.targetFamily,
                    targetFamily
                ) ||
                body.usage.some(([ordinal]) =>
                    ordinal !== outerOrdinal &&
                    ordinal !== innerOrdinal &&
                    ordinal !== baseOrdinal
                )
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'The direct mixed binder accepts only recursive pairs, ' +
                        'finite closed source chains inside c(source) or ' +
                        'F[c](source), direct outer-only H[c] leaves, and ' +
                        'finite closed target maps'
                );
            }
            const compiledFactorization =
                this.compileDirectMixedFactorization(
                    factorization,
                    baseCategory,
                    outerSourceFamily,
                    innerSourceFamily,
                    nodeProvenance
                );
            if (
                usageCount(body.usage, outerOrdinal) !==
                    compiledFactorization.outerUsageCount ||
                usageCount(body.usage, innerOrdinal) !==
                    compiledFactorization.innerUsageCount ||
                usageCount(body.usage, baseOrdinal) !==
                    compiledFactorization.baseUsageCount
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'Direct mixed recursive occurrence counts do not match ' +
                        'the internally factorized leaf/action tree'
                );
            }
            const resultFamily =
                compiledFactorization.compilation.targetFamily;
            if (!kernelExpressionEquals(
                resultFamily,
                this.mixedFunctorFamily(
                    baseCategory,
                    innerSourceFamily,
                    targetFamily,
                    nodeProvenance
                )
            )) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    'Direct mixed recursive compiler produced the wrong ' +
                        'internally classified target family'
                );
            }
            const resultExpression =
                compiledFactorization.compilation.term;

            const resultType: CoreType = {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategory(
                    baseCategory,
                    outerSourceFamily,
                    resultFamily,
                    nodeProvenance
                ),
                baseCategory,
                sourceFamily: outerSourceFamily,
                targetFamily: resultFamily
            };
            const resultNode: TemporaryCategoricalNode = {
                tag: 'explicit-core-term',
                term: resultExpression,
                provenance: nodeProvenance
            };
            const remainingUsage = removeUsage(
                removeUsage(
                    removeUsage(body.usage, innerOrdinal),
                    outerOrdinal
                ),
                baseOrdinal
            );
            const recovered = compiledFactorization.recovered;
            const closed = deepFreeze({
                term: resultExpression,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered
            });
            const provisional = this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                body.abstractions
            );
            const evidence = deepFreeze({
                rule:
                    'categorical.direct-mixed-displayed-functor' as const,
                name: outerName,
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: baseCategory,
                bindingNames: [
                    baseName,
                    outerName,
                    innerName
                ] as const,
                bindingModes: [
                    'natural',
                    'functorial',
                    'functorial'
                ] as const,
                outerSourceFamily,
                innerSourceFamily,
                rootSourceFamily:
                    compiledFactorization.rootSourceFamilies[0] ??
                        innerSourceFamily,
                rootSourceFamilies:
                    compiledFactorization.rootSourceFamilies,
                initialTargetFamily:
                    compiledFactorization.initialTargetFamilies[0] ??
                        targetFamily,
                initialTargetFamilies:
                    compiledFactorization.initialTargetFamilies,
                targetFamily,
                resultFamily,
                rootKind: compiledFactorization.leafCount === 1
                    ? compiledFactorization.rootKinds[0]
                    : 'recursive-pair' as const,
                leafCount: compiledFactorization.leafCount,
                outerUsageCount:
                    compiledFactorization.outerUsageCount,
                innerUsageCount:
                    compiledFactorization.innerUsageCount,
                sourceChainLength:
                    compiledFactorization.sourceChainLength,
                targetChainLength:
                    compiledFactorization.targetChainLength,
                pairNodeCount:
                    compiledFactorization.pairNodeCount,
                pairDepth: compiledFactorization.pairDepth,
                contextSize: 3 as const,
                contextRelation:
                    'natural-base-then-two-functorial-fibre-binders' as const,
                body: this.normalizeNode(
                    body,
                    [
                        innerOrdinal,
                        outerOrdinal,
                        baseOrdinal,
                        ...outerScope
                    ]
                ),
                result: this.normalizeNode(
                    provisional,
                    outerScope
                ),
                structuralPrerequisites:
                    compiledFactorization.compilation
                        .structuralPrerequisites,
                dependentPrerequisites:
                    compiledFactorization.compilation
                        .dependentPrerequisites,
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence]
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            this.activeTokenOrdinals.shift();
            this.activeTokenOrdinals.shift();
            this.activeTokenOrdinals.shift();
        }
    }

    /**
     * First direct displayed-functor abstraction.
     *
     * The callback sees only `a : E[k]`; the hidden base `k` is recovered
     * from the indexed classifier whenever a displayed functor is applied to
     * `a`. The recorded body remains the explicit nested `FF[k](a)` IR.
     */
    displayedFunctorLambda(
        name: string,
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        bodyBuilder: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        assertSafeIdentifier(name, 'Displayed-functor binder hint');
        kernelAssertScoped(baseCategory);
        kernelAssertScoped(sourceFamily);
        kernelAssertScoped(targetFamily);
        const nodeProvenance = this.nodeProvenance(
            `displayed-functor abstraction ${name}`,
            options.provenance
        );
        if (this.options.displayedFunctorAbstraction !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Direct displayed-functor abstraction requires the ' +
                'FIBRED-BINDER-1 capability'
            );
        }
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (
            variation !== 'functorial' ||
            dependency !== 'displayed'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Displayed-functor binder '${name}' requires functorial ` +
                'variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                `Displayed-functor binder '${name}' is covariant`
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'FIBRED-BINDER-1 abstracts one displayed object-level input'
            );
        }

        const baseToken = this.slot(
            `${name}Base`,
            baseCategory,
            nodeProvenance
        );
        const baseOrdinal = baseToken.node.tag === 'slot-token'
            ? baseToken.node.ordinal
            : -1;
        const fibreToken = this.indexedObjectSlot(
            name,
            baseCategory,
            sourceFamily,
            baseOrdinal,
            nodeProvenance
        );
        const fibreOrdinal =
            fibreToken.node.tag === 'slot-token'
                ? fibreToken.node.ordinal
                : -1;
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(baseOrdinal);
        this.activeTokenOrdinals.unshift(fibreOrdinal);
        this.activeDisplayedBases.set(baseOrdinal, baseToken);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(
                    fibreToken as CoreCategoricalSlotToken
                ),
                nodeProvenance
            );
            if (
                body.type.tag !== 'indexed-object' ||
                body.type.indexOrdinal !== baseOrdinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    body.type.family,
                    targetFamily
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Displayed-functor abstraction '${name}' body is not an ` +
                    'object of the target family over its hidden base'
                );
            }
            const weakeningSection =
                this.displayedSectionWeakeningBody(
                    body,
                    fibreOrdinal,
                    baseOrdinal,
                    baseCategory,
                    targetFamily
                );
            let chain:
                readonly InternalCoreCategoricalTerm[] = [];
            if (weakeningSection === undefined) {
                const candidate = this.directDisplayedFunctorChain(
                    body,
                    fibreOrdinal,
                    baseOrdinal,
                    baseCategory,
                    sourceFamily
                );
                if (
                    candidate === undefined ||
                    usageCount(body.usage, fibreOrdinal) !== 1 ||
                    usageCount(body.usage, baseOrdinal) !==
                        candidate.length
                ) {
                    this.fail(
                        'UNAVAILABLE_DISPLAYED_ACTION',
                        nodeProvenance,
                        'The displayed binder accepts identity, eta, a ' +
                            'finite closed displayed-functor chain, or the ' +
                            'exact qualified section weakening'
                    );
                }
                chain = candidate;
            }

            let rule:
                | 'categorical.displayed-functor-identity'
                | 'categorical.displayed-functor-eta'
                | 'categorical.displayed-functor-composition'
                | 'categorical.displayed-functor-weakening';
            let resultExpression: KernelExpression;
            const prerequisites:
                CoreCategoricalDependentApplicationPrerequisiteId[] = [
                    'sigma-projection-pullback',
                    'sigma-pi-uncurrying-proof'
                ];
            if (weakeningSection !== undefined) {
                rule = 'categorical.displayed-functor-weakening';
                prerequisites.push(
                    'sigma-first-projection',
                    'section-pullback-functor',
                    'constant-displayed-family-object'
                );
                resultExpression =
                    this.lowerDisplayedSectionWeakening(
                        weakeningSection,
                        baseCategory,
                        sourceFamily,
                        targetFamily,
                        nodeProvenance
                    );
            } else if (chain.length === 0) {
                if (
                    !kernelExpressionEquals(
                        sourceFamily,
                        targetFamily
                    )
                ) {
                    this.fail(
                        'CLASSIFIER_ARGUMENT_MISMATCH',
                        nodeProvenance,
                        'Displayed identity body requires identical source ' +
                        'and target families'
                    );
                }
                rule = 'categorical.displayed-functor-identity';
                prerequisites.push('displayed-identity');
                resultExpression = kernelCall(
                    kernelFree(
                        coreCategoricalFibredStructureCoreName(
                            'displayed-identity'
                        ),
                        nodeProvenance
                    ),
                    [
                        {
                            plicity: 'implicit',
                            value: baseCategory
                        },
                        {
                            plicity: 'implicit',
                            value: sourceFamily
                        }
                    ],
                    nodeProvenance
                );
            } else if (chain.length === 1) {
                rule = 'categorical.displayed-functor-eta';
                resultExpression =
                    (chain[0].closed as ElaboratedSurfaceTerm).term;
            } else {
                rule = 'categorical.displayed-functor-composition';
                prerequisites.push(
                    'generic-category-composition',
                    'displayed-hom-classifier-reduction'
                );
                let source = sourceFamily;
                let middle =
                    chain[0].type.tag === 'displayed-functor'
                        ? chain[0].type.targetFamily
                        : sourceFamily;
                resultExpression =
                    (chain[0].closed as ElaboratedSurfaceTerm).term;
                for (const next of chain.slice(1)) {
                    if (
                        next.type.tag !== 'displayed-functor' ||
                        !kernelExpressionEquals(
                            next.type.sourceFamily,
                            middle
                        )
                    ) {
                        this.fail(
                            'CLASSIFIER_ARGUMENT_MISMATCH',
                            nodeProvenance,
                            'Displayed-functor chain has incompatible ' +
                            'adjacent families'
                        );
                    }
                    resultExpression =
                        this.dependentCompositionCall(
                            [
                                {
                                    plicity: 'implicit',
                                    value:
                                        this.displayedCategoryCategory(
                                            baseCategory,
                                            nodeProvenance
                                        )
                                },
                                {
                                    plicity: 'implicit',
                                    value: source
                                },
                                {
                                    plicity: 'implicit',
                                    value: middle
                                },
                                {
                                    plicity: 'implicit',
                                    value:
                                        next.type.targetFamily
                                },
                                {
                                    plicity: 'explicit',
                                    value:
                                        (next.closed as
                                            ElaboratedSurfaceTerm).term
                                },
                                {
                                    plicity: 'explicit',
                                    value: resultExpression
                                }
                            ],
                            nodeProvenance
                        );
                    middle = next.type.targetFamily;
                }
            }

            const resultType: CoreType = {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategory(
                    baseCategory,
                    sourceFamily,
                    targetFamily,
                    nodeProvenance
                ),
                baseCategory,
                sourceFamily,
                targetFamily
            };
            const resultNode: TemporaryCategoricalNode = {
                tag: 'explicit-core-term',
                term: resultExpression,
                provenance: nodeProvenance
            };
            const remainingUsage = removeUsage(
                removeUsage(body.usage, fibreOrdinal),
                baseOrdinal
            );
            const closed = deepFreeze({
                term: resultExpression,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: weakeningSection === undefined
                    ? chain.flatMap(displayed =>
                        displayed.closed === undefined
                            ? []
                            : [...displayed.closed.recovered]
                    )
                    : [...weakeningSection.closed.recovered]
            });
            const provisional = this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                body.abstractions
            );
            const evidence = deepFreeze({
                rule,
                name,
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: baseCategory,
                sourceFamily,
                targetFamily,
                chainLength: chain.length,
                body: this.normalizeNode(
                    body,
                    [
                        fibreOrdinal,
                        baseOrdinal,
                        ...outerScope
                    ]
                ),
                result: this.normalizeNode(
                    provisional,
                    outerScope
                ),
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites:
                    Object.freeze(prerequisites),
                provenance: nodeProvenance
            });
            return this.makeTerm(
                resultNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence],
                false,
                weakeningSection === undefined
                    ? {}
                    : {
                        displayedSectionWeakening: {
                            section: weakeningSection
                        }
                    }
            );
        } finally {
            this.activeDisplayedBases.delete(baseOrdinal);
            this.activeTokenOrdinals.shift();
            this.activeTokenOrdinals.shift();
        }
    }

    /**
     * Factor the reviewed `:^nd` component grammar back into a genuine
     * coherence-carrying displayed transformation.
     *
     * A leaf must be the component of one already-coherent closed
     * transformation at the current slot. Composition recursively factors
     * both children and composes the recovered outer transformations in
     * `Functord_cat`. Any other pointwise term remains deliberately
     * unqualified: component data alone does not synthesize naturality.
     */
    private factorDisplayedTransforComponent(
        term: InternalCoreCategoricalTerm,
        ordinal: number
    ): InternalCoreCategoricalTerm | undefined {
        if (
            term.type.tag !== 'indexed-transfor' ||
            term.type.indexOrdinal !== ordinal
        ) {
            return undefined;
        }

        if (
            term.node.tag === 'typed-application' &&
            term.node.judgment.target ===
                'displayed-transfor-component-capped' &&
            term.node.argument[CORE_CATEGORICAL_BOUNDARY] !== true
        ) {
            const argument = term.node.argument as
                InternalCoreCategoricalTerm;
            const subject = term.node.subject;
            if (
                argument.node.tag !== 'slot-token' ||
                argument.node.ordinal !== ordinal ||
                subject.type.tag !== 'displayed-transfor' ||
                !kernelExpressionEquals(
                    subject.type.baseCategory,
                    term.type.baseCategory
                ) ||
                !kernelExpressionEquals(
                    subject.type.sourceFamily,
                    term.type.sourceFamily
                ) ||
                !kernelExpressionEquals(
                    subject.type.targetFamily,
                    term.type.targetFamily
                ) ||
                !kernelExpressionEquals(
                    subject.type.sourceFunctor,
                    term.type.sourceFunctor
                ) ||
                !kernelExpressionEquals(
                    subject.type.targetFunctor,
                    term.type.targetFunctor
                ) ||
                usageCount(subject.usage, ordinal) !== 0 ||
                usageCount(term.usage, ordinal) !== 1 ||
                subject.closed === undefined
            ) {
                return undefined;
            }
            return subject;
        }

        if (term.node.tag !== 'typed-cell-composition') {
            return undefined;
        }
        const outer = this.factorDisplayedTransforComponent(
            term.node.outer,
            ordinal
        );
        const inner = this.factorDisplayedTransforComponent(
            term.node.inner,
            ordinal
        );
        if (
            outer === undefined ||
            inner === undefined ||
            outer.type.tag !== 'displayed-transfor' ||
            inner.type.tag !== 'displayed-transfor' ||
            outer.closed === undefined ||
            inner.closed === undefined ||
            !kernelExpressionEquals(
                outer.type.baseCategory,
                inner.type.baseCategory
            ) ||
            !kernelExpressionEquals(
                outer.type.sourceFamily,
                inner.type.sourceFamily
            ) ||
            !kernelExpressionEquals(
                outer.type.targetFamily,
                inner.type.targetFamily
            ) ||
            !kernelExpressionEquals(
                inner.type.targetFunctor,
                outer.type.sourceFunctor
            ) ||
            !kernelExpressionEquals(
                term.type.baseCategory,
                inner.type.baseCategory
            ) ||
            !kernelExpressionEquals(
                term.type.sourceFamily,
                inner.type.sourceFamily
            ) ||
            !kernelExpressionEquals(
                term.type.targetFamily,
                inner.type.targetFamily
            ) ||
            !kernelExpressionEquals(
                term.type.sourceFunctor,
                inner.type.sourceFunctor
            ) ||
            !kernelExpressionEquals(
                term.type.targetFunctor,
                outer.type.targetFunctor
            ) ||
            usageCount(outer.usage, ordinal) !== 0 ||
            usageCount(inner.usage, ordinal) !== 0
        ) {
            return undefined;
        }

        const nodeProvenance = term.node.provenance;
        const resultExpression = this.dependentCompositionCall(
            [
                {
                    plicity: 'implicit',
                    value: this.displayedFunctorCategory(
                        inner.type.baseCategory,
                        inner.type.sourceFamily,
                        inner.type.targetFamily,
                        nodeProvenance
                    )
                },
                {
                    plicity: 'implicit',
                    value: inner.type.sourceFunctor
                },
                {
                    plicity: 'implicit',
                    value: inner.type.targetFunctor
                },
                {
                    plicity: 'implicit',
                    value: outer.type.targetFunctor
                },
                {
                    plicity: 'explicit',
                    value: outer.closed.term
                },
                {
                    plicity: 'explicit',
                    value: inner.closed.term
                }
            ],
            nodeProvenance
        );
        const resultType: CoreType = {
            tag: 'displayed-transfor',
            category: this.displayedTransforCategory(
                inner.type.baseCategory,
                inner.type.sourceFamily,
                inner.type.targetFamily,
                inner.type.sourceFunctor,
                outer.type.targetFunctor,
                nodeProvenance
            ),
            baseCategory: inner.type.baseCategory,
            sourceFamily: inner.type.sourceFamily,
            targetFamily: inner.type.targetFamily,
            sourceFunctor: inner.type.sourceFunctor,
            targetFunctor: outer.type.targetFunctor
        };
        const resultNode: TemporaryCategoricalNode = {
            tag: 'explicit-core-term',
            term: resultExpression,
            provenance: nodeProvenance
        };
        const closed = deepFreeze({
            term: resultExpression,
            type: copyCoreType(resultType),
            sourceSpan: this.spanFor(nodeProvenance),
            recovered: [
                ...outer.closed.recovered,
                ...inner.closed.recovered
            ]
        });
        return this.makeTerm(
            resultNode,
            resultType,
            mergeUsage(outer.usage, inner.usage),
            closed,
            [...outer.abstractions, ...inner.abstractions]
        );
    }

    /**
     * Direct recursively factored displayed-transfor abstraction.
     *
     * The callback sees `k : Obj K`. A leaf `eta[k]` lowers back to the
     * already-coherent `eta`; a typed recursive vertical composition lowers
     * to composition of the recovered outer transformations. Arbitrary
     * pointwise families are not promoted to coherent transformations.
     */
    displayedTransforLambda(
        name: string,
        baseCategory: KernelExpression,
        sourceFamily: KernelExpression,
        targetFamily: KernelExpression,
        sourceFunctor: KernelExpression,
        targetFunctor: KernelExpression,
        bodyBuilder: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        assertSafeIdentifier(name, 'Displayed-transfor binder hint');
        kernelAssertScoped(baseCategory);
        kernelAssertScoped(sourceFamily);
        kernelAssertScoped(targetFamily);
        kernelAssertScoped(sourceFunctor);
        kernelAssertScoped(targetFunctor);
        const nodeProvenance = this.nodeProvenance(
            `displayed-transfor abstraction ${name}`,
            options.provenance
        );
        if (this.options.displayedTransforAbstraction !== true) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Direct displayed-transfor abstraction requires the ' +
                'FIBRED-TRANSFD-1 capability'
            );
        }
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'natural';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';
        if (
            variation !== 'natural' ||
            dependency !== 'displayed'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Displayed-transfor binder '${name}' requires natural ` +
                'variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                `Displayed-transfor binder '${name}' is covariant`
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'FIBRED-TRANSFD-1 abstracts one natural base object slot'
            );
        }

        const token = this.slot(name, baseCategory, nodeProvenance);
        const ordinal = token.node.tag === 'slot-token'
            ? token.node.ordinal
            : -1;
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(ordinal);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(token as CoreCategoricalSlotToken),
                nodeProvenance
            );
            if (
                body.type.tag !== 'indexed-transfor' ||
                body.type.indexOrdinal !== ordinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    body.type.sourceFamily,
                    sourceFamily
                ) ||
                !kernelExpressionEquals(
                    body.type.targetFamily,
                    targetFamily
                ) ||
                !kernelExpressionEquals(
                    body.type.sourceFunctor,
                    sourceFunctor
                ) ||
                !kernelExpressionEquals(
                    body.type.targetFunctor,
                    targetFunctor
                )
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'The displayed-transfor body must be an indexed ' +
                        'transformation with the requested contextual base, ' +
                        'families, and endpoints'
                );
            }

            const factored = this.factorDisplayedTransforComponent(
                body,
                ordinal
            );
            if (
                factored === undefined ||
                factored.type.tag !== 'displayed-transfor' ||
                factored.closed === undefined ||
                usageCount(factored.usage, ordinal) !== 0 ||
                !kernelExpressionEquals(
                    factored.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    factored.type.sourceFamily,
                    sourceFamily
                ) ||
                !kernelExpressionEquals(
                    factored.type.targetFamily,
                    targetFamily
                ) ||
                !kernelExpressionEquals(
                    factored.type.sourceFunctor,
                    sourceFunctor
                ) ||
                !kernelExpressionEquals(
                    factored.type.targetFunctor,
                    targetFunctor
                )
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'The active :^nd frontend accepts component eta leaves ' +
                        'and their typed recursive vertical compositions; ' +
                        'this body needs another coherence-carrying outer ' +
                        'constructor'
                );
            }
            const bodyIr = this.normalizeNode(
                body,
                [ordinal, ...outerScope]
            );
            const resultIr = this.normalizeNode(
                factored,
                outerScope
            );
            const rule =
                body.node.tag === 'typed-cell-composition'
                    ? 'categorical.displayed-transfor-composition' as const
                    : 'categorical.displayed-transfor-eta' as const;
            const evidence = deepFreeze({
                rule,
                name,
                plicity,
                variation: 'natural' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: baseCategory,
                sourceFamily,
                targetFamily,
                sourceFunctor,
                targetFunctor,
                body: bodyIr,
                result: resultIr,
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites:
                    collectDependentPrerequisites(bodyIr),
                provenance: nodeProvenance
            });
            const closed = deepFreeze({
                term: factored.closed.term,
                type: copyCoreType(factored.type),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: [...factored.closed.recovered]
            });
            return this.makeTerm(
                factored.node,
                factored.type,
                factored.usage,
                closed,
                [...factored.abstractions, evidence]
            );
        } finally {
            this.activeTokenOrdinals.shift();
        }
    }

    dependentLambda(
        name: string,
        baseCategory: KernelExpression,
        family: KernelExpression,
        bodyBuilder: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        assertSafeIdentifier(name, 'Dependent categorical binder hint');
        kernelAssertScoped(baseCategory);
        kernelAssertScoped(family);
        const nodeProvenance = this.nodeProvenance(
            `dependent categorical abstraction ${name}`,
            options.provenance
        );
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'natural';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'displayed';

        const judgment = selectCoreCategoricalAbstraction({
            requestedLayer: 'categorical',
            expectedClassifier: 'displayed-or-indexed-family',
            provenance: nodeProvenance
        });
        if (
            judgment.id !== 'natural-indexed-abstraction' ||
            variation !== 'natural' ||
            dependency !== 'displayed'
        ) {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                `Dependent categorical binder '${name}' requires natural ` +
                'variation and displayed dependency'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                `Dependent categorical binder '${name}' is covariant over ` +
                'its indexed base'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'USABILITY-2A1 abstracts one indexed object-level input'
            );
        }

        const token = this.slot(name, baseCategory, nodeProvenance);
        const ordinal = token.node.tag === 'slot-token'
            ? token.node.ordinal
            : -1;
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(ordinal);
        try {
            // Evaluate exactly once; no callback is retained.
            const body = this.requireTerm(
                bodyBuilder(token as CoreCategoricalSlotToken),
                nodeProvenance
            );
            if (
                body.type.tag !== 'indexed-object' ||
                body.type.indexOrdinal !== ordinal ||
                !kernelExpressionEquals(
                    body.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(body.type.family, family)
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Dependent abstraction '${name}' body is not an object ` +
                    'of the requested family at its contextual index'
                );
            }

            const composition =
                this.lowerDependentSectionComposition(
                    body,
                    name,
                    ordinal,
                    outerScope,
                    baseCategory,
                    family,
                    plicity,
                    nodeProvenance
                );
            if (composition !== undefined) return composition;

            const etaArgument =
                body.node.tag === 'typed-application' &&
                body.node.judgment.target ===
                    'section-object-evaluation' &&
                body.node.argument[
                    CORE_CATEGORICAL_BOUNDARY
                ] !== true
                    ? body.node.argument as
                        InternalCoreCategoricalTerm
                    : undefined;
            const etaSubject =
                body.node.tag === 'typed-application'
                    ? body.node.subject
                    : undefined;
            if (
                etaArgument?.node.tag !== 'slot-token' ||
                etaArgument.node.ordinal !== ordinal ||
                etaSubject === undefined ||
                etaSubject.type.tag !== 'dependent-section' ||
                !kernelExpressionEquals(
                    etaSubject.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    etaSubject.type.family,
                    family
                ) ||
                usageCount(etaSubject.usage, ordinal) !== 0 ||
                usageCount(body.usage, ordinal) !== 1 ||
                etaSubject.closed === undefined
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'The active dependent frontend qualifies direct section ' +
                    'eta and the exact approved FF[k](s[k]) composition; ' +
                    'this body needs another displayed structural operation'
                );
            }

            const bodyIr = this.normalizeNode(
                body,
                [ordinal, ...outerScope]
            );
            const resultIr = this.normalizeNode(
                etaSubject,
                outerScope
            );
            const evidence = deepFreeze({
                rule: 'categorical.dependent-eta' as const,
                name,
                plicity,
                variation: 'natural' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'displayed' as const,
                sourceCategory: baseCategory,
                targetFamily: family,
                body: bodyIr,
                result: resultIr,
                structuralPrerequisites: Object.freeze([]),
                dependentPrerequisites: Object.freeze([
                    'section-object-evaluation' as const
                ]),
                provenance: nodeProvenance
            });
            const closed = deepFreeze({
                term: etaSubject.closed.term,
                type: copyCoreType(etaSubject.type),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: [...etaSubject.closed.recovered]
            });
            return this.makeTerm(
                etaSubject.node,
                etaSubject.type,
                etaSubject.usage,
                closed,
                [...etaSubject.abstractions, evidence]
            );
        } finally {
            this.activeTokenOrdinals.shift();
        }
    }

    categoricalLambda(
        name: string,
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        bodyBuilder: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalBinderOptions = {}
    ): CoreCategoricalTerm {
        assertSafeIdentifier(name, 'Categorical binder hint');
        kernelAssertScoped(sourceCategory);
        kernelAssertScoped(targetCategory);
        const nodeProvenance = this.nodeProvenance(
            `categorical abstraction ${name}`,
            options.provenance
        );
        const plicity = options.plicity ?? 'explicit';
        const variation = options.variation ?? 'functorial';
        const polarity = options.polarity ?? 'covariant';
        const cellLevel = options.cellLevel ?? 'object';
        const dependency = options.dependency ?? 'ordinary';

        selectCoreCategoricalAbstraction({
            requestedLayer: 'categorical',
            expectedClassifier: 'ordinary-functor',
            provenance: nodeProvenance
        });
        if (variation === 'object-only') {
            this.fail(
                'OBJECT_ONLY_ARROW_USE',
                nodeProvenance,
                `Object-only categorical binder '${name}' cannot be checked ` +
                'as an ordinary functor with arrow action'
            );
        }
        if (variation === 'natural' || dependency === 'displayed') {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Natural/indexed or displayed categorical abstraction is ' +
                'staged for USABILITY-2A1'
            );
        }
        if (polarity !== 'covariant') {
            this.fail(
                'POLARITY_MISMATCH',
                nodeProvenance,
                'USABILITY-1B ordinary abstraction is covariant; represent ' +
                'contravariance through an opposite source classifier'
            );
        }
        if (cellLevel !== 'object') {
            this.fail(
                'CLASSIFIER_ARGUMENT_MISMATCH',
                nodeProvenance,
                'USABILITY-1B abstracts one object-level categorical input'
            );
        }

        const token = this.slot(name, sourceCategory, nodeProvenance);
        const outerScope = [...this.activeTokenOrdinals];
        this.activeTokenOrdinals.unshift(token.node.tag === 'slot-token'
            ? token.node.ordinal
            : -1);
        let body: InternalCoreCategoricalTerm;
        try {
            // Evaluate exactly once; no callback is stored.
            body = this.requireTerm(
                bodyBuilder(token as CoreCategoricalSlotToken),
                nodeProvenance
            );

            const expectedBodyType =
                this.categoricalTypeForCategoryObject(
                targetCategory,
                nodeProvenance,
                `categorical abstraction ${name} target`
            );
            if (
                body.type.tag === 'indexed-object' ||
                body.type.tag === 'indexed-functor' ||
                body.type.tag === 'indexed-transfor' ||
                body.type.tag === 'nested-indexed-object' ||
                !coreTypeEquals(body.type, expectedBodyType)
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Categorical abstraction '${name}' body has the wrong ` +
                    'target classifier'
                );
            }
            const ordinal = token.node.tag === 'slot-token'
                ? token.node.ordinal
                : -1;
            const etaArgument =
                body.node.tag === 'typed-application' &&
                body.node.judgment.target === 'functor-object' &&
                body.node.argument[
                    CORE_CATEGORICAL_BOUNDARY
                ] !== true
                    ? body.node.argument as
                        InternalCoreCategoricalTerm
                    : undefined;
            const etaSubject =
                body.node.tag === 'typed-application'
                    ? body.node.subject
                    : undefined;
            if (
                etaArgument?.node.tag === 'slot-token' &&
                etaArgument.node.ordinal === ordinal &&
                etaSubject !== undefined &&
                usageCount(etaSubject.usage, ordinal) === 0 &&
                usageCount(body.usage, ordinal) === 1 &&
                etaSubject.type.tag === 'functor' &&
                kernelExpressionEquals(
                    etaSubject.type.sourceCategory,
                    sourceCategory
                ) &&
                kernelExpressionEquals(
                    etaSubject.type.targetCategory,
                    targetCategory
                ) &&
                etaSubject.closed !== undefined
            ) {
                const bodyIr = this.normalizeNode(
                    body,
                    [ordinal, ...outerScope]
                );
                const resultIr = this.normalizeNode(
                    etaSubject,
                    outerScope
                );
                const evidence = deepFreeze({
                    rule: 'categorical.eta' as const,
                    name,
                    plicity,
                    variation: 'functorial' as const,
                    polarity: 'covariant' as const,
                    cellLevel: 'object' as const,
                    dependency: 'ordinary' as const,
                    sourceCategory,
                    targetCategory,
                    body: bodyIr,
                    result: resultIr,
                    structuralPrerequisites: Object.freeze([]),
                    dependentPrerequisites: Object.freeze([]),
                    provenance: nodeProvenance
                });
                const closed = deepFreeze({
                    term: etaSubject.closed.term,
                    type: copyCoreType(etaSubject.type),
                    sourceSpan: this.spanFor(nodeProvenance),
                    recovered: [...etaSubject.closed.recovered]
                });
                return this.makeTerm(
                    etaSubject.node,
                    etaSubject.type,
                    etaSubject.usage,
                    closed,
                    [...etaSubject.abstractions, evidence]
                );
            }

            const abstractionNode: TemporaryCategoricalNode = {
                tag: 'categorical-abstraction',
                ordinal,
                name,
                sourceCategory,
                targetCategory,
                body,
                provenance: nodeProvenance
            };
            const resultType: CoreType = {
                tag: 'functor',
                sourceCategory,
                targetCategory
            };
            const remainingUsage = removeUsage(body.usage, ordinal);
            const provisional = this.makeTerm(
                abstractionNode,
                resultType,
                remainingUsage,
                undefined,
                body.abstractions
            );

            if (outerScope.length > 0) {
                return provisional;
            }

            const wiring = new Map<
                number,
                CoreCategoricalContextualCompilation
            >([[
                ordinal,
                this.identityFunctor(
                    sourceCategory,
                    nodeProvenance
                )
            ]]);
            const compilation =
                this.directDiagonal(
                    body,
                    ordinal,
                    sourceCategory,
                    targetCategory,
                    nodeProvenance
                ) ??
                this.compileContextual(
                    body,
                    sourceCategory,
                    wiring,
                    nodeProvenance
                );
            if (
                !kernelExpressionEquals(
                    compilation.targetCategory,
                    targetCategory
                )
            ) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Categorical abstraction '${name}' lowered to the ` +
                        'wrong target category'
                );
            }
            const bodyIr = this.normalizeNode(body, [ordinal]);
            const resultIr = this.normalizeNode(provisional, []);
            const evidence = deepFreeze({
                rule: 'categorical.bracket' as const,
                name,
                plicity,
                variation: 'functorial' as const,
                polarity: 'covariant' as const,
                cellLevel: 'object' as const,
                dependency: 'ordinary' as const,
                sourceCategory,
                targetCategory,
                body: bodyIr,
                result: resultIr,
                structuralPrerequisites:
                    compilation.structuralPrerequisites,
                dependentPrerequisites: Object.freeze([]),
                provenance: nodeProvenance
            });
            const closed = deepFreeze({
                term: compilation.term,
                type: copyCoreType(resultType),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: body.closed === undefined
                    ? []
                    : [...body.closed.recovered]
            });
            return this.makeTerm(
                abstractionNode,
                resultType,
                remainingUsage,
                closed,
                [...body.abstractions, evidence]
            );
        } finally {
            this.activeTokenOrdinals.shift();
        }
    }

    compile(termValue: CoreCategoricalTerm): ElaboratedSurfaceTerm {
        const term = this.requireTerm(
            termValue,
            this.defaultProvenance
        );
        if (term.usage.length !== 0 || term.closed === undefined) {
            this.fail(
                'UNLOWERED_CONTEXT',
                this.defaultProvenance,
                'Categorical term still has open contextual slots'
            );
        }
        return term.closed;
    }

    inspect(
        termValue: CoreCategoricalTerm
    ): CoreCategoricalTermInspection {
        const term = this.requireTerm(
            termValue,
            this.defaultProvenance
        );
        const ir = this.normalizeNode(
            term,
            this.activeTokenOrdinals
        );
        return deepFreeze({
            type: this.normalizeClassifier(
                term.type,
                this.activeTokenOrdinals,
                term.node.provenance
            ),
            usage: term.usage.map(([ordinal, count]) => ({
                index: this.activeTokenOrdinals.indexOf(ordinal),
                count
            })),
            ir,
            abstractions: [...term.abstractions],
            dependentPrerequisites:
                collectDependentPrerequisites(ir),
            lowered: term.closed !== undefined
        });
    }
}
