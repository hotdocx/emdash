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
 *   when its FIBRED-BINDER-1 capability is enabled.
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
    readonly baseCategory: KernelExpression;
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
    readonly baseCategory: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly index: number;
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

export type CoreCategoricalClassifier =
    | CoreType
    | CoreCategoricalIndexedObjectClassifier
    | CoreCategoricalIndexedFunctorClassifier
    | CoreCategoricalIndexedTransforClassifier;

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
        readonly tag: 'typed-pair';
        readonly left: CoreCategoricalContextualIr;
        readonly right: CoreCategoricalContextualIr;
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
            readonly rule: 'categorical.displayed-transfor-eta';
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
    | CoreCategoricalDependentPrerequisiteId
    | CoreCategoricalDependentCompositionPrerequisiteId;

export interface CoreCategoricalScopedBuilderOptions {
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
     * Enable only the FIBRED-TRANSFD-1 coherent component-eta abstraction.
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
        readonly tag: 'typed-pair';
        readonly left: InternalCoreCategoricalTerm;
        readonly right: InternalCoreCategoricalTerm;
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
    readonly family: KernelExpression;
    readonly indexOrdinal: number;
}

interface InternalCoreCategoricalIndexedFunctorClassifier {
    readonly tag: 'indexed-functor';
    readonly baseCategory: KernelExpression;
    readonly sourceFamily: KernelExpression;
    readonly targetFamily: KernelExpression;
    readonly indexOrdinal: number;
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

type InternalCoreCategoricalClassifier =
    | CoreType
    | InternalCoreCategoricalIndexedObjectClassifier
    | InternalCoreCategoricalIndexedFunctorClassifier
    | InternalCoreCategoricalIndexedTransforClassifier;

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
            family: classifier.family,
            indexOrdinal: classifier.indexOrdinal
        };
    }
    if (classifier.tag === 'indexed-functor') {
        return {
            tag: 'indexed-functor',
            baseCategory: classifier.baseCategory,
            sourceFamily: classifier.sourceFamily,
            targetFamily: classifier.targetFamily,
            indexOrdinal: classifier.indexOrdinal
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
    return copyCoreType(classifier);
};

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
            case 'typed-pair':
                visit(current.left);
                visit(current.right);
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
            type.tag === 'indexed-transfor'
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

    private indexedObjectSlot(
        name: string,
        baseCategory: KernelExpression,
        family: KernelExpression,
        indexOrdinal: number,
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
                tag: 'indexed-object',
                baseCategory,
                family,
                indexOrdinal
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
                endpoint.type.tag === 'indexed-transfor'
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
        const resultType: CoreType = {
            tag: 'object',
            category: fibre
        };
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

    private applyDisplayedFunctor(
        subject: InternalCoreCategoricalTerm,
        argumentValue:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        expectedShape: CoreCategoricalExpectedShape | undefined,
        nodeProvenance: Provenance
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
                    baseCategory: base,
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
        if (
            argument.type.tag !== 'indexed-object' ||
            argument.type.indexOrdinal !==
                subject.type.indexOrdinal ||
            !kernelExpressionEquals(
                argument.type.baseCategory,
                subject.type.baseCategory
            ) ||
            !kernelExpressionEquals(
                argument.type.family,
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
        return this.makeTerm(
            {
                tag: 'typed-application',
                judgment:
                    CORE_CATEGORICAL_DEPENDENT_CONTINUATION_APPLICATION,
                subject,
                argument,
                provenance: nodeProvenance
            },
            {
                tag: 'indexed-object',
                baseCategory: subject.type.baseCategory,
                family: subject.type.targetFamily,
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
            if (argument.type.tag === 'indexed-object') {
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
                    argument.type.indexOrdinal
                );
                if (baseToken === undefined) {
                    this.fail(
                        'ESCAPED_SLOT',
                        nodeProvenance,
                        'Direct displayed-functor application lost its ' +
                        'hidden base slot'
                    );
                }
                const indexedFunctor = this.applyDisplayedFunctor(
                    subject,
                    baseToken,
                    'fibre-functor',
                    nodeProvenance
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
            type = closed.type;
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
            classifier.tag !== 'indexed-transfor'
        ) {
            return copyCoreType(classifier);
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
                family: classifier.family,
                index
            };
        }
        if (classifier.tag === 'indexed-functor') {
            return {
                tag: 'indexed-functor',
                baseCategory: classifier.baseCategory,
                sourceFamily: classifier.sourceFamily,
                targetFamily: classifier.targetFamily,
                index
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
            case 'typed-pair':
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    'Typed fibre pairs lower only inside the reviewed ' +
                        'displayed contextual bracket'
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
                { value: section.closed.term }
            ],
            nodeProvenance
        );
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
     * First direct displayed-transfor abstraction.
     *
     * The callback sees `k : Obj K` and may project one already-coherent,
     * closed displayed transfor at that slot. The eta body is reified as
     * `eta[k]` and lowers back to `eta`; arbitrary pointwise families are not
     * promoted to coherent displayed transformations.
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
            const etaArgument =
                body.node.tag === 'typed-application' &&
                body.node.judgment.target ===
                    'displayed-transfor-component-capped' &&
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
                ) ||
                etaArgument?.node.tag !== 'slot-token' ||
                etaArgument.node.ordinal !== ordinal ||
                etaSubject === undefined ||
                etaSubject.type.tag !== 'displayed-transfor' ||
                !kernelExpressionEquals(
                    etaSubject.type.baseCategory,
                    baseCategory
                ) ||
                !kernelExpressionEquals(
                    etaSubject.type.sourceFamily,
                    sourceFamily
                ) ||
                !kernelExpressionEquals(
                    etaSubject.type.targetFamily,
                    targetFamily
                ) ||
                !kernelExpressionEquals(
                    etaSubject.type.sourceFunctor,
                    sourceFunctor
                ) ||
                !kernelExpressionEquals(
                    etaSubject.type.targetFunctor,
                    targetFunctor
                ) ||
                usageCount(etaSubject.usage, ordinal) !== 0 ||
                usageCount(body.usage, ordinal) !== 1 ||
                etaSubject.closed === undefined
            ) {
                this.fail(
                    'UNAVAILABLE_DISPLAYED_ACTION',
                    nodeProvenance,
                    'FIBRED-TRANSFD-1 accepts exactly coherent component ' +
                    'eta: λ k. eta[k] for one closed displayed transfor eta'
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
                rule: 'categorical.displayed-transfor-eta' as const,
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
                dependentPrerequisites: Object.freeze([
                    'displayed-transfor-component-capped' as const
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
