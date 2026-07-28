/**
 * Stable root-only TypeScript facade for the categorical frontend.
 *
 * The facade owns declaration scope, source sites, structural compilation,
 * generic LF checking, and deterministic explicit-Core inspection. It is a
 * typed construction API, not a textual parser. Categorical callbacks lower
 * immediately through `CoreCategoricalScopedBuilder` and are never retained
 * as executable semantic state.
 */

import {
    CoreCheckerError,
    CoreCheckerErrorCode
} from './checker';
import {
    CoreCategoricalAbstractionEvidence,
    CoreCategoricalBinderOptions,
    CoreCategoricalFrontendError,
    CoreCategoricalFrontendErrorCode,
    CoreCategoricalHomBoundary,
    CoreCategoricalScopedBuilder,
    CoreCategoricalSlotToken,
    CoreCategoricalTerm,
    CoreCategoricalTermInspection
} from './categorical_surface';
import {
    CORE_CATEGORICAL_DEPENDENT_PREREQUISITES,
    CoreCategoricalDependentCompilation,
    compileCoreCategoricalDependentTransfer,
    coreCategoricalDependentCoreName
} from './categorical_dependent_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PREREQUISITES,
    CoreCategoricalDependentCompositionCompilation,
    compileCoreCategoricalDependentCompositionTransfer,
    coreCategoricalDependentCompositionCoreName
} from './categorical_dependent_composition_transfer';
import {
    CoreCategoricalComprehensionCompilation,
    compileCoreCategoricalComprehensionTransfer,
    coreCategoricalComprehensionCoreName
} from './categorical_comprehension_transfer';
import {
    CoreCategoricalFibredProductCompilation,
    compileCoreCategoricalFibredProductTransfer,
    coreCategoricalFibredProductCoreName
} from './categorical_fibred_product_transfer';
import {
    CoreCategoricalFibredStructureCompilation,
    compileCoreCategoricalFibredStructureTransfer,
    coreCategoricalFibredStructureCoreName
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES,
    CoreCategoricalFibredBinderCompilation,
    compileCoreCategoricalFibredBinderProof,
    compileCoreCategoricalFibredBinderTransfer,
    coreCategoricalFibredBinderClassifiers
} from './categorical_fibred_binder_transfer';
import {
    CoreCategoricalFibredTransfdCompilation,
    compileCoreCategoricalFibredTransfdProof,
    compileCoreCategoricalFibredTransfdTransfer,
    coreCategoricalFibredTransfdClassifiers,
    coreCategoricalFibredTransfdCoreName
} from './categorical_fibred_transfd_transfer';
import {
    CoreCategoricalFibredWeakenReindexCompilation,
    compileCoreCategoricalFibredWeakenReindexTransfer,
    coreCategoricalFibredWeakenReindexCoreName
} from './categorical_fibred_weaken_reindex_transfer';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES,
    CoreCategoricalFibredDependentTargetCompilation,
    compileCoreCategoricalFibredDependentTargetTransfer
} from './categorical_fibred_dependent_target_transfer';
import {
    validateCoreCategoricalFibredWeakenReindexContract
} from './categorical_fibred_weaken_reindex_contract';
import {
    validateCoreCategoricalFibredDependentTargetContract
} from './categorical_fibred_dependent_target_contract';
import {
    CoreCategoricalContextDependencyPlan,
    coreCategoricalClosedContextClassifier,
    coreCategoricalContextSlotReference,
    coreCategoricalDisplayedContextClassifier,
    planCoreCategoricalContextDependencies
} from './categorical_context_dependencies';
import {
    CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT,
    validateCoreCategoricalGroupedSequentialContract
} from './categorical_grouped_sequential_contract';
import {
    CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CoreCategoricalStructuralPrerequisiteId,
    coreCategoricalStructuralCoreName,
    coreCategoricalStructuralSymbolCoreName
} from './categorical_structural_transfer';
import {
    CoreCategoricalExpectedShape
} from './categorical_surface_spec';
import {
    coreDisplayedFamilyType,
    coreSectionCategory
} from './dependent';
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
    serializeCoreExpression
} from './core_serialization';
import {
    ElaboratedSurfaceTerm
} from './elaborator';
import {
    KernelExpression,
    Plicity,
    Provenance,
    SourceSpan,
    binderMode,
    formatSourceSpan,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    provenance,
    sourceSpan
} from './kernel';
import {
    CoreLfDeclarationEnvironment,
    CoreLfDeclarationError,
    CoreLfDeclarationErrorCode
} from './lf_declarations';
import {
    CoreLfComparisonResult,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
    CoreLfProofComparisonResult
} from './lf_transfer_proof';
import {
    CoreType,
    coreObjectCategoryEquals,
    coreTypeObjectCategory,
    coreTypeToKernelType
} from './surface';

export const CORE_CATEGORICAL_PROGRAM_REVISION =
    'USABILITY-2A1-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PROGRAM_REVISION =
    'USABILITY-DEPENDENT-1A-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_COMPREHENSION_PROGRAM_REVISION =
    'FIBRED-COMPREHENSION-1A-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_FIBRED_PRODUCT_PROGRAM_REVISION =
    'FIBRED-PRODUCT-1A-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_PROGRAM_REVISION =
    'FIBRED-STRUCTURE-1A-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_FIBRED_BINDER_PROGRAM_REVISION =
    'FIBRED-BINDER-1-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_FIBRED_TRANSFD_PROGRAM_REVISION =
    'FIBRED-TRANSFD-1-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_GROUPED_SEQUENTIAL_PROGRAM_REVISION =
    'FIBRED-GROUPED-SEQUENTIAL-1-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_PROGRAM_REVISION =
    'FIBRED-WEAKEN-REINDEX-1-CATEGORICAL-PROGRAM-1' as const;

export const CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_PROGRAM_REVISION =
    'FIBRED-DEPENDENT-TARGET-1-CATEGORICAL-PROGRAM-1' as const;

const CORE_CATEGORICAL_CATEGORY =
    Symbol('CoreCategoricalProgramCategory');
const CORE_CATEGORICAL_DISPLAYED_FAMILY =
    Symbol('CoreCategoricalProgramDisplayedFamily');
const CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTEXT =
    Symbol('CoreCategoricalGroupedSequentialContext');

export interface CoreCategoricalCategory {
    readonly [CORE_CATEGORICAL_CATEGORY]: true;
    readonly label: string;
}

interface InternalCoreCategoricalCategory
extends CoreCategoricalCategory {
    readonly programIdentity: symbol;
    readonly expression: KernelExpression;
}

export interface CoreCategoricalDisplayedFamily {
    readonly [CORE_CATEGORICAL_DISPLAYED_FAMILY]: true;
    readonly label: string;
}

interface InternalCoreCategoricalDisplayedFamily
extends CoreCategoricalDisplayedFamily {
    readonly programIdentity: symbol;
    readonly baseCategory: InternalCoreCategoricalCategory;
    readonly expression: KernelExpression;
    /**
     * Elaboration-only origin retained for the approved canonical
     * reindexing of an independent sibling group. This metadata is not a
     * kernel equality and is never serialized into explicit Core.
     */
    readonly groupedProduct?: {
        readonly left: InternalCoreCategoricalDisplayedFamily;
        readonly right: InternalCoreCategoricalDisplayedFamily;
    };
}

export interface CoreCategoricalGroupedSequentialBinding {
    readonly name: string;
    readonly family: CoreCategoricalDisplayedFamily;
}

export interface CoreCategoricalGroupedSequentialExtension {
    readonly position: number;
    readonly name: string;
    readonly originalFamily: CoreCategoricalDisplayedFamily;
    readonly effectiveFamily: CoreCategoricalDisplayedFamily;
    readonly sourceCategory: CoreCategoricalCategory;
    readonly totalCategory: CoreCategoricalCategory;
    readonly projectionToPrevious: CoreCategoricalTerm;
    readonly projectionToBase: CoreCategoricalTerm;
    readonly pullbackPastPositions: readonly number[];
    readonly presentation:
        | 'direct-sigma-extension'
        | 'pullback-then-sigma-extension';
}

export interface CoreCategoricalGroupedSequentialContext {
    readonly [CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTEXT]: true;
    readonly revision:
        typeof CORE_CATEGORICAL_GROUPED_SEQUENTIAL_PROGRAM_REVISION;
    readonly baseName: string;
    readonly baseCategory: CoreCategoricalCategory;
    readonly siblings: readonly {
        readonly position: number;
        readonly name: string;
        readonly family: CoreCategoricalDisplayedFamily;
    }[];
    readonly plan: CoreCategoricalContextDependencyPlan;
    readonly sequential: {
        readonly syntax: string;
        readonly extensions:
            readonly CoreCategoricalGroupedSequentialExtension[];
        readonly totalCategory: CoreCategoricalCategory;
    };
    readonly grouped: {
        readonly syntax: string;
        readonly association: 'left';
        readonly family: CoreCategoricalDisplayedFamily;
        readonly totalCategory: CoreCategoricalCategory;
    };
    readonly boundary: {
        readonly newLambdapiOwnerOrRule: false;
        readonly totalCategoryEqualityClaimed: false;
        readonly totalCategoryEquivalenceClaimed: false;
        readonly arrowLevelTotalComparisonClaimed: false;
    };
}

interface InternalCoreCategoricalGroupedSequentialContext
extends CoreCategoricalGroupedSequentialContext {
    readonly programIdentity: symbol;
}

export interface CoreCategoricalGroupedSequentialComparison {
    readonly id: string;
    readonly status: 'equal';
    readonly steps: number;
    readonly ruleIds: readonly string[];
}

export interface CoreCategoricalGroupedSequentialObject {
    readonly context: CoreCategoricalGroupedSequentialContext;
    readonly basePoint: CoreCategoricalTerm;
    readonly siblingValues: readonly CoreCategoricalTerm[];
    readonly sequentialPrefixObjects: readonly CoreCategoricalTerm[];
    readonly sequentialObject: CoreCategoricalTerm;
    readonly groupedTuple: CoreCategoricalTerm;
    readonly groupedFibreObject: CoreCategoricalTerm;
    readonly groupedObject: CoreCategoricalTerm;
    readonly sequentialFibreComparisons:
        readonly CoreCategoricalGroupedSequentialComparison[];
    readonly groupedFibreComparison:
        CoreCategoricalGroupedSequentialComparison;
    readonly totalCategoryCompared: false;
}

export interface CoreCategoricalSourceSite {
    readonly file?: string;
    readonly line: number;
    readonly column?: number;
    readonly endLine?: number;
    readonly endColumn?: number;
    readonly detail?: string;
}

export interface CoreCategoricalProgramOptions {
    readonly sourceFile?: string;
    /**
     * The default preserves the exact reviewed USABILITY-2A1 program. The
     * continuation profile adds only the approved D-003 section-composition
     * closure. The fibred-comprehension profile additionally exposes the
     * approved asymmetric base-change totalization. The fibred-product
     * profile extends that root-only lineage with the approved transparent
     * family product and same-base transport. The fibred-structure profile
     * adds the fixed-base displayed projections/pairing and frontend-only
     * canonical grouped-product reindexing approved by
     * D-DTTLF-USABILITY-006. The fibred-binder profile additionally exposes
     * the existing-authority direct displayed-functor abstraction and
     * proof-only direct/nested classifier comparison.
     * The fibred-transfd profile adds the coherent direct `:^nd` eta
     * abstraction, fibre components, point components, and the active
     * transported higher cell. The grouped-sequential profile additionally
     * connects the generic dependency graph to finite sequential
     * Sigma/pullback and grouped transparent-product context presentations.
     * The weakening/reindexing profile then adds the exact contextual
     * `indexOf` section weakening and existing-authority displayed
     * base-change action. The dependent-target profile finally adds the
     * exact contravariant category family, pulled-back displayed-family
     * motive, internal-Pi package, Sigma-total target, and target-fibre
     * computation selected by D-DTTLF-USABILITY-007/007A.
     */
    readonly profile?:
        | 'reviewed-usability-2a1'
        | 'usability-dependent-1a'
        | 'fibred-comprehension-1a'
        | 'fibred-product-1a'
        | 'fibred-structure-1a'
        | 'fibred-binder-1'
        | 'fibred-transfd-1'
        | 'fibred-grouped-sequential-1'
        | 'fibred-weaken-reindex-1'
        | 'fibred-dependent-target-1';
}

export interface CoreCategoricalApplyOptions {
    readonly expectedShape?: CoreCategoricalExpectedShape;
    readonly source?: CoreCategoricalSourceSite;
}

export interface CoreCategoricalLambdaOptions {
    readonly plicity?: Plicity;
    readonly variation?: CoreCategoricalBinderOptions['variation'];
    readonly polarity?: CoreCategoricalBinderOptions['polarity'];
    readonly cellLevel?: CoreCategoricalBinderOptions['cellLevel'];
    readonly dependency?: CoreCategoricalBinderOptions['dependency'];
    readonly source?: CoreCategoricalSourceSite;
}

export type CoreCategoricalProgramErrorCode =
    | 'FOREIGN_CATEGORY'
    | 'FOREIGN_DISPLAYED_FAMILY'
    | 'DISPLAYED_BASE_MISMATCH'
    | 'EXPECTED_CATEGORY_OBJECT'
    | 'EXPECTED_FUNCTOR'
    | 'EXPECTED_DISPLAYED_FUNCTOR'
    | 'EXPECTED_DISPLAYED_TRANSFOR'
    | 'EXPECTED_HOM'
    | 'DISPLAYED_SOURCE_MISMATCH'
    | 'UNAVAILABLE_COMPREHENSION'
    | 'UNAVAILABLE_FIBRED_PRODUCT'
    | 'UNAVAILABLE_FIBRED_STRUCTURE'
    | 'UNAVAILABLE_FIBRED_BINDER'
    | 'UNAVAILABLE_FIBRED_TRANSFD'
    | 'UNAVAILABLE_GROUPED_SEQUENTIAL'
    | 'UNAVAILABLE_WEAKEN_REINDEX'
    | 'UNAVAILABLE_DEPENDENT_TARGET'
    | 'INVALID_GROUPED_SEQUENTIAL_CONTEXT'
    | 'UNEXPECTED_KIND';

export class CoreCategoricalProgramError extends Error {
    constructor(
        public readonly code: CoreCategoricalProgramErrorCode,
        public readonly provenance: Provenance,
        message: string
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreCategoricalProgramError';
    }
}

export type CoreCategoricalDiagnosticPhase =
    | 'surface'
    | 'declaration'
    | 'checking'
    | 'program';

export type CoreCategoricalDiagnosticCode =
    | CoreCategoricalFrontendErrorCode
    | CoreLfDeclarationErrorCode
    | CoreCheckerErrorCode
    | CoreCategoricalProgramErrorCode;

export interface CoreCategoricalDiagnostic {
    readonly phase: CoreCategoricalDiagnosticPhase;
    readonly code: CoreCategoricalDiagnosticCode;
    readonly message: string;
    readonly detail: string;
    readonly span?: SourceSpan;
    readonly location?: string;
}

export interface CoreCategoricalProgramCompilation {
    readonly construction: 'direct-typescript-categorical-program';
    readonly explicitTerm: KernelExpression;
    readonly inferredType: KernelExpression;
    readonly expectedType: KernelExpression;
    readonly surfaceType: CoreType;
    readonly explicitCore: string;
    readonly explicitInferredType: string;
    readonly explicitExpectedType: string;
    readonly abstractions:
        readonly CoreCategoricalAbstractionEvidence[];
    readonly structuralPrerequisites:
        readonly CoreCategoricalStructuralPrerequisiteId[];
    readonly dependentPrerequisites:
        CoreCategoricalTermInspection['dependentPrerequisites'];
    readonly productionLambdapiDependency: false;
}

export interface CoreCategoricalFibredBinderClassifierCompatibility {
    readonly directClassifier: KernelExpression;
    readonly nestedClassifier: KernelExpression;
    readonly explicitDirectClassifier: string;
    readonly explicitNestedClassifier: string;
    readonly runtime: CoreLfComparisonResult;
    readonly proofTime: CoreLfProofComparisonResult;
    readonly preservesPresentations: true;
}

export interface CoreCategoricalFibredTransfdClassifierCompatibility {
    readonly directClassifier: KernelExpression;
    readonly ordinaryNextHomClassifier: KernelExpression;
    readonly sigmaPiNextHomClassifier: KernelExpression;
    readonly explicitDirectClassifier: string;
    readonly explicitOrdinaryNextHomClassifier: string;
    readonly explicitSigmaPiNextHomClassifier: string;
    readonly directOrdinaryRuntime: CoreLfComparisonResult;
    readonly directOrdinaryProofTime: CoreLfProofComparisonResult;
    readonly directOrdinaryObjectRuntime: CoreLfComparisonResult;
    readonly directSigmaPiRuntime: CoreLfComparisonResult;
    readonly preservesPresentations: true;
}

export interface CoreCategoricalFibredDependentTargetCompatibility {
    readonly runtime: CoreLfComparisonResult;
    readonly proofTime: CoreLfProofComparisonResult;
    readonly runtimeCategoryPresentationCollapseInstalled: false;
    readonly preservesPresentations: true;
}

const explicitFunctorial = binderMode('explicit', 'functorial');

const categoricalLabels: Record<string, string> = {};
for (const prerequisite of CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES) {
    categoricalLabels[
        coreCategoricalStructuralCoreName(prerequisite.id)
    ] = `emdash.categorical.${prerequisite.id}`;
}
categoricalLabels[
    coreCategoricalStructuralSymbolCoreName(
        CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
    )
] = 'emdash.categorical.functor-category';
for (const prerequisite of CORE_CATEGORICAL_DEPENDENT_PREREQUISITES) {
    categoricalLabels[
        coreCategoricalDependentCoreName(prerequisite.id)
    ] = `emdash.categorical.${prerequisite.id}`;
}
for (
    const prerequisite of
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PREREQUISITES
) {
    if (
        prerequisite.id === 'terminal-category' ||
        prerequisite.id === 'generic-category-composition'
    ) {
        categoricalLabels[
            coreCategoricalDependentCompositionCoreName(
                prerequisite.id
            )
        ] = `emdash.categorical.${prerequisite.id}`;
    }
}
categoricalLabels[
    CORE_DIRECTED_1A_PRIMITIVE_NAMES['displayed-functor-category']
] = 'emdash.categorical.displayed-functor-category';
categoricalLabels[
    CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category']
] = 'emdash.categorical.sigma-category';
categoricalLabels[
    CORE_DIRECTED_1B_PRIMITIVE_NAMES['sigma-first-projection']
] = 'emdash.categorical.sigma-first-projection';
categoricalLabels[
    CORE_DIRECTED_1B_PRIMITIVE_NAMES['dependent-pair']
] = 'emdash.categorical.dependent-pair';
categoricalLabels[
    CORE_DIRECTED_1C_PRIMITIVE_NAMES['section-object-evaluation']
] = 'emdash.categorical.section-object-evaluation';
categoricalLabels[
    coreCategoricalComprehensionCoreName('sigma-arrow')
] = 'emdash.categorical.sigma-arrow';
categoricalLabels[
    coreCategoricalComprehensionCoreName(
        'sigma-pullback-total-functor'
    )
] = 'emdash.categorical.sigma-pullback-total-functor';
categoricalLabels[
    coreCategoricalFibredProductCoreName(
        'postcomposition-action'
    )
] = 'emdash.categorical.postcomposition-action';
categoricalLabels[
    coreCategoricalFibredProductCoreName(
        'internal-product-functor'
    )
] = 'emdash.categorical.internal-product-functor';
categoricalLabels[
    coreCategoricalFibredProductCoreName(
        'partial-product-functor'
    )
] = 'emdash.categorical.partial-product-functor';
categoricalLabels[
    coreCategoricalFibredProductCoreName(
        'product-left-action'
    )
] = 'emdash.categorical.product-left-action';
categoricalLabels[
    coreCategoricalFibredProductCoreName(
        'fixed-right-product-map'
    )
] = 'emdash.categorical.fixed-right-product-map';
categoricalLabels[
    coreCategoricalFibredStructureCoreName(
        'precomposition-functor'
    )
] = 'emdash.categorical.precomposition-functor';
categoricalLabels[
    coreCategoricalFibredStructureCoreName(
        'precomposition-action'
    )
] = 'emdash.categorical.precomposition-action';
categoricalLabels[
    coreCategoricalFibredStructureCoreName(
        'displayed-identity'
    )
] = 'emdash.categorical.displayed-identity';
categoricalLabels[
    coreCategoricalFibredStructureCoreName(
        'displayed-product-left-projection'
    )
] = 'emdash.categorical.displayed-product-left-projection';
categoricalLabels[
    coreCategoricalFibredStructureCoreName(
        'displayed-product-right-projection'
    )
] = 'emdash.categorical.displayed-product-right-projection';
categoricalLabels[
    coreCategoricalFibredStructureCoreName(
        'displayed-product-pair'
    )
] = 'emdash.categorical.displayed-product-pair';
categoricalLabels[
    CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES
        .displayedFamilyClassifier
] = 'emdash.categorical.displayed-family-classifier';
categoricalLabels[
    CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES
        .sigmaProjectionPullback
] = 'emdash.categorical.sigma-projection-pullback';
for (const [
    id,
    label
] of [
    [
        'displayed-transformation-category',
        'emdash.categorical.displayed-transformation-category'
    ],
    [
        'displayed-transformation-classifier',
        'emdash.categorical.displayed-transformation-classifier'
    ],
    [
        'displayed-component',
        'emdash.categorical.displayed-component'
    ],
    [
        'transport-lhs',
        'emdash.categorical.displayed-transport-lhs'
    ],
    [
        'transport-rhs',
        'emdash.categorical.displayed-transport-rhs'
    ],
    [
        'higher-cell',
        'emdash.categorical.displayed-transfor-higher-cell'
    ]
] as const) {
    categoricalLabels[
        coreCategoricalFibredTransfdCoreName(id)
    ] = label;
}
for (const [
    coreName,
    label
] of [
    [
        CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
            .oppositeCategory,
        'emdash.categorical.opposite-category'
    ],
    [
        CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
            .displayedCategoryFunctor,
        'emdash.categorical.displayed-category-functor'
    ],
    [
        CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
            .sectionCategoryFunctor,
        'emdash.categorical.section-category-functor'
    ],
    [
        CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
            .pullbackPi,
        'emdash.categorical.pullback-section-package'
    ]
] as const) {
    categoricalLabels[coreName] = label;
}
for (const [
    id,
    label
] of [
    [
        'pullbackDisplayedFamilyFunctor',
        'emdash.categorical.displayed-pullback-functor'
    ],
    [
        'pointFunctor',
        'emdash.categorical.point-functor'
    ],
    [
        'sectionPullback',
        'emdash.categorical.section-pullback'
    ],
    [
        'sectionPullbackSection',
        'emdash.categorical.section-pullback-section'
    ]
] as const) {
    categoricalLabels[
        coreCategoricalFibredWeakenReindexCoreName(id)
    ] = label;
}

export const CORE_CATEGORICAL_EXPLICIT_FREE_LABELS:
Readonly<Record<string, string>> = Object.freeze({
    ...categoricalLabels
});

export function serializeCoreCategoricalExpression(
    expression: KernelExpression
): string {
    return serializeCoreExpression(expression, {
        freeReferenceLabels: CORE_CATEGORICAL_EXPLICIT_FREE_LABELS
    });
}

const diagnostic = (
    phase: CoreCategoricalDiagnosticPhase,
    code: CoreCategoricalDiagnosticCode,
    nodeProvenance: Provenance,
    message: string
): CoreCategoricalDiagnostic => {
    const span = nodeProvenance.span === undefined
        ? undefined
        : Object.freeze({
            file: nodeProvenance.span.file,
            start: Object.freeze({ ...nodeProvenance.span.start }),
            end: Object.freeze({ ...nodeProvenance.span.end })
        });
    return Object.freeze({
        phase,
        code,
        message,
        detail: nodeProvenance.detail,
        span,
        location: span === undefined
            ? undefined
            : formatSourceSpan(span)
    });
};

/**
 * Normalize the stable error families exposed by the facade.
 */
export function coreCategoricalDiagnosticFromError(
    error: unknown
): CoreCategoricalDiagnostic | undefined {
    if (error instanceof CoreCategoricalFrontendError) {
        return diagnostic(
            'surface',
            error.code,
            error.provenance,
            error.message
        );
    }
    if (error instanceof CoreLfDeclarationError) {
        return diagnostic(
            'declaration',
            error.code,
            error.provenance,
            error.message
        );
    }
    if (error instanceof CoreCheckerError) {
        return diagnostic(
            'checking',
            error.code,
            error.provenance,
            error.message
        );
    }
    if (error instanceof CoreCategoricalProgramError) {
        return diagnostic(
            'program',
            error.code,
            error.provenance,
            error.message
        );
    }
    return undefined;
}

const collectStructuralPrerequisites = (
    abstractions: readonly CoreCategoricalAbstractionEvidence[]
): readonly CoreCategoricalStructuralPrerequisiteId[] => {
    const result: CoreCategoricalStructuralPrerequisiteId[] = [];
    for (const abstraction of abstractions) {
        for (const prerequisite of abstraction.structuralPrerequisites) {
            if (!result.includes(prerequisite)) {
                result.push(prerequisite);
            }
        }
    }
    return Object.freeze(result);
};

const collectDependentPrerequisites = (
    inspection: CoreCategoricalTermInspection
): CoreCategoricalTermInspection['dependentPrerequisites'] => {
    const result = [...inspection.dependentPrerequisites];
    for (const abstraction of inspection.abstractions) {
        for (const prerequisite of abstraction.dependentPrerequisites) {
            if (!result.includes(prerequisite)) {
                result.push(prerequisite);
            }
        }
    }
    return Object.freeze(result);
};

const groupedSequentialComparison = (
    id: string,
    result: CoreLfComparisonResult
): CoreCategoricalGroupedSequentialComparison => {
    if (result.status !== 'equal') {
        throw new Error(
            `Grouped/sequential comparison '${id}' did not close`
        );
    }
    return Object.freeze({
        id,
        status: 'equal' as const,
        steps: result.steps,
        ruleIds: Object.freeze(
            result.trace.flatMap(entry =>
                entry.reduction.kind === 'runtime'
                    ? [entry.reduction.ruleId]
                    : []
            )
        )
    });
};

/**
 * End-user construction scope for the reviewed categorical programs.
 *
 * The default retains the graduated ordinary/indexed-eta envelope. Explicit
 * root-only continuation profiles may add only their reviewed capabilities.
 */
export class CoreCategoricalProgram {
    private readonly programIdentity = Symbol('CoreCategoricalProgram');
    private readonly sourceFile: string;
    private readonly dependent:
        | CoreCategoricalDependentCompilation
        | CoreCategoricalDependentCompositionCompilation
        | CoreCategoricalComprehensionCompilation
        | CoreCategoricalFibredProductCompilation
        | CoreCategoricalFibredStructureCompilation
        | CoreCategoricalFibredBinderCompilation
        | CoreCategoricalFibredTransfdCompilation
        | CoreCategoricalFibredWeakenReindexCompilation
        | CoreCategoricalFibredDependentTargetCompilation;
    private readonly comprehensionEnabled: boolean;
    private readonly fibredProductEnabled: boolean;
    private readonly fibredStructureEnabled: boolean;
    private readonly fibredBinderEnabled: boolean;
    private readonly fibredTransfdEnabled: boolean;
    private readonly groupedSequentialEnabled: boolean;
    private readonly fibredWeakenReindexEnabled: boolean;
    private readonly fibredDependentTargetEnabled: boolean;
    private readonly builder: CoreCategoricalScopedBuilder;
    private environment: CoreLfDeclarationEnvironment;

    constructor(options: CoreCategoricalProgramOptions = {}) {
        this.sourceFile =
            options.sourceFile ?? '<categorical-program>';
        const profile =
            options.profile ?? 'reviewed-usability-2a1';
        this.comprehensionEnabled =
            profile === 'fibred-comprehension-1a' ||
            profile === 'fibred-product-1a' ||
            profile === 'fibred-structure-1a' ||
            profile === 'fibred-binder-1' ||
            profile === 'fibred-transfd-1' ||
            profile === 'fibred-grouped-sequential-1' ||
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.fibredProductEnabled =
            profile === 'fibred-product-1a' ||
            profile === 'fibred-structure-1a' ||
            profile === 'fibred-binder-1' ||
            profile === 'fibred-transfd-1' ||
            profile === 'fibred-grouped-sequential-1' ||
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.fibredStructureEnabled =
            profile === 'fibred-structure-1a' ||
            profile === 'fibred-binder-1' ||
            profile === 'fibred-transfd-1' ||
            profile === 'fibred-grouped-sequential-1' ||
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.fibredBinderEnabled =
            profile === 'fibred-binder-1' ||
            profile === 'fibred-transfd-1' ||
            profile === 'fibred-grouped-sequential-1' ||
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.fibredTransfdEnabled =
            profile === 'fibred-transfd-1' ||
            profile === 'fibred-grouped-sequential-1' ||
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.groupedSequentialEnabled =
            profile === 'fibred-grouped-sequential-1' ||
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.fibredWeakenReindexEnabled =
            profile === 'fibred-weaken-reindex-1' ||
            profile === 'fibred-dependent-target-1';
        this.fibredDependentTargetEnabled =
            profile === 'fibred-dependent-target-1';
        if (this.groupedSequentialEnabled) {
            validateCoreCategoricalGroupedSequentialContract();
        }
        if (this.fibredWeakenReindexEnabled) {
            validateCoreCategoricalFibredWeakenReindexContract();
        }
        if (this.fibredDependentTargetEnabled) {
            validateCoreCategoricalFibredDependentTargetContract();
        }
        this.dependent = this.fibredDependentTargetEnabled
            ? compileCoreCategoricalFibredDependentTargetTransfer()
            : this.fibredWeakenReindexEnabled
            ? compileCoreCategoricalFibredWeakenReindexTransfer()
            : this.fibredTransfdEnabled
            ? compileCoreCategoricalFibredTransfdTransfer()
            : this.fibredBinderEnabled
            ? compileCoreCategoricalFibredBinderTransfer()
            : this.fibredStructureEnabled
            ? compileCoreCategoricalFibredStructureTransfer()
            : this.fibredProductEnabled
            ? compileCoreCategoricalFibredProductTransfer()
            : this.comprehensionEnabled
            ? compileCoreCategoricalComprehensionTransfer()
            : profile === 'usability-dependent-1a'
                ? compileCoreCategoricalDependentCompositionTransfer()
                : compileCoreCategoricalDependentTransfer();
        this.environment = this.dependent.compiled.environment;
        this.builder = new CoreCategoricalScopedBuilder(
            this.at('categorical program'),
            {
                dependentSectionComposition:
                    profile !== 'reviewed-usability-2a1',
                displayedFunctorAbstraction:
                    this.fibredBinderEnabled,
                displayedTransforAbstraction:
                    this.fibredTransfdEnabled,
                displayedWeakeningReindexing:
                    this.fibredWeakenReindexEnabled
            }
        );
    }

    private at(
        fallbackDetail: string,
        site?: CoreCategoricalSourceSite
    ): Provenance {
        const line = site?.line ?? 1;
        const column = site?.column ?? 1;
        return provenance(
            'surface',
            site?.detail ?? fallbackDetail,
            sourceSpan(
                site?.file ?? this.sourceFile,
                line,
                column,
                site?.endLine ?? line,
                site?.endColumn ?? column + 1
            )
        );
    }

    private requireCategory(
        value: CoreCategoricalCategory,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalCategory {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreCategoricalCategory)[
                CORE_CATEGORICAL_CATEGORY
            ] !== true ||
            (value as InternalCoreCategoricalCategory).programIdentity !==
                this.programIdentity
        ) {
            throw new CoreCategoricalProgramError(
                'FOREIGN_CATEGORY',
                nodeProvenance,
                'Categorical category belongs to another program'
            );
        }
        return value as InternalCoreCategoricalCategory;
    }

    private makeCategory(
        label: string,
        expression: KernelExpression
    ): CoreCategoricalCategory {
        return Object.freeze({
            [CORE_CATEGORICAL_CATEGORY]: true as const,
            programIdentity: this.programIdentity,
            label,
            expression
        });
    }

    private requireDisplayedFamily(
        value: CoreCategoricalDisplayedFamily,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalDisplayedFamily {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreCategoricalDisplayedFamily)[
                CORE_CATEGORICAL_DISPLAYED_FAMILY
            ] !== true ||
            (value as InternalCoreCategoricalDisplayedFamily)
                .programIdentity !== this.programIdentity
        ) {
            throw new CoreCategoricalProgramError(
                'FOREIGN_DISPLAYED_FAMILY',
                nodeProvenance,
                'Displayed family belongs to another program'
            );
        }
        return value as InternalCoreCategoricalDisplayedFamily;
    }

    private makeDisplayedFamily(
        label: string,
        baseCategory: InternalCoreCategoricalCategory,
        expression: KernelExpression,
        groupedProduct?: {
            readonly left: InternalCoreCategoricalDisplayedFamily;
            readonly right: InternalCoreCategoricalDisplayedFamily;
        }
    ): CoreCategoricalDisplayedFamily {
        return Object.freeze({
            [CORE_CATEGORICAL_DISPLAYED_FAMILY]: true as const,
            programIdentity: this.programIdentity,
            label,
            baseCategory,
            expression,
            groupedProduct: groupedProduct === undefined
                ? undefined
                : Object.freeze({ ...groupedProduct })
        });
    }

    private requireComprehension(
        nodeProvenance: Provenance
    ): void {
        if (!this.comprehensionEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_COMPREHENSION',
                nodeProvenance,
                'Fibred comprehension is available only in the explicit ' +
                "'fibred-comprehension-1a' root profile"
            );
        }
    }

    private requireFibredProduct(
        nodeProvenance: Provenance
    ): void {
        if (!this.fibredProductEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_FIBRED_PRODUCT',
                nodeProvenance,
                'Fibrewise family products are available only in the ' +
                "explicit 'fibred-product-1a' or " +
                "'fibred-structure-1a' root profile"
            );
        }
    }

    private requireFibredStructure(
        nodeProvenance: Provenance
    ): void {
        if (!this.fibredStructureEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_FIBRED_STRUCTURE',
                nodeProvenance,
                'Fibrewise displayed projections and pairing are ' +
                "available only in the explicit 'fibred-structure-1a' " +
                'root profile'
            );
        }
    }

    private requireFibredBinder(
        nodeProvenance: Provenance
    ): void {
        if (!this.fibredBinderEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_FIBRED_BINDER',
                nodeProvenance,
                'Direct displayed-functor abstraction is available only ' +
                "in the explicit 'fibred-binder-1' root profile"
            );
        }
    }

    private requireFibredTransfd(
        nodeProvenance: Provenance
    ): void {
        if (!this.fibredTransfdEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_FIBRED_TRANSFD',
                nodeProvenance,
                'Direct displayed-transfor abstraction and higher cells ' +
                "are available only in the explicit 'fibred-transfd-1' " +
                'root profile'
            );
        }
    }

    private requireGroupedSequential(
        nodeProvenance: Provenance
    ): void {
        if (!this.groupedSequentialEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_GROUPED_SEQUENTIAL',
                nodeProvenance,
                'Dependency-directed sequential/grouped contexts are ' +
                'available only in the explicit ' +
                "'fibred-grouped-sequential-1' root profile"
            );
        }
    }

    private requireFibredWeakenReindex(
        nodeProvenance: Provenance
    ): void {
        if (!this.fibredWeakenReindexEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_WEAKEN_REINDEX',
                nodeProvenance,
                'Contextual displayed weakening and displayed-functor ' +
                    'reindexing are available only in the explicit ' +
                    "'fibred-weaken-reindex-1' root profile"
            );
        }
    }

    private requireFibredDependentTarget(
        nodeProvenance: Provenance
    ): void {
        if (!this.fibredDependentTargetEnabled) {
            throw new CoreCategoricalProgramError(
                'UNAVAILABLE_DEPENDENT_TARGET',
                nodeProvenance,
                'Contravariant category families and their dependent ' +
                    'section targets are available only in the explicit ' +
                    "'fibred-dependent-target-1' root profile"
            );
        }
    }

    private requireGroupedSequentialContext(
        value: CoreCategoricalGroupedSequentialContext,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalGroupedSequentialContext {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreCategoricalGroupedSequentialContext)[
                CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTEXT
            ] !== true ||
            (value as InternalCoreCategoricalGroupedSequentialContext)
                .programIdentity !== this.programIdentity
        ) {
            throw new CoreCategoricalProgramError(
                'INVALID_GROUPED_SEQUENTIAL_CONTEXT',
                nodeProvenance,
                'Grouped/sequential context belongs to another program'
            );
        }
        return value as InternalCoreCategoricalGroupedSequentialContext;
    }

    private makeTerm(
        expression: KernelExpression,
        type: CoreType,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        return this.builder.fromElaborated({
            term: expression,
            type,
            sourceSpan: nodeProvenance.span as SourceSpan,
            recovered: Object.freeze([])
        });
    }

    private functorCategoryExpression(
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalStructuralSymbolCoreName(
                    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS
                        .functorCategory
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

    private productCategoryExpression(
        leftCategory: KernelExpression,
        rightCategory: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName(
                    'product-category'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'explicit',
                    value: leftCategory
                },
                {
                    plicity: 'explicit',
                    value: rightCategory
                }
            ],
            nodeProvenance
        );
    }

    private displayedFunctorCategoryExpression(
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
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'explicit',
                    value: sourceFamily
                },
                {
                    plicity: 'explicit',
                    value: targetFamily
                }
            ],
            nodeProvenance
        );
    }

    private displayedTransforCategoryExpression(
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
                {
                    plicity: 'implicit',
                    value: baseCategory
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
                    value: sourceFunctor
                },
                {
                    plicity: 'explicit',
                    value: targetFunctor
                }
            ],
            nodeProvenance
        );
    }

    private displayedProductExpression(
        base: KernelExpression,
        left: KernelExpression,
        right: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const cat = kernelApplication(
            'category-of-categories',
            [],
            nodeProvenance
        );
        const catProduct = this.productCategoryExpression(
            cat,
            cat,
            nodeProvenance
        );
        const catEndofunctors = this.functorCategoryExpression(
            cat,
            cat,
            nodeProvenance
        );
        const uncurryPackage = kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName(
                    'uncurry-package'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: cat },
                { plicity: 'implicit', value: cat },
                { plicity: 'implicit', value: cat }
            ],
            nodeProvenance
        );
        const uncurriedProduct = kernelApplication(
            'functor-object',
            [
                {
                    value: this.functorCategoryExpression(
                        cat,
                        catEndofunctors,
                        nodeProvenance
                    )
                },
                {
                    value: this.functorCategoryExpression(
                        catProduct,
                        cat,
                        nodeProvenance
                    )
                },
                { value: uncurryPackage },
                {
                    value: kernelFree(
                        coreCategoricalFibredProductCoreName(
                            'internal-product-functor'
                        ),
                        nodeProvenance
                    )
                }
            ],
            nodeProvenance
        );
        const familyCategory = this.functorCategoryExpression(
            base,
            cat,
            nodeProvenance
        );
        const pairedFamilies = kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName(
                    'product-pair'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: familyCategory
                },
                {
                    plicity: 'implicit',
                    value: familyCategory
                },
                {
                    plicity: 'explicit',
                    value: left
                },
                {
                    plicity: 'explicit',
                    value: right
                }
            ],
            nodeProvenance
        );
        return kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName(
                    'functor-composition'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: base },
                {
                    plicity: 'implicit',
                    value: catProduct
                },
                { plicity: 'implicit', value: cat },
                {
                    plicity: 'explicit',
                    value: uncurriedProduct
                },
                {
                    plicity: 'explicit',
                    value: pairedFamilies
                }
            ],
            nodeProvenance
        );
    }

    private displayedPullbackExpression(
        sourceCategory: KernelExpression,
        targetCategory: KernelExpression,
        family: KernelExpression,
        substitution: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'displayed-pullback',
            [
                { value: sourceCategory },
                { value: targetCategory },
                { value: family },
                { value: substitution }
            ],
            nodeProvenance
        );
    }

    private reindexDisplayedFamily(
        family: InternalCoreCategoricalDisplayedFamily,
        sourceBase: InternalCoreCategoricalCategory,
        targetCategory: KernelExpression,
        substitution: KernelExpression,
        nodeProvenance: Provenance
    ): InternalCoreCategoricalDisplayedFamily {
        if (
            this.fibredStructureEnabled &&
            family.groupedProduct !== undefined
        ) {
            const left = this.reindexDisplayedFamily(
                family.groupedProduct.left,
                sourceBase,
                targetCategory,
                substitution,
                nodeProvenance
            );
            const right = this.reindexDisplayedFamily(
                family.groupedProduct.right,
                sourceBase,
                targetCategory,
                substitution,
                nodeProvenance
            );
            return this.makeDisplayedFamily(
                `${family.label}[substitution]`,
                sourceBase,
                this.displayedProductExpression(
                    sourceBase.expression,
                    left.expression,
                    right.expression,
                    nodeProvenance
                ),
                { left, right }
            ) as InternalCoreCategoricalDisplayedFamily;
        }
        return this.makeDisplayedFamily(
            `${family.label}[substitution]`,
            sourceBase,
            this.displayedPullbackExpression(
                sourceBase.expression,
                targetCategory,
                family.expression,
                substitution,
                nodeProvenance
            )
        ) as InternalCoreCategoricalDisplayedFamily;
    }

    private fibreCategoryOfExpression(
        baseCategory: KernelExpression,
        family: KernelExpression,
        point: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'functor-object',
            [
                { value: baseCategory },
                {
                    value: kernelApplication(
                        'category-of-categories',
                        [],
                        nodeProvenance
                    )
                },
                { value: family },
                { value: point }
            ],
            nodeProvenance
        );
    }

    private fibreCategoryExpression(
        family: InternalCoreCategoricalDisplayedFamily,
        point: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return this.fibreCategoryOfExpression(
            family.baseCategory.expression,
            family.expression,
            point,
            nodeProvenance
        );
    }

    private totalCategoryExpression(
        family: InternalCoreCategoricalDisplayedFamily,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: family.baseCategory.expression
                },
                {
                    plicity: 'explicit',
                    value: family.expression
                }
            ],
            nodeProvenance
        );
    }

    private oppositeCategoryExpression(
        categoryValue: KernelExpression,
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
                value: categoryValue
            }],
            nodeProvenance
        );
    }

    private categoryOfCategoriesExpression(
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'category-of-categories',
            [],
            nodeProvenance
        );
    }

    private dependentSectionMotiveExpression(
        baseCategory: KernelExpression,
        contravariantFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const categoryOfCategories =
            this.categoryOfCategoriesExpression(nodeProvenance);
        return this.displayedPullbackExpression(
            baseCategory,
            this.oppositeCategoryExpression(
                categoryOfCategories,
                nodeProvenance
            ),
            kernelFree(
                CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                    .displayedCategoryFunctor,
                nodeProvenance
            ),
            contravariantFamily,
            nodeProvenance
        );
    }

    private dependentSectionPackageExpression(
        baseCategory: KernelExpression,
        contravariantFamily: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                    .pullbackPi,
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: baseCategory
                },
                {
                    plicity: 'explicit',
                    value: contravariantFamily
                }
            ],
            nodeProvenance
        );
    }

    private dependentPairExpression(
        family: InternalCoreCategoricalDisplayedFamily,
        first: KernelExpression,
        second: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        const base = family.baseCategory.expression;
        const binderType = coreTypeToKernelType(
            {
                tag: 'object',
                category: base
            },
            nodeProvenance.span as SourceSpan,
            'dependent-pair base classifier'
        );
        const point = kernelBound(0, nodeProvenance);
        const fibreClassifier = kernelApplication(
            'object-classifier',
            [{
                value: this.fibreCategoryExpression(
                    family,
                    point,
                    nodeProvenance
                )
            }],
            nodeProvenance
        );
        return kernelCall(
            kernelFree(
                CORE_DIRECTED_1B_PRIMITIVE_NAMES['dependent-pair'],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: kernelApplication(
                        'object-classifier',
                        [{ value: base }],
                        nodeProvenance
                    )
                },
                {
                    plicity: 'implicit',
                    value: kernelLambda(
                        kernelBinder(
                            'pairPoint',
                            binderType,
                            explicitFunctorial,
                            nodeProvenance
                        ),
                        fibreClassifier,
                        nodeProvenance
                    )
                },
                { plicity: 'explicit', value: first },
                { plicity: 'explicit', value: second }
            ],
            nodeProvenance
        );
    }

    private productObjectPairExpression(
        leftCategory: KernelExpression,
        rightCategory: KernelExpression,
        left: KernelExpression,
        right: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName('product-pair'),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: leftCategory
                },
                {
                    plicity: 'implicit',
                    value: rightCategory
                },
                { plicity: 'explicit', value: left },
                { plicity: 'explicit', value: right }
            ],
            nodeProvenance
        );
    }

    private requireObjectTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly expression: KernelExpression;
        readonly category: KernelExpression;
    } {
        const inspection = this.builder.inspect(value);
        if (inspection.type.tag !== 'object') {
            throw new CoreCategoricalProgramError(
                'EXPECTED_CATEGORY_OBJECT',
                nodeProvenance,
                `${detail} must be a closed category object`
            );
        }
        return {
            expression: this.builder.compile(value).term,
            category: inspection.type.category
        };
    }

    private requireFunctorTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly expression: KernelExpression;
        readonly sourceCategory: KernelExpression;
        readonly targetCategory: KernelExpression;
    } {
        const inspection = this.builder.inspect(value);
        if (inspection.type.tag !== 'functor') {
            throw new CoreCategoricalProgramError(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                `${detail} must be an ordinary functor`
            );
        }
        return {
            expression: this.builder.compile(value).term,
            sourceCategory: inspection.type.sourceCategory,
            targetCategory: inspection.type.targetCategory
        };
    }

    private requireContravariantCategoryFamilyTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly expression: KernelExpression;
        readonly baseCategory: KernelExpression;
        readonly targetCategory: KernelExpression;
    } {
        this.requireFibredDependentTarget(nodeProvenance);
        const family = this.requireFunctorTerm(
            value,
            nodeProvenance,
            detail
        );
        const expectedTarget = this.oppositeCategoryExpression(
            this.categoryOfCategoriesExpression(nodeProvenance),
            nodeProvenance
        );
        if (!kernelExpressionEquals(
            family.targetCategory,
            expectedTarget
        )) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                `${detail} must target Op(Cat_cat)`
            );
        }
        return Object.freeze({
            expression: family.expression,
            baseCategory: family.sourceCategory,
            targetCategory: family.targetCategory
        });
    }

    private requireDisplayedFunctorTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly expression: KernelExpression;
        readonly baseCategory: KernelExpression;
        readonly sourceFamily: KernelExpression;
        readonly targetFamily: KernelExpression;
    } {
        const inspection = this.builder.inspect(value);
        if (inspection.type.tag !== 'displayed-functor') {
            throw new CoreCategoricalProgramError(
                'EXPECTED_DISPLAYED_FUNCTOR',
                nodeProvenance,
                `${detail} must be a displayed functor`
            );
        }
        return {
            expression: this.builder.compile(value).term,
            baseCategory: inspection.type.baseCategory,
            sourceFamily: inspection.type.sourceFamily,
            targetFamily: inspection.type.targetFamily
        };
    }

    private requireDisplayedTransforTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly expression: KernelExpression;
        readonly category: KernelExpression;
        readonly baseCategory: KernelExpression;
        readonly sourceFamily: KernelExpression;
        readonly targetFamily: KernelExpression;
        readonly sourceFunctor: KernelExpression;
        readonly targetFunctor: KernelExpression;
    } {
        const inspection = this.builder.inspect(value);
        if (inspection.type.tag !== 'displayed-transfor') {
            throw new CoreCategoricalProgramError(
                'EXPECTED_DISPLAYED_TRANSFOR',
                nodeProvenance,
                `${detail} must be a displayed transformation`
            );
        }
        return {
            expression: this.builder.compile(value).term,
            category: inspection.type.category,
            baseCategory: inspection.type.baseCategory,
            sourceFamily: inspection.type.sourceFamily,
            targetFamily: inspection.type.targetFamily,
            sourceFunctor: inspection.type.sourceFunctor,
            targetFunctor: inspection.type.targetFunctor
        };
    }

    private requireHomTerm(
        value: CoreCategoricalTerm,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly expression: KernelExpression;
        readonly category: KernelExpression;
        readonly sourceObject: KernelExpression;
        readonly targetObject: KernelExpression;
    } {
        const inspection = this.builder.inspect(value);
        if (inspection.type.tag !== 'hom') {
            throw new CoreCategoricalProgramError(
                'EXPECTED_HOM',
                nodeProvenance,
                `${detail} must be a closed category arrow`
            );
        }
        return {
            expression: this.builder.compile(value).term,
            category: inspection.type.category,
            sourceObject: inspection.type.sourceObject,
            targetObject: inspection.type.targetObject
        };
    }

    private requireSameCategory(
        actual: KernelExpression,
        expected: KernelExpression,
        nodeProvenance: Provenance,
        detail: string
    ): void {
        if (!coreObjectCategoryEquals(actual, expected)) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_CATEGORY_OBJECT',
                nodeProvenance,
                `${detail} belongs to the wrong category`
            );
        }
    }

    private convertObjectToCategory(
        value: CoreCategoricalTerm,
        expectedCategory: KernelExpression,
        nodeProvenance: Provenance,
        detail: string
    ): {
        readonly term: CoreCategoricalTerm;
        readonly comparison: CoreLfComparisonResult;
    } {
        const actual = this.requireObjectTerm(
            value,
            nodeProvenance,
            detail
        );
        const runtime = 'composedRuntime' in this.dependent
            ? this.dependent.composedRuntime
            : this.dependent.structural.composedRuntime;
        const comparison = coreLfDefinitionalCompare(
            this.environment,
            actual.category,
            expectedCategory,
            4_000,
            undefined,
            runtime
        );
        if (comparison.status !== 'equal') {
            throw new CoreCategoricalProgramError(
                'EXPECTED_CATEGORY_OBJECT',
                nodeProvenance,
                `${detail} belongs to a category that does not convert ` +
                'to the dependency-directed expected fibre'
            );
        }
        return Object.freeze({
            term: this.makeTerm(
                actual.expression,
                {
                    tag: 'object',
                    category: expectedCategory
                },
                nodeProvenance
            ),
            comparison
        });
    }

    private assume(
        name: string,
        type: CoreType,
        nodeProvenance: Provenance
    ): CoreCategoricalTerm {
        const span = nodeProvenance.span as SourceSpan;
        const kernelType = coreTypeToKernelType(
            type,
            span,
            `categorical program assumption ${name}`
        );
        this.environment = this.environment.extend({
            name,
            type: kernelType,
            mode: explicitFunctorial,
            provenance: nodeProvenance
        });
        const elaborated: ElaboratedSurfaceTerm = {
            term: kernelFree(name, nodeProvenance),
            type,
            sourceSpan: span,
            recovered: Object.freeze([])
        };
        return this.builder.fromElaborated(elaborated);
    }

    category(
        name: string,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalCategory {
        const nodeProvenance = this.at(
            `category assumption ${name}`,
            source
        );
        this.environment = this.environment.extend({
            name,
            type: kernelApplication(
                'category-universe',
                [],
                nodeProvenance
            ),
            mode: explicitFunctorial,
            provenance: nodeProvenance
        });
        return this.makeCategory(
            name,
            kernelFree(name, nodeProvenance)
        );
    }

    displayedFamily(
        name: string,
        baseValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalDisplayedFamily {
        const nodeProvenance = this.at(
            `displayed family assumption ${name}`,
            source
        );
        const baseCategory = this.requireCategory(
            baseValue,
            nodeProvenance
        );
        this.environment = this.environment.extend({
            name,
            type: coreDisplayedFamilyType(
                baseCategory.expression,
                nodeProvenance
            ),
            mode: explicitFunctorial,
            provenance: nodeProvenance
        });
        return this.makeDisplayedFamily(
            name,
            baseCategory,
            kernelFree(name, nodeProvenance)
        );
    }

    /**
     * Assume a category-valued contravariant family
     * `G : Functor(K,Op(Cat_cat))`.
     */
    contravariantCategoryFamily(
        name: string,
        baseValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `contravariant category family assumption ${name}`,
            source
        );
        this.requireFibredDependentTarget(nodeProvenance);
        const base = this.requireCategory(
            baseValue,
            nodeProvenance
        );
        const target = this.oppositeCategoryExpression(
            this.categoryOfCategoriesExpression(nodeProvenance),
            nodeProvenance
        );
        return this.assume(name, {
            tag: 'functor',
            sourceCategory: base.expression,
            targetCategory: target
        }, nodeProvenance);
    }

    /**
     * Pull back the internal displayed-category family along
     * `G : K -> Op(Cat_cat)`.
     *
     * The fibre at `k` is the displayed-family category over `G[k]`.
     */
    dependentSectionMotive(
        contravariantFamilyValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalDisplayedFamily {
        const nodeProvenance = this.at(
            'dependent section motive family',
            source
        );
        const family = this.requireContravariantCategoryFamilyTerm(
            contravariantFamilyValue,
            nodeProvenance,
            'Dependent section motive input'
        );
        const base = this.makeCategory(
            'source(dependent-section-motive)',
            family.baseCategory
        ) as InternalCoreCategoricalCategory;
        return this.makeDisplayedFamily(
            'Pullback(Catd_cat_func,G)',
            base,
            this.dependentSectionMotiveExpression(
                family.baseCategory,
                family.expression,
                nodeProvenance
            )
        );
    }

    /**
     * Form the Cat-valued family over the explicit total context
     * `Sigma(K,Pullback(Catd_cat_func,G))`.
     *
     * Its fibre at `(k,M)` computes to `Pi_cat(G[k],M)`.
     */
    dependentSectionTarget(
        contravariantFamilyValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalDisplayedFamily {
        const nodeProvenance = this.at(
            'dependent section total-context target',
            source
        );
        const family = this.requireContravariantCategoryFamilyTerm(
            contravariantFamilyValue,
            nodeProvenance,
            'Dependent section target input'
        );
        const base = this.makeCategory(
            'source(dependent-section-target)',
            family.baseCategory
        ) as InternalCoreCategoricalCategory;
        const motive = this.makeDisplayedFamily(
            'Pullback(Catd_cat_func,G)',
            base,
            this.dependentSectionMotiveExpression(
                family.baseCategory,
                family.expression,
                nodeProvenance
            )
        ) as InternalCoreCategoricalDisplayedFamily;
        const total = this.makeCategory(
            'Sigma(Pullback(Catd_cat_func,G))',
            this.totalCategoryExpression(motive, nodeProvenance)
        ) as InternalCoreCategoricalCategory;
        return this.makeDisplayedFamily(
            'Sigma(Pi_pullback_funcd(G))',
            total,
            kernelCall(
                kernelFree(
                    CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                        'sigma-telescope-family'
                    ],
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: family.baseCategory
                    },
                    {
                        plicity: 'implicit',
                        value: motive.expression
                    },
                    {
                        plicity: 'explicit',
                        value:
                            this.dependentSectionPackageExpression(
                                family.baseCategory,
                                family.expression,
                                nodeProvenance
                            )
                    }
                ],
                nodeProvenance
            )
        );
    }

    /**
     * Expected normal form of the dependent target fibre at `(k,M)`.
     *
     * This helper validates the same motive indices as `dependentPair`; it
     * does not synthesize a section or add an equality.
     */
    dependentSectionCategoryAt(
        contravariantFamilyValue: CoreCategoricalTerm,
        pointValue: CoreCategoricalTerm,
        displayedFamilyValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalCategory {
        const nodeProvenance = this.at(
            'dependent section target fibre normal form',
            source
        );
        const family = this.requireContravariantCategoryFamilyTerm(
            contravariantFamilyValue,
            nodeProvenance,
            'Dependent section fibre family'
        );
        const point = this.requireObjectTerm(
            pointValue,
            nodeProvenance,
            'Dependent section fibre base point'
        );
        this.requireSameCategory(
            point.category,
            family.baseCategory,
            nodeProvenance,
            'Dependent section fibre base point'
        );
        const motive = this.dependentSectionMotiveExpression(
            family.baseCategory,
            family.expression,
            nodeProvenance
        );
        const displayedFamily = this.requireObjectTerm(
            displayedFamilyValue,
            nodeProvenance,
            'Dependent section fibre displayed family'
        );
        this.requireSameCategory(
            displayedFamily.category,
            this.fibreCategoryOfExpression(
                family.baseCategory,
                motive,
                point.expression,
                nodeProvenance
            ),
            nodeProvenance,
            'Dependent section fibre displayed family'
        );
        const categoryAtPoint = kernelApplication(
            'functor-object',
            [
                { value: family.baseCategory },
                { value: family.targetCategory },
                { value: family.expression },
                { value: point.expression }
            ],
            nodeProvenance
        );
        return this.makeCategory(
            'Pi(G[k],M)',
            coreSectionCategory(
                categoryAtPoint,
                displayedFamily.expression,
                nodeProvenance
            )
        );
    }

    /**
     * Product of two independent displayed siblings over the same base.
     *
     * This emits the active transparent semantic construction directly:
     *
     *   uncurry(Product_cat_func) o Product_pair(B,C).
     *
     * There is intentionally no `Product_catd` Core owner.
     */
    displayedProduct(
        leftValue: CoreCategoricalDisplayedFamily,
        rightValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalDisplayedFamily {
        const nodeProvenance = this.at(
            'fibrewise product of displayed siblings',
            source
        );
        this.requireFibredProduct(nodeProvenance);
        const left = this.requireDisplayedFamily(
            leftValue,
            nodeProvenance
        );
        const right = this.requireDisplayedFamily(
            rightValue,
            nodeProvenance
        );
        if (!kernelExpressionEquals(
            left.baseCategory.expression,
            right.baseCategory.expression
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Displayed product factors must have the same base category'
            );
        }

        return this.makeDisplayedFamily(
            `Productd(${left.label},${right.label})`,
            left.baseCategory,
            this.displayedProductExpression(
                left.baseCategory.expression,
                left.expression,
                right.expression,
                nodeProvenance
            ),
            { left, right }
        );
    }

    private displayedProductProjection(
        side: 'left' | 'right',
        leftValue: CoreCategoricalDisplayedFamily,
        rightValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `fibrewise product ${side} projection`,
            source
        );
        this.requireFibredStructure(nodeProvenance);
        const left = this.requireDisplayedFamily(
            leftValue,
            nodeProvenance
        );
        const right = this.requireDisplayedFamily(
            rightValue,
            nodeProvenance
        );
        if (!kernelExpressionEquals(
            left.baseCategory.expression,
            right.baseCategory.expression
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Displayed projection factors must have the same base'
            );
        }
        const base = left.baseCategory.expression;
        const product = this.displayedProductExpression(
            base,
            left.expression,
            right.expression,
            nodeProvenance
        );
        const target = side === 'left'
            ? left.expression
            : right.expression;
        const expression = kernelCall(
            kernelFree(
                coreCategoricalFibredStructureCoreName(
                    side === 'left'
                        ? 'displayed-product-left-projection'
                        : 'displayed-product-right-projection'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: base },
                {
                    plicity: 'explicit',
                    value: left.expression
                },
                {
                    plicity: 'explicit',
                    value: right.expression
                }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            expression,
            {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategoryExpression(
                    base,
                    product,
                    target,
                    nodeProvenance
                ),
                baseCategory: base,
                sourceFamily: product,
                targetFamily: target
            },
            nodeProvenance
        );
    }

    displayedProductLeftProjection(
        leftValue: CoreCategoricalDisplayedFamily,
        rightValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        return this.displayedProductProjection(
            'left',
            leftValue,
            rightValue,
            source
        );
    }

    displayedProductRightProjection(
        leftValue: CoreCategoricalDisplayedFamily,
        rightValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        return this.displayedProductProjection(
            'right',
            leftValue,
            rightValue,
            source
        );
    }

    /**
     * Pair two displayed functors with one literal shared source family.
     */
    displayedProductPair(
        leftValue: CoreCategoricalTerm,
        rightValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'fibrewise displayed-functor pairing',
            source
        );
        this.requireFibredStructure(nodeProvenance);
        const left = this.requireDisplayedFunctorTerm(
            leftValue,
            nodeProvenance,
            'Left displayed-pair component'
        );
        const right = this.requireDisplayedFunctorTerm(
            rightValue,
            nodeProvenance,
            'Right displayed-pair component'
        );
        if (!kernelExpressionEquals(
            left.baseCategory,
            right.baseCategory
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Displayed-pair components must have the same base'
            );
        }
        if (!kernelExpressionEquals(
            left.sourceFamily,
            right.sourceFamily
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_SOURCE_MISMATCH',
                nodeProvenance,
                'Displayed-pair components must have one literal shared ' +
                'source family'
            );
        }
        const target = this.displayedProductExpression(
            left.baseCategory,
            left.targetFamily,
            right.targetFamily,
            nodeProvenance
        );
        const expression = kernelCall(
            kernelFree(
                coreCategoricalFibredStructureCoreName(
                    'displayed-product-pair'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: left.baseCategory
                },
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
                {
                    plicity: 'explicit',
                    value: left.expression
                },
                {
                    plicity: 'explicit',
                    value: right.expression
                }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            expression,
            {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategoryExpression(
                    left.baseCategory,
                    left.sourceFamily,
                    target,
                    nodeProvenance
                ),
                baseCategory: left.baseCategory,
                sourceFamily: left.sourceFamily,
                targetFamily: target
            },
            nodeProvenance
        );
    }

    /**
     * Transparent exchange of two independent displayed siblings.
     */
    displayedProductSwap(
        leftValue: CoreCategoricalDisplayedFamily,
        rightValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const right = this.displayedProductRightProjection(
            leftValue,
            rightValue,
            source
        );
        const left = this.displayedProductLeftProjection(
            leftValue,
            rightValue,
            source
        );
        return this.displayedProductPair(right, left, source);
    }

    /**
     * Transparent contraction into two copies of one displayed family.
     */
    displayedProductDiagonal(
        familyValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'fibrewise displayed diagonal',
            source
        );
        this.requireFibredStructure(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const base = family.baseCategory.expression;
        const identity = kernelCall(
            kernelFree(
                coreCategoricalFibredStructureCoreName(
                    'displayed-identity'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: base },
                {
                    plicity: 'implicit',
                    value: family.expression
                }
            ],
            nodeProvenance
        );
        const target = this.displayedProductExpression(
            base,
            family.expression,
            family.expression,
            nodeProvenance
        );
        const expression = kernelCall(
            kernelFree(
                coreCategoricalFibredStructureCoreName(
                    'displayed-product-pair'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: base },
                {
                    plicity: 'implicit',
                    value: family.expression
                },
                {
                    plicity: 'implicit',
                    value: family.expression
                },
                {
                    plicity: 'implicit',
                    value: family.expression
                },
                { plicity: 'explicit', value: identity },
                { plicity: 'explicit', value: identity }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            expression,
            {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategoryExpression(
                    base,
                    family.expression,
                    target,
                    nodeProvenance
                ),
                baseCategory: base,
                sourceFamily: family.expression,
                targetFamily: target
            },
            nodeProvenance
        );
    }

    /**
     * Expose the iterable off-diagonal action of a displayed functor.
     *
     * This is intentionally profile-gated: earlier frozen profiles retain
     * their component-only surface, while FIBRED-STRUCTURE-1A can exercise
     * the approved `tapp1_func` rules and their next-cell action.
     */
    displayedFunctorFullAction(
        displayedFunctorValue: CoreCategoricalTerm,
        sourcePointValue: CoreCategoricalTerm,
        targetPointValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'full displayed-functor base action',
            source
        );
        this.requireFibredStructure(nodeProvenance);
        const displayedFunctor = this.requireDisplayedFunctorTerm(
            displayedFunctorValue,
            nodeProvenance,
            'Full displayed action subject'
        );
        const sourcePoint = this.requireObjectTerm(
            sourcePointValue,
            nodeProvenance,
            'Full displayed action source point'
        );
        const targetPoint = this.requireObjectTerm(
            targetPointValue,
            nodeProvenance,
            'Full displayed action target point'
        );
        this.requireSameCategory(
            sourcePoint.category,
            displayedFunctor.baseCategory,
            nodeProvenance,
            'Full displayed action source point'
        );
        this.requireSameCategory(
            targetPoint.category,
            displayedFunctor.baseCategory,
            nodeProvenance,
            'Full displayed action target point'
        );
        const sourceHom = kernelApplication(
            'hom-category',
            [
                { value: displayedFunctor.baseCategory },
                { value: sourcePoint.expression },
                { value: targetPoint.expression }
            ],
            nodeProvenance
        );
        const sourceFibre = this.fibreCategoryOfExpression(
            displayedFunctor.baseCategory,
            displayedFunctor.sourceFamily,
            sourcePoint.expression,
            nodeProvenance
        );
        const targetFibre = this.fibreCategoryOfExpression(
            displayedFunctor.baseCategory,
            displayedFunctor.targetFamily,
            targetPoint.expression,
            nodeProvenance
        );
        return this.makeTerm(
            kernelApplication(
                'transfor-hom-full',
                [
                    { value: displayedFunctor.baseCategory },
                    {
                        value: kernelApplication(
                            'category-of-categories',
                            [],
                            nodeProvenance
                        )
                    },
                    { value: displayedFunctor.sourceFamily },
                    { value: displayedFunctor.targetFamily },
                    { value: sourcePoint.expression },
                    { value: targetPoint.expression },
                    { value: displayedFunctor.expression }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: sourceHom,
                targetCategory: this.functorCategoryExpression(
                    sourceFibre,
                    targetFibre,
                    nodeProvenance
                )
            },
            nodeProvenance
        );
    }

    fibre(
        familyValue: CoreCategoricalDisplayedFamily,
        point: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalCategory {
        const nodeProvenance = this.at(
            'displayed fibre category',
            source
        );
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const pointInspection = this.builder.inspect(point);
        if (
            pointInspection.type.tag === 'indexed-object' ||
            pointInspection.type.tag === 'indexed-functor' ||
            pointInspection.type.tag === 'indexed-transfor'
        ) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_CATEGORY_OBJECT',
                nodeProvenance,
                `Fibre point for displayed family '${family.label}' is an ` +
                'open indexed object, not a closed base object'
            );
        }
        const pointCategory = coreTypeObjectCategory(
            pointInspection.type,
            nodeProvenance.span as SourceSpan,
            `fibre point for displayed family '${family.label}'`
        );
        if (
            pointCategory === undefined ||
            !coreObjectCategoryEquals(
                pointCategory,
                family.baseCategory.expression
            )
        ) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_CATEGORY_OBJECT',
                nodeProvenance,
                `Fibre point for displayed family '${family.label}' is ` +
                `not an object of base category ` +
                `'${family.baseCategory.label}'`
            );
        }
        const pointExpression = this.builder.compile(point).term;
        return this.makeCategory(
            `${family.label}[point]`,
            this.fibreCategoryExpression(
                family,
                pointExpression,
                nodeProvenance
            )
        );
    }

    totalCategory(
        familyValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalCategory {
        const nodeProvenance = this.at(
            'Sigma total category',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        return this.makeCategory(
            `Sigma(${family.label})`,
            this.totalCategoryExpression(family, nodeProvenance)
        );
    }

    sigmaProjection(
        familyValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'Sigma first projection',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    CORE_DIRECTED_1B_PRIMITIVE_NAMES[
                        'sigma-first-projection'
                    ],
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: family.baseCategory.expression
                    },
                    {
                        plicity: 'explicit',
                        value: family.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory:
                    this.totalCategoryExpression(
                        family,
                        nodeProvenance
                    ),
                targetCategory: family.baseCategory.expression
            },
            nodeProvenance
        );
    }

    groupedSequentialContext(
        baseName: string,
        baseValue: CoreCategoricalCategory,
        bindingValues:
            readonly CoreCategoricalGroupedSequentialBinding[],
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalGroupedSequentialContext {
        const nodeProvenance = this.at(
            'dependency-directed grouped/sequential context',
            source
        );
        this.requireGroupedSequential(nodeProvenance);
        if (
            bindingValues.length <
                CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
                    .input.minimumSiblingCount
        ) {
            throw new CoreCategoricalProgramError(
                'INVALID_GROUPED_SEQUENTIAL_CONTEXT',
                nodeProvenance,
                'A grouped/sequential context requires at least two ' +
                'displayed sibling bindings'
            );
        }
        const base = this.requireCategory(
            baseValue,
            nodeProvenance
        );
        const names = new Set<string>([baseName]);
        const siblings = bindingValues.map((binding, offset) => {
            if (names.has(binding.name)) {
                throw new CoreCategoricalProgramError(
                    'INVALID_GROUPED_SEQUENTIAL_CONTEXT',
                    nodeProvenance,
                    `Duplicate contextual binding name '${binding.name}'`
                );
            }
            names.add(binding.name);
            const family = this.requireDisplayedFamily(
                binding.family,
                nodeProvenance
            );
            if (!kernelExpressionEquals(
                family.baseCategory.expression,
                base.expression
            )) {
                throw new CoreCategoricalProgramError(
                    'DISPLAYED_BASE_MISMATCH',
                    nodeProvenance,
                    `Displayed sibling '${binding.name}' is not over ` +
                    `base category '${base.label}'`
                );
            }
            return Object.freeze({
                position: offset + 1,
                name: binding.name,
                family
            });
        });
        const plan = planCoreCategoricalContextDependencies({
            slots: [
                {
                    name: baseName,
                    classifier:
                        coreCategoricalClosedContextClassifier(
                            {
                                tag: 'object',
                                category: base.expression
                            },
                            nodeProvenance
                        ),
                    provenance: nodeProvenance
                },
                ...siblings.map(sibling => ({
                    name: sibling.name,
                    classifier:
                        coreCategoricalDisplayedContextClassifier(
                            base.expression,
                            sibling.family.expression,
                            [
                                coreCategoricalContextSlotReference(
                                    sibling.position - 1,
                                    nodeProvenance
                                )
                            ],
                            {
                                tag: 'indexed-object' as const,
                                baseCategory: base.expression,
                                family: sibling.family.expression,
                                index: sibling.position - 1
                            },
                            nodeProvenance
                        ),
                    provenance: nodeProvenance
                }))
            ],
            siblingGroups: [{
                positions: siblings.map(sibling => sibling.position),
                provenance: nodeProvenance
            }]
        });
        if (
            plan.groupedProducts.length !== 1 ||
            plan.groupedProducts[0].positions.length !== siblings.length
        ) {
            throw new CoreCategoricalProgramError(
                'INVALID_GROUPED_SEQUENTIAL_CONTEXT',
                nodeProvenance,
                'Dependency planner did not retain the requested sibling ' +
                'block'
            );
        }

        const extensions:
            CoreCategoricalGroupedSequentialExtension[] = [];
        let currentCategory =
            baseValue;
        let projectionToBase: CoreCategoricalTerm | undefined;
        for (const sibling of siblings) {
            const intent = plan.sequential[sibling.position];
            if (intent.kind !== 'displayed-sigma-extension') {
                throw new CoreCategoricalProgramError(
                    'INVALID_GROUPED_SEQUENTIAL_CONTEXT',
                    nodeProvenance,
                    `Dependency planner did not emit a Sigma extension ` +
                    `for '${sibling.name}'`
                );
            }
            const effectiveFamily = sibling.position === 1
                ? sibling.family
                : this.pullbackFamily(
                    sibling.family,
                    projectionToBase as CoreCategoricalTerm,
                    source
                ) as InternalCoreCategoricalDisplayedFamily;
            const totalCategory = this.totalCategory(
                effectiveFamily,
                source
            );
            const projectionToPrevious = this.sigmaProjection(
                effectiveFamily,
                source
            );
            const nextProjectionToBase = sibling.position === 1
                ? projectionToPrevious
                : this.composeFunctors(
                    projectionToBase as CoreCategoricalTerm,
                    projectionToPrevious,
                    source
                );
            extensions.push(Object.freeze({
                position: sibling.position,
                name: sibling.name,
                originalFamily: sibling.family,
                effectiveFamily,
                sourceCategory: currentCategory,
                totalCategory,
                projectionToPrevious,
                projectionToBase: nextProjectionToBase,
                pullbackPastPositions: Object.freeze([
                    ...intent.pullbackPastPositions
                ]),
                presentation: intent.presentation
            }));
            currentCategory = totalCategory;
            projectionToBase = nextProjectionToBase;
        }

        let groupedFamily:
            CoreCategoricalDisplayedFamily = siblings[0].family;
        for (const sibling of siblings.slice(1)) {
            groupedFamily = this.displayedProduct(
                groupedFamily,
                sibling.family,
                source
            );
        }
        const groupedTotal = this.totalCategory(
            groupedFamily,
            source
        );
        const sequentialSyntax = [
            `${baseName} : ${base.label}`,
            ...siblings.map(sibling =>
                `${sibling.name} : ${sibling.family.label}[${baseName}]`
            )
        ].join('; ');
        const groupedNames =
            siblings.map(sibling => sibling.name).join(',');
        const groupedFamilies =
            siblings.map(sibling => sibling.family.label).join(',');

        return Object.freeze({
            [CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTEXT]:
                true as const,
            revision:
                CORE_CATEGORICAL_GROUPED_SEQUENTIAL_PROGRAM_REVISION,
            programIdentity: this.programIdentity,
            baseName,
            baseCategory: baseValue,
            siblings: Object.freeze(
                siblings.map(sibling => Object.freeze({
                    position: sibling.position,
                    name: sibling.name,
                    family:
                        sibling.family as
                            CoreCategoricalDisplayedFamily
                }))
            ),
            plan,
            sequential: Object.freeze({
                syntax: sequentialSyntax,
                extensions: Object.freeze(extensions),
                totalCategory:
                    extensions[extensions.length - 1].totalCategory
            }),
            grouped: Object.freeze({
                syntax:
                    `${baseName} : ${base.label}; ` +
                    `(${groupedNames}) : ` +
                    `P(${groupedFamilies})[${baseName}]`,
                association: 'left' as const,
                family: groupedFamily,
                totalCategory: groupedTotal
            }),
            boundary: Object.freeze({
                newLambdapiOwnerOrRule: false as const,
                totalCategoryEqualityClaimed: false as const,
                totalCategoryEquivalenceClaimed: false as const,
                arrowLevelTotalComparisonClaimed: false as const
            })
        });
    }

    groupedSequentialObject(
        contextValue: CoreCategoricalGroupedSequentialContext,
        basePointValue: CoreCategoricalTerm,
        siblingValues: readonly CoreCategoricalTerm[],
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalGroupedSequentialObject {
        const nodeProvenance = this.at(
            'grouped/sequential context object',
            source
        );
        this.requireGroupedSequential(nodeProvenance);
        const context = this.requireGroupedSequentialContext(
            contextValue,
            nodeProvenance
        );
        if (siblingValues.length !== context.siblings.length) {
            throw new CoreCategoricalProgramError(
                'INVALID_GROUPED_SEQUENTIAL_CONTEXT',
                nodeProvenance,
                `Expected ${context.siblings.length} sibling values but ` +
                `received ${siblingValues.length}`
            );
        }
        const base = this.requireCategory(
            context.baseCategory,
            nodeProvenance
        );
        const convertedBase = this.convertObjectToCategory(
            basePointValue,
            base.expression,
            nodeProvenance,
            'Grouped/sequential base point'
        ).term;
        const basePoint = this.requireObjectTerm(
            convertedBase,
            nodeProvenance,
            'Grouped/sequential base point'
        );

        const originalComponents = siblingValues.map(
            (value, index) => {
                const family = this.requireDisplayedFamily(
                    context.siblings[index].family,
                    nodeProvenance
                );
                const expected = this.fibreCategoryExpression(
                    family,
                    basePoint.expression,
                    nodeProvenance
                );
                return this.convertObjectToCategory(
                    value,
                    expected,
                    nodeProvenance,
                    `Sibling value '${context.siblings[index].name}'`
                ).term;
            }
        );

        const sequentialPrefixObjects: CoreCategoricalTerm[] = [];
        const sequentialFibreComparisons:
            CoreCategoricalGroupedSequentialComparison[] = [];
        let sequentialPoint = convertedBase;
        for (
            let index = 0;
            index < context.sequential.extensions.length;
            index += 1
        ) {
            const extension =
                context.sequential.extensions[index];
            const family = this.requireDisplayedFamily(
                extension.effectiveFamily,
                nodeProvenance
            );
            const point = this.requireObjectTerm(
                sequentialPoint,
                nodeProvenance,
                'Sequential prefix object'
            );
            const expectedFibre = this.fibreCategoryExpression(
                family,
                point.expression,
                nodeProvenance
            );
            const converted = this.convertObjectToCategory(
                originalComponents[index],
                expectedFibre,
                nodeProvenance,
                `Sequential component '${extension.name}'`
            );
            sequentialFibreComparisons.push(
                groupedSequentialComparison(
                    `sequential-${extension.name}-fibre`,
                    converted.comparison
                )
            );
            const total = this.requireCategory(
                extension.totalCategory,
                nodeProvenance
            );
            sequentialPoint = this.makeTerm(
                this.dependentPairExpression(
                    family,
                    point.expression,
                    this.requireObjectTerm(
                        converted.term,
                        nodeProvenance,
                        `Sequential component '${extension.name}'`
                    ).expression,
                    nodeProvenance
                ),
                {
                    tag: 'object',
                    category: total.expression
                },
                nodeProvenance
            );
            sequentialPrefixObjects.push(sequentialPoint);
        }

        let groupedTuple = originalComponents[0];
        let groupedTupleInspection = this.requireObjectTerm(
            groupedTuple,
            nodeProvenance,
            'First grouped component'
        );
        for (
            let index = 1;
            index < originalComponents.length;
            index += 1
        ) {
            const right = this.requireObjectTerm(
                originalComponents[index],
                nodeProvenance,
                `Grouped component '${context.siblings[index].name}'`
            );
            const productCategory = this.productCategoryExpression(
                groupedTupleInspection.category,
                right.category,
                nodeProvenance
            );
            groupedTuple = this.makeTerm(
                this.productObjectPairExpression(
                    groupedTupleInspection.category,
                    right.category,
                    groupedTupleInspection.expression,
                    right.expression,
                    nodeProvenance
                ),
                {
                    tag: 'object',
                    category: productCategory
                },
                nodeProvenance
            );
            groupedTupleInspection = this.requireObjectTerm(
                groupedTuple,
                nodeProvenance,
                'Accumulated grouped tuple'
            );
        }
        const groupedFamily = this.requireDisplayedFamily(
            context.grouped.family,
            nodeProvenance
        );
        const groupedFibre = this.fibreCategoryExpression(
            groupedFamily,
            basePoint.expression,
            nodeProvenance
        );
        const convertedGrouped = this.convertObjectToCategory(
            groupedTuple,
            groupedFibre,
            nodeProvenance,
            'Grouped product tuple'
        );
        const groupedTotal = this.requireCategory(
            context.grouped.totalCategory,
            nodeProvenance
        );
        const groupedObject = this.makeTerm(
            this.dependentPairExpression(
                groupedFamily,
                basePoint.expression,
                this.requireObjectTerm(
                    convertedGrouped.term,
                    nodeProvenance,
                    'Grouped product tuple'
                ).expression,
                nodeProvenance
            ),
            {
                tag: 'object',
                category: groupedTotal.expression
            },
            nodeProvenance
        );

        return Object.freeze({
            context: contextValue,
            basePoint: convertedBase,
            siblingValues: Object.freeze([...originalComponents]),
            sequentialPrefixObjects:
                Object.freeze(sequentialPrefixObjects),
            sequentialObject:
                sequentialPrefixObjects[
                    sequentialPrefixObjects.length - 1
                ],
            groupedTuple,
            groupedFibreObject: convertedGrouped.term,
            groupedObject,
            sequentialFibreComparisons:
                Object.freeze(sequentialFibreComparisons),
            groupedFibreComparison: groupedSequentialComparison(
                'grouped-product-fibre',
                convertedGrouped.comparison
            ),
            totalCategoryCompared: false as const
        });
    }

    pullbackFamily(
        familyValue: CoreCategoricalDisplayedFamily,
        substitutionValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalDisplayedFamily {
        const nodeProvenance = this.at(
            'displayed-family substitution',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const substitution = this.requireFunctorTerm(
            substitutionValue,
            nodeProvenance,
            'Displayed-family substitution'
        );
        if (!kernelExpressionEquals(
            substitution.targetCategory,
            family.baseCategory.expression
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                `Substitution target does not match displayed family ` +
                `'${family.label}'`
            );
        }
        const sourceCategory = this.makeCategory(
            `source(${family.label})`,
            substitution.sourceCategory
        ) as InternalCoreCategoricalCategory;
        return this.reindexDisplayedFamily(
            family,
            sourceCategory,
            substitution.targetCategory,
            substitution.expression,
            nodeProvenance
        );
    }

    substituteFamily(
        familyValue: CoreCategoricalDisplayedFamily,
        substitutionValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalDisplayedFamily {
        return this.pullbackFamily(
            familyValue,
            substitutionValue,
            source
        );
    }

    /**
     * Reindex a displayed functor along an ordinary base substitution.
     *
     * The result is the hom action of the already-active
     * `Pullback_catd_func`; no pointwise coherence is synthesized.
     */
    pullbackDisplayedFunctor(
        displayedFunctorValue: CoreCategoricalTerm,
        substitutionValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed-functor base change',
            source
        );
        this.requireFibredWeakenReindex(nodeProvenance);
        const displayedFunctor = this.requireDisplayedFunctorTerm(
            displayedFunctorValue,
            nodeProvenance,
            'Displayed-functor base-change subject'
        );
        const substitution = this.requireFunctorTerm(
            substitutionValue,
            nodeProvenance,
            'Displayed-functor base substitution'
        );
        if (!kernelExpressionEquals(
            substitution.targetCategory,
            displayedFunctor.baseCategory
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Displayed-functor substitution has the wrong codomain'
            );
        }
        const sourceFamily = this.displayedPullbackExpression(
            substitution.sourceCategory,
            substitution.targetCategory,
            displayedFunctor.sourceFamily,
            substitution.expression,
            nodeProvenance
        );
        const targetFamily = this.displayedPullbackExpression(
            substitution.sourceCategory,
            substitution.targetCategory,
            displayedFunctor.targetFamily,
            substitution.expression,
            nodeProvenance
        );
        const sourceDisplayedCategory = kernelApplication(
            'displayed-category-category',
            [{ value: substitution.targetCategory }],
            nodeProvenance
        );
        const targetDisplayedCategory = kernelApplication(
            'displayed-category-category',
            [{ value: substitution.sourceCategory }],
            nodeProvenance
        );
        const pullbackFunctor = kernelCall(
            kernelFree(
                coreCategoricalFibredWeakenReindexCoreName(
                    'pullbackDisplayedFamilyFunctor'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: substitution.sourceCategory
                },
                {
                    plicity: 'implicit',
                    value: substitution.targetCategory
                },
                {
                    plicity: 'explicit',
                    value: substitution.expression
                }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            kernelApplication(
                'functor-hom-capped',
                [
                    { value: sourceDisplayedCategory },
                    { value: targetDisplayedCategory },
                    { value: pullbackFunctor },
                    { value: displayedFunctor.sourceFamily },
                    { value: displayedFunctor.targetFamily },
                    { value: displayedFunctor.expression }
                ],
                nodeProvenance
            ),
            {
                tag: 'displayed-functor',
                category: this.displayedFunctorCategoryExpression(
                    substitution.sourceCategory,
                    sourceFamily,
                    targetFamily,
                    nodeProvenance
                ),
                baseCategory: substitution.sourceCategory,
                sourceFamily,
                targetFamily
            },
            nodeProvenance
        );
    }

    dependentPair(
        familyValue: CoreCategoricalDisplayedFamily,
        firstValue: CoreCategoricalTerm,
        secondValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'dependent pair',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const first = this.requireObjectTerm(
            firstValue,
            nodeProvenance,
            'Dependent-pair first component'
        );
        this.requireSameCategory(
            first.category,
            family.baseCategory.expression,
            nodeProvenance,
            'Dependent-pair first component'
        );
        const second = this.requireObjectTerm(
            secondValue,
            nodeProvenance,
            'Dependent-pair second component'
        );
        const expectedFibre = this.fibreCategoryExpression(
            family,
            first.expression,
            nodeProvenance
        );
        this.requireSameCategory(
            second.category,
            expectedFibre,
            nodeProvenance,
            'Dependent-pair second component'
        );
        const expression = this.dependentPairExpression(
            family,
            first.expression,
            second.expression,
            nodeProvenance
        );
        return this.makeTerm(
            expression,
            {
                tag: 'object',
                category:
                    this.totalCategoryExpression(
                        family,
                        nodeProvenance
                    )
            },
            nodeProvenance
        );
    }

    familyTransport(
        familyValue: CoreCategoricalDisplayedFamily,
        baseArrowValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed-family arrow transport',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const baseArrow = this.requireHomTerm(
            baseArrowValue,
            nodeProvenance,
            'Displayed-family transport index'
        );
        if (!kernelExpressionEquals(
            baseArrow.category,
            family.baseCategory.expression
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                `Transport arrow is outside the base of displayed family ` +
                `'${family.label}'`
            );
        }
        const sourceFibre = this.fibreCategoryExpression(
            family,
            baseArrow.sourceObject,
            nodeProvenance
        );
        const targetFibre = this.fibreCategoryExpression(
            family,
            baseArrow.targetObject,
            nodeProvenance
        );
        return this.makeTerm(
            kernelApplication(
                'functor-hom-capped',
                [
                    { value: family.baseCategory.expression },
                    {
                        value: kernelApplication(
                            'category-of-categories',
                            [],
                            nodeProvenance
                        )
                    },
                    { value: family.expression },
                    { value: baseArrow.sourceObject },
                    { value: baseArrow.targetObject },
                    { value: baseArrow.expression }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: sourceFibre,
                targetCategory: targetFibre
            },
            nodeProvenance
        );
    }

    sigmaArrow(
        familyValue: CoreCategoricalDisplayedFamily,
        sourceValue: CoreCategoricalTerm,
        targetValue: CoreCategoricalTerm,
        baseArrowValue: CoreCategoricalTerm,
        fibreArrowValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'canonical Sigma arrow',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const sourceObject = this.requireObjectTerm(
            sourceValue,
            nodeProvenance,
            'Sigma-arrow source fibre value'
        );
        const targetObject = this.requireObjectTerm(
            targetValue,
            nodeProvenance,
            'Sigma-arrow target fibre value'
        );
        const baseArrow = this.requireHomTerm(
            baseArrowValue,
            nodeProvenance,
            'Sigma-arrow base component'
        );
        if (!kernelExpressionEquals(
            baseArrow.category,
            family.baseCategory.expression
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Sigma-arrow base component is outside the family base'
            );
        }
        const sourceFibre = this.fibreCategoryExpression(
            family,
            baseArrow.sourceObject,
            nodeProvenance
        );
        const targetFibre = this.fibreCategoryExpression(
            family,
            baseArrow.targetObject,
            nodeProvenance
        );
        this.requireSameCategory(
            sourceObject.category,
            sourceFibre,
            nodeProvenance,
            'Sigma-arrow source fibre value'
        );
        this.requireSameCategory(
            targetObject.category,
            targetFibre,
            nodeProvenance,
            'Sigma-arrow target fibre value'
        );
        const transport = kernelApplication(
            'functor-hom-capped',
            [
                { value: family.baseCategory.expression },
                {
                    value: kernelApplication(
                        'category-of-categories',
                        [],
                        nodeProvenance
                    )
                },
                { value: family.expression },
                { value: baseArrow.sourceObject },
                { value: baseArrow.targetObject },
                { value: baseArrow.expression }
            ],
            nodeProvenance
        );
        const transportedSource = kernelApplication(
            'functor-object',
            [
                { value: sourceFibre },
                { value: targetFibre },
                { value: transport },
                { value: sourceObject.expression }
            ],
            nodeProvenance
        );
        const fibreArrow = this.requireHomTerm(
            fibreArrowValue,
            nodeProvenance,
            'Sigma-arrow fibre component'
        );
        if (
            !kernelExpressionEquals(
                fibreArrow.category,
                targetFibre
            ) ||
            !kernelExpressionEquals(
                fibreArrow.sourceObject,
                transportedSource
            ) ||
            !kernelExpressionEquals(
                fibreArrow.targetObject,
                targetObject.expression
            )
        ) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_HOM',
                nodeProvenance,
                'Sigma-arrow fibre component has the wrong transported ' +
                'source, target, or fibre'
            );
        }
        const sourcePair = this.dependentPairExpression(
            family,
            baseArrow.sourceObject,
            sourceObject.expression,
            nodeProvenance
        );
        const targetPair = this.dependentPairExpression(
            family,
            baseArrow.targetObject,
            targetObject.expression,
            nodeProvenance
        );
        const total = this.totalCategoryExpression(
            family,
            nodeProvenance
        );
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalComprehensionCoreName(
                        'sigma-arrow'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: family.baseCategory.expression
                    },
                    {
                        plicity: 'explicit',
                        value: family.expression
                    },
                    {
                        plicity: 'implicit',
                        value: baseArrow.sourceObject
                    },
                    {
                        plicity: 'implicit',
                        value: baseArrow.targetObject
                    },
                    {
                        plicity: 'explicit',
                        value: sourceObject.expression
                    },
                    {
                        plicity: 'explicit',
                        value: targetObject.expression
                    },
                    {
                        plicity: 'explicit',
                        value: baseArrow.expression
                    },
                    {
                        plicity: 'explicit',
                        value: fibreArrow.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'hom',
                category: total,
                sourceObject: sourcePair,
                targetObject: targetPair
            },
            nodeProvenance
        );
    }

    pullbackTotal(
        substitutionValue: CoreCategoricalTerm,
        familyValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'pullback totalization',
            source
        );
        this.requireComprehension(nodeProvenance);
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const substitution = this.requireFunctorTerm(
            substitutionValue,
            nodeProvenance,
            'Pullback totalization substitution'
        );
        if (!kernelExpressionEquals(
            substitution.targetCategory,
            family.baseCategory.expression
        )) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                `Pullback totalization target does not match family ` +
                `'${family.label}'`
            );
        }
        const sourceBase = this.makeCategory(
            `source(${family.label})`,
            substitution.sourceCategory
        ) as InternalCoreCategoricalCategory;
        const reindexed = this.reindexDisplayedFamily(
            family,
            sourceBase,
            substitution.targetCategory,
            substitution.expression,
            nodeProvenance
        );
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalComprehensionCoreName(
                        'sigma-pullback-total-functor'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: substitution.sourceCategory
                    },
                    {
                        plicity: 'implicit',
                        value: substitution.targetCategory
                    },
                    {
                        plicity: 'explicit',
                        value: substitution.expression
                    },
                    {
                        plicity: 'explicit',
                        value: family.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory:
                    this.totalCategoryExpression(
                        reindexed,
                        nodeProvenance
                    ),
                targetCategory:
                    this.totalCategoryExpression(
                        family,
                        nodeProvenance
                    )
            },
            nodeProvenance
        );
    }

    section(
        name: string,
        familyValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `dependent section assumption ${name}`,
            source
        );
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        const category = coreSectionCategory(
            family.baseCategory.expression,
            family.expression,
            nodeProvenance
        );
        return this.assume(name, {
            tag: 'dependent-section',
            category,
            baseCategory: family.baseCategory.expression,
            family: family.expression
        }, nodeProvenance);
    }

    displayedFunctor(
        name: string,
        sourceValue: CoreCategoricalDisplayedFamily,
        targetValue: CoreCategoricalDisplayedFamily,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `displayed functor assumption ${name}`,
            source
        );
        const sourceFamily = this.requireDisplayedFamily(
            sourceValue,
            nodeProvenance
        );
        const targetFamily = this.requireDisplayedFamily(
            targetValue,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                sourceFamily.baseCategory.expression,
                targetFamily.baseCategory.expression
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                `Displayed functor '${name}' has families over different ` +
                'base categories'
            );
        }
        const category = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                    'displayed-functor-category'
                ],
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: sourceFamily.baseCategory.expression
                },
                {
                    plicity: 'explicit',
                    value: sourceFamily.expression
                },
                {
                    plicity: 'explicit',
                    value: targetFamily.expression
                }
            ],
            nodeProvenance
        );
        return this.assume(name, {
            tag: 'displayed-functor',
            category,
            baseCategory: sourceFamily.baseCategory.expression,
            sourceFamily: sourceFamily.expression,
            targetFamily: targetFamily.expression
        }, nodeProvenance);
    }

    displayedTransfor(
        name: string,
        sourceFunctorValue: CoreCategoricalTerm,
        targetFunctorValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `displayed transfor assumption ${name}`,
            source
        );
        this.requireFibredTransfd(nodeProvenance);
        const sourceFunctor = this.requireDisplayedFunctorTerm(
            sourceFunctorValue,
            nodeProvenance,
            `source of displayed transfor '${name}'`
        );
        const targetFunctor = this.requireDisplayedFunctorTerm(
            targetFunctorValue,
            nodeProvenance,
            `target of displayed transfor '${name}'`
        );
        if (
            !kernelExpressionEquals(
                sourceFunctor.baseCategory,
                targetFunctor.baseCategory
            ) ||
            !kernelExpressionEquals(
                sourceFunctor.sourceFamily,
                targetFunctor.sourceFamily
            ) ||
            !kernelExpressionEquals(
                sourceFunctor.targetFamily,
                targetFunctor.targetFamily
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_SOURCE_MISMATCH',
                nodeProvenance,
                `Displayed transfor '${name}' has incompatible displayed-` +
                'functor endpoints'
            );
        }
        const category = this.displayedTransforCategoryExpression(
            sourceFunctor.baseCategory,
            sourceFunctor.sourceFamily,
            sourceFunctor.targetFamily,
            sourceFunctor.expression,
            targetFunctor.expression,
            nodeProvenance
        );
        return this.assume(name, {
            tag: 'displayed-transfor',
            category,
            baseCategory: sourceFunctor.baseCategory,
            sourceFamily: sourceFunctor.sourceFamily,
            targetFamily: sourceFunctor.targetFamily,
            sourceFunctor: sourceFunctor.expression,
            targetFunctor: targetFunctor.expression
        }, nodeProvenance);
    }

    composeDisplayedTransfor(
        outerValue: CoreCategoricalTerm,
        innerValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed transfor vertical composition',
            source
        );
        this.requireFibredTransfd(nodeProvenance);
        const outer = this.requireDisplayedTransforTerm(
            outerValue,
            nodeProvenance,
            'outer displayed transfor'
        );
        const inner = this.requireDisplayedTransforTerm(
            innerValue,
            nodeProvenance,
            'inner displayed transfor'
        );
        if (
            !kernelExpressionEquals(
                outer.baseCategory,
                inner.baseCategory
            ) ||
            !kernelExpressionEquals(
                outer.sourceFamily,
                inner.sourceFamily
            ) ||
            !kernelExpressionEquals(
                outer.targetFamily,
                inner.targetFamily
            ) ||
            !kernelExpressionEquals(
                inner.targetFunctor,
                outer.sourceFunctor
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_SOURCE_MISMATCH',
                nodeProvenance,
                'Displayed transfor vertical composition has incompatible ' +
                'endpoints'
            );
        }
        const category = this.displayedTransforCategoryExpression(
            inner.baseCategory,
            inner.sourceFamily,
            inner.targetFamily,
            inner.sourceFunctor,
            outer.targetFunctor,
            nodeProvenance
        );
        const expression = kernelCall(
            kernelFree(
                coreCategoricalDependentCompositionCoreName(
                    'generic-category-composition'
                ),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: this.displayedFunctorCategoryExpression(
                        inner.baseCategory,
                        inner.sourceFamily,
                        inner.targetFamily,
                        nodeProvenance
                    )
                },
                {
                    plicity: 'implicit',
                    value: inner.sourceFunctor
                },
                {
                    plicity: 'implicit',
                    value: inner.targetFunctor
                },
                {
                    plicity: 'implicit',
                    value: outer.targetFunctor
                },
                {
                    plicity: 'explicit',
                    value: outer.expression
                },
                {
                    plicity: 'explicit',
                    value: inner.expression
                }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            expression,
            {
                tag: 'displayed-transfor',
                category,
                baseCategory: inner.baseCategory,
                sourceFamily: inner.sourceFamily,
                targetFamily: inner.targetFamily,
                sourceFunctor: inner.sourceFunctor,
                targetFunctor: outer.targetFunctor
            },
            nodeProvenance
        );
    }

    functorCategory(
        sourceValue: CoreCategoricalCategory,
        targetValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalCategory {
        const nodeProvenance = this.at(
            'ordinary functor category',
            source
        );
        const sourceCategory = this.requireCategory(
            sourceValue,
            nodeProvenance
        );
        const targetCategory = this.requireCategory(
            targetValue,
            nodeProvenance
        );
        return this.makeCategory(
            `Functor(${sourceCategory.label}, ${targetCategory.label})`,
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralSymbolCoreName(
                        CORE_CATEGORICAL_STRUCTURAL_SYMBOLS
                            .functorCategory
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'explicit',
                        value: sourceCategory.expression
                    },
                    {
                        plicity: 'explicit',
                        value: targetCategory.expression
                    }
                ],
                nodeProvenance
            )
        );
    }

    productCategory(
        leftValue: CoreCategoricalCategory,
        rightValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalCategory {
        const nodeProvenance = this.at(
            'ordinary product category',
            source
        );
        const left = this.requireCategory(
            leftValue,
            nodeProvenance
        );
        const right = this.requireCategory(
            rightValue,
            nodeProvenance
        );
        return this.makeCategory(
            `Product(${left.label}, ${right.label})`,
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralCoreName(
                        'product-category'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'explicit',
                        value: left.expression
                    },
                    {
                        plicity: 'explicit',
                        value: right.expression
                    }
                ],
                nodeProvenance
            )
        );
    }

    private productProjection(
        side: 'left' | 'right',
        leftValue: CoreCategoricalCategory,
        rightValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `ordinary product ${side} projection`,
            source
        );
        const left = this.requireCategory(
            leftValue,
            nodeProvenance
        );
        const right = this.requireCategory(
            rightValue,
            nodeProvenance
        );
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralCoreName(
                        side === 'left'
                            ? 'product-left-projection'
                            : 'product-right-projection'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: left.expression
                    },
                    {
                        plicity: 'implicit',
                        value: right.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: this.productCategoryExpression(
                    left.expression,
                    right.expression,
                    nodeProvenance
                ),
                targetCategory: side === 'left'
                    ? left.expression
                    : right.expression
            },
            nodeProvenance
        );
    }

    productLeftProjection(
        leftValue: CoreCategoricalCategory,
        rightValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        return this.productProjection(
            'left',
            leftValue,
            rightValue,
            source
        );
    }

    productRightProjection(
        leftValue: CoreCategoricalCategory,
        rightValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        return this.productProjection(
            'right',
            leftValue,
            rightValue,
            source
        );
    }

    composeFunctors(
        outerValue: CoreCategoricalTerm,
        innerValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'ordinary functor composition',
            source
        );
        this.requireComprehension(nodeProvenance);
        const outer = this.requireFunctorTerm(
            outerValue,
            nodeProvenance,
            'Outer composition operand'
        );
        const inner = this.requireFunctorTerm(
            innerValue,
            nodeProvenance,
            'Inner composition operand'
        );
        if (!kernelExpressionEquals(
            inner.targetCategory,
            outer.sourceCategory
        )) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                'Functor composition operands have incompatible middle ' +
                'categories'
            );
        }
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralCoreName(
                        'functor-composition'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: inner.sourceCategory
                    },
                    {
                        plicity: 'implicit',
                        value: inner.targetCategory
                    },
                    {
                        plicity: 'implicit',
                        value: outer.targetCategory
                    },
                    {
                        plicity: 'explicit',
                        value: outer.expression
                    },
                    {
                        plicity: 'explicit',
                        value: inner.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: inner.sourceCategory,
                targetCategory: outer.targetCategory
            },
            nodeProvenance
        );
    }

    identityFunctor(
        categoryValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'ordinary identity functor',
            source
        );
        const category = this.requireCategory(
            categoryValue,
            nodeProvenance
        );
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralCoreName(
                        'identity-functor'
                    ),
                    nodeProvenance
                ),
                [{
                    plicity: 'implicit',
                    value: category.expression
                }],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: category.expression,
                targetCategory: category.expression
            },
            nodeProvenance
        );
    }

    functorPair(
        leftValue: CoreCategoricalTerm,
        rightValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'ordinary functor pairing',
            source
        );
        const left = this.requireFunctorTerm(
            leftValue,
            nodeProvenance,
            'Left functor-pair component'
        );
        const right = this.requireFunctorTerm(
            rightValue,
            nodeProvenance,
            'Right functor-pair component'
        );
        if (!kernelExpressionEquals(
            left.sourceCategory,
            right.sourceCategory
        )) {
            throw new CoreCategoricalProgramError(
                'EXPECTED_FUNCTOR',
                nodeProvenance,
                'Functor-pair components must have one shared source'
            );
        }
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralCoreName(
                        'product-pair'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: this.functorCategoryExpression(
                            left.sourceCategory,
                            left.targetCategory,
                            nodeProvenance
                        )
                    },
                    {
                        plicity: 'implicit',
                        value: this.functorCategoryExpression(
                            right.sourceCategory,
                            right.targetCategory,
                            nodeProvenance
                        )
                    },
                    {
                        plicity: 'explicit',
                        value: left.expression
                    },
                    {
                        plicity: 'explicit',
                        value: right.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: left.sourceCategory,
                targetCategory: this.productCategoryExpression(
                    left.targetCategory,
                    right.targetCategory,
                    nodeProvenance
                )
            },
            nodeProvenance
        );
    }

    productMap(
        leftValue: CoreCategoricalTerm,
        rightValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'componentwise product functor',
            source
        );
        const left = this.requireFunctorTerm(
            leftValue,
            nodeProvenance,
            'Left product-map component'
        );
        const right = this.requireFunctorTerm(
            rightValue,
            nodeProvenance,
            'Right product-map component'
        );
        const productCategory = (
            first: KernelExpression,
            second: KernelExpression
        ): KernelExpression => kernelCall(
            kernelFree(
                coreCategoricalStructuralCoreName(
                    'product-category'
                ),
                nodeProvenance
            ),
            [
                { plicity: 'explicit', value: first },
                { plicity: 'explicit', value: second }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            kernelCall(
                kernelFree(
                    coreCategoricalStructuralCoreName(
                        'product-map'
                    ),
                    nodeProvenance
                ),
                [
                    {
                        plicity: 'implicit',
                        value: left.sourceCategory
                    },
                    {
                        plicity: 'implicit',
                        value: left.targetCategory
                    },
                    {
                        plicity: 'implicit',
                        value: right.sourceCategory
                    },
                    {
                        plicity: 'implicit',
                        value: right.targetCategory
                    },
                    {
                        plicity: 'explicit',
                        value: left.expression
                    },
                    {
                        plicity: 'explicit',
                        value: right.expression
                    }
                ],
                nodeProvenance
            ),
            {
                tag: 'functor',
                sourceCategory: productCategory(
                    left.sourceCategory,
                    right.sourceCategory
                ),
                targetCategory: productCategory(
                    left.targetCategory,
                    right.targetCategory
                )
            },
            nodeProvenance
        );
    }

    object(
        name: string,
        categoryValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `object assumption ${name}`,
            source
        );
        const category = this.requireCategory(
            categoryValue,
            nodeProvenance
        );
        return this.assume(name, {
            tag: 'object',
            category: category.expression
        }, nodeProvenance);
    }

    functor(
        name: string,
        sourceValue: CoreCategoricalCategory,
        targetValue: CoreCategoricalCategory,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `functor assumption ${name}`,
            source
        );
        const sourceCategory = this.requireCategory(
            sourceValue,
            nodeProvenance
        );
        const targetCategory = this.requireCategory(
            targetValue,
            nodeProvenance
        );
        return this.assume(name, {
            tag: 'functor',
            sourceCategory: sourceCategory.expression,
            targetCategory: targetCategory.expression
        }, nodeProvenance);
    }

    hom(
        name: string,
        categoryValue: CoreCategoricalCategory,
        sourceObject: CoreCategoricalTerm,
        targetObject: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `arrow assumption ${name}`,
            source
        );
        const category = this.requireCategory(
            categoryValue,
            nodeProvenance
        );
        const endpoints = [
            this.builder.inspect(sourceObject),
            this.builder.inspect(targetObject)
        ];
        for (const endpoint of endpoints) {
            if (
                endpoint.type.tag === 'indexed-object' ||
                endpoint.type.tag === 'indexed-functor' ||
                endpoint.type.tag === 'indexed-transfor'
            ) {
                throw new CoreCategoricalProgramError(
                    'EXPECTED_CATEGORY_OBJECT',
                    nodeProvenance,
                    `Arrow assumption '${name}' has an open indexed endpoint`
                );
            }
            const endpointCategory = coreTypeObjectCategory(
                endpoint.type,
                nodeProvenance.span as SourceSpan,
                `endpoint of arrow assumption ${name}`
            );
            if (
                endpointCategory === undefined ||
                !coreObjectCategoryEquals(
                    endpointCategory,
                    category.expression
                )
            ) {
                throw new CoreCategoricalProgramError(
                    'EXPECTED_CATEGORY_OBJECT',
                    nodeProvenance,
                    `Arrow assumption '${name}' has an endpoint outside ` +
                    `category '${category.label}'`
                );
            }
        }
        return this.assume(name, {
            tag: 'hom',
            category: category.expression,
            sourceObject: this.builder.compile(sourceObject).term,
            targetObject: this.builder.compile(targetObject).term
        }, nodeProvenance);
    }

    homBoundary(
        categoryValue: CoreCategoricalCategory,
        sourceObject: CoreCategoricalTerm,
        targetObject: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalHomBoundary {
        const nodeProvenance = this.at(
            'whole Hom-action boundary',
            source
        );
        const category = this.requireCategory(
            categoryValue,
            nodeProvenance
        );
        return this.builder.homBoundary(
            category.expression,
            sourceObject,
            targetObject,
            nodeProvenance
        );
    }

    apply(
        subject: CoreCategoricalTerm,
        argument:
            | CoreCategoricalTerm
            | CoreCategoricalHomBoundary,
        options: CoreCategoricalApplyOptions = {}
    ): CoreCategoricalTerm {
        return this.builder.apply(
            subject,
            argument,
            options.expectedShape,
            this.at('categorical application', options.source)
        );
    }

    /**
     * Contextual base index of the active `:^fd` callback token.
     */
    indexOf(
        displayedObject: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed contextual index',
            source
        );
        this.requireFibredWeakenReindex(nodeProvenance);
        return this.builder.indexOf(
            displayedObject,
            nodeProvenance
        );
    }

    lambda(
        name: string,
        sourceValue: CoreCategoricalCategory,
        targetValue: CoreCategoricalCategory,
        body: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalLambdaOptions = {}
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `categorical abstraction ${name}`,
            options.source
        );
        const sourceCategory = this.requireCategory(
            sourceValue,
            nodeProvenance
        );
        const targetCategory = this.requireCategory(
            targetValue,
            nodeProvenance
        );
        return this.builder.categoricalLambda(
            name,
            sourceCategory.expression,
            targetCategory.expression,
            body,
            {
                plicity: options.plicity,
                variation: options.variation,
                polarity: options.polarity,
                cellLevel: options.cellLevel,
                dependency: options.dependency,
                provenance: nodeProvenance
            }
        );
    }

    dependentLambda(
        name: string,
        familyValue: CoreCategoricalDisplayedFamily,
        body: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalLambdaOptions = {}
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `dependent categorical abstraction ${name}`,
            options.source
        );
        const family = this.requireDisplayedFamily(
            familyValue,
            nodeProvenance
        );
        return this.builder.dependentLambda(
            name,
            family.baseCategory.expression,
            family.expression,
            body,
            {
                plicity: options.plicity,
                variation: options.variation,
                polarity: options.polarity,
                cellLevel: options.cellLevel,
                dependency: options.dependency,
                provenance: nodeProvenance
            }
        );
    }

    /**
     * Direct `λ a :^fd E. body`-equivalent abstraction.
     *
     * The builder hides a natural base slot, records the body as the nested
     * `k :^n K; a :^f E[k]` contextual presentation, and lowers only the
     * FIBRED-BINDER-1 identity/eta/composition contract.
     */
    displayedFunctorLambda(
        name: string,
        sourceValue: CoreCategoricalDisplayedFamily,
        targetValue: CoreCategoricalDisplayedFamily,
        body: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalLambdaOptions = {}
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `displayed-functor abstraction ${name}`,
            options.source
        );
        this.requireFibredBinder(nodeProvenance);
        const sourceFamily = this.requireDisplayedFamily(
            sourceValue,
            nodeProvenance
        );
        const targetFamily = this.requireDisplayedFamily(
            targetValue,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                sourceFamily.baseCategory.expression,
                targetFamily.baseCategory.expression
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                `Displayed-functor abstraction '${name}' has source and ` +
                'target families over different bases'
            );
        }
        return this.builder.displayedFunctorLambda(
            name,
            sourceFamily.baseCategory.expression,
            sourceFamily.expression,
            targetFamily.expression,
            body,
            {
                plicity: options.plicity,
                variation: options.variation,
                polarity: options.polarity,
                cellLevel: options.cellLevel,
                dependency: options.dependency,
                provenance: nodeProvenance
            }
        );
    }

    displayedTransforComponent(
        transformation: CoreCategoricalTerm,
        point: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed transfor fibre component',
            source
        );
        this.requireFibredTransfd(nodeProvenance);
        return this.builder.apply(
            transformation,
            point,
            'displayed-component',
            nodeProvenance
        );
    }

    displayedTransforPoint(
        transformation: CoreCategoricalTerm,
        point: CoreCategoricalTerm,
        fibreObject: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed transfor point component',
            source
        );
        this.requireFibredTransfd(nodeProvenance);
        const component = this.builder.apply(
            transformation,
            point,
            'displayed-component',
            nodeProvenance
        );
        return this.builder.apply(
            component,
            fibreObject,
            'point-component',
            nodeProvenance
        );
    }

    /**
     * Active component-level displayed naturality cell:
     *
     *   eta[p][u] :
     *     D[p](FF[x](u)) -> GG[y](E[p](u)).
     */
    displayedTransforNaturality(
        transformationValue: CoreCategoricalTerm,
        baseArrowValue: CoreCategoricalTerm,
        fibreObjectValue: CoreCategoricalTerm,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            'displayed transfor higher naturality cell',
            source
        );
        this.requireFibredTransfd(nodeProvenance);
        const transformation = this.requireDisplayedTransforTerm(
            transformationValue,
            nodeProvenance,
            'displayed naturality subject'
        );
        const baseArrow = this.requireHomTerm(
            baseArrowValue,
            nodeProvenance,
            'displayed naturality base arrow'
        );
        if (
            !kernelExpressionEquals(
                baseArrow.category,
                transformation.baseCategory
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Displayed naturality arrow belongs to the wrong base'
            );
        }
        const fibreObject = this.requireObjectTerm(
            fibreObjectValue,
            nodeProvenance,
            'displayed naturality fibre object'
        );
        const sourceFibre = this.fibreCategoryOfExpression(
            transformation.baseCategory,
            transformation.sourceFamily,
            baseArrow.sourceObject,
            nodeProvenance
        );
        const targetFibre = this.fibreCategoryOfExpression(
            transformation.baseCategory,
            transformation.targetFamily,
            baseArrow.targetObject,
            nodeProvenance
        );
        this.requireSameCategory(
            fibreObject.category,
            sourceFibre,
            nodeProvenance,
            'Displayed naturality fibre object'
        );
        const transport = (
            side: 'transport-lhs' | 'transport-rhs',
            displayedFunctor: KernelExpression
        ): KernelExpression => kernelCall(
            kernelFree(
                coreCategoricalFibredTransfdCoreName(side),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: transformation.baseCategory
                },
                {
                    plicity: 'implicit',
                    value: transformation.sourceFamily
                },
                {
                    plicity: 'implicit',
                    value: transformation.targetFamily
                },
                {
                    plicity: 'explicit',
                    value: displayedFunctor
                },
                {
                    plicity: 'implicit',
                    value: baseArrow.sourceObject
                },
                {
                    plicity: 'implicit',
                    value: baseArrow.targetObject
                },
                {
                    plicity: 'explicit',
                    value: baseArrow.expression
                }
            ],
            nodeProvenance
        );
        const applyTransport = (
            functor: KernelExpression
        ): KernelExpression => kernelApplication(
            'functor-object',
            [
                { value: sourceFibre },
                { value: targetFibre },
                { value: functor },
                { value: fibreObject.expression }
            ],
            nodeProvenance
        );
        const sourceObject = applyTransport(transport(
            'transport-lhs',
            transformation.sourceFunctor
        ));
        const targetObject = applyTransport(transport(
            'transport-rhs',
            transformation.targetFunctor
        ));
        const expression = kernelCall(
            kernelFree(
                coreCategoricalFibredTransfdCoreName('higher-cell'),
                nodeProvenance
            ),
            [
                {
                    plicity: 'implicit',
                    value: transformation.baseCategory
                },
                {
                    plicity: 'implicit',
                    value: transformation.sourceFamily
                },
                {
                    plicity: 'implicit',
                    value: transformation.targetFamily
                },
                {
                    plicity: 'implicit',
                    value: transformation.sourceFunctor
                },
                {
                    plicity: 'implicit',
                    value: transformation.targetFunctor
                },
                {
                    plicity: 'explicit',
                    value: transformation.expression
                },
                {
                    plicity: 'implicit',
                    value: baseArrow.sourceObject
                },
                {
                    plicity: 'implicit',
                    value: baseArrow.targetObject
                },
                {
                    plicity: 'explicit',
                    value: baseArrow.expression
                },
                {
                    plicity: 'explicit',
                    value: fibreObject.expression
                }
            ],
            nodeProvenance
        );
        return this.makeTerm(
            expression,
            {
                tag: 'hom',
                category: targetFibre,
                sourceObject,
                targetObject
            },
            nodeProvenance
        );
    }

    /**
     * Direct `λ k :^nd K. eta[k]`-equivalent coherent eta abstraction.
     */
    displayedTransforLambda(
        name: string,
        sourceFunctorValue: CoreCategoricalTerm,
        targetFunctorValue: CoreCategoricalTerm,
        body: (
            token: CoreCategoricalSlotToken
        ) => CoreCategoricalTerm,
        options: CoreCategoricalLambdaOptions = {}
    ): CoreCategoricalTerm {
        const nodeProvenance = this.at(
            `displayed-transfor abstraction ${name}`,
            options.source
        );
        this.requireFibredTransfd(nodeProvenance);
        const sourceFunctor = this.requireDisplayedFunctorTerm(
            sourceFunctorValue,
            nodeProvenance,
            `source endpoint of displayed-transfor abstraction '${name}'`
        );
        const targetFunctor = this.requireDisplayedFunctorTerm(
            targetFunctorValue,
            nodeProvenance,
            `target endpoint of displayed-transfor abstraction '${name}'`
        );
        if (
            !kernelExpressionEquals(
                sourceFunctor.baseCategory,
                targetFunctor.baseCategory
            ) ||
            !kernelExpressionEquals(
                sourceFunctor.sourceFamily,
                targetFunctor.sourceFamily
            ) ||
            !kernelExpressionEquals(
                sourceFunctor.targetFamily,
                targetFunctor.targetFamily
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_SOURCE_MISMATCH',
                nodeProvenance,
                `Displayed-transfor abstraction '${name}' has incompatible ` +
                'displayed-functor endpoints'
            );
        }
        return this.builder.displayedTransforLambda(
            name,
            sourceFunctor.baseCategory,
            sourceFunctor.sourceFamily,
            sourceFunctor.targetFamily,
            sourceFunctor.expression,
            targetFunctor.expression,
            body,
            {
                plicity: options.plicity,
                variation: options.variation,
                polarity: options.polarity,
                cellLevel: options.cellLevel,
                dependency: options.dependency,
                provenance: nodeProvenance
            }
        );
    }

    displayedTransforClassifierCompatibility(
        sourceFunctorValue: CoreCategoricalTerm,
        targetFunctorValue: CoreCategoricalTerm,
        stepLimit = 2_000,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalFibredTransfdClassifierCompatibility {
        const nodeProvenance = this.at(
            'displayed-transfor direct/next-hom compatibility',
            source
        );
        this.requireFibredTransfd(nodeProvenance);
        const sourceFunctor = this.requireDisplayedFunctorTerm(
            sourceFunctorValue,
            nodeProvenance,
            'displayed-transfor compatibility source'
        );
        const targetFunctor = this.requireDisplayedFunctorTerm(
            targetFunctorValue,
            nodeProvenance,
            'displayed-transfor compatibility target'
        );
        if (
            !kernelExpressionEquals(
                sourceFunctor.baseCategory,
                targetFunctor.baseCategory
            ) ||
            !kernelExpressionEquals(
                sourceFunctor.sourceFamily,
                targetFunctor.sourceFamily
            ) ||
            !kernelExpressionEquals(
                sourceFunctor.targetFamily,
                targetFunctor.targetFamily
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_SOURCE_MISMATCH',
                nodeProvenance,
                'Displayed-transfor compatibility requires matching ' +
                'displayed-functor classifiers'
            );
        }
        const compilation = this.fibredDependentTargetEnabled
            ? (
                this.dependent as
                    CoreCategoricalFibredDependentTargetCompilation
            ).prerequisite.prerequisite
            : this.fibredWeakenReindexEnabled
            ? (
                this.dependent as
                    CoreCategoricalFibredWeakenReindexCompilation
            ).prerequisite
            : this.dependent as
                CoreCategoricalFibredTransfdCompilation;
        const classifiers = coreCategoricalFibredTransfdClassifiers(
            sourceFunctor.baseCategory,
            sourceFunctor.sourceFamily,
            sourceFunctor.targetFamily,
            sourceFunctor.expression,
            targetFunctor.expression,
            nodeProvenance
        );
        const proof = compileCoreCategoricalFibredTransfdProof(
            compilation,
            this.environment
        );
        return Object.freeze({
            directClassifier: classifiers.direct,
            ordinaryNextHomClassifier:
                classifiers.ordinaryNextHom,
            sigmaPiNextHomClassifier:
                classifiers.sigmaPiNextHom,
            explicitDirectClassifier:
                serializeCoreCategoricalExpression(
                    classifiers.direct
                ),
            explicitOrdinaryNextHomClassifier:
                serializeCoreCategoricalExpression(
                    classifiers.ordinaryNextHom
                ),
            explicitSigmaPiNextHomClassifier:
                serializeCoreCategoricalExpression(
                    classifiers.sigmaPiNextHom
                ),
            directOrdinaryRuntime: coreLfDefinitionalCompare(
                this.environment,
                classifiers.ordinaryNextHom,
                classifiers.direct,
                stepLimit,
                undefined,
                compilation.composedRuntime
            ),
            directOrdinaryProofTime:
                proof.compare(
                    classifiers.ordinaryNextHom,
                    classifiers.direct,
                    { stepLimit }
                ),
            directOrdinaryObjectRuntime:
                coreLfDefinitionalCompare(
                    this.environment,
                    classifiers.ordinaryObjectClassifier,
                    classifiers.directObjectClassifier,
                    stepLimit,
                    undefined,
                    compilation.composedRuntime
                ),
            directSigmaPiRuntime: coreLfDefinitionalCompare(
                this.environment,
                classifiers.sigmaPiNextHom,
                classifiers.direct,
                stepLimit,
                undefined,
                compilation.composedRuntime
            ),
            preservesPresentations: true as const
        });
    }

    /**
     * Execute the active proof-only Sigma/Pi uncurrying comparison while
     * retaining the negative runtime comparison.
     */
    displayedFunctorClassifierCompatibility(
        sourceValue: CoreCategoricalDisplayedFamily,
        targetValue: CoreCategoricalDisplayedFamily,
        stepLimit = 2_000,
        source?: CoreCategoricalSourceSite
    ): CoreCategoricalFibredBinderClassifierCompatibility {
        const nodeProvenance = this.at(
            'displayed-functor direct/nested classifier compatibility',
            source
        );
        this.requireFibredBinder(nodeProvenance);
        const sourceFamily = this.requireDisplayedFamily(
            sourceValue,
            nodeProvenance
        );
        const targetFamily = this.requireDisplayedFamily(
            targetValue,
            nodeProvenance
        );
        if (
            !kernelExpressionEquals(
                sourceFamily.baseCategory.expression,
                targetFamily.baseCategory.expression
            )
        ) {
            throw new CoreCategoricalProgramError(
                'DISPLAYED_BASE_MISMATCH',
                nodeProvenance,
                'Direct/nested classifier comparison requires one base'
            );
        }
        const compilation =
            this.dependent as CoreCategoricalFibredBinderCompilation;
        const classifiers = coreCategoricalFibredBinderClassifiers(
            sourceFamily.baseCategory.expression,
            sourceFamily.expression,
            targetFamily.expression,
            nodeProvenance
        );
        const proof = compileCoreCategoricalFibredBinderProof(
            compilation,
            this.environment
        );
        return Object.freeze({
            directClassifier: classifiers.direct,
            nestedClassifier: classifiers.nested,
            explicitDirectClassifier:
                serializeCoreCategoricalExpression(
                    classifiers.direct
                ),
            explicitNestedClassifier:
                serializeCoreCategoricalExpression(
                    classifiers.nested
                ),
            runtime: coreLfDefinitionalCompare(
                this.environment,
                classifiers.nested,
                classifiers.direct,
                stepLimit,
                undefined,
                compilation.composedRuntime
            ),
            proofTime: proof.compare(
                classifiers.nested,
                classifiers.direct,
                { stepLimit }
            ),
            preservesPresentations: true as const
        });
    }

    inspect(
        term: CoreCategoricalTerm
    ): CoreCategoricalTermInspection {
        return this.builder.inspect(term);
    }

    serializeCategory(
        value: CoreCategoricalCategory
    ): string {
        const category = this.requireCategory(
            value,
            this.at('categorical category serialization')
        );
        return serializeCoreCategoricalExpression(
            category.expression
        );
    }

    dependentTargetCategoryCompatibility(
        leftValue: CoreCategoricalCategory,
        rightValue: CoreCategoricalCategory,
        stepLimit = 4_000
    ): CoreCategoricalFibredDependentTargetCompatibility {
        const nodeProvenance = this.at(
            'dependent-target runtime/proof category comparison'
        );
        this.requireFibredDependentTarget(nodeProvenance);
        const left = this.requireCategory(
            leftValue,
            nodeProvenance
        );
        const right = this.requireCategory(
            rightValue,
            nodeProvenance
        );
        const compilation =
            this.dependent as
                CoreCategoricalFibredDependentTargetCompilation;
        return Object.freeze({
            runtime: coreLfDefinitionalCompare(
                this.environment,
                left.expression,
                right.expression,
                stepLimit,
                undefined,
                compilation.composedRuntime
            ),
            proofTime:
                compilation.proofProgram
                    .compareUnderOpaqueDeclarationExtension(
                        this.environment,
                        compilation.composedRuntime,
                        left.expression,
                        right.expression
                    ),
            runtimeCategoryPresentationCollapseInstalled:
                false as const,
            preservesPresentations: true as const
        });
    }

    compareCategories(
        leftValue: CoreCategoricalCategory,
        rightValue: CoreCategoricalCategory,
        stepLimit = 512
    ): CoreLfComparisonResult {
        const nodeProvenance = this.at(
            'categorical category comparison'
        );
        const left = this.requireCategory(
            leftValue,
            nodeProvenance
        );
        const right = this.requireCategory(
            rightValue,
            nodeProvenance
        );
        const runtime = 'composedRuntime' in this.dependent
            ? this.dependent.composedRuntime
            : this.dependent.structural.composedRuntime;
        return coreLfDefinitionalCompare(
            this.environment,
            left.expression,
            right.expression,
            stepLimit,
            undefined,
            runtime
        );
    }

    compareDisplayedFamilies(
        leftValue: CoreCategoricalDisplayedFamily,
        rightValue: CoreCategoricalDisplayedFamily,
        stepLimit = 512
    ): CoreLfComparisonResult {
        const nodeProvenance = this.at(
            'displayed-family comparison'
        );
        const left = this.requireDisplayedFamily(
            leftValue,
            nodeProvenance
        );
        const right = this.requireDisplayedFamily(
            rightValue,
            nodeProvenance
        );
        const runtime = 'composedRuntime' in this.dependent
            ? this.dependent.composedRuntime
            : this.dependent.structural.composedRuntime;
        return coreLfDefinitionalCompare(
            this.environment,
            left.expression,
            right.expression,
            stepLimit,
            undefined,
            runtime
        );
    }

    compare(
        left: CoreCategoricalTerm,
        right: CoreCategoricalTerm,
        stepLimit = 512
    ): CoreLfComparisonResult {
        const leftCompilation = this.compile(left);
        const rightCompilation = this.compile(right);
        const runtime = 'composedRuntime' in this.dependent
            ? this.dependent.composedRuntime
            : this.dependent.structural.composedRuntime;
        return coreLfDefinitionalCompare(
            this.environment,
            leftCompilation.explicitTerm,
            rightCompilation.explicitTerm,
            stepLimit,
            undefined,
            runtime
        );
    }

    compile(
        term: CoreCategoricalTerm
    ): CoreCategoricalProgramCompilation {
        const lowered = this.builder.compile(term);
        const inspected = this.builder.inspect(term);
        const expectedType = coreTypeToKernelType(
            lowered.type,
            lowered.sourceSpan,
            'categorical program expected result'
        );
        const checker = this.dependent.compiled.createChecker(
            this.environment
        );
        const inferred = checker.infer(
            checker.rootContext,
            lowered.term
        );
        if (inferred.type.tag === 'kind') {
            throw new CoreCategoricalProgramError(
                'UNEXPECTED_KIND',
                lowered.term.provenance,
                'Categorical program unexpectedly inferred checker-only KIND'
            );
        }
        const checked = checker.check(
            checker.rootContext,
            inferred.term,
            expectedType
        );
        const prerequisites = collectStructuralPrerequisites(
            inspected.abstractions
        );
        return Object.freeze({
            construction: 'direct-typescript-categorical-program',
            explicitTerm: checked.term,
            inferredType: inferred.type,
            expectedType,
            surfaceType: lowered.type,
            explicitCore:
                serializeCoreCategoricalExpression(checked.term),
            explicitInferredType:
                serializeCoreCategoricalExpression(inferred.type),
            explicitExpectedType:
                serializeCoreCategoricalExpression(expectedType),
            abstractions: Object.freeze([...inspected.abstractions]),
            structuralPrerequisites: prerequisites,
            dependentPrerequisites:
                collectDependentPrerequisites(inspected),
            productionLambdapiDependency: false
        });
    }
}
