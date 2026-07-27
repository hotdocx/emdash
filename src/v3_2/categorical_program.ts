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

const CORE_CATEGORICAL_CATEGORY =
    Symbol('CoreCategoricalProgramCategory');
const CORE_CATEGORICAL_DISPLAYED_FAMILY =
    Symbol('CoreCategoricalProgramDisplayedFamily');

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
     * approved asymmetric base-change totalization and remains root-only.
     */
    readonly profile?:
        | 'reviewed-usability-2a1'
        | 'usability-dependent-1a'
        | 'fibred-comprehension-1a';
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
    | 'EXPECTED_HOM'
    | 'UNAVAILABLE_COMPREHENSION'
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
        | CoreCategoricalComprehensionCompilation;
    private readonly comprehensionEnabled: boolean;
    private readonly builder: CoreCategoricalScopedBuilder;
    private environment: CoreLfDeclarationEnvironment;

    constructor(options: CoreCategoricalProgramOptions = {}) {
        this.sourceFile =
            options.sourceFile ?? '<categorical-program>';
        const profile =
            options.profile ?? 'reviewed-usability-2a1';
        this.comprehensionEnabled =
            profile === 'fibred-comprehension-1a';
        this.dependent = this.comprehensionEnabled
            ? compileCoreCategoricalComprehensionTransfer()
            : profile === 'usability-dependent-1a'
                ? compileCoreCategoricalDependentCompositionTransfer()
                : compileCoreCategoricalDependentTransfer();
        this.environment = this.dependent.compiled.environment;
        this.builder = new CoreCategoricalScopedBuilder(
            this.at('categorical program'),
            {
                dependentSectionComposition:
                    profile !== 'reviewed-usability-2a1'
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
        expression: KernelExpression
    ): CoreCategoricalDisplayedFamily {
        return Object.freeze({
            [CORE_CATEGORICAL_DISPLAYED_FAMILY]: true as const,
            programIdentity: this.programIdentity,
            label,
            baseCategory,
            expression
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

    private fibreCategoryExpression(
        family: InternalCoreCategoricalDisplayedFamily,
        point: KernelExpression,
        nodeProvenance: Provenance
    ): KernelExpression {
        return kernelApplication(
            'functor-object',
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
                { value: point }
            ],
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
            pointInspection.type.tag === 'indexed-functor'
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
        return this.makeDisplayedFamily(
            `${family.label}[substitution]`,
            sourceCategory,
            kernelApplication(
                'displayed-pullback',
                [
                    { value: substitution.sourceCategory },
                    { value: substitution.targetCategory },
                    { value: family.expression },
                    { value: substitution.expression }
                ],
                nodeProvenance
            )
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
        const reindexed = this.makeDisplayedFamily(
            `${family.label}[substitution]`,
            sourceBase,
            kernelApplication(
                'displayed-pullback',
                [
                    { value: substitution.sourceCategory },
                    { value: substitution.targetCategory },
                    { value: family.expression },
                    { value: substitution.expression }
                ],
                nodeProvenance
            )
        ) as InternalCoreCategoricalDisplayedFamily;
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
                endpoint.type.tag === 'indexed-functor'
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

    inspect(
        term: CoreCategoricalTerm
    ): CoreCategoricalTermInspection {
        return this.builder.inspect(term);
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
