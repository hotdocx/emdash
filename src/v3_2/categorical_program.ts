/**
 * Stable root-only TypeScript facade for the ordinary categorical frontend.
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
    CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CoreCategoricalStructuralCompilation,
    CoreCategoricalStructuralPrerequisiteId,
    compileCoreCategoricalStructuralTransfer,
    coreCategoricalStructuralCoreName,
    coreCategoricalStructuralSymbolCoreName
} from './categorical_structural_transfer';
import {
    CoreCategoricalExpectedShape
} from './categorical_surface_spec';
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
    kernelCall,
    kernelFree,
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
    'USABILITY-1D-CATEGORICAL-PROGRAM-1' as const;

const CORE_CATEGORICAL_CATEGORY =
    Symbol('CoreCategoricalProgramCategory');

export interface CoreCategoricalCategory {
    readonly [CORE_CATEGORICAL_CATEGORY]: true;
    readonly label: string;
}

interface InternalCoreCategoricalCategory
extends CoreCategoricalCategory {
    readonly programIdentity: symbol;
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
    | 'EXPECTED_CATEGORY_OBJECT'
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

/**
 * End-user construction scope for the reviewed ordinary categorical slice.
 */
export class CoreCategoricalProgram {
    private readonly programIdentity = Symbol('CoreCategoricalProgram');
    private readonly sourceFile: string;
    private readonly structural: CoreCategoricalStructuralCompilation;
    private readonly builder: CoreCategoricalScopedBuilder;
    private environment: CoreLfDeclarationEnvironment;

    constructor(options: CoreCategoricalProgramOptions = {}) {
        this.sourceFile =
            options.sourceFile ?? '<categorical-program>';
        this.structural =
            compileCoreCategoricalStructuralTransfer();
        this.environment = this.structural.compiled.environment;
        this.builder = new CoreCategoricalScopedBuilder(
            this.at('categorical program')
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
        const checker = this.structural.compiled.createChecker(
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
            surfaceType: inspected.type,
            explicitCore:
                serializeCoreCategoricalExpression(checked.term),
            explicitInferredType:
                serializeCoreCategoricalExpression(inferred.type),
            explicitExpectedType:
                serializeCoreCategoricalExpression(expectedType),
            abstractions: Object.freeze([...inspected.abstractions]),
            structuralPrerequisites: prerequisites,
            productionLambdapiDependency: false
        });
    }
}
