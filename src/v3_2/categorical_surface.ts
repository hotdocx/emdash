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
 * - one honest indexed/displayed section-eta abstraction.
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
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CoreCategoricalStructuralPrerequisiteId,
    coreCategoricalStructuralCoreName,
    coreCategoricalStructuralSymbolCoreName
} from './categorical_structural_transfer';
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
    transferredTargets: Object.freeze(
        CORE_CATEGORICAL_DEPENDENT_PREREQUISITES.map(
            prerequisite => prerequisite.id
        )
    )
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

export type CoreCategoricalClassifier =
    | CoreType
    | CoreCategoricalIndexedObjectClassifier;

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
        readonly target: CoreCategoricalApplicationJudgment['target'];
        readonly subject: CoreCategoricalContextualIr;
        readonly argument:
            | CoreCategoricalContextualIr
            | CoreCategoricalHomBoundaryIr;
        readonly type: CoreCategoricalClassifier;
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
            readonly rule: 'categorical.dependent-eta';
            readonly variation: 'natural';
            readonly dependency: 'displayed';
            readonly targetFamily: KernelExpression;
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
    | CoreCategoricalDependentPrerequisiteId;

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
        readonly judgment: CoreCategoricalApplicationJudgment;
        readonly subject: InternalCoreCategoricalTerm;
        readonly argument:
            | InternalCoreCategoricalTerm
            | InternalCoreCategoricalHomBoundary;
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
}

interface InternalCoreCategoricalIndexedObjectClassifier {
    readonly tag: 'indexed-object';
    readonly baseCategory: KernelExpression;
    readonly family: KernelExpression;
    readonly indexOrdinal: number;
}

type InternalCoreCategoricalClassifier =
    | CoreType
    | InternalCoreCategoricalIndexedObjectClassifier;

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
                    current.target === 'displayed-functor-transport'
                ) {
                    add(current.target);
                }
                visit(current.subject);
                if (current.argument.tag === 'hom-boundary') {
                    visitBoundary(current.argument);
                } else {
                    visit(current.argument);
                }
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

    constructor(
        private readonly defaultProvenance: Provenance = provenance(
            'derived',
            'scoped categorical surface builder',
            DEFAULT_CATEGORICAL_SPAN
        )
    ) {}

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
        slotToken = false
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
            abstractions: deepFreeze([...abstractions])
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

    private categoricalObjectCategory(
        type: InternalCoreCategoricalClassifier,
        nodeProvenance: Provenance,
        detail: string
    ): KernelExpression | undefined {
        if (type.tag === 'indexed-object') return undefined;
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
            if (endpoint.type.tag === 'indexed-object') {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `${label} Hom-boundary endpoint is an open indexed fibre ` +
                    'object, not a closed category object'
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
            | 'functor.hom.capped',
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
        nodeProvenance: Provenance
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
            ]
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
        if (
            subject.closed === undefined ||
            argument.closed === undefined
        ) {
            this.fail(
                'UNAVAILABLE_DISPLAYED_ACTION',
                nodeProvenance,
                'Open displayed application requires the indexed contextual ' +
                'classifier staged for USABILITY-2A1'
            );
        }

        const base = subject.type.baseCategory;
        const sourceFamily = subject.type.sourceFamily;
        const targetFamily = subject.type.targetFamily;
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
            nodeProvenance
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
        if (classifier.tag !== 'indexed-object') {
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
        return {
            tag: 'indexed-object',
            baseCategory: classifier.baseCategory,
            family: classifier.family,
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
                    'USABILITY-2A1 qualifies dependent section eta only; ' +
                    'this body needs an additional active displayed ' +
                    'structural abstraction'
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
