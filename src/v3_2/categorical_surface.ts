/**
 * USABILITY-1B ordinary categorical surface and contextual IR.
 *
 * The builder supports the first dependency-ready vertical slice:
 *
 * - typed explicit Core leaves;
 * - scoped categorical object slots;
 * - classifier-directed ordinary functor application;
 * - whole Hom-action requests; and
 * - functorial eta abstraction.
 *
 * Callback tokens and callbacks are temporary construction devices. The
 * recorded abstraction body is immutable first-order locally nameless data,
 * and the compiled result is existing explicit Core. Non-eta bracket cases
 * fail with the exact structural prerequisite needed by USABILITY-1C.
 */

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
    kernelAssertScoped,
    kernelExpressionEquals,
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

export type CoreCategoricalContextualIr =
    | {
        readonly tag: 'slot-reference';
        readonly index: number;
        readonly hint: string;
        readonly type: CoreType;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'explicit-core-term';
        readonly term: KernelExpression;
        readonly type: CoreType;
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
        readonly type: CoreType;
        readonly provenance: Provenance;
    };

export interface CoreCategoricalHomBoundaryIr {
    readonly tag: 'hom-boundary';
    readonly category: KernelExpression;
    readonly sourceEndpoint: CoreCategoricalContextualIr;
    readonly targetEndpoint: CoreCategoricalContextualIr;
    readonly provenance: Provenance;
}

export interface CoreCategoricalAbstractionEvidence {
    readonly rule: 'categorical.eta';
    readonly name: string;
    readonly plicity: Plicity;
    readonly variation: 'functorial';
    readonly polarity: 'covariant';
    readonly cellLevel: 'object';
    readonly dependency: 'ordinary';
    readonly sourceCategory: KernelExpression;
    readonly targetCategory: KernelExpression;
    readonly body: CoreCategoricalContextualIr;
    readonly result: CoreCategoricalContextualIr;
    readonly provenance: Provenance;
}

export interface CoreCategoricalTermInspection {
    readonly type: CoreType;
    readonly usage: readonly CoreCategoricalSlotUsage[];
    readonly ir: CoreCategoricalContextualIr;
    readonly abstractions:
        readonly CoreCategoricalAbstractionEvidence[];
    readonly lowered: boolean;
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
    readonly expectedClassifier?: 'outer-lf-pi' | 'ordinary-functor';
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
    };

interface InternalCoreCategoricalTerm extends CoreCategoricalTerm {
    readonly builderIdentity: symbol;
    readonly node: TemporaryCategoricalNode;
    readonly type: CoreType;
    readonly usage: InternalCategoricalUsage;
    readonly closed?: ElaboratedSurfaceTerm;
    readonly abstractions:
        readonly CoreCategoricalAbstractionEvidence[];
    readonly [CORE_CATEGORICAL_SLOT]?: true;
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
        default: {
            const exhaustive: never = type;
            return exhaustive;
        }
    }
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
    return layer === 'outer-lf'
        ? abstractionById('outer-lf-abstraction')
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
        type: CoreType,
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
            type: deepFreeze(copyCoreType(type)),
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

        const objectCategory = coreTypeObjectCategory(
            argument.type,
            this.spanFor(nodeProvenance),
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
        } else if (
            selection.operation === 'functor.object' &&
            subject.closed !== undefined
        ) {
            type = coreTypeForCategoryObject(
                subject.type.targetCategory,
                this.spanFor(nodeProvenance),
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

    private normalizeNode(
        term: InternalCoreCategoricalTerm,
        scope: readonly number[]
    ): CoreCategoricalContextualIr {
        switch (term.node.tag) {
            case 'explicit-core-term':
                return deepFreeze({
                    tag: 'explicit-core-term',
                    term: term.node.term,
                    type: copyCoreType(term.type),
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
                    type: copyCoreType(term.type),
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
                    type: copyCoreType(term.type),
                    provenance: term.node.provenance
                });
            default: {
                const exhaustive: never = term.node;
                return exhaustive;
            }
        }
    }

    private missingBracketTarget(
        body: InternalCoreCategoricalTerm,
        ordinal: number
    ): string {
        const count = usageCount(body.usage, ordinal);
        if (count === 0) return 'constant-functor-abstraction';
        if (count > 1) return 'diagonal-functor-abstraction';
        if (body.node.tag === 'slot-token') return 'identity-functor';
        if (body.node.tag === 'typed-application') {
            return 'evaluation-functor';
        }
        return 'functor-composition';
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
                'staged for USABILITY-2A'
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

            const expectedBodyType = coreTypeForCategoryObject(
                targetCategory,
                this.spanFor(nodeProvenance),
                `categorical abstraction ${name} target`
            );
            if (!coreTypeEquals(body.type, expectedBodyType)) {
                this.fail(
                    'CLASSIFIER_ARGUMENT_MISMATCH',
                    nodeProvenance,
                    `Categorical abstraction '${name}' body has the wrong ` +
                    'target classifier'
                );
            }
            if (
                body.node.tag !== 'typed-application' ||
                body.node.judgment.target !== 'functor-object' ||
                body.node.argument[
                    CORE_CATEGORICAL_BOUNDARY
                ] === true
            ) {
                const target = this.missingBracketTarget(
                    body,
                    token.node.tag === 'slot-token'
                        ? token.node.ordinal
                        : -1
                );
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    `Categorical abstraction '${name}' is not the eta case; ` +
                    `its next bracket prerequisite is '${target}'`
                );
            }

            const argument = body.node.argument as
                InternalCoreCategoricalTerm;
            const ordinal = token.node.tag === 'slot-token'
                ? token.node.ordinal
                : -1;
            if (
                argument.node.tag !== 'slot-token' ||
                argument.node.ordinal !== ordinal ||
                usageCount(body.node.subject.usage, ordinal) !== 0 ||
                usageCount(body.usage, ordinal) !== 1 ||
                body.node.subject.type.tag !== 'functor' ||
                !kernelExpressionEquals(
                    body.node.subject.type.sourceCategory,
                    sourceCategory
                ) ||
                !kernelExpressionEquals(
                    body.node.subject.type.targetCategory,
                    targetCategory
                ) ||
                body.node.subject.closed === undefined
            ) {
                this.fail(
                    'MISSING_STRUCTURAL_OWNER',
                    nodeProvenance,
                    `Categorical abstraction '${name}' requires general ` +
                    'evaluation/structural bracket lowering'
                );
            }

            const bodyIr = this.normalizeNode(
                body,
                [ordinal, ...outerScope]
            );
            const resultIr = this.normalizeNode(
                body.node.subject,
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
                provenance: nodeProvenance
            });
            const subject = body.node.subject;
            const closed = deepFreeze({
                term: (subject.closed as ElaboratedSurfaceTerm).term,
                type: copyCoreType(subject.type),
                sourceSpan: this.spanFor(nodeProvenance),
                recovered: [
                    ...(subject.closed as ElaboratedSurfaceTerm).recovered
                ]
            });
            return this.makeTerm(
                subject.node,
                subject.type,
                subject.usage,
                closed,
                [...subject.abstractions, evidence]
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
        return deepFreeze({
            type: copyCoreType(term.type),
            usage: term.usage.map(([ordinal, count]) => ({
                index: this.activeTokenOrdinals.indexOf(ordinal),
                count
            })),
            ir: this.normalizeNode(
                term,
                this.activeTokenOrdinals
            ),
            abstractions: [...term.abstractions],
            lowered: term.closed !== undefined
        });
    }
}
