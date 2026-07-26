/**
 * Declarative schema-directed elaboration for the active v3.2 projection
 * family.
 *
 * This is intentionally not a second evaluator. It interprets backend-neutral
 * operation schemas, recovers rigid slots from a checked surface context, and
 * lowers to explicit emdash Core owner applications.
 */

import {
    KernelExpression,
    SourceSpan,
    formatSourceSpan,
    kernelApplication,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import { serializeKernelExpression } from './lambdapi';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    CoreTypeField,
    CoreTypeTemplate,
    OperationOperandName,
    SURFACE_OPERATION_SCHEMAS,
    SchemaValue,
    SurfaceOperationId,
    SurfaceOperationSchema
} from './schema';
import {
    CoreType,
    SurfaceContext,
    SurfaceTerm,
    coreObjectCategoryEquals,
    coreTypeForCategoryObject,
    coreTypeObjectCategory,
    isObjectLikeCoreType
} from './surface';

export type ElaborationErrorCode =
    | 'UNBOUND_NAME'
    | 'OPERATION_ARITY_MISMATCH'
    | 'EXPECTED_FUNCTOR'
    | 'EXPECTED_OBJECT'
    | 'EXPECTED_HOM'
    | 'EXPECTED_TRANSFOR'
    | 'CATEGORY_MISMATCH';

export class V32ElaborationError extends Error {
    constructor(
        public readonly code: ElaborationErrorCode,
        public readonly span: SourceSpan,
        message: string
    ) {
        super(`${message} at ${formatSourceSpan(span)}`);
        this.name = 'V32ElaborationError';
    }
}

export interface RecoveredSlot {
    operation: SurfaceOperationId;
    owner: CoreOwnerId;
    slot: string;
    value: KernelExpression;
    span: SourceSpan;
}

export interface ElaboratedSurfaceTerm {
    term: KernelExpression;
    type: CoreType;
    sourceSpan: SourceSpan;
    recovered: readonly RecoveredSlot[];
}

type ElaboratedOperands = Record<
    OperationOperandName,
    ElaboratedSurfaceTerm
>;

const recoveredProvenance = (
    owner: CoreOwnerId,
    slot: string,
    span: SourceSpan
) => provenance(
    'recovered',
    `${owner} slot ${slot} recovered from operand types`,
    span
);

const derivedProvenance = (detail: string, span: SourceSpan) =>
    provenance('derived', detail, span);

const surfaceProvenance = (detail: string, span: SourceSpan) =>
    provenance('surface', detail, span);

const renderExpression = (expression: KernelExpression): string =>
    serializeKernelExpression(expression);

function categoryMismatch(
    span: SourceSpan,
    operationName: string,
    expected: KernelExpression,
    actual: KernelExpression
): never {
    throw new V32ElaborationError(
        'CATEGORY_MISMATCH',
        span,
        `${operationName} expected category ` +
        `${renderExpression(expected)}, but received ` +
        renderExpression(actual)
    );
}

function recoveredSlot(
    operation: SurfaceOperationId,
    owner: CoreOwnerId,
    slot: string,
    value: KernelExpression,
    span: SourceSpan
): RecoveredSlot {
    return { operation, owner, slot, value, span };
}

function coreTypeField(
    type: CoreType,
    field: CoreTypeField,
    span: SourceSpan
): KernelExpression {
    switch (field) {
        case 'category':
            if (type.tag === 'object' || type.tag === 'hom') {
                return type.category;
            }
            break;
        case 'sourceCategory':
            if (type.tag === 'functor' || type.tag === 'transfor') {
                return type.sourceCategory;
            }
            break;
        case 'targetCategory':
            if (type.tag === 'functor' || type.tag === 'transfor') {
                return type.targetCategory;
            }
            break;
        case 'sourceObject':
            if (type.tag === 'hom') return type.sourceObject;
            break;
        case 'targetObject':
            if (type.tag === 'hom') return type.targetObject;
            break;
        case 'sourceFunctor':
            if (type.tag === 'transfor') return type.sourceFunctor;
            break;
        case 'targetFunctor':
            if (type.tag === 'transfor') return type.targetFunctor;
            break;
        case 'objectCategory': {
            const category = coreTypeObjectCategory(
                type,
                span,
                `schema object-category view of ${type.tag}`
            );
            if (category) return category;
            break;
        }
        default: {
            const exhaustive: never = field;
            return exhaustive;
        }
    }

    throw new Error(
        `Invalid operation schema: Core type ${type.tag} has no field ${field}`
    );
}

function evaluateSchemaValue(
    schemaValue: SchemaValue,
    operands: ElaboratedOperands,
    span: SourceSpan
): KernelExpression {
    switch (schemaValue.kind) {
        case 'operand-term':
            return operands[schemaValue.operand].term;
        case 'operand-type-field':
            return coreTypeField(
                operands[schemaValue.operand].type,
                schemaValue.field,
                span
            );
        case 'owner-application': {
            const ownerSchema = CORE_OWNER_SCHEMAS[schemaValue.owner];
            if (ownerSchema.slots.length !== schemaValue.arguments.length) {
                throw new Error(
                    `Invalid operation schema: nested owner ` +
                    `${schemaValue.owner} expects ${ownerSchema.slots.length} ` +
                    `arguments, received ${schemaValue.arguments.length}`
                );
            }
            return kernelApplication(
                schemaValue.owner,
                schemaValue.arguments.map(argument => ({
                    value: evaluateSchemaValue(argument, operands, span)
                })),
                derivedProvenance(
                    `result classifier application of ${schemaValue.owner}`,
                    span
                )
            );
        }
        default: {
            const exhaustive: never = schemaValue;
            return exhaustive;
        }
    }
}

function instantiateCoreType(
    template: CoreTypeTemplate,
    operands: ElaboratedOperands,
    span: SourceSpan
): CoreType {
    switch (template.tag) {
        case 'category':
            return { tag: 'category' };
        case 'object':
            return {
                tag: 'object',
                category: evaluateSchemaValue(
                    template.category,
                    operands,
                    span
                )
            };
        case 'object-of-category':
            return coreTypeForCategoryObject(
                evaluateSchemaValue(
                    template.category,
                    operands,
                    span
                ),
                span,
                'schema-directed object category view'
            );
        case 'functor':
            return {
                tag: 'functor',
                sourceCategory: evaluateSchemaValue(
                    template.sourceCategory,
                    operands,
                    span
                ),
                targetCategory: evaluateSchemaValue(
                    template.targetCategory,
                    operands,
                    span
                )
            };
        case 'hom':
            return {
                tag: 'hom',
                category: evaluateSchemaValue(
                    template.category,
                    operands,
                    span
                ),
                sourceObject: evaluateSchemaValue(
                    template.sourceObject,
                    operands,
                    span
                ),
                targetObject: evaluateSchemaValue(
                    template.targetObject,
                    operands,
                    span
                )
            };
        case 'transfor':
            return {
                tag: 'transfor',
                sourceCategory: evaluateSchemaValue(
                    template.sourceCategory,
                    operands,
                    span
                ),
                targetCategory: evaluateSchemaValue(
                    template.targetCategory,
                    operands,
                    span
                ),
                sourceFunctor: evaluateSchemaValue(
                    template.sourceFunctor,
                    operands,
                    span
                ),
                targetFunctor: evaluateSchemaValue(
                    template.targetFunctor,
                    operands,
                    span
                )
            };
        default: {
            const exhaustive: never = template;
            return exhaustive;
        }
    }
}

/**
 * Interpret one declarative operation schema from already elaborated terms.
 *
 * This is the reusable boundary for later typed surface layers: they may
 * classify and construct contextual terms independently, then reuse the same
 * owner telescope, constraint, result-type, and provenance interpreter once
 * every operand is closed explicit Core.
 */
export function elaborateSurfaceOperationFromOperands(
    operation: SurfaceOperationId,
    operandList: readonly ElaboratedSurfaceTerm[],
    span: SourceSpan
): ElaboratedSurfaceTerm {
    const schema: SurfaceOperationSchema =
        SURFACE_OPERATION_SCHEMAS[operation];
    if (operandList.length !== schema.operands.length) {
        throw new V32ElaborationError(
            'OPERATION_ARITY_MISMATCH',
            span,
            `${schema.diagnosticLabel} expects ${schema.operands.length} ` +
            `surface operands, received ${operandList.length}`
        );
    }

    const partialOperands: Partial<ElaboratedOperands> = {};
    schema.operands.forEach((operandSchema, index) => {
        const operand = operandList[index];
        const matchesExpectedKind =
            operandSchema.expectedKind === 'object-like'
                ? isObjectLikeCoreType(operand.type)
                : operand.type.tag === operandSchema.expectedKind;
        if (!matchesExpectedKind) {
            throw new V32ElaborationError(
                operandSchema.errorCode,
                operand.sourceSpan,
                `${schema.diagnosticLabel} expects ` +
                operandSchema.expectation
            );
        }
        partialOperands[operandSchema.name] = operand;
    });
    const operands = partialOperands as ElaboratedOperands;

    for (const constraint of schema.constraints) {
        const left = evaluateSchemaValue(constraint.left, operands, span);
        const right = evaluateSchemaValue(
            constraint.right,
            operands,
            span
        );
        const equalCategories = constraint.comparison === 'object-category'
            ? coreObjectCategoryEquals(left, right)
            : kernelExpressionEquals(left, right);
        if (!equalCategories) {
            categoryMismatch(
                operands[constraint.blame].sourceSpan,
                schema.diagnosticLabel,
                left,
                right
            );
        }
    }

    const nodeProvenance = surfaceProvenance(
        `surface operation ${operation}`,
        span
    );
    const term = kernelApplication(
        schema.owner,
        schema.ownerArguments.map(argument => {
            const value = evaluateSchemaValue(
                argument.value,
                operands,
                span
            );
            return {
                value,
                provenance: argument.origin === 'recovered'
                    ? recoveredProvenance(
                        schema.owner,
                        argument.slot,
                        span
                    )
                    : value.provenance
            };
        }),
        nodeProvenance
    );

    const childRecovered = schema.operands.flatMap(
        operandSchema => operands[operandSchema.name].recovered
    );
    const ownRecovered = schema.ownerArguments.flatMap(argument => {
        if (argument.origin !== 'recovered') return [];
        const value = evaluateSchemaValue(
            argument.value,
            operands,
            span
        );
        return [recoveredSlot(
            operation,
            schema.owner,
            argument.slot,
            value,
            span
        )];
    });

    return {
        term,
        type: instantiateCoreType(schema.result, operands, span),
        sourceSpan: span,
        recovered: [...childRecovered, ...ownRecovered]
    };
}

function elaborateOperation(
    context: SurfaceContext,
    surface: Extract<SurfaceTerm, { tag: 'operation' }>
): ElaboratedSurfaceTerm {
    return elaborateSurfaceOperationFromOperands(
        surface.operation,
        surface.operands.map(operand =>
            elaborateSurfaceTerm(context, operand)
        ),
        surface.span
    );
}

export function elaborateSurfaceTerm(
    context: SurfaceContext,
    surface: SurfaceTerm
): ElaboratedSurfaceTerm {
    switch (surface.tag) {
        case 'reference': {
            const binding = context.lookup(surface.name);
            if (!binding) {
                throw new V32ElaborationError(
                    'UNBOUND_NAME',
                    surface.span,
                    `Unbound v3.2 surface name '${surface.name}'`
                );
            }
            return {
                term: kernelFree(
                    binding.name,
                    surfaceProvenance(
                        `surface reference ${binding.name}`,
                        surface.span
                    )
                ),
                type: binding.coreType,
                sourceSpan: surface.span,
                recovered: []
            };
        }
        case 'operation':
            return elaborateOperation(context, surface);
        default: {
            const exhaustive: never = surface;
            return exhaustive;
        }
    }
}
