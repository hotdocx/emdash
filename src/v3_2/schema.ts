/**
 * Backend-neutral owner and surface-operation schemas for emdash Core.
 *
 * The identifiers in this file describe mathematical roles rather than
 * Lambdapi spellings. A backend must bind every owner identifier separately.
 */

export type Plicity = 'explicit' | 'implicit';

export type CoreTypeTag =
    | 'category'
    | 'object'
    | 'functor'
    | 'hom'
    | 'transfor';

export type CoreOwnerKind = 'classifier' | 'projection';

export type CoreSlotRole =
    | 'classifier'
    | 'source-category'
    | 'target-category'
    | 'category'
    | 'source-endpoint'
    | 'target-endpoint'
    | 'functor'
    | 'source-functor'
    | 'target-functor'
    | 'transfor'
    | 'object'
    | 'arrow';

export interface CoreOwnerSlotSchema {
    name: string;
    plicity: Plicity;
    role: CoreSlotRole;
}

export interface ClassifierOwnerSchema {
    kind: 'classifier';
    classifier:
        | 'category-universe'
        | 'decode'
        | 'object'
        | 'functor'
        | 'hom'
        | 'transfor';
    slots: readonly CoreOwnerSlotSchema[];
}

export interface ProjectionOwnerSchema {
    kind: 'projection';
    family: 'functor-action' | 'transfor-action';
    dimension: 'object' | 'hom';
    extent: 'capped';
    variance: 'diagonal' | 'off-diagonal';
    slots: readonly CoreOwnerSlotSchema[];
}

export type CoreOwnerSchema = ClassifierOwnerSchema | ProjectionOwnerSchema;

/**
 * The small Core owner catalog needed by ELAB-1A.
 *
 * No entry contains a backend symbol or module name. Slot order and plicity
 * are semantic declaration data shared by checking and all backends.
 */
export const CORE_OWNER_SCHEMAS = {
    'category-universe': {
        kind: 'classifier',
        classifier: 'category-universe',
        slots: []
    },
    decode: {
        kind: 'classifier',
        classifier: 'decode',
        slots: [
            { name: 'classifier', plicity: 'explicit', role: 'classifier' }
        ]
    },
    'object-classifier': {
        kind: 'classifier',
        classifier: 'object',
        slots: [
            { name: 'A', plicity: 'explicit', role: 'category' }
        ]
    },
    'functor-classifier': {
        kind: 'classifier',
        classifier: 'functor',
        slots: [
            { name: 'A', plicity: 'explicit', role: 'source-category' },
            { name: 'B', plicity: 'explicit', role: 'target-category' }
        ]
    },
    'hom-classifier': {
        kind: 'classifier',
        classifier: 'hom',
        slots: [
            { name: 'A', plicity: 'explicit', role: 'category' },
            { name: 'X', plicity: 'explicit', role: 'source-endpoint' },
            { name: 'Y', plicity: 'explicit', role: 'target-endpoint' }
        ]
    },
    'transfor-classifier': {
        kind: 'classifier',
        classifier: 'transfor',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'explicit', role: 'source-functor' },
            { name: 'G', plicity: 'explicit', role: 'target-functor' }
        ]
    },
    'functor-object': {
        kind: 'projection',
        family: 'functor-action',
        dimension: 'object',
        extent: 'capped',
        variance: 'diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'explicit', role: 'functor' },
            { name: 'X', plicity: 'explicit', role: 'object' }
        ]
    },
    'functor-hom-capped': {
        kind: 'projection',
        family: 'functor-action',
        dimension: 'hom',
        extent: 'capped',
        variance: 'diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'explicit', role: 'functor' },
            { name: 'X', plicity: 'implicit', role: 'source-endpoint' },
            { name: 'Y', plicity: 'implicit', role: 'target-endpoint' },
            { name: 'f', plicity: 'explicit', role: 'arrow' }
        ]
    },
    'transfor-component-capped': {
        kind: 'projection',
        family: 'transfor-action',
        dimension: 'object',
        extent: 'capped',
        variance: 'diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'implicit', role: 'source-functor' },
            { name: 'G', plicity: 'implicit', role: 'target-functor' },
            { name: 'Y', plicity: 'explicit', role: 'object' },
            { name: 'eta', plicity: 'explicit', role: 'transfor' }
        ]
    },
    'transfor-hom-capped': {
        kind: 'projection',
        family: 'transfor-action',
        dimension: 'hom',
        extent: 'capped',
        variance: 'off-diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'implicit', role: 'source-functor' },
            { name: 'G', plicity: 'implicit', role: 'target-functor' },
            { name: 'X', plicity: 'implicit', role: 'source-endpoint' },
            { name: 'Y', plicity: 'implicit', role: 'target-endpoint' },
            { name: 'eta', plicity: 'explicit', role: 'transfor' },
            { name: 'f', plicity: 'explicit', role: 'arrow' }
        ]
    }
} as const satisfies Record<string, CoreOwnerSchema>;

export type CoreOwnerId = keyof typeof CORE_OWNER_SCHEMAS;

export type SurfaceOperationId =
    | 'functor.object'
    | 'functor.hom.capped'
    | 'transfor.component.capped'
    | 'transfor.hom.capped';

export type OperationOperandName = 'subject' | 'argument';

export type CoreTypeField =
    | 'category'
    | 'sourceCategory'
    | 'targetCategory'
    | 'sourceObject'
    | 'targetObject'
    | 'sourceFunctor'
    | 'targetFunctor';

export type SchemaValue =
    | {
        kind: 'operand-term';
        operand: OperationOperandName;
    }
    | {
        kind: 'operand-type-field';
        operand: OperationOperandName;
        field: CoreTypeField;
    }
    | {
        kind: 'owner-application';
        owner: CoreOwnerId;
        arguments: readonly SchemaValue[];
    };

export interface OperationOperandSchema {
    name: OperationOperandName;
    expectedType: CoreTypeTag;
    errorCode:
        | 'EXPECTED_FUNCTOR'
        | 'EXPECTED_OBJECT'
        | 'EXPECTED_HOM'
        | 'EXPECTED_TRANSFOR';
    expectation: string;
}

export interface OperationConstraintSchema {
    kind: 'equal';
    left: SchemaValue;
    right: SchemaValue;
    blame: OperationOperandName;
    errorCode: 'CATEGORY_MISMATCH';
}

export interface OperationOwnerArgumentSchema {
    slot: string;
    value: SchemaValue;
    origin: 'surface' | 'recovered';
}

export type CoreTypeTemplate =
    | { tag: 'category' }
    | { tag: 'object'; category: SchemaValue }
    | {
        tag: 'functor';
        sourceCategory: SchemaValue;
        targetCategory: SchemaValue;
    }
    | {
        tag: 'hom';
        category: SchemaValue;
        sourceObject: SchemaValue;
        targetObject: SchemaValue;
    }
    | {
        tag: 'transfor';
        sourceCategory: SchemaValue;
        targetCategory: SchemaValue;
        sourceFunctor: SchemaValue;
        targetFunctor: SchemaValue;
    };

export interface SurfaceOperationSchema {
    owner: CoreOwnerId;
    diagnosticLabel: string;
    operands: readonly OperationOperandSchema[];
    constraints: readonly OperationConstraintSchema[];
    ownerArguments: readonly OperationOwnerArgumentSchema[];
    result: CoreTypeTemplate;
}

const operandTerm = (
    operand: OperationOperandName
): SchemaValue => ({ kind: 'operand-term', operand });

const operandTypeField = (
    operand: OperationOperandName,
    field: CoreTypeField
): SchemaValue => ({ kind: 'operand-type-field', operand, field });

const ownerApplication = (
    owner: CoreOwnerId,
    ...values: readonly SchemaValue[]
): SchemaValue => ({ kind: 'owner-application', owner, arguments: values });

const subjectSource = operandTypeField('subject', 'sourceCategory');
const subjectTarget = operandTypeField('subject', 'targetCategory');
const argumentCategory = operandTypeField('argument', 'category');
const subjectTerm = operandTerm('subject');
const argumentTerm = operandTerm('argument');
const sourceFunctor = operandTypeField('subject', 'sourceFunctor');
const targetFunctor = operandTypeField('subject', 'targetFunctor');
const sourceObject = operandTypeField('argument', 'sourceObject');
const targetObject = operandTypeField('argument', 'targetObject');

const sameSourceCategory: OperationConstraintSchema = {
    kind: 'equal',
    left: subjectSource,
    right: argumentCategory,
    blame: 'argument',
    errorCode: 'CATEGORY_MISMATCH'
};

const functorObjectAt = (functor: SchemaValue, object: SchemaValue) =>
    ownerApplication(
        'functor-object',
        subjectSource,
        subjectTarget,
        functor,
        object
    );

/**
 * Declarative lowering and result-classifier schemas for the capped ladder.
 *
 * The elaborator interprets these records uniformly. Adding an operation must
 * not require another operation-specific switch branch.
 */
export const SURFACE_OPERATION_SCHEMAS = {
    'functor.object': {
        owner: 'functor-object',
        diagnosticLabel: 'functor object action',
        operands: [
            {
                name: 'subject',
                expectedType: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'its first operand to be an ordinary functor'
            },
            {
                name: 'argument',
                expectedType: 'object',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'its second operand to be an object'
            }
        ],
        constraints: [sameSourceCategory],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectTerm, origin: 'surface' },
            { slot: 'X', value: argumentTerm, origin: 'surface' }
        ],
        result: {
            tag: 'object',
            category: subjectTarget
        }
    },
    'functor.hom.capped': {
        owner: 'functor-hom-capped',
        diagnosticLabel: 'functor hom action',
        operands: [
            {
                name: 'subject',
                expectedType: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'an ordinary functor'
            },
            {
                name: 'argument',
                expectedType: 'hom',
                errorCode: 'EXPECTED_HOM',
                expectation: 'an ordinary source arrow'
            }
        ],
        constraints: [sameSourceCategory],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectTerm, origin: 'surface' },
            { slot: 'X', value: sourceObject, origin: 'recovered' },
            { slot: 'Y', value: targetObject, origin: 'recovered' },
            { slot: 'f', value: argumentTerm, origin: 'surface' }
        ],
        result: {
            tag: 'hom',
            category: subjectTarget,
            sourceObject: functorObjectAt(subjectTerm, sourceObject),
            targetObject: functorObjectAt(subjectTerm, targetObject)
        }
    },
    'transfor.component.capped': {
        owner: 'transfor-component-capped',
        diagnosticLabel: 'transfor point component',
        operands: [
            {
                name: 'subject',
                expectedType: 'transfor',
                errorCode: 'EXPECTED_TRANSFOR',
                expectation: 'an ordinary transfor'
            },
            {
                name: 'argument',
                expectedType: 'object',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'an ordinary source object'
            }
        ],
        constraints: [sameSourceCategory],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: sourceFunctor, origin: 'recovered' },
            { slot: 'G', value: targetFunctor, origin: 'recovered' },
            { slot: 'Y', value: argumentTerm, origin: 'surface' },
            { slot: 'eta', value: subjectTerm, origin: 'surface' }
        ],
        result: {
            tag: 'hom',
            category: subjectTarget,
            sourceObject: functorObjectAt(sourceFunctor, argumentTerm),
            targetObject: functorObjectAt(targetFunctor, argumentTerm)
        }
    },
    'transfor.hom.capped': {
        owner: 'transfor-hom-capped',
        diagnosticLabel: 'transfor off-diagonal hom action',
        operands: [
            {
                name: 'subject',
                expectedType: 'transfor',
                errorCode: 'EXPECTED_TRANSFOR',
                expectation: 'an ordinary transfor'
            },
            {
                name: 'argument',
                expectedType: 'hom',
                errorCode: 'EXPECTED_HOM',
                expectation: 'an ordinary source arrow'
            }
        ],
        constraints: [sameSourceCategory],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: sourceFunctor, origin: 'recovered' },
            { slot: 'G', value: targetFunctor, origin: 'recovered' },
            { slot: 'X', value: sourceObject, origin: 'recovered' },
            { slot: 'Y', value: targetObject, origin: 'recovered' },
            { slot: 'eta', value: subjectTerm, origin: 'surface' },
            { slot: 'f', value: argumentTerm, origin: 'surface' }
        ],
        result: {
            tag: 'hom',
            category: subjectTarget,
            sourceObject: functorObjectAt(sourceFunctor, sourceObject),
            targetObject: functorObjectAt(targetFunctor, targetObject)
        }
    }
} as const satisfies Record<SurfaceOperationId, SurfaceOperationSchema>;

/**
 * Fail fast if a catalog edit breaks the declared owner telescope.
 */
export function validateSurfaceOperationCatalog(): void {
    for (const [
        operationId,
        operation
    ] of Object.entries(SURFACE_OPERATION_SCHEMAS)) {
        const owner = CORE_OWNER_SCHEMAS[operation.owner];
        if (owner.slots.length !== operation.ownerArguments.length) {
            throw new Error(
                `Operation ${operationId} supplies ` +
                `${operation.ownerArguments.length} arguments to owner ` +
                `${operation.owner}, which declares ${owner.slots.length}`
            );
        }
        owner.slots.forEach((slot, index) => {
            const supplied = operation.ownerArguments[index];
            if (slot.name !== supplied.slot) {
                throw new Error(
                    `Operation ${operationId} supplies slot ` +
                    `${supplied.slot} at position ${index}, expected ${slot.name}`
                );
            }
        });
    }
}

validateSurfaceOperationCatalog();
