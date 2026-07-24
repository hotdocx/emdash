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

export type CoreOwnerKind =
    | 'classifier'
    | 'category-former'
    | 'functor-constructor'
    | 'projection';

export type CoreSlotRole =
    | 'classifier'
    | 'source-category'
    | 'target-category'
    | 'base-category'
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
        | 'groupoid-universe'
        | 'category-universe'
        | 'decode'
        | 'object'
        | 'functor'
        | 'hom'
        | 'transfor';
    slots: readonly CoreOwnerSlotSchema[];
}

export interface CategoryFormerOwnerSchema {
    kind: 'category-former';
    former:
        | 'category-of-categories'
        | 'opposite'
        | 'hom'
        | 'transfor'
        | 'displayed-family';
    slots: readonly CoreOwnerSlotSchema[];
}

export interface FunctorConstructorOwnerSchema {
    kind: 'functor-constructor';
    constructor: 'internal-hom-source' | 'internal-hom-target';
    slots: readonly CoreOwnerSlotSchema[];
}

export interface ProjectionOwnerSchema {
    kind: 'projection';
    family: 'functor-action' | 'transfor-action';
    dimension: 'object' | 'hom';
    extent: 'full' | 'capped' | 'evaluator';
    variance: 'diagonal' | 'off-diagonal';
    slots: readonly CoreOwnerSlotSchema[];
}

export type CoreOwnerSchema =
    | ClassifierOwnerSchema
    | CategoryFormerOwnerSchema
    | FunctorConstructorOwnerSchema
    | ProjectionOwnerSchema;

/**
 * The current backend-neutral Core owner catalog.
 *
 * No entry contains a backend symbol or module name. Slot order and plicity
 * are semantic declaration data shared by checking and all backends.
 */
export const CORE_OWNER_SCHEMAS = {
    'groupoid-universe': {
        kind: 'classifier',
        classifier: 'groupoid-universe',
        slots: []
    },
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
    'category-of-categories': {
        kind: 'category-former',
        former: 'category-of-categories',
        slots: []
    },
    'opposite-category': {
        kind: 'category-former',
        former: 'opposite',
        slots: [
            { name: 'A', plicity: 'explicit', role: 'category' }
        ]
    },
    'hom-category': {
        kind: 'category-former',
        former: 'hom',
        slots: [
            { name: 'A', plicity: 'explicit', role: 'category' },
            { name: 'X', plicity: 'explicit', role: 'source-endpoint' },
            { name: 'Y', plicity: 'explicit', role: 'target-endpoint' }
        ]
    },
    'transfor-category': {
        kind: 'category-former',
        former: 'transfor',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'explicit', role: 'source-functor' },
            { name: 'G', plicity: 'explicit', role: 'target-functor' }
        ]
    },
    'displayed-category-category': {
        kind: 'category-former',
        former: 'displayed-family',
        slots: [
            { name: 'K', plicity: 'explicit', role: 'base-category' }
        ]
    },
    'internal-hom-source': {
        kind: 'functor-constructor',
        constructor: 'internal-hom-source',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'target-category' },
            { name: 'B', plicity: 'implicit', role: 'source-category' },
            { name: 'F', plicity: 'explicit', role: 'functor' }
        ]
    },
    'internal-hom-target': {
        kind: 'functor-constructor',
        constructor: 'internal-hom-target',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'target-category' },
            { name: 'B', plicity: 'implicit', role: 'source-category' },
            { name: 'F', plicity: 'explicit', role: 'functor' }
        ]
    },
    'functor-object': {
        kind: 'projection',
        family: 'functor-action',
        dimension: 'object',
        extent: 'evaluator',
        variance: 'diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'explicit', role: 'functor' },
            { name: 'X', plicity: 'explicit', role: 'object' }
        ]
    },
    'functor-hom-full': {
        kind: 'projection',
        family: 'functor-action',
        dimension: 'hom',
        extent: 'full',
        variance: 'diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'explicit', role: 'functor' },
            { name: 'X', plicity: 'implicit', role: 'source-endpoint' },
            { name: 'Y', plicity: 'implicit', role: 'target-endpoint' }
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
    'transfor-component-full': {
        kind: 'projection',
        family: 'transfor-action',
        dimension: 'object',
        extent: 'full',
        variance: 'diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'implicit', role: 'source-functor' },
            { name: 'G', plicity: 'implicit', role: 'target-functor' },
            { name: 'Y', plicity: 'explicit', role: 'object' }
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
    'transfor-hom-full': {
        kind: 'projection',
        family: 'transfor-action',
        dimension: 'hom',
        extent: 'full',
        variance: 'off-diagonal',
        slots: [
            { name: 'A', plicity: 'implicit', role: 'source-category' },
            { name: 'B', plicity: 'implicit', role: 'target-category' },
            { name: 'F', plicity: 'implicit', role: 'source-functor' },
            { name: 'G', plicity: 'implicit', role: 'target-functor' },
            { name: 'X', plicity: 'implicit', role: 'source-endpoint' },
            { name: 'Y', plicity: 'implicit', role: 'target-endpoint' },
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

export interface ProjectionPairSchema {
    family: ProjectionOwnerSchema['family'];
    dimension: ProjectionOwnerSchema['dimension'];
    variance: ProjectionOwnerSchema['variance'];
    full: CoreOwnerId;
    capped: CoreOwnerId;
    evaluator: CoreOwnerId;
}

/**
 * The active kernel owns each evaluator connection by a rule of the shape
 * `fapp0(full, argument) ↪ capped`. Recording the pairs here keeps that
 * relationship visible without turning either side into a backend spelling.
 */
export const PROJECTION_PAIR_SCHEMAS = {
    'functor-hom': {
        family: 'functor-action',
        dimension: 'hom',
        variance: 'diagonal',
        full: 'functor-hom-full',
        capped: 'functor-hom-capped',
        evaluator: 'functor-object'
    },
    'transfor-component': {
        family: 'transfor-action',
        dimension: 'object',
        variance: 'diagonal',
        full: 'transfor-component-full',
        capped: 'transfor-component-capped',
        evaluator: 'functor-object'
    },
    'transfor-hom': {
        family: 'transfor-action',
        dimension: 'hom',
        variance: 'off-diagonal',
        full: 'transfor-hom-full',
        capped: 'transfor-hom-capped',
        evaluator: 'functor-object'
    }
} as const satisfies Record<string, ProjectionPairSchema>;

export type SurfaceOperationId =
    | 'internal-hom.source'
    | 'internal-hom.target'
    | 'functor.object'
    | 'functor.hom.full'
    | 'functor.hom.capped'
    | 'transfor.component.full'
    | 'transfor.component.capped'
    | 'transfor.hom.full'
    | 'transfor.hom.capped';

export type OperationOperandName = string;

export type CoreTypeField =
    | 'category'
    | 'sourceCategory'
    | 'targetCategory'
    | 'sourceObject'
    | 'targetObject'
    | 'sourceFunctor'
    | 'targetFunctor'
    | 'objectCategory';

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
    expectedKind: CoreTypeTag | 'object-like';
    errorCode:
        | 'EXPECTED_FUNCTOR'
        | 'EXPECTED_OBJECT'
        | 'EXPECTED_HOM'
        | 'EXPECTED_TRANSFOR';
    expectation: string;
}

export interface OperationConstraintSchema {
    kind: 'equal';
    comparison: 'category' | 'object-category';
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
    | { tag: 'object-of-category'; category: SchemaValue }
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
const argumentObjectCategory = operandTypeField('argument', 'objectCategory');
const subjectTerm = operandTerm('subject');
const argumentTerm = operandTerm('argument');
const subjectSourceFunctor = operandTypeField('subject', 'sourceFunctor');
const subjectTargetFunctor = operandTypeField('subject', 'targetFunctor');
const sourceObject = operandTypeField('argument', 'sourceObject');
const targetObject = operandTypeField('argument', 'targetObject');

const sourceEndpointTerm = operandTerm('sourceEndpoint');
const targetEndpointTerm = operandTerm('targetEndpoint');
const sourceEndpointCategory = operandTypeField(
    'sourceEndpoint',
    'objectCategory'
);
const targetEndpointCategory = operandTypeField(
    'targetEndpoint',
    'objectCategory'
);

const sourceFunctorTerm = operandTerm('sourceFunctor');
const targetFunctorTerm = operandTerm('targetFunctor');
const sourceFunctorSource = operandTypeField(
    'sourceFunctor',
    'sourceCategory'
);
const sourceFunctorTarget = operandTypeField(
    'sourceFunctor',
    'targetCategory'
);
const targetFunctorSource = operandTypeField(
    'targetFunctor',
    'sourceCategory'
);
const targetFunctorTarget = operandTypeField(
    'targetFunctor',
    'targetCategory'
);

const equal = (
    left: SchemaValue,
    right: SchemaValue,
    blame: OperationOperandName,
    comparison: OperationConstraintSchema['comparison'] = 'category'
): OperationConstraintSchema => ({
    kind: 'equal',
    comparison,
    left,
    right,
    blame,
    errorCode: 'CATEGORY_MISMATCH'
});

const functorObjectAt = (
    sourceCategory: SchemaValue,
    targetCategory: SchemaValue,
    functor: SchemaValue,
    object: SchemaValue
) =>
    ownerApplication(
        'functor-object',
        sourceCategory,
        targetCategory,
        functor,
        object
    );

const homCategoryAt = (
    category: SchemaValue,
    source: SchemaValue,
    target: SchemaValue
) => ownerApplication('hom-category', category, source, target);

const oppositeCategoryAt = (category: SchemaValue) =>
    ownerApplication('opposite-category', category);

const displayedCategoryAt = (baseCategory: SchemaValue) =>
    ownerApplication('displayed-category-category', baseCategory);

const transforCategoryAt = (
    sourceCategory: SchemaValue,
    targetCategory: SchemaValue,
    sourceFunctor: SchemaValue,
    targetFunctor: SchemaValue
) => ownerApplication(
    'transfor-category',
    sourceCategory,
    targetCategory,
    sourceFunctor,
    targetFunctor
);

/**
 * Declarative lowering and result-classifier schemas for the projection ladder.
 *
 * The elaborator interprets these records uniformly. Adding an operation must
 * not require another operation-specific switch branch.
 */
export const SURFACE_OPERATION_SCHEMAS = {
    'internal-hom.source': {
        owner: 'internal-hom-source',
        diagnosticLabel: 'source-internalized hom',
        operands: [
            {
                name: 'subject',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'an ordinary endpoint functor'
            }
        ],
        constraints: [],
        ownerArguments: [
            { slot: 'A', value: subjectTarget, origin: 'recovered' },
            { slot: 'B', value: subjectSource, origin: 'recovered' },
            { slot: 'F', value: subjectTerm, origin: 'surface' }
        ],
        result: {
            tag: 'functor',
            sourceCategory: oppositeCategoryAt(subjectTarget),
            targetCategory: displayedCategoryAt(subjectSource)
        }
    },
    'internal-hom.target': {
        owner: 'internal-hom-target',
        diagnosticLabel: 'target-internalized hom',
        operands: [
            {
                name: 'subject',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'an ordinary endpoint functor'
            }
        ],
        constraints: [],
        ownerArguments: [
            { slot: 'A', value: subjectTarget, origin: 'recovered' },
            { slot: 'B', value: subjectSource, origin: 'recovered' },
            { slot: 'F', value: subjectTerm, origin: 'surface' }
        ],
        result: {
            tag: 'functor',
            sourceCategory: subjectTarget,
            targetCategory: displayedCategoryAt(
                oppositeCategoryAt(subjectSource)
            )
        }
    },
    'functor.object': {
        owner: 'functor-object',
        diagnosticLabel: 'functor object action',
        operands: [
            {
                name: 'subject',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'its first operand to be an ordinary functor'
            },
            {
                name: 'argument',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'its second operand to be an object of a category'
            }
        ],
        constraints: [
            equal(
                subjectSource,
                argumentObjectCategory,
                'argument',
                'object-category'
            )
        ],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectTerm, origin: 'surface' },
            { slot: 'X', value: argumentTerm, origin: 'surface' }
        ],
        result: {
            tag: 'object-of-category',
            category: subjectTarget
        }
    },
    'functor.hom.full': {
        owner: 'functor-hom-full',
        diagnosticLabel: 'full functor hom action',
        operands: [
            {
                name: 'subject',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'an ordinary functor'
            },
            {
                name: 'sourceEndpoint',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'a source endpoint object'
            },
            {
                name: 'targetEndpoint',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'a target endpoint object'
            }
        ],
        constraints: [
            equal(
                subjectSource,
                sourceEndpointCategory,
                'sourceEndpoint',
                'object-category'
            ),
            equal(
                subjectSource,
                targetEndpointCategory,
                'targetEndpoint',
                'object-category'
            )
        ],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectTerm, origin: 'surface' },
            { slot: 'X', value: sourceEndpointTerm, origin: 'surface' },
            { slot: 'Y', value: targetEndpointTerm, origin: 'surface' }
        ],
        result: {
            tag: 'functor',
            sourceCategory: homCategoryAt(
                subjectSource,
                sourceEndpointTerm,
                targetEndpointTerm
            ),
            targetCategory: homCategoryAt(
                subjectTarget,
                functorObjectAt(
                    subjectSource,
                    subjectTarget,
                    subjectTerm,
                    sourceEndpointTerm
                ),
                functorObjectAt(
                    subjectSource,
                    subjectTarget,
                    subjectTerm,
                    targetEndpointTerm
                )
            )
        }
    },
    'functor.hom.capped': {
        owner: 'functor-hom-capped',
        diagnosticLabel: 'functor hom action',
        operands: [
            {
                name: 'subject',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'an ordinary functor'
            },
            {
                name: 'argument',
                expectedKind: 'hom',
                errorCode: 'EXPECTED_HOM',
                expectation: 'an ordinary source arrow'
            }
        ],
        constraints: [
            equal(subjectSource, argumentCategory, 'argument')
        ],
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
            sourceObject: functorObjectAt(
                subjectSource,
                subjectTarget,
                subjectTerm,
                sourceObject
            ),
            targetObject: functorObjectAt(
                subjectSource,
                subjectTarget,
                subjectTerm,
                targetObject
            )
        }
    },
    'transfor.component.full': {
        owner: 'transfor-component-full',
        diagnosticLabel: 'full transfor point component',
        operands: [
            {
                name: 'sourceFunctor',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'a source functor'
            },
            {
                name: 'targetFunctor',
                expectedKind: 'functor',
                errorCode: 'EXPECTED_FUNCTOR',
                expectation: 'a target functor'
            },
            {
                name: 'argument',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'a source object'
            }
        ],
        constraints: [
            equal(sourceFunctorSource, targetFunctorSource, 'targetFunctor'),
            equal(sourceFunctorTarget, targetFunctorTarget, 'targetFunctor'),
            equal(
                sourceFunctorSource,
                argumentObjectCategory,
                'argument',
                'object-category'
            )
        ],
        ownerArguments: [
            { slot: 'A', value: sourceFunctorSource, origin: 'recovered' },
            { slot: 'B', value: sourceFunctorTarget, origin: 'recovered' },
            { slot: 'F', value: sourceFunctorTerm, origin: 'surface' },
            { slot: 'G', value: targetFunctorTerm, origin: 'surface' },
            { slot: 'Y', value: argumentTerm, origin: 'surface' }
        ],
        result: {
            tag: 'functor',
            sourceCategory: transforCategoryAt(
                sourceFunctorSource,
                sourceFunctorTarget,
                sourceFunctorTerm,
                targetFunctorTerm
            ),
            targetCategory: homCategoryAt(
                sourceFunctorTarget,
                functorObjectAt(
                    sourceFunctorSource,
                    sourceFunctorTarget,
                    sourceFunctorTerm,
                    argumentTerm
                ),
                functorObjectAt(
                    sourceFunctorSource,
                    sourceFunctorTarget,
                    targetFunctorTerm,
                    argumentTerm
                )
            )
        }
    },
    'transfor.component.capped': {
        owner: 'transfor-component-capped',
        diagnosticLabel: 'transfor point component',
        operands: [
            {
                name: 'subject',
                expectedKind: 'transfor',
                errorCode: 'EXPECTED_TRANSFOR',
                expectation: 'an ordinary transfor'
            },
            {
                name: 'argument',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'an object of the transfor source category'
            }
        ],
        constraints: [
            equal(
                subjectSource,
                argumentObjectCategory,
                'argument',
                'object-category'
            )
        ],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectSourceFunctor, origin: 'recovered' },
            { slot: 'G', value: subjectTargetFunctor, origin: 'recovered' },
            { slot: 'Y', value: argumentTerm, origin: 'surface' },
            { slot: 'eta', value: subjectTerm, origin: 'surface' }
        ],
        result: {
            tag: 'hom',
            category: subjectTarget,
            sourceObject: functorObjectAt(
                subjectSource,
                subjectTarget,
                subjectSourceFunctor,
                argumentTerm
            ),
            targetObject: functorObjectAt(
                subjectSource,
                subjectTarget,
                subjectTargetFunctor,
                argumentTerm
            )
        }
    },
    'transfor.hom.full': {
        owner: 'transfor-hom-full',
        diagnosticLabel: 'full transfor off-diagonal hom action',
        operands: [
            {
                name: 'subject',
                expectedKind: 'transfor',
                errorCode: 'EXPECTED_TRANSFOR',
                expectation: 'an ordinary transfor'
            },
            {
                name: 'sourceEndpoint',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'a source endpoint object'
            },
            {
                name: 'targetEndpoint',
                expectedKind: 'object-like',
                errorCode: 'EXPECTED_OBJECT',
                expectation: 'a target endpoint object'
            }
        ],
        constraints: [
            equal(
                subjectSource,
                sourceEndpointCategory,
                'sourceEndpoint',
                'object-category'
            ),
            equal(
                subjectSource,
                targetEndpointCategory,
                'targetEndpoint',
                'object-category'
            )
        ],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectSourceFunctor, origin: 'recovered' },
            { slot: 'G', value: subjectTargetFunctor, origin: 'recovered' },
            { slot: 'X', value: sourceEndpointTerm, origin: 'surface' },
            { slot: 'Y', value: targetEndpointTerm, origin: 'surface' },
            { slot: 'eta', value: subjectTerm, origin: 'surface' }
        ],
        result: {
            tag: 'functor',
            sourceCategory: homCategoryAt(
                subjectSource,
                sourceEndpointTerm,
                targetEndpointTerm
            ),
            targetCategory: homCategoryAt(
                subjectTarget,
                functorObjectAt(
                    subjectSource,
                    subjectTarget,
                    subjectSourceFunctor,
                    sourceEndpointTerm
                ),
                functorObjectAt(
                    subjectSource,
                    subjectTarget,
                    subjectTargetFunctor,
                    targetEndpointTerm
                )
            )
        }
    },
    'transfor.hom.capped': {
        owner: 'transfor-hom-capped',
        diagnosticLabel: 'transfor off-diagonal hom action',
        operands: [
            {
                name: 'subject',
                expectedKind: 'transfor',
                errorCode: 'EXPECTED_TRANSFOR',
                expectation: 'an ordinary transfor'
            },
            {
                name: 'argument',
                expectedKind: 'hom',
                errorCode: 'EXPECTED_HOM',
                expectation: 'an ordinary source arrow'
            }
        ],
        constraints: [
            equal(subjectSource, argumentCategory, 'argument')
        ],
        ownerArguments: [
            { slot: 'A', value: subjectSource, origin: 'recovered' },
            { slot: 'B', value: subjectTarget, origin: 'recovered' },
            { slot: 'F', value: subjectSourceFunctor, origin: 'recovered' },
            { slot: 'G', value: subjectTargetFunctor, origin: 'recovered' },
            { slot: 'X', value: sourceObject, origin: 'recovered' },
            { slot: 'Y', value: targetObject, origin: 'recovered' },
            { slot: 'eta', value: subjectTerm, origin: 'surface' },
            { slot: 'f', value: argumentTerm, origin: 'surface' }
        ],
        result: {
            tag: 'hom',
            category: subjectTarget,
            sourceObject: functorObjectAt(
                subjectSource,
                subjectTarget,
                subjectSourceFunctor,
                sourceObject
            ),
            targetObject: functorObjectAt(
                subjectSource,
                subjectTarget,
                subjectTargetFunctor,
                targetObject
            )
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

        const operandNames = operation.operands.map(operand => operand.name);
        if (new Set(operandNames).size !== operandNames.length) {
            throw new Error(
                `Operation ${operationId} declares a duplicate operand name`
            );
        }
    }
}

export function validateProjectionPairCatalog(): void {
    for (const [pairId, pair] of Object.entries(PROJECTION_PAIR_SCHEMAS)) {
        const full = CORE_OWNER_SCHEMAS[pair.full];
        const capped = CORE_OWNER_SCHEMAS[pair.capped];
        const evaluator = CORE_OWNER_SCHEMAS[pair.evaluator];

        if (full.kind !== 'projection' || full.extent !== 'full') {
            throw new Error(
                `Projection pair ${pairId} does not name a full projection`
            );
        }
        if (capped.kind !== 'projection' || capped.extent !== 'capped') {
            throw new Error(
                `Projection pair ${pairId} does not name a capped projection`
            );
        }
        if (
            full.family !== pair.family ||
            capped.family !== pair.family ||
            full.dimension !== pair.dimension ||
            capped.dimension !== pair.dimension ||
            full.variance !== pair.variance ||
            capped.variance !== pair.variance
        ) {
            throw new Error(
                `Projection pair ${pairId} disagrees with its owner metadata`
            );
        }
        if (
            evaluator.kind !== 'projection' ||
            evaluator.family !== 'functor-action' ||
            evaluator.dimension !== 'object' ||
            evaluator.extent !== 'evaluator'
        ) {
            throw new Error(
                `Projection pair ${pairId} has a non-evaluator projection`
            );
        }
    }
}

validateSurfaceOperationCatalog();
validateProjectionPairCatalog();
