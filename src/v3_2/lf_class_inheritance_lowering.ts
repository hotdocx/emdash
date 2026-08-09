/**
 * Ordinary outer-LF lowering for direct class-parent conversions.
 *
 * Identity planning remains in `lf_class_inheritance`. This module turns one
 * reviewed identity layout into transparent definitions which reconstruct
 * each direct parent from the child's existing physical projections. It adds
 * no Core node, rewrite rule, proof rule, or instance-search behavior.
 */

import { BinderMode } from './kernel';
import {
    CoreLfClassDirectParentSchema,
    CoreLfClassReference,
    CoreLfClassSchema
} from './lf_class_schema';
import {
    CoreLfClassInheritanceLayout,
    CoreLfClassInheritanceSlot,
    CoreLfClassInheritanceError,
    validateCoreLfClassInheritanceLayout
} from './lf_class_inheritance';
import {
    CoreLfStructureMacroError,
    CoreLfStructureNamedParameterArgument,
    CoreLfStructureParameterHandle,
    CoreLfStructureProjectionHandle,
    constructCoreLfNamedStructure
} from './lf_structure_macro';
import {
    CoreLfQualifiedSymbol,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferProvenance,
    coreLfTransferExplicitBody
} from './lf_transfer';

export const CORE_LF_CLASS_INHERITANCE_LOWERING_PROFILE = Object.freeze({
    revision: 'emdash-lf-class-inheritance-lowering-v1' as const
});

export type CoreLfClassInheritanceLoweringErrorCode =
    | 'INVALID_INHERITANCE_LOWERING'
    | 'LAYOUT_MISMATCH'
    | 'PARENT_LAYOUT_MISMATCH'
    | 'INVALID_PARENT_CONVERSION'
    | 'DUPLICATE_PARENT_CONVERSION'
    | 'MISSING_PARENT_CONVERSION'
    | 'DUPLICATE_SYMBOL'
    | 'UNMAPPED_PARENT_FIELD'
    | 'INVALID_APPLICATION'
    | 'FOREIGN_ARGUMENT'
    | 'DUPLICATE_ARGUMENT'
    | 'MISSING_ARGUMENT';

export class CoreLfClassInheritanceLoweringError extends Error {
    constructor(
        public readonly code: CoreLfClassInheritanceLoweringErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfClassInheritanceLoweringError';
    }
}

export interface CoreLfClassDirectParentLoweringInput {
    readonly layout: CoreLfClassInheritanceLayout;
    readonly conversionName: string;
}

export interface CoreLfLowerClassInheritanceInput {
    readonly layout: CoreLfClassInheritanceLayout;
    readonly order: number;
    readonly directParents:
        readonly CoreLfClassDirectParentLoweringInput[];
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfClassParentConversionReceiver {
    readonly authoringRole: 'class-evidence';
    readonly corePlicity: 'explicit';
}

export interface CoreLfClassParentConversionHandle {
    readonly ordinal: number;
    readonly child: CoreLfClassReference;
    readonly parent: CoreLfClassReference;
    readonly parameters: readonly CoreLfStructureParameterHandle[];
    readonly symbol: CoreLfQualifiedSymbol;
    readonly term: CoreLfTransferExpression;
    readonly type: CoreLfTransferExpression;
    readonly receiver: CoreLfClassParentConversionReceiver;
}

export interface CoreLfClassInheritanceLoweringExpansion {
    readonly kind: 'expanded-class-inheritance';
    readonly revision:
        typeof CORE_LF_CLASS_INHERITANCE_LOWERING_PROFILE.revision;
    readonly status: 'parent-conversions-expanded';
    readonly layout: CoreLfClassInheritanceLayout;
    readonly sourceOrders: readonly number[];
    readonly declarations: readonly CoreLfTransferDeclaration[];
    readonly directParentConversions:
        readonly CoreLfClassParentConversionHandle[];
    readonly nextOrder: number;
}

export interface CoreLfApplyClassParentConversionInput {
    readonly conversion: CoreLfClassParentConversionHandle;
    readonly parameters:
        readonly CoreLfStructureNamedParameterArgument[];
    readonly evidence: CoreLfTransferExpression;
}

interface CheckedParentInput {
    readonly path: string;
    readonly layout: CoreLfClassInheritanceLayout;
    readonly conversionName: string;
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const OUTPUT_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u;

const fail = (
    code: CoreLfClassInheritanceLoweringErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfClassInheritanceLoweringError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) return value.map(cloneData) as T;
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value as Record<string, unknown>).map(
                ([key, entry]) => [key, cloneData(entry)]
            )
        ) as T;
    }
    return value;
};

const qualifiedSymbol = (
    value: unknown,
    path: string,
    code: CoreLfClassInheritanceLoweringErrorCode
): CoreLfQualifiedSymbol => {
    if (
        !record(value) ||
        typeof value.moduleId !== 'string' ||
        !MODULE_ID.test(value.moduleId) ||
        typeof value.name !== 'string' ||
        value.name.length === 0 ||
        value.name.trim() !== value.name ||
        /[\s\u0000-\u001f\u007f]/u.test(value.name)
    ) {
        return fail(code, path, 'Expected one valid exact qualified symbol');
    }
    return { moduleId: value.moduleId, name: value.name };
};

const symbolKey = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}\u0000${value.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const classReference = (
    value: unknown,
    path: string,
    code: CoreLfClassInheritanceLoweringErrorCode
): CoreLfClassReference => {
    if (
        !record(value) ||
        !Number.isSafeInteger(value.parameterCount) ||
        (value.parameterCount as number) < 0
    ) {
        return fail(code, path, 'Expected one valid class reference');
    }
    return {
        classId: qualifiedSymbol(value.classId, `${path}.classId`, code),
        parameterCount: value.parameterCount as number
    };
};

const sameReference = (
    left: CoreLfClassReference,
    right: CoreLfClassReference
): boolean =>
    sameSymbol(left.classId, right.classId) &&
    left.parameterCount === right.parameterCount;

const mode = (
    value: unknown,
    path: string,
    code: CoreLfClassInheritanceLoweringErrorCode
): BinderMode => {
    if (
        !record(value) ||
        (
            value.plicity !== 'explicit' &&
            value.plicity !== 'implicit'
        ) ||
        (
            value.variation !== 'functorial' &&
            value.variation !== 'natural' &&
            value.variation !== 'object-only'
        )
    ) {
        return fail(code, path, 'Expected one valid binder mode');
    }
    return {
        plicity: value.plicity,
        variation: value.variation
    };
};

const sameMode = (left: BinderMode, right: BinderMode): boolean =>
    left.plicity === right.plicity &&
    left.variation === right.variation;

const parameterHandle = (
    value: unknown,
    path: string,
    structure: CoreLfQualifiedSymbol
): CoreLfStructureParameterHandle => {
    if (
        !record(value) ||
        !Number.isSafeInteger(value.ordinal) ||
        (value.ordinal as number) < 0 ||
        typeof value.binderName !== 'string' ||
        !OUTPUT_NAME.test(value.binderName) ||
        !record(value.modes)
    ) {
        return fail(
            'INVALID_APPLICATION',
            path,
            'Malformed class-conversion parameter handle'
        );
    }
    const owner = qualifiedSymbol(
        value.structure,
        `${path}.structure`,
        'INVALID_APPLICATION'
    );
    if (!sameSymbol(owner, structure)) {
        return fail(
            'INVALID_APPLICATION',
            path,
            'Class-conversion parameter has a foreign structure owner'
        );
    }
    return {
        ordinal: value.ordinal as number,
        binderName: value.binderName,
        structure: owner,
        modes: {
            carrier: mode(
                value.modes.carrier,
                `${path}.modes.carrier`,
                'INVALID_APPLICATION'
            ),
            constructor: mode(
                value.modes.constructor,
                `${path}.modes.constructor`,
                'INVALID_APPLICATION'
            ),
            projection: mode(
                value.modes.projection,
                `${path}.modes.projection`,
                'INVALID_APPLICATION'
            )
        }
    };
};

const sameParameter = (
    left: CoreLfStructureParameterHandle,
    right: unknown
): boolean => {
    if (!record(right) || !record(right.modes)) return false;
    let owner: CoreLfQualifiedSymbol;
    let carrier: BinderMode;
    let constructor: BinderMode;
    let projection: BinderMode;
    try {
        owner = qualifiedSymbol(
            right.structure,
            'argument.parameter.structure',
            'FOREIGN_ARGUMENT'
        );
        carrier = mode(
            right.modes.carrier,
            'argument.parameter.modes.carrier',
            'FOREIGN_ARGUMENT'
        );
        constructor = mode(
            right.modes.constructor,
            'argument.parameter.modes.constructor',
            'FOREIGN_ARGUMENT'
        );
        projection = mode(
            right.modes.projection,
            'argument.parameter.modes.projection',
            'FOREIGN_ARGUMENT'
        );
    } catch {
        return false;
    }
    return right.ordinal === left.ordinal &&
        right.binderName === left.binderName &&
        sameSymbol(owner, left.structure) &&
        sameMode(carrier, left.modes.carrier) &&
        sameMode(constructor, left.modes.constructor) &&
        sameMode(projection, left.modes.projection);
};

const cloneOpenTerm = (
    value: unknown,
    path: string
): CoreLfTransferExpression => {
    if (!record(value) || typeof value.tag !== 'string') {
        return fail(
            'INVALID_APPLICATION',
            path,
            'Expected one ordinary transfer term'
        );
    }
    switch (value.tag) {
        case 'type':
            return { tag: 'type' };
        case 'bound':
            if (
                !Number.isSafeInteger(value.index) ||
                (value.index as number) < 0
            ) {
                return fail(
                    'INVALID_APPLICATION',
                    `${path}.index`,
                    'Open transfer term has an invalid bound index'
                );
            }
            return { tag: 'bound', index: value.index as number };
        case 'global':
            return {
                tag: 'global',
                symbol: qualifiedSymbol(
                    value.symbol,
                    `${path}.symbol`,
                    'INVALID_APPLICATION'
                )
            };
        case 'call':
            if (!Array.isArray(value.arguments) || value.arguments.length === 0) {
                return fail(
                    'INVALID_APPLICATION',
                    `${path}.arguments`,
                    'Transfer call requires at least one argument'
                );
            }
            return {
                tag: 'call',
                callee: cloneOpenTerm(value.callee, `${path}.callee`),
                arguments: value.arguments.map((argument, index) => {
                    if (
                        !record(argument) ||
                        (
                            argument.plicity !== 'explicit' &&
                            argument.plicity !== 'implicit'
                        )
                    ) {
                        return fail(
                            'INVALID_APPLICATION',
                            `${path}.arguments[${index}]`,
                            'Transfer argument has invalid plicity'
                        );
                    }
                    return {
                        plicity: argument.plicity,
                        value: cloneOpenTerm(
                            argument.value,
                            `${path}.arguments[${index}].value`
                        )
                    };
                })
            };
        case 'pi':
        case 'lambda':
            if (
                !record(value.binder) ||
                typeof value.binder.hint !== 'string' ||
                !OUTPUT_NAME.test(value.binder.hint)
            ) {
                return fail(
                    'INVALID_APPLICATION',
                    `${path}.binder`,
                    'Transfer binder is malformed'
                );
            }
            return {
                tag: value.tag,
                binder: {
                    hint: value.binder.hint,
                    mode: mode(
                        value.binder.mode,
                        `${path}.binder.mode`,
                        'INVALID_APPLICATION'
                    ),
                    type: cloneOpenTerm(
                        value.binder.type,
                        `${path}.binder.type`
                    )
                },
                body: cloneOpenTerm(value.body, `${path}.body`)
            };
        case 'capture':
        case 'wildcard':
            return fail(
                'INVALID_APPLICATION',
                path,
                'Class-conversion applications reject rule-only syntax'
            );
        default:
            return fail(
                'INVALID_APPLICATION',
                path,
                'Unknown transfer term tag'
            );
    }
};

const shiftTerm = (
    expression: CoreLfTransferExpression,
    amount: number,
    cutoff = 0
): CoreLfTransferExpression => {
    switch (expression.tag) {
        case 'type':
        case 'global':
            return cloneData(expression);
        case 'bound': {
            if (expression.index < cutoff) return { ...expression };
            const index = expression.index + amount;
            if (!Number.isSafeInteger(index) || index < cutoff) {
                return fail(
                    'INVALID_INHERITANCE_LOWERING',
                    'input.layout.schema.directParents',
                    'Parent substitution escapes the child telescope'
                );
            }
            return { tag: 'bound', index };
        }
        case 'call':
            return {
                tag: 'call',
                callee: shiftTerm(expression.callee, amount, cutoff),
                arguments: expression.arguments.map(argument => ({
                    plicity: argument.plicity,
                    value: shiftTerm(argument.value, amount, cutoff)
                }))
            };
        case 'pi':
        case 'lambda':
            return {
                tag: expression.tag,
                binder: {
                    hint: expression.binder.hint,
                    mode: { ...expression.binder.mode },
                    type: shiftTerm(
                        expression.binder.type,
                        amount,
                        cutoff
                    )
                },
                body: shiftTerm(expression.body, amount, cutoff + 1)
            };
        case 'capture':
        case 'wildcard':
            return fail(
                'INVALID_INHERITANCE_LOWERING',
                'input.layout.schema.directParents',
                'Parent applications cannot contain rule-only syntax'
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const snapshotLayout = (
    value: unknown,
    path: string,
    code: 'LAYOUT_MISMATCH' | 'PARENT_LAYOUT_MISMATCH'
): CoreLfClassInheritanceLayout => {
    try {
        return validateCoreLfClassInheritanceLayout(value);
    } catch (error) {
        if (error instanceof CoreLfClassInheritanceError) {
            return fail(code, path, error.message);
        }
        return fail(code, path, 'Malformed class identity layout');
    }
};

const validateProvenance = (
    value: unknown
): CoreLfTransferProvenance => {
    if (
        !record(value) ||
        typeof value.authorityPath !== 'string' ||
        value.authorityPath.trim().length === 0 ||
        typeof value.sourceFragment !== 'string' ||
        value.sourceFragment.trim().length === 0 ||
        (
            value.canonicalCommandOrdinal !== undefined &&
            (
                !Number.isSafeInteger(value.canonicalCommandOrdinal) ||
                (value.canonicalCommandOrdinal as number) < 0
            )
        )
    ) {
        return fail(
            'INVALID_INHERITANCE_LOWERING',
            'input.provenance',
            'Class inheritance lowering requires valid source provenance'
        );
    }
    return {
        authorityPath: value.authorityPath,
        sourceFragment: value.sourceFragment,
        ...(value.canonicalCommandOrdinal === undefined
            ? {}
            : {
                canonicalCommandOrdinal:
                    value.canonicalCommandOrdinal as number
            })
    };
};

const childReference = (
    schema: CoreLfClassSchema
): CoreLfClassReference => ({
    classId: cloneData(schema.classId),
    parameterCount: schema.parameters.length
});

const globalTerm = (
    symbol: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({
    tag: 'global',
    symbol: cloneData(symbol)
});

const call = (
    callee: CoreLfTransferExpression,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => ({
    tag: 'call',
    callee,
    arguments: arguments_.map(argument => ({
        plicity: argument.plicity,
        value: cloneData(argument.value)
    }))
});

const carrierApplication = (
    schema: CoreLfClassSchema,
    innerBinderCount: number
): CoreLfTransferExpression => schema.parameters.length === 0
    ? globalTerm(schema.structure.carrier)
    : call(
        globalTerm(schema.structure.carrier),
        schema.parameters.map(parameter => ({
            plicity: parameter.parameter.modes.carrier.plicity,
            value: {
                tag: 'bound' as const,
                index:
                    innerBinderCount +
                    schema.parameters.length -
                    parameter.parameter.ordinal -
                    1
            }
        }))
    );

const wrapClassParameters = (
    tag: 'pi' | 'lambda',
    schema: CoreLfClassSchema,
    body: CoreLfTransferExpression
): CoreLfTransferExpression => schema.parameters.reduceRight(
    (current, parameter) => ({
        tag,
        binder: {
            hint: parameter.parameter.binderName,
            mode: cloneData(parameter.parameter.modes.projection),
            type: cloneData(parameter.declaredType)
        },
        body: current
    }),
    body
);

const childProjection = (
    schema: CoreLfClassSchema,
    field: CoreLfStructureProjectionHandle
): CoreLfTransferExpression => call(
    globalTerm(field.symbol),
    [
        ...schema.parameters.map(parameter => ({
            plicity: parameter.parameter.modes.projection.plicity,
            value: {
                tag: 'bound' as const,
                index:
                    schema.parameters.length -
                    parameter.parameter.ordinal
            }
        })),
        {
            plicity: 'explicit' as const,
            value: { tag: 'bound' as const, index: 0 }
        }
    ]
);

const identityKey = (
    identity: CoreLfClassInheritanceSlot['canonicalIdentity']
): string => `${symbolKey(identity.declaringClass)}\u0000${identity.ordinal}`;

const matchingChildSlot = (
    child: CoreLfClassInheritanceLayout,
    parentSlot: CoreLfClassInheritanceSlot,
    path: string
): CoreLfClassInheritanceSlot => {
    const parentIdentities = new Set(
        parentSlot.identities.map(identityKey)
    );
    const matches = child.slots.filter(slot =>
        slot.identities.some(identity =>
            parentIdentities.has(identityKey(identity))
        )
    );
    if (matches.length !== 1) {
        return fail(
            'UNMAPPED_PARENT_FIELD',
            path,
            matches.length === 0
                ? 'Parent identity has no child physical slot'
                : 'Parent identity maps to multiple child physical slots'
        );
    }
    return matches[0];
};

const conversionType = (
    child: CoreLfClassInheritanceLayout,
    parent: CoreLfClassDirectParentSchema
): CoreLfTransferExpression => wrapClassParameters(
    'pi',
    child.schema,
    {
        tag: 'pi',
        binder: {
            hint: 'self',
            mode: {
                plicity: 'explicit',
                variation: 'functorial'
            },
            type: carrierApplication(child.schema, 0)
        },
        body: shiftTerm(parent.application, 1)
    }
);

const conversionBody = (
    child: CoreLfClassInheritanceLayout,
    parent: CoreLfClassDirectParentSchema,
    parentLayout: CoreLfClassInheritanceLayout,
    path: string
): CoreLfTransferExpression => {
    const parameters = parentLayout.schema.structure.parameters.map(
        (parameter, index) => ({
            parameter,
            value: shiftTerm(parent.arguments[index].value, 1)
        })
    );
    const fields = parentLayout.slots.map((parentSlot, index) => {
        const childSlot = matchingChildSlot(
            child,
            parentSlot,
            `${path}.layout.slots[${index}]`
        );
        return {
            field: parentSlot.physicalField,
            value: childProjection(
                child.schema,
                childSlot.physicalField
            )
        };
    });
    let constructed: CoreLfTransferExpression;
    try {
        constructed = constructCoreLfNamedStructure({
            structure: parentLayout.schema.structure,
            parameters,
            fields
        });
    } catch (error) {
        if (error instanceof CoreLfStructureMacroError) {
            return fail(
                'INVALID_INHERITANCE_LOWERING',
                path,
                `Parent reconstruction is invalid: ${error.message}`
            );
        }
        throw error;
    }
    return wrapClassParameters(
        'lambda',
        child.schema,
        {
            tag: 'lambda',
            binder: {
                hint: 'self',
                mode: {
                    plicity: 'explicit',
                    variation: 'functorial'
                },
                type: carrierApplication(child.schema, 0)
            },
            body: constructed
        }
    );
};

const checkedParentInputs = (
    layout: CoreLfClassInheritanceLayout,
    value: unknown
): readonly CheckedParentInput[] => {
    if (!Array.isArray(value)) {
        return fail(
            'INVALID_INHERITANCE_LOWERING',
            'input.directParents',
            'Direct parent conversions must be an array'
        );
    }
    const canonical: Array<CheckedParentInput | undefined> =
        new Array(layout.schema.directParents.length);
    const names = new Map<string, string>();
    const childSymbols = new Set([
        symbolKey(layout.schema.structure.carrier),
        symbolKey(layout.schema.structure.constructor),
        ...layout.schema.structure.projections.map(field =>
            symbolKey(field.symbol)
        )
    ]);

    value.forEach((entry, inputIndex) => {
        const path = `input.directParents[${inputIndex}]`;
        if (
            !record(entry) ||
            typeof entry.conversionName !== 'string' ||
            !OUTPUT_NAME.test(entry.conversionName)
        ) {
            return fail(
                'INVALID_PARENT_CONVERSION',
                path,
                'Direct parent entry needs one valid conversion name'
            );
        }
        const parentLayout = snapshotLayout(
            entry.layout,
            `${path}.layout`,
            'PARENT_LAYOUT_MISMATCH'
        );
        const parentReference: CoreLfClassReference = {
            classId: parentLayout.classId,
            parameterCount: parentLayout.schema.parameters.length
        };
        const ordinal = layout.schema.directParents.findIndex(parent =>
            sameReference(parent.parent, parentReference)
        );
        if (ordinal < 0) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.layout`,
                'Supplied layout is not one of the child direct parents'
            );
        }
        if (canonical[ordinal] !== undefined) {
            return fail(
                'DUPLICATE_PARENT_CONVERSION',
                `${path}.layout`,
                'Direct parent conversion was supplied more than once'
            );
        }
        const symbol: CoreLfQualifiedSymbol = {
            moduleId: layout.classId.moduleId,
            name: entry.conversionName
        };
        const key = symbolKey(symbol);
        if (childSymbols.has(key) || names.has(key)) {
            return fail(
                'DUPLICATE_SYMBOL',
                `${path}.conversionName`,
                `Generated conversion symbol '${entry.conversionName}' ` +
                    'collides with another child symbol'
            );
        }
        names.set(key, path);
        canonical[ordinal] = {
            path,
            layout: parentLayout,
            conversionName: entry.conversionName
        };
    });

    layout.schema.directParents.forEach((parent, index) => {
        if (canonical[index] === undefined) {
            fail(
                'MISSING_PARENT_CONVERSION',
                'input.directParents',
                `Missing conversion for direct parent ` +
                    `'${parent.parent.classId.moduleId}.` +
                    `${parent.parent.classId.name}'`
            );
        }
    });
    return canonical as readonly CheckedParentInput[];
};

/**
 * Expand one identity layout to transparent direct-parent definitions.
 */
export function lowerCoreLfClassInheritance(
    input: CoreLfLowerClassInheritanceInput
): CoreLfClassInheritanceLoweringExpansion {
    if (!record(input)) {
        return fail(
            'INVALID_INHERITANCE_LOWERING',
            'input',
            'Class inheritance lowering input must be an object'
        );
    }
    const layout = snapshotLayout(input.layout, 'input.layout', 'LAYOUT_MISMATCH');
    if (!Number.isSafeInteger(input.order) || input.order < 0) {
        return fail(
            'INVALID_INHERITANCE_LOWERING',
            'input.order',
            'First conversion source order must be nonnegative and safe'
        );
    }
    const parents = checkedParentInputs(layout, input.directParents);
    if (input.order > Number.MAX_SAFE_INTEGER - parents.length) {
        return fail(
            'INVALID_INHERITANCE_LOWERING',
            'input.order',
            'Direct parent conversions exceed the safe source-order range'
        );
    }
    const provenance = validateProvenance(input.provenance);
    const child = childReference(layout.schema);

    const directParentConversions = parents.map((entry, ordinal) => {
        const parentSchema = layout.schema.directParents[ordinal];
        const parent: CoreLfClassReference = {
            classId: cloneData(entry.layout.classId),
            parameterCount: entry.layout.schema.parameters.length
        };
        if (!sameReference(parentSchema.parent, parent)) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${entry.path}.layout`,
                'Parent layout no longer matches canonical direct-parent order'
            );
        }
        const symbol: CoreLfQualifiedSymbol = {
            moduleId: layout.classId.moduleId,
            name: entry.conversionName
        };
        const type = conversionType(layout, parentSchema);
        const body = conversionBody(
            layout,
            parentSchema,
            entry.layout,
            entry.path
        );
        const handle: CoreLfClassParentConversionHandle = {
            ordinal,
            child: cloneData(child),
            parent,
            parameters: cloneData(layout.schema.structure.parameters),
            symbol,
            term: globalTerm(symbol),
            type: cloneData(type),
            receiver: {
                authoringRole: 'class-evidence',
                corePlicity: 'explicit'
            }
        };
        const declaration: CoreLfTransferDeclaration = {
            order: input.order + ordinal,
            symbol: cloneData(symbol),
            type,
            body: coreLfTransferExplicitBody(body),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'transparent'
            },
            provenance: cloneData(provenance)
        };
        return { handle, declaration };
    });
    const sourceOrders = directParentConversions.map(
        entry => entry.declaration.order
    );

    return deepFreeze(cloneData({
        kind: 'expanded-class-inheritance' as const,
        revision: CORE_LF_CLASS_INHERITANCE_LOWERING_PROFILE.revision,
        status: 'parent-conversions-expanded' as const,
        layout,
        sourceOrders,
        declarations: directParentConversions.map(entry =>
            entry.declaration
        ),
        directParentConversions: directParentConversions.map(entry =>
            entry.handle
        ),
        nextOrder: input.order + directParentConversions.length
    }));
}

const conversionSnapshot = (
    value: unknown
): CoreLfClassParentConversionHandle => {
    if (
        !record(value) ||
        !Number.isSafeInteger(value.ordinal) ||
        (value.ordinal as number) < 0 ||
        !Array.isArray(value.parameters) ||
        !record(value.receiver) ||
        value.receiver.authoringRole !== 'class-evidence' ||
        value.receiver.corePlicity !== 'explicit'
    ) {
        return fail(
            'INVALID_APPLICATION',
            'input.conversion',
            'Expected one complete direct-parent conversion handle'
        );
    }
    const child = classReference(
        value.child,
        'input.conversion.child',
        'INVALID_APPLICATION'
    );
    const parent = classReference(
        value.parent,
        'input.conversion.parent',
        'INVALID_APPLICATION'
    );
    const symbol = qualifiedSymbol(
        value.symbol,
        'input.conversion.symbol',
        'INVALID_APPLICATION'
    );
    if (symbol.moduleId !== child.classId.moduleId) {
        return fail(
            'INVALID_APPLICATION',
            'input.conversion.symbol',
            'Conversion symbol is outside the child module'
        );
    }
    const term = cloneOpenTerm(value.term, 'input.conversion.term');
    if (term.tag !== 'global' || !sameSymbol(term.symbol, symbol)) {
        return fail(
            'INVALID_APPLICATION',
            'input.conversion.term',
            'Conversion term does not name its conversion symbol'
        );
    }
    if (value.parameters.length !== child.parameterCount) {
        return fail(
            'INVALID_APPLICATION',
            'input.conversion.parameters',
            'Conversion parameter count differs from its child class'
        );
    }
    const parameterNames = new Set<string>();
    const parameters = value.parameters.map((entry, index) => {
        const checked = parameterHandle(
            entry,
            `input.conversion.parameters[${index}]`,
            child.classId
        );
        if (
            checked.ordinal !== index ||
            parameterNames.has(checked.binderName)
        ) {
            return fail(
                'INVALID_APPLICATION',
                `input.conversion.parameters[${index}]`,
                'Conversion parameters are duplicated or out of order'
            );
        }
        parameterNames.add(checked.binderName);
        return checked;
    });
    return deepFreeze({
        ordinal: value.ordinal as number,
        child,
        parent,
        parameters,
        symbol,
        term,
        type: cloneOpenTerm(value.type, 'input.conversion.type'),
        receiver: {
            authoringRole: 'class-evidence',
            corePlicity: 'explicit'
        }
    });
};

/** Assemble a fully explicit call to one generated parent conversion. */
export function applyCoreLfClassParentConversion(
    input: CoreLfApplyClassParentConversionInput
): CoreLfTransferExpression {
    if (!record(input)) {
        return fail(
            'INVALID_APPLICATION',
            'input',
            'Class parent-conversion application must be an object'
        );
    }
    const conversion = conversionSnapshot(input.conversion);
    if (!Array.isArray(input.parameters)) {
        return fail(
            'INVALID_APPLICATION',
            'input.parameters',
            'Class parent-conversion parameters must be an array'
        );
    }
    const values: Array<CoreLfTransferExpression | undefined> =
        new Array(conversion.parameters.length);
    input.parameters.forEach((argument, index) => {
        const path = `input.parameters[${index}]`;
        if (!record(argument) || !record(argument.parameter)) {
            return fail(
                'FOREIGN_ARGUMENT',
                `${path}.parameter`,
                'Class conversion parameter is not a child parameter handle'
            );
        }
        const ordinal = argument.parameter.ordinal;
        const expected = Number.isSafeInteger(ordinal)
            ? conversion.parameters[ordinal as number]
            : undefined;
        if (expected === undefined || !sameParameter(expected, argument.parameter)) {
            return fail(
                'FOREIGN_ARGUMENT',
                `${path}.parameter`,
                'Class conversion parameter belongs to another child'
            );
        }
        if (values[expected.ordinal] !== undefined) {
            return fail(
                'DUPLICATE_ARGUMENT',
                `${path}.parameter`,
                `Parameter '${expected.binderName}' was supplied twice`
            );
        }
        values[expected.ordinal] = cloneOpenTerm(
            argument.value,
            `${path}.value`
        );
    });
    conversion.parameters.forEach(parameter => {
        if (values[parameter.ordinal] === undefined) {
            fail(
                'MISSING_ARGUMENT',
                'input.parameters',
                `Missing parameter '${parameter.binderName}'`
            );
        }
    });
    const evidence = cloneOpenTerm(input.evidence, 'input.evidence');
    return deepFreeze(call(
        globalTerm(conversion.symbol),
        [
            ...conversion.parameters.map(parameter => ({
                plicity: parameter.modes.projection.plicity,
                value: values[parameter.ordinal]!
            })),
            { plicity: 'explicit' as const, value: evidence }
        ]
    ));
}
