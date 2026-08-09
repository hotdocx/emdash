/**
 * Serializable class metadata over one generated outer-LF structure.
 *
 * This layer records authoring identities, parameter roles, declared methods,
 * and ordered parent applications. It emits no declaration or rule, performs
 * no instance search, and marks every parentful layout as unlowered.
 */

import {
    CoreLfStructureDeclarationExpansion,
    CoreLfStructureHandle,
    CoreLfStructureParameterHandle,
    CoreLfStructureProjectionHandle
} from './lf_structure_macro';
import {
    CoreLfQualifiedSymbol,
    CoreLfTransferArgument,
    CoreLfTransferExpression
} from './lf_transfer';
import { BinderMode } from './kernel';

export const CORE_LF_CLASS_SCHEMA_PROFILE = Object.freeze({
    revision: 'emdash-lf-class-schema-v1' as const
});

export type CoreLfClassParameterRole =
    | 'input'
    | 'output'
    | 'semi-output';

export type CoreLfClassLayoutStatus =
    | 'parent-free'
    | 'parents-unlowered';

export type CoreLfClassSchemaErrorCode =
    | 'INVALID_CLASS_SCHEMA'
    | 'INVALID_PARAMETER_ROLE'
    | 'FOREIGN_PARAMETER'
    | 'DUPLICATE_PARAMETER_ROLE'
    | 'INVALID_PARENT'
    | 'DUPLICATE_PARENT'
    | 'INVALID_PARENT_ARGUMENT'
    | 'FOREIGN_PARENT_ARGUMENT'
    | 'DUPLICATE_PARENT_ARGUMENT'
    | 'MISSING_PARENT_ARGUMENT';

export class CoreLfClassSchemaError extends Error {
    constructor(
        public readonly code: CoreLfClassSchemaErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfClassSchemaError';
    }
}

export interface CoreLfClassParameterRoleAssignment {
    readonly parameter: CoreLfStructureParameterHandle;
    readonly role: CoreLfClassParameterRole;
}

export interface CoreLfClassDirectParentInput {
    readonly parent: CoreLfClassSchema;
    readonly arguments: readonly {
        readonly parameter: CoreLfStructureParameterHandle;
        readonly value: CoreLfTransferExpression;
    }[];
}

export interface CoreLfDeclareClassSchemaInput {
    readonly expansion: CoreLfStructureDeclarationExpansion;
    readonly parameterRoles?:
        readonly CoreLfClassParameterRoleAssignment[];
    readonly directParents?: readonly CoreLfClassDirectParentInput[];
}

export interface CoreLfClassParameterIdentity {
    readonly declaringClass: CoreLfQualifiedSymbol;
    readonly ordinal: number;
}

export interface CoreLfClassMethodIdentity {
    readonly declaringClass: CoreLfQualifiedSymbol;
    readonly ordinal: number;
}

export interface CoreLfClassParameterSchema {
    readonly identity: CoreLfClassParameterIdentity;
    readonly parameter: CoreLfStructureParameterHandle;
    readonly role: CoreLfClassParameterRole;
    /** Open under the preceding class parameters. */
    readonly declaredType: CoreLfTransferExpression;
}

export interface CoreLfClassMethodReceiver {
    readonly authoringRole: 'class-evidence';
    readonly corePlicity: 'explicit';
}

export interface CoreLfClassMethodSchema {
    readonly identity: CoreLfClassMethodIdentity;
    readonly projection: CoreLfStructureProjectionHandle;
    readonly receiver: CoreLfClassMethodReceiver;
    /** Open under every class parameter and preceding declared method. */
    readonly declaredType: CoreLfTransferExpression;
}

export interface CoreLfClassReference {
    readonly classId: CoreLfQualifiedSymbol;
    readonly parameterCount: number;
}

export interface CoreLfClassDirectParentSchema {
    readonly ordinal: number;
    readonly parent: CoreLfClassReference;
    readonly arguments: readonly CoreLfTransferArgument[];
    /** Ordinary parent-carrier application, open under child parameters. */
    readonly application: CoreLfTransferExpression;
}

export interface CoreLfClassSchema {
    readonly revision:
        typeof CORE_LF_CLASS_SCHEMA_PROFILE.revision;
    readonly classId: CoreLfQualifiedSymbol;
    readonly layoutStatus: CoreLfClassLayoutStatus;
    readonly structure: CoreLfStructureHandle;
    readonly parameters: readonly CoreLfClassParameterSchema[];
    readonly declaredMethods: readonly CoreLfClassMethodSchema[];
    readonly directParents: readonly CoreLfClassDirectParentSchema[];
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const OUTPUT_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u;

const fail = (
    code: CoreLfClassSchemaErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfClassSchemaError(code, path, message);
};

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

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const qualifiedSymbol = (
    value: unknown,
    path: string,
    code: CoreLfClassSchemaErrorCode = 'INVALID_CLASS_SCHEMA'
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
    return {
        moduleId: value.moduleId,
        name: value.name
    };
};

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const symbolKey = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}\u0000${value.name}`;

const displaySymbol = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}.${value.name}`;

const binderMode = (
    value: unknown,
    path: string,
    code: CoreLfClassSchemaErrorCode = 'INVALID_CLASS_SCHEMA'
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

const cloneExpression = (
    value: unknown,
    path: string,
    depth: number,
    code: CoreLfClassSchemaErrorCode
): CoreLfTransferExpression => {
    if (!record(value) || typeof value.tag !== 'string') {
        return fail(code, path, 'Expected one ordinary transfer expression');
    }
    switch (value.tag) {
        case 'type':
            return { tag: 'type' };
        case 'bound': {
            if (
                !Number.isSafeInteger(value.index) ||
                (value.index as number) < 0 ||
                (value.index as number) >= depth
            ) {
                return fail(
                    code,
                    `${path}.index`,
                    `Bound index escapes class-schema depth ${depth}`
                );
            }
            return { tag: 'bound', index: value.index as number };
        }
        case 'global':
            return {
                tag: 'global',
                symbol: qualifiedSymbol(value.symbol, `${path}.symbol`, code)
            };
        case 'call': {
            if (!Array.isArray(value.arguments) || value.arguments.length === 0) {
                return fail(
                    code,
                    `${path}.arguments`,
                    'Transfer call requires at least one argument'
                );
            }
            return {
                tag: 'call',
                callee: cloneExpression(
                    value.callee,
                    `${path}.callee`,
                    depth,
                    code
                ),
                arguments: value.arguments.map((argument, index) => {
                    if (
                        !record(argument) ||
                        (
                            argument.plicity !== 'explicit' &&
                            argument.plicity !== 'implicit'
                        )
                    ) {
                        return fail(
                            code,
                            `${path}.arguments[${index}]`,
                            'Transfer call argument has invalid plicity'
                        );
                    }
                    return {
                        plicity: argument.plicity,
                        value: cloneExpression(
                            argument.value,
                            `${path}.arguments[${index}].value`,
                            depth,
                            code
                        )
                    };
                })
            };
        }
        case 'pi':
        case 'lambda': {
            if (
                !record(value.binder) ||
                typeof value.binder.hint !== 'string' ||
                !OUTPUT_NAME.test(value.binder.hint)
            ) {
                return fail(
                    code,
                    `${path}.binder`,
                    'Transfer binder is malformed'
                );
            }
            return {
                tag: value.tag,
                binder: {
                    hint: value.binder.hint,
                    mode: binderMode(
                        value.binder.mode,
                        `${path}.binder.mode`,
                        code
                    ),
                    type: cloneExpression(
                        value.binder.type,
                        `${path}.binder.type`,
                        depth,
                        code
                    )
                },
                body: cloneExpression(
                    value.body,
                    `${path}.body`,
                    depth + 1,
                    code
                )
            };
        }
        case 'capture':
        case 'wildcard':
            return fail(
                code,
                path,
                'Class-schema terms cannot contain rule-only syntax'
            );
        default:
            return fail(code, path, 'Unknown transfer expression tag');
    }
};

const sameExpression = (
    left: CoreLfTransferExpression,
    right: CoreLfTransferExpression
): boolean => {
    if (left.tag !== right.tag) return false;
    switch (left.tag) {
        case 'type':
            return true;
        case 'bound':
            return right.tag === 'bound' && left.index === right.index;
        case 'global':
            return right.tag === 'global' &&
                sameSymbol(left.symbol, right.symbol);
        case 'call':
            return right.tag === 'call' &&
                sameExpression(left.callee, right.callee) &&
                left.arguments.length === right.arguments.length &&
                left.arguments.every((argument, index) =>
                    argument.plicity === right.arguments[index].plicity &&
                    sameExpression(
                        argument.value,
                        right.arguments[index].value
                    )
                );
        case 'pi':
        case 'lambda':
            return right.tag === left.tag &&
                left.binder.hint === right.binder.hint &&
                sameMode(left.binder.mode, right.binder.mode) &&
                sameExpression(left.binder.type, right.binder.type) &&
                sameExpression(left.body, right.body);
        case 'capture':
            return right.tag === 'capture' &&
                left.name === right.name &&
                JSON.stringify(left.allowedBoundIndices) ===
                    JSON.stringify(right.allowedBoundIndices);
        case 'wildcard':
            return right.tag === 'wildcard' &&
                (
                    left.checking === undefined
                        ? right.checking === undefined
                        : right.checking !== undefined &&
                            sameExpression(left.checking, right.checking)
                );
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
};

const safeSymbol = (value: unknown): CoreLfQualifiedSymbol | undefined => {
    try {
        return qualifiedSymbol(value, 'handle');
    } catch {
        return undefined;
    }
};

const safeMode = (value: unknown): BinderMode | undefined => {
    try {
        return binderMode(value, 'handle');
    } catch {
        return undefined;
    }
};

const sameParameterHandle = (
    canonical: CoreLfStructureParameterHandle,
    value: unknown
): boolean => {
    if (!record(value) || !record(value.modes)) return false;
    const structure = safeSymbol(value.structure);
    const carrier = safeMode(value.modes.carrier);
    const constructor = safeMode(value.modes.constructor);
    const projection = safeMode(value.modes.projection);
    return structure !== undefined &&
        carrier !== undefined &&
        constructor !== undefined &&
        projection !== undefined &&
        value.ordinal === canonical.ordinal &&
        value.binderName === canonical.binderName &&
        sameSymbol(structure, canonical.structure) &&
        sameMode(carrier, canonical.modes.carrier) &&
        sameMode(constructor, canonical.modes.constructor) &&
        sameMode(projection, canonical.modes.projection);
};

const sameProjectionHandle = (
    canonical: CoreLfStructureProjectionHandle,
    value: unknown
): boolean => {
    if (!record(value)) return false;
    const structure = safeSymbol(value.structure);
    const symbol = safeSymbol(value.symbol);
    const fieldMode = safeMode(value.fieldMode);
    return structure !== undefined &&
        symbol !== undefined &&
        fieldMode !== undefined &&
        value.ordinal === canonical.ordinal &&
        value.binderName === canonical.binderName &&
        value.betaRuleId === canonical.betaRuleId &&
        sameSymbol(structure, canonical.structure) &&
        sameSymbol(symbol, canonical.symbol) &&
        sameMode(fieldMode, canonical.fieldMode);
};

const cloneStructureHandle = (
    value: unknown,
    path: string
): CoreLfStructureHandle => {
    if (!record(value)) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            path,
            'Class schema requires one structure handle'
        );
    }
    const carrier = qualifiedSymbol(value.carrier, `${path}.carrier`);
    const constructor = qualifiedSymbol(
        value.constructor,
        `${path}.constructor`
    );
    const carrierTerm = cloneExpression(
        value.carrierTerm,
        `${path}.carrierTerm`,
        0,
        'INVALID_CLASS_SCHEMA'
    );
    const constructorTerm = cloneExpression(
        value.constructorTerm,
        `${path}.constructorTerm`,
        0,
        'INVALID_CLASS_SCHEMA'
    );
    if (
        carrierTerm.tag !== 'global' ||
        !sameSymbol(carrierTerm.symbol, carrier) ||
        constructorTerm.tag !== 'global' ||
        !sameSymbol(constructorTerm.symbol, constructor)
    ) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            path,
            'Structure handle heads do not match its symbols'
        );
    }
    if (!Array.isArray(value.parameters)) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            `${path}.parameters`,
            'Structure parameters must be an array'
        );
    }
    const parameterNames = new Set<string>();
    const parameters = value.parameters.map((parameter, index) => {
        const parameterPath = `${path}.parameters[${index}]`;
        if (
            !record(parameter) ||
            parameter.ordinal !== index ||
            typeof parameter.binderName !== 'string' ||
            !OUTPUT_NAME.test(parameter.binderName) ||
            !record(parameter.modes)
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                parameterPath,
                'Malformed structure parameter handle'
            );
        }
        if (parameterNames.has(parameter.binderName)) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                parameterPath,
                'Duplicate structure parameter handle'
            );
        }
        parameterNames.add(parameter.binderName);
        const structure = qualifiedSymbol(
            parameter.structure,
            `${parameterPath}.structure`
        );
        if (!sameSymbol(structure, carrier)) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${parameterPath}.structure`,
                'Structure parameter has a foreign declaring carrier'
            );
        }
        return {
            ordinal: index,
            binderName: parameter.binderName,
            structure,
            modes: {
                carrier: binderMode(
                    parameter.modes.carrier,
                    `${parameterPath}.modes.carrier`
                ),
                constructor: binderMode(
                    parameter.modes.constructor,
                    `${parameterPath}.modes.constructor`
                ),
                projection: binderMode(
                    parameter.modes.projection,
                    `${parameterPath}.modes.projection`
                )
            }
        };
    });
    if (!Array.isArray(value.projections) || value.projections.length === 0) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            `${path}.projections`,
            'Class structure requires at least one declared field'
        );
    }
    const fieldNames = new Set<string>();
    const projectionSymbols = new Set<string>();
    const projections = value.projections.map((projection, index) => {
        const projectionPath = `${path}.projections[${index}]`;
        if (
            !record(projection) ||
            projection.ordinal !== index ||
            typeof projection.binderName !== 'string' ||
            !OUTPUT_NAME.test(projection.binderName) ||
            typeof projection.betaRuleId !== 'string' ||
            projection.betaRuleId.length === 0
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                projectionPath,
                'Malformed structure projection handle'
            );
        }
        const structure = qualifiedSymbol(
            projection.structure,
            `${projectionPath}.structure`
        );
        const symbol = qualifiedSymbol(
            projection.symbol,
            `${projectionPath}.symbol`
        );
        if (!sameSymbol(structure, carrier)) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${projectionPath}.structure`,
                'Structure projection has a foreign declaring carrier'
            );
        }
        if (
            fieldNames.has(projection.binderName) ||
            projectionSymbols.has(symbolKey(symbol))
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                projectionPath,
                'Duplicate structure projection handle'
            );
        }
        fieldNames.add(projection.binderName);
        projectionSymbols.add(symbolKey(symbol));
        return {
            ordinal: index,
            binderName: projection.binderName,
            structure,
            symbol,
            fieldMode: binderMode(
                projection.fieldMode,
                `${projectionPath}.fieldMode`
            ),
            betaRuleId: projection.betaRuleId
        };
    });
    return {
        carrier,
        carrierTerm,
        constructor,
        constructorTerm,
        parameters,
        projections
    };
};

const globalTerm = (
    symbol: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({
    tag: 'global',
    symbol: { ...symbol }
});

const carrierApplication = (
    structure: CoreLfStructureHandle,
    arguments_: readonly CoreLfTransferArgument[]
): CoreLfTransferExpression => arguments_.length === 0
    ? globalTerm(structure.carrier)
    : {
        tag: 'call',
        callee: globalTerm(structure.carrier),
        arguments: arguments_.map(argument => ({
            plicity: argument.plicity,
            value: argument.value
        }))
    };

interface ExpansionSeam {
    readonly structure: CoreLfStructureHandle;
    readonly parameterTypes: readonly CoreLfTransferExpression[];
    readonly methodTypes: readonly CoreLfTransferExpression[];
}

const expansionSeam = (
    value: unknown,
    path: string
): ExpansionSeam => {
    if (
        !record(value) ||
        value.kind !== 'expanded-structure-declaration' ||
        !Array.isArray(value.declarations) ||
        !Array.isArray(value.runtimeRules) ||
        !Array.isArray(value.sourceOrders)
    ) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            path,
            'Class schema requires one complete structure expansion'
        );
    }
    const structure = cloneStructureHandle(value.handle, `${path}.handle`);
    const expectedDeclarations = structure.projections.length + 2;
    if (
        value.declarations.length !== expectedDeclarations ||
        value.runtimeRules.length !== structure.projections.length ||
        value.sourceOrders.length !==
            expectedDeclarations + structure.projections.length
    ) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            path,
            'Structure expansion package has inconsistent cardinality'
        );
    }
    const declarations = value.declarations;
    const carrierDeclaration = declarations[0];
    const constructorDeclaration = declarations[1];
    if (!record(carrierDeclaration) || !record(constructorDeclaration)) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            `${path}.declarations`,
            'Structure expansion declarations are malformed'
        );
    }
    const carrierSymbol = qualifiedSymbol(
        carrierDeclaration.symbol,
        `${path}.declarations[0].symbol`
    );
    const constructorSymbol = qualifiedSymbol(
        constructorDeclaration.symbol,
        `${path}.declarations[1].symbol`
    );
    if (
        !sameSymbol(carrierSymbol, structure.carrier) ||
        !sameSymbol(constructorSymbol, structure.constructor)
    ) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            `${path}.declarations`,
            'Structure carrier or constructor declaration is misaligned'
        );
    }
    structure.projections.forEach((projection, index) => {
        const declaration = declarations[index + 2];
        const rule = value.runtimeRules[index];
        if (!record(declaration) || !record(rule)) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${path}.declarations[${index + 2}]`,
                'Structure projection package is malformed'
            );
        }
        const declarationSymbol = qualifiedSymbol(
            declaration.symbol,
            `${path}.declarations[${index + 2}].symbol`
        );
        if (
            !sameSymbol(declarationSymbol, projection.symbol) ||
            rule.id !== projection.betaRuleId
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${path}.declarations[${index + 2}]`,
                'Structure projection declaration or beta is misaligned'
            );
        }
    });

    const carrierType = cloneExpression(
        carrierDeclaration.type,
        `${path}.declarations[0].type`,
        0,
        'INVALID_CLASS_SCHEMA'
    );
    const constructorType = cloneExpression(
        constructorDeclaration.type,
        `${path}.declarations[1].type`,
        0,
        'INVALID_CLASS_SCHEMA'
    );
    const parameterTypes: CoreLfTransferExpression[] = [];
    let carrierCursor = carrierType;
    structure.parameters.forEach((parameter, index) => {
        if (
            carrierCursor.tag !== 'pi' ||
            carrierCursor.binder.hint !== parameter.binderName ||
            !sameMode(
                carrierCursor.binder.mode,
                parameter.modes.carrier
            )
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${path}.declarations[0].type`,
                `Carrier parameter ${index} is misaligned with its handle`
            );
        }
        parameterTypes.push(carrierCursor.binder.type);
        carrierCursor = carrierCursor.body;
    });
    if (carrierCursor.tag !== 'type') {
        return fail(
            'INVALID_CLASS_SCHEMA',
            `${path}.declarations[0].type`,
            'Class carrier telescope must end in TYPE'
        );
    }

    let constructorCursor = constructorType;
    structure.parameters.forEach((parameter, index) => {
        if (
            constructorCursor.tag !== 'pi' ||
            constructorCursor.binder.hint !== parameter.binderName ||
            !sameMode(
                constructorCursor.binder.mode,
                parameter.modes.constructor
            ) ||
            !sameExpression(
                constructorCursor.binder.type,
                parameterTypes[index]
            )
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${path}.declarations[1].type`,
                `Constructor parameter ${index} is misaligned with carrier`
            );
        }
        constructorCursor = constructorCursor.body;
    });
    const methodTypes: CoreLfTransferExpression[] = [];
    structure.projections.forEach((projection, index) => {
        if (
            constructorCursor.tag !== 'pi' ||
            constructorCursor.binder.hint !== projection.binderName ||
            !sameMode(
                constructorCursor.binder.mode,
                projection.fieldMode
            )
        ) {
            return fail(
                'INVALID_CLASS_SCHEMA',
                `${path}.declarations[1].type`,
                `Constructor field ${index} is misaligned with its handle`
            );
        }
        methodTypes.push(constructorCursor.binder.type);
        constructorCursor = constructorCursor.body;
    });
    const resultArguments = structure.parameters.map(parameter => ({
        plicity: parameter.modes.carrier.plicity,
        value: {
            tag: 'bound' as const,
            index:
                structure.projections.length +
                structure.parameters.length -
                parameter.ordinal -
                1
        }
    }));
    if (!sameExpression(
        constructorCursor,
        carrierApplication(structure, resultArguments)
    )) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            `${path}.declarations[1].type`,
            'Constructor result does not return its declared carrier'
        );
    }
    return { structure, parameterTypes, methodTypes };
};

const classRole = (
    value: unknown,
    path: string
): CoreLfClassParameterRole => {
    if (
        value !== 'input' &&
        value !== 'output' &&
        value !== 'semi-output'
    ) {
        return fail(
            'INVALID_PARAMETER_ROLE',
            path,
            'Class parameter role must be input, output, or semi-output'
        );
    }
    return value;
};

interface ClassSchemaReferenceView {
    readonly classId: CoreLfQualifiedSymbol;
    readonly structure: CoreLfStructureHandle;
}

const classSchemaReference = (
    value: unknown,
    path: string
): ClassSchemaReferenceView => {
    try {
        if (
            !record(value) ||
            value.revision !== CORE_LF_CLASS_SCHEMA_PROFILE.revision ||
            (
                value.layoutStatus !== 'parent-free' &&
                value.layoutStatus !== 'parents-unlowered'
            ) ||
            !Array.isArray(value.parameters) ||
            !Array.isArray(value.declaredMethods) ||
            !Array.isArray(value.directParents)
        ) {
            return fail(
                'INVALID_PARENT',
                path,
                'Direct parent must be one complete class-schema snapshot'
            );
        }
        const classId = qualifiedSymbol(
            value.classId,
            `${path}.classId`,
            'INVALID_PARENT'
        );
        const structure = cloneStructureHandle(
            value.structure,
            `${path}.structure`
        );
        if (
            !sameSymbol(classId, structure.carrier) ||
            value.parameters.length !== structure.parameters.length ||
            value.declaredMethods.length !== structure.projections.length ||
            (
                value.layoutStatus === 'parent-free' &&
                value.directParents.length !== 0
            ) ||
            (
                value.layoutStatus === 'parents-unlowered' &&
                value.directParents.length === 0
            )
        ) {
            return fail(
                'INVALID_PARENT',
                path,
                'Direct parent class-schema snapshot is inconsistent'
            );
        }
        value.parameters.forEach((parameter, index) => {
            if (
                !record(parameter) ||
                !record(parameter.identity) ||
                parameter.identity.ordinal !== index ||
                !sameParameterHandle(
                    structure.parameters[index],
                    parameter.parameter
                )
            ) {
                return fail(
                    'INVALID_PARENT',
                    `${path}.parameters[${index}]`,
                    'Direct parent parameter metadata is inconsistent'
                );
            }
            const declaringClass = qualifiedSymbol(
                parameter.identity.declaringClass,
                `${path}.parameters[${index}].identity.declaringClass`,
                'INVALID_PARENT'
            );
            if (!sameSymbol(declaringClass, classId)) {
                return fail(
                    'INVALID_PARENT',
                    `${path}.parameters[${index}].identity`,
                    'Direct parent parameter identity is foreign'
                );
            }
            classRole(
                parameter.role,
                `${path}.parameters[${index}].role`
            );
            cloneExpression(
                parameter.declaredType,
                `${path}.parameters[${index}].declaredType`,
                index,
                'INVALID_PARENT'
            );
        });
        value.declaredMethods.forEach((method, index) => {
            if (
                !record(method) ||
                !record(method.identity) ||
                !record(method.receiver) ||
                method.identity.ordinal !== index ||
                method.receiver.authoringRole !== 'class-evidence' ||
                method.receiver.corePlicity !== 'explicit' ||
                !sameProjectionHandle(
                    structure.projections[index],
                    method.projection
                )
            ) {
                return fail(
                    'INVALID_PARENT',
                    `${path}.declaredMethods[${index}]`,
                    'Direct parent method metadata is inconsistent'
                );
            }
            const declaringClass = qualifiedSymbol(
                method.identity.declaringClass,
                `${path}.declaredMethods[${index}].identity.declaringClass`,
                'INVALID_PARENT'
            );
            if (!sameSymbol(declaringClass, classId)) {
                return fail(
                    'INVALID_PARENT',
                    `${path}.declaredMethods[${index}].identity`,
                    'Direct parent method identity is foreign'
                );
            }
            cloneExpression(
                method.declaredType,
                `${path}.declaredMethods[${index}].declaredType`,
                structure.parameters.length + index,
                'INVALID_PARENT'
            );
        });
        return { classId, structure };
    } catch (error) {
        if (error instanceof CoreLfClassSchemaError) {
            if (error.code === 'INVALID_PARENT') throw error;
            return fail('INVALID_PARENT', error.path, error.message);
        }
        throw error;
    }
};

/**
 * Reference one class parameter in the complete class-parameter telescope.
 */
export function coreLfClassParameterTerm(
    expansion: CoreLfStructureDeclarationExpansion,
    parameter: CoreLfStructureParameterHandle
): CoreLfTransferExpression {
    const seam = expansionSeam(expansion, 'expansion');
    const ordinal = record(parameter) && Number.isSafeInteger(parameter.ordinal)
        ? parameter.ordinal
        : -1;
    const canonical = ordinal >= 0
        ? seam.structure.parameters[ordinal]
        : undefined;
    if (
        canonical === undefined ||
        !sameParameterHandle(canonical, parameter)
    ) {
        return fail(
            'FOREIGN_PARAMETER',
            'parameter',
            'Parameter does not belong to the selected class structure'
        );
    }
    return deepFreeze({
        tag: 'bound' as const,
        index: seam.structure.parameters.length - canonical.ordinal - 1
    });
}

/**
 * Classify one generated structure without lowering inheritance or search.
 */
export function declareCoreLfClassSchema(
    input: CoreLfDeclareClassSchemaInput
): CoreLfClassSchema {
    if (!record(input)) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            'input',
            'Class-schema input must be an object'
        );
    }
    const seam = expansionSeam(input.expansion, 'input.expansion');
    const rolesInput = input.parameterRoles ?? [];
    if (!Array.isArray(rolesInput)) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            'input.parameterRoles',
            'Class parameter roles must be an array'
        );
    }
    const roles: CoreLfClassParameterRole[] = seam.structure.parameters.map(
        () => 'input'
    );
    const assignedRoles = new Set<number>();
    rolesInput.forEach((assignment, index) => {
        const path = `input.parameterRoles[${index}]`;
        if (!record(assignment)) {
            return fail(
                'INVALID_PARAMETER_ROLE',
                path,
                'Class parameter role assignment must be an object'
            );
        }
        const ordinal = record(assignment.parameter) &&
            Number.isSafeInteger(assignment.parameter.ordinal)
            ? assignment.parameter.ordinal as number
            : -1;
        const canonical = ordinal >= 0
            ? seam.structure.parameters[ordinal]
            : undefined;
        if (
            canonical === undefined ||
            !sameParameterHandle(canonical, assignment.parameter)
        ) {
            return fail(
                'FOREIGN_PARAMETER',
                `${path}.parameter`,
                'Role parameter does not belong to the class structure'
            );
        }
        if (assignedRoles.has(canonical.ordinal)) {
            return fail(
                'DUPLICATE_PARAMETER_ROLE',
                `${path}.parameter`,
                `Parameter '${canonical.binderName}' has two role assignments`
            );
        }
        assignedRoles.add(canonical.ordinal);
        roles[canonical.ordinal] = classRole(
            assignment.role,
            `${path}.role`
        );
    });

    const parentInputs = input.directParents ?? [];
    if (!Array.isArray(parentInputs)) {
        return fail(
            'INVALID_CLASS_SCHEMA',
            'input.directParents',
            'Direct class parents must be an array'
        );
    }
    const parentIds = new Set<string>();
    const directParents = parentInputs.map((parentInput, parentIndex) => {
        const path = `input.directParents[${parentIndex}]`;
        if (!record(parentInput)) {
            return fail(
                'INVALID_PARENT',
                path,
                'Direct parent input must be an object'
            );
        }
        const parent = classSchemaReference(
            parentInput.parent,
            `${path}.parent`
        );
        if (sameSymbol(parent.classId, seam.structure.carrier)) {
            return fail(
                'INVALID_PARENT',
                `${path}.parent`,
                'A class cannot be its own direct parent'
            );
        }
        const parentKey = symbolKey(parent.classId);
        if (parentIds.has(parentKey)) {
            return fail(
                'DUPLICATE_PARENT',
                `${path}.parent`,
                `Direct parent '${displaySymbol(parent.classId)}' is repeated`
            );
        }
        parentIds.add(parentKey);
        if (!Array.isArray(parentInput.arguments)) {
            return fail(
                'INVALID_PARENT',
                `${path}.arguments`,
                'Direct parent arguments must be an array'
            );
        }
        const values: Array<CoreLfTransferExpression | undefined> =
            new Array(parent.structure.parameters.length);
        parentInput.arguments.forEach((argument, argumentIndex) => {
            const argumentPath = `${path}.arguments[${argumentIndex}]`;
            if (!record(argument)) {
                return fail(
                    'INVALID_PARENT_ARGUMENT',
                    argumentPath,
                    'Parent argument assignment must be an object'
                );
            }
            const ordinal = record(argument.parameter) &&
                Number.isSafeInteger(argument.parameter.ordinal)
                ? argument.parameter.ordinal as number
                : -1;
            const canonical = ordinal >= 0
                ? parent.structure.parameters[ordinal]
                : undefined;
            if (
                canonical === undefined ||
                !sameParameterHandle(canonical, argument.parameter)
            ) {
                return fail(
                    'FOREIGN_PARENT_ARGUMENT',
                    `${argumentPath}.parameter`,
                    'Argument parameter does not belong to the direct parent'
                );
            }
            if (values[canonical.ordinal] !== undefined) {
                return fail(
                    'DUPLICATE_PARENT_ARGUMENT',
                    `${argumentPath}.parameter`,
                    `Parent parameter '${canonical.binderName}' is repeated`
                );
            }
            values[canonical.ordinal] = cloneExpression(
                argument.value,
                `${argumentPath}.value`,
                seam.structure.parameters.length,
                'INVALID_PARENT_ARGUMENT'
            );
        });
        parent.structure.parameters.forEach(parameter => {
            if (values[parameter.ordinal] === undefined) {
                fail(
                    'MISSING_PARENT_ARGUMENT',
                    `${path}.arguments`,
                    `Missing parent parameter '${parameter.binderName}'`
                );
            }
        });
        const arguments_: CoreLfTransferArgument[] =
            parent.structure.parameters.map(parameter => ({
                plicity: parameter.modes.carrier.plicity,
                value: values[parameter.ordinal]!
            }));
        return {
            ordinal: parentIndex,
            parent: {
                classId: { ...parent.classId },
                parameterCount: parent.structure.parameters.length
            },
            arguments: arguments_,
            application: carrierApplication(parent.structure, arguments_)
        };
    });

    const classId = { ...seam.structure.carrier };
    return deepFreeze({
        revision: CORE_LF_CLASS_SCHEMA_PROFILE.revision,
        classId,
        layoutStatus: directParents.length === 0
            ? 'parent-free' as const
            : 'parents-unlowered' as const,
        structure: seam.structure,
        parameters: seam.structure.parameters.map((parameter, index) => ({
            identity: {
                declaringClass: { ...classId },
                ordinal: index
            },
            parameter,
            role: roles[index],
            declaredType: seam.parameterTypes[index]
        })),
        declaredMethods: seam.structure.projections.map(
            (projection, index) => ({
                identity: {
                    declaringClass: { ...classId },
                    ordinal: index
                },
                projection,
                receiver: {
                    authoringRole: 'class-evidence' as const,
                    corePlicity: 'explicit' as const
                },
                declaredType: seam.methodTypes[index]
            })
        ),
        directParents
    });
}
