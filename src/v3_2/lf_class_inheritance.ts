/**
 * Pure class-inheritance identity/layout planning.
 *
 * This tranche computes strict C3 order and assigns inherited logical field
 * identities to an existing class structure's private physical projections.
 * It deliberately emits no conversion term, declaration, rule, or instance.
 */

import {
    CORE_LF_CLASS_SCHEMA_PROFILE,
    CoreLfClassMethodIdentity,
    CoreLfClassReference,
    CoreLfClassSchema
} from './lf_class_schema';
import {
    CoreLfStructureProjectionHandle
} from './lf_structure_macro';
import {
    CoreLfQualifiedSymbol
} from './lf_transfer';
import { BinderMode } from './kernel';

export const CORE_LF_CLASS_INHERITANCE_LAYOUT_PROFILE = Object.freeze({
    revision: 'emdash-lf-class-inheritance-layout-v1' as const
});

export type CoreLfClassInheritanceErrorCode =
    | 'INVALID_INHERITANCE_LAYOUT'
    | 'PARENT_LAYOUT_MISMATCH'
    | 'INCONSISTENT_C3'
    | 'FOREIGN_FIELD'
    | 'DUPLICATE_FIELD_BINDING'
    | 'FOREIGN_INHERITED_IDENTITY'
    | 'DUPLICATE_INHERITED_IDENTITY'
    | 'MISSING_INHERITED_IDENTITY'
    | 'FIELD_NAME_CONFLICT';

export class CoreLfClassInheritanceError extends Error {
    constructor(
        public readonly code: CoreLfClassInheritanceErrorCode,
        public readonly path: string,
        message: string,
        public readonly evidence?: readonly string[]
    ) {
        super(message);
        this.name = 'CoreLfClassInheritanceError';
    }
}

export interface CoreLfClassInheritedFieldBindingInput {
    readonly field: CoreLfStructureProjectionHandle;
    readonly inherited: readonly CoreLfClassMethodIdentity[];
}

export interface CoreLfPlanClassInheritanceInput {
    readonly schema: CoreLfClassSchema;
    readonly directParentLayouts:
        readonly CoreLfClassInheritanceLayout[];
    readonly fieldBindings?:
        readonly CoreLfClassInheritedFieldBindingInput[];
}

export interface CoreLfClassInheritanceSlot {
    readonly ordinal: number;
    readonly physicalField: CoreLfStructureProjectionHandle;
    readonly localIdentity: CoreLfClassMethodIdentity;
    readonly canonicalIdentity: CoreLfClassMethodIdentity;
    readonly identities: readonly CoreLfClassMethodIdentity[];
}

export interface CoreLfClassQualifiedMethodAlias {
    readonly declaringClass: CoreLfQualifiedSymbol;
    readonly binderName: string;
    readonly identity: CoreLfClassMethodIdentity;
    readonly slotOrdinal: number;
}

export interface CoreLfClassUnqualifiedMethodLookup {
    readonly binderName: string;
    readonly slotOrdinal: number;
    readonly canonicalIdentity: CoreLfClassMethodIdentity;
    readonly selectedDeclaringClass: CoreLfQualifiedSymbol;
}

export interface CoreLfClassInheritanceLayout {
    readonly revision:
        typeof CORE_LF_CLASS_INHERITANCE_LAYOUT_PROFILE.revision;
    readonly status: 'identity-layout-planned';
    readonly classId: CoreLfQualifiedSymbol;
    readonly schema: CoreLfClassSchema;
    readonly directParents: readonly CoreLfClassReference[];
    readonly resolutionOrder: readonly CoreLfClassReference[];
    readonly slots: readonly CoreLfClassInheritanceSlot[];
    readonly qualifiedMethods: readonly CoreLfClassQualifiedMethodAlias[];
    readonly unqualifiedMethods:
        readonly CoreLfClassUnqualifiedMethodLookup[];
}

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const OUTPUT_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u;

const fail = (
    code: CoreLfClassInheritanceErrorCode,
    path: string,
    message: string,
    evidence?: readonly string[]
): never => {
    throw new CoreLfClassInheritanceError(
        code,
        path,
        message,
        evidence === undefined ? undefined : Object.freeze([...evidence])
    );
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
    code: CoreLfClassInheritanceErrorCode =
        'INVALID_INHERITANCE_LAYOUT'
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

const displaySymbol = (value: CoreLfQualifiedSymbol): string =>
    `${value.moduleId}.${value.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const mode = (
    value: unknown,
    path: string
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
        return fail(
            'INVALID_INHERITANCE_LAYOUT',
            path,
            'Expected one valid binder mode'
        );
    }
    return {
        plicity: value.plicity,
        variation: value.variation
    };
};

const sameMode = (left: BinderMode, right: BinderMode): boolean =>
    left.plicity === right.plicity &&
    left.variation === right.variation;

const safeSymbol = (value: unknown): CoreLfQualifiedSymbol | undefined => {
    try {
        return qualifiedSymbol(value, 'value');
    } catch {
        return undefined;
    }
};

const safeMode = (value: unknown): BinderMode | undefined => {
    try {
        return mode(value, 'value');
    } catch {
        return undefined;
    }
};

const sameProjection = (
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

const methodIdentity = (
    value: unknown,
    path: string,
    code: CoreLfClassInheritanceErrorCode =
        'INVALID_INHERITANCE_LAYOUT'
): CoreLfClassMethodIdentity => {
    if (
        !record(value) ||
        !Number.isSafeInteger(value.ordinal) ||
        (value.ordinal as number) < 0
    ) {
        return fail(code, path, 'Malformed class method identity');
    }
    return {
        declaringClass: qualifiedSymbol(
            value.declaringClass,
            `${path}.declaringClass`,
            code
        ),
        ordinal: value.ordinal as number
    };
};

const identityKey = (value: CoreLfClassMethodIdentity): string =>
    `${symbolKey(value.declaringClass)}\u0000${value.ordinal}`;

const sameIdentity = (
    left: CoreLfClassMethodIdentity,
    right: CoreLfClassMethodIdentity
): boolean => identityKey(left) === identityKey(right);

const compareIdentity = (
    left: CoreLfClassMethodIdentity,
    right: CoreLfClassMethodIdentity
): number => {
    const leftClass = symbolKey(left.declaringClass);
    const rightClass = symbolKey(right.declaringClass);
    if (leftClass < rightClass) return -1;
    if (leftClass > rightClass) return 1;
    return left.ordinal - right.ordinal;
};

const classReference = (
    value: unknown,
    path: string,
    code: CoreLfClassInheritanceErrorCode =
        'INVALID_INHERITANCE_LAYOUT'
): CoreLfClassReference => {
    if (
        !record(value) ||
        !Number.isSafeInteger(value.parameterCount) ||
        (value.parameterCount as number) < 0
    ) {
        return fail(code, path, 'Malformed class reference');
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

const schemaSnapshot = (
    value: unknown,
    path: string
): CoreLfClassSchema => {
    if (
        !record(value) ||
        value.revision !== CORE_LF_CLASS_SCHEMA_PROFILE.revision ||
        (
            value.layoutStatus !== 'parent-free' &&
            value.layoutStatus !== 'parents-unlowered'
        ) ||
        !record(value.structure) ||
        !Array.isArray(value.structure.parameters) ||
        !Array.isArray(value.structure.projections) ||
        !Array.isArray(value.parameters) ||
        !Array.isArray(value.declaredMethods) ||
        !Array.isArray(value.directParents)
    ) {
        return fail(
            'INVALID_INHERITANCE_LAYOUT',
            path,
            'Inheritance planning requires one complete class schema'
        );
    }
    const structure = value.structure;
    const structureParameters = structure.parameters as unknown[];
    const structureProjections = structure.projections as unknown[];
    const classId = qualifiedSymbol(value.classId, `${path}.classId`);
    const carrier = qualifiedSymbol(
        structure.carrier,
        `${path}.structure.carrier`
    );
    if (
        !sameSymbol(classId, carrier) ||
        value.parameters.length !== structureParameters.length ||
        value.declaredMethods.length !== structureProjections.length ||
        value.declaredMethods.length === 0 ||
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
            'INVALID_INHERITANCE_LAYOUT',
            path,
            'Class schema cardinality or layout status is inconsistent'
        );
    }
    value.parameters.forEach((parameter, index) => {
        if (
            !record(parameter) ||
            !record(parameter.identity) ||
            parameter.identity.ordinal !== index ||
            !record(parameter.parameter) ||
            parameter.parameter.ordinal !== index
        ) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                `${path}.parameters[${index}]`,
                'Class parameter metadata is inconsistent'
            );
        }
        const identityClass = qualifiedSymbol(
            parameter.identity.declaringClass,
            `${path}.parameters[${index}].identity.declaringClass`
        );
        const owner = qualifiedSymbol(
            parameter.parameter.structure,
            `${path}.parameters[${index}].parameter.structure`
        );
        if (
            !sameSymbol(identityClass, classId) ||
            !sameSymbol(owner, classId)
        ) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                `${path}.parameters[${index}]`,
                'Class parameter metadata has a foreign owner'
            );
        }
    });
    value.declaredMethods.forEach((method, index) => {
        if (
            !record(method) ||
            !record(method.identity) ||
            method.identity.ordinal !== index ||
            !sameProjection(
                structureProjections[index] as
                    CoreLfStructureProjectionHandle,
                method.projection
            )
        ) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                `${path}.declaredMethods[${index}]`,
                'Class method metadata is inconsistent'
            );
        }
        const identityClass = qualifiedSymbol(
            method.identity.declaringClass,
            `${path}.declaredMethods[${index}].identity.declaringClass`
        );
        if (!sameSymbol(identityClass, classId)) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                `${path}.declaredMethods[${index}].identity`,
                'Class method identity has a foreign owner'
            );
        }
    });
    const parentIds = new Set<string>();
    value.directParents.forEach((parent, index) => {
        if (!record(parent)) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                `${path}.directParents[${index}]`,
                'Class direct-parent metadata is malformed'
            );
        }
        const reference = classReference(
            parent.parent,
            `${path}.directParents[${index}].parent`
        );
        const key = symbolKey(reference.classId);
        if (sameSymbol(reference.classId, classId) || parentIds.has(key)) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                `${path}.directParents[${index}].parent`,
                'Class direct-parent metadata is cyclic or duplicated'
            );
        }
        parentIds.add(key);
    });
    return value as unknown as CoreLfClassSchema;
};

const layoutSnapshot = (
    value: unknown,
    path: string
): CoreLfClassInheritanceLayout => {
    if (
        !record(value) ||
        value.revision !==
            CORE_LF_CLASS_INHERITANCE_LAYOUT_PROFILE.revision ||
        value.status !== 'identity-layout-planned' ||
        !Array.isArray(value.directParents) ||
        !Array.isArray(value.resolutionOrder) ||
        !Array.isArray(value.slots) ||
        !Array.isArray(value.qualifiedMethods) ||
        !Array.isArray(value.unqualifiedMethods)
    ) {
        return fail(
            'PARENT_LAYOUT_MISMATCH',
            path,
            'Expected one complete parent identity layout'
        );
    }
    const slots = value.slots;
    const schema = schemaSnapshot(value.schema, `${path}.schema`);
    const classId = qualifiedSymbol(
        value.classId,
        `${path}.classId`,
        'PARENT_LAYOUT_MISMATCH'
    );
    if (
        !sameSymbol(classId, schema.classId) ||
        value.directParents.length !== schema.directParents.length ||
        slots.length !== schema.declaredMethods.length ||
        value.resolutionOrder.length === 0
    ) {
        return fail(
            'PARENT_LAYOUT_MISMATCH',
            path,
            'Parent identity layout is inconsistent with its schema'
        );
    }
    value.directParents.forEach((parent, index) => {
        const actual = classReference(
            parent,
            `${path}.directParents[${index}]`,
            'PARENT_LAYOUT_MISMATCH'
        );
        const expected = schema.directParents[index].parent;
        if (!sameReference(actual, expected)) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.directParents[${index}]`,
                'Parent identity layout changed direct-parent order'
            );
        }
    });
    const resolutionIds = new Set<string>();
    value.resolutionOrder.forEach((entry, index) => {
        const reference = classReference(
            entry,
            `${path}.resolutionOrder[${index}]`,
            'PARENT_LAYOUT_MISMATCH'
        );
        const key = symbolKey(reference.classId);
        if (resolutionIds.has(key)) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.resolutionOrder[${index}]`,
                'Parent resolution order repeats a class ID'
            );
        }
        resolutionIds.add(key);
        if (
            index === 0 &&
            !sameReference(reference, {
                classId: schema.classId,
                parameterCount: schema.parameters.length
            })
        ) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.resolutionOrder[0]`,
                'Parent resolution order must begin with itself'
            );
        }
    });
    const seenIdentities = new Set<string>();
    slots.forEach((slot, index) => {
        if (
            !record(slot) ||
            slot.ordinal !== index ||
            !Array.isArray(slot.identities) ||
            slot.identities.length === 0 ||
            !sameProjection(
                schema.declaredMethods[index].projection,
                slot.physicalField
            )
        ) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.slots[${index}]`,
                'Parent physical slot is inconsistent'
            );
        }
        const local = methodIdentity(
            slot.localIdentity,
            `${path}.slots[${index}].localIdentity`,
            'PARENT_LAYOUT_MISMATCH'
        );
        const expectedLocal = schema.declaredMethods[index].identity;
        const canonical = methodIdentity(
            slot.canonicalIdentity,
            `${path}.slots[${index}].canonicalIdentity`,
            'PARENT_LAYOUT_MISMATCH'
        );
        let containsLocal = false;
        let containsCanonical = false;
        slot.identities.forEach((identity, identityIndex) => {
            const checked = methodIdentity(
                identity,
                `${path}.slots[${index}].identities[${identityIndex}]`,
                'PARENT_LAYOUT_MISMATCH'
            );
            const key = identityKey(checked);
            if (seenIdentities.has(key)) {
                return fail(
                    'PARENT_LAYOUT_MISMATCH',
                    `${path}.slots[${index}].identities[${identityIndex}]`,
                    'Parent layout assigns one identity to two slots'
                );
            }
            seenIdentities.add(key);
            containsLocal ||= sameIdentity(checked, local);
            containsCanonical ||= sameIdentity(checked, canonical);
        });
        if (
            !sameIdentity(local, expectedLocal) ||
            !containsLocal ||
            !containsCanonical
        ) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.slots[${index}]`,
                'Parent slot identities are inconsistent'
            );
        }
    });
    value.qualifiedMethods.forEach((alias, index) => {
        if (
            !record(alias) ||
            typeof alias.binderName !== 'string' ||
            !OUTPUT_NAME.test(alias.binderName) ||
            !Number.isSafeInteger(alias.slotOrdinal) ||
            (alias.slotOrdinal as number) < 0 ||
            (alias.slotOrdinal as number) >= slots.length
        ) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.qualifiedMethods[${index}]`,
                'Parent qualified method alias is malformed'
            );
        }
        const declaringClass = qualifiedSymbol(
            alias.declaringClass,
            `${path}.qualifiedMethods[${index}].declaringClass`,
            'PARENT_LAYOUT_MISMATCH'
        );
        const identity = methodIdentity(
            alias.identity,
            `${path}.qualifiedMethods[${index}].identity`,
            'PARENT_LAYOUT_MISMATCH'
        );
        const slot = slots[alias.slotOrdinal as number];
        if (
            !sameSymbol(declaringClass, identity.declaringClass) ||
            !(slot as Record<string, unknown>).identities ||
            !(slot as unknown as {
                identities: readonly CoreLfClassMethodIdentity[];
            }).identities.some(candidate =>
                sameIdentity(candidate, identity)
            )
        ) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `${path}.qualifiedMethods[${index}]`,
                'Parent qualified method alias points to a foreign slot'
            );
        }
    });
    return value as unknown as CoreLfClassInheritanceLayout;
};

const mergeC3 = (
    child: CoreLfClassReference,
    parentLayouts: readonly CoreLfClassInheritanceLayout[],
    path: string
): readonly CoreLfClassReference[] => {
    const known = new Map<string, CoreLfClassReference>();
    const register = (
        value: CoreLfClassReference,
        entryPath: string
    ): CoreLfClassReference => {
        const key = symbolKey(value.classId);
        const previous = known.get(key);
        if (
            previous !== undefined &&
            previous.parameterCount !== value.parameterCount
        ) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                entryPath,
                `Class '${displaySymbol(value.classId)}' changed parameter count`
            );
        }
        if (previous === undefined) known.set(key, value);
        return previous ?? value;
    };
    register(child, path);
    const sequences: CoreLfClassReference[][] = [
        ...parentLayouts.map((layout, parentIndex) =>
            layout.resolutionOrder.map((entry, entryIndex) => register(
                classReference(
                    entry,
                    `${path}[${parentIndex}].resolutionOrder[${entryIndex}]`,
                    'PARENT_LAYOUT_MISMATCH'
                ),
                `${path}[${parentIndex}].resolutionOrder[${entryIndex}]`
            ))
        ),
        parentLayouts.map((layout, parentIndex) => register({
            classId: { ...layout.classId },
            parameterCount: layout.schema.parameters.length
        }, `${path}[${parentIndex}]`))
    ].filter(sequence => sequence.length > 0);
    const result: CoreLfClassReference[] = [{
        classId: { ...child.classId },
        parameterCount: child.parameterCount
    }];
    while (sequences.length > 0) {
        let selected: CoreLfClassReference | undefined;
        for (const sequence of sequences) {
            const head = sequence[0];
            const headKey = symbolKey(head.classId);
            const appearsInTail = sequences.some(candidate =>
                candidate.slice(1).some(entry =>
                    symbolKey(entry.classId) === headKey
                )
            );
            if (!appearsInTail) {
                selected = head;
                break;
            }
        }
        if (selected === undefined) {
            const evidence = sequences.map(sequence => sequence
                .map(entry => displaySymbol(entry.classId))
                .join(' > '));
            return fail(
                'INCONSISTENT_C3',
                path,
                'Strict C3 merge has no admissible head',
                evidence
            );
        }
        const selectedKey = symbolKey(selected.classId);
        result.push({
            classId: { ...selected.classId },
            parameterCount: selected.parameterCount
        });
        for (let index = sequences.length - 1; index >= 0; index--) {
            sequences[index] = sequences[index].filter(entry =>
                symbolKey(entry.classId) !== selectedKey
            );
            if (sequences[index].length === 0) sequences.splice(index, 1);
        }
    }
    return result;
};

interface InheritedIdentityClass {
    readonly identities: readonly CoreLfClassMethodIdentity[];
    readonly canonicalCandidates: readonly CoreLfClassMethodIdentity[];
}

const inheritedClasses = (
    parents: readonly CoreLfClassInheritanceLayout[]
): {
    readonly classes: readonly InheritedIdentityClass[];
    readonly classByIdentity: ReadonlyMap<string, number>;
} => {
    const representatives = new Map<string, string>();
    const identities = new Map<string, CoreLfClassMethodIdentity>();
    const canonicalKeys = new Set<string>();
    const find = (key: string): string => {
        const parent = representatives.get(key) ?? key;
        if (parent === key) return key;
        const root = find(parent);
        representatives.set(key, root);
        return root;
    };
    const ensure = (identity: CoreLfClassMethodIdentity): string => {
        const key = identityKey(identity);
        if (!representatives.has(key)) representatives.set(key, key);
        if (!identities.has(key)) identities.set(key, cloneData(identity));
        return key;
    };
    const union = (left: string, right: string): void => {
        const leftRoot = find(left);
        const rightRoot = find(right);
        if (leftRoot === rightRoot) return;
        const first = leftRoot < rightRoot ? leftRoot : rightRoot;
        const second = leftRoot < rightRoot ? rightRoot : leftRoot;
        representatives.set(second, first);
    };
    parents.forEach(parent => parent.slots.forEach(slot => {
        const keys = slot.identities.map(ensure);
        keys.slice(1).forEach(key => union(keys[0], key));
        canonicalKeys.add(ensure(slot.canonicalIdentity));
    }));
    const groups = new Map<string, string[]>();
    identities.forEach((_identity, key) => {
        const root = find(key);
        const group = groups.get(root) ?? [];
        group.push(key);
        groups.set(root, group);
    });
    const classes = [...groups.values()]
        .map(keys => {
            const members = keys
                .map(key => identities.get(key)!)
                .sort(compareIdentity);
            const candidates = keys
                .filter(key => canonicalKeys.has(key))
                .map(key => identities.get(key)!)
                .sort(compareIdentity);
            return {
                identities: members,
                canonicalCandidates:
                    candidates.length === 0 ? members : candidates
            };
        })
        .sort((left, right) => compareIdentity(
            left.canonicalCandidates[0],
            right.canonicalCandidates[0]
        ));
    const classByIdentity = new Map<string, number>();
    classes.forEach((group, index) => group.identities.forEach(identity =>
        classByIdentity.set(identityKey(identity), index)
    ));
    return { classes, classByIdentity };
};

/**
 * Plan strict C3 and logical identity sharing over private physical fields.
 */
export function planCoreLfClassInheritance(
    input: CoreLfPlanClassInheritanceInput
): CoreLfClassInheritanceLayout {
    if (!record(input)) {
        return fail(
            'INVALID_INHERITANCE_LAYOUT',
            'input',
            'Class inheritance input must be an object'
        );
    }
    const schema = schemaSnapshot(input.schema, 'input.schema');
    if (!Array.isArray(input.directParentLayouts)) {
        return fail(
            'INVALID_INHERITANCE_LAYOUT',
            'input.directParentLayouts',
            'Direct parent layouts must be an array'
        );
    }
    if (input.directParentLayouts.length !== schema.directParents.length) {
        return fail(
            'PARENT_LAYOUT_MISMATCH',
            'input.directParentLayouts',
            'Direct parent layout count does not match the class schema'
        );
    }
    const parents = input.directParentLayouts.map((layout, index) => {
        const checked = layoutSnapshot(
            layout,
            `input.directParentLayouts[${index}]`
        );
        if (!sameReference(
            {
                classId: checked.classId,
                parameterCount: checked.schema.parameters.length
            },
            schema.directParents[index].parent
        )) {
            return fail(
                'PARENT_LAYOUT_MISMATCH',
                `input.directParentLayouts[${index}]`,
                'Direct parent layout does not match schema order'
            );
        }
        return checked;
    });
    const childReference: CoreLfClassReference = {
        classId: { ...schema.classId },
        parameterCount: schema.parameters.length
    };
    const resolutionOrder = mergeC3(
        childReference,
        parents,
        'input.directParentLayouts'
    );

    const inherited = inheritedClasses(parents);
    const bindings = input.fieldBindings ?? [];
    if (!Array.isArray(bindings)) {
        return fail(
            'INVALID_INHERITANCE_LAYOUT',
            'input.fieldBindings',
            'Field bindings must be an array'
        );
    }
    const groupsByField: number[][] = schema.declaredMethods.map(() => []);
    const boundFields = new Set<number>();
    const assignedGroups = new Map<number, number>();
    bindings.forEach((binding, bindingIndex) => {
        const path = `input.fieldBindings[${bindingIndex}]`;
        if (!record(binding) || !Array.isArray(binding.inherited)) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                path,
                'Inherited field binding must be an object with an array'
            );
        }
        const ordinal = record(binding.field) &&
            Number.isSafeInteger(binding.field.ordinal)
            ? binding.field.ordinal as number
            : -1;
        const canonicalField = ordinal >= 0
            ? schema.structure.projections[ordinal]
            : undefined;
        if (
            canonicalField === undefined ||
            !sameProjection(canonicalField, binding.field)
        ) {
            return fail(
                'FOREIGN_FIELD',
                `${path}.field`,
                'Physical field does not belong to the child class'
            );
        }
        if (boundFields.has(ordinal)) {
            return fail(
                'DUPLICATE_FIELD_BINDING',
                `${path}.field`,
                `Physical field '${canonicalField.binderName}' is repeated`
            );
        }
        boundFields.add(ordinal);
        const mentionedGroups = new Set<number>();
        binding.inherited.forEach((identity, identityIndex) => {
            const identityPath = `${path}.inherited[${identityIndex}]`;
            const checked = methodIdentity(
                identity,
                identityPath,
                'FOREIGN_INHERITED_IDENTITY'
            );
            const group = inherited.classByIdentity.get(identityKey(checked));
            if (group === undefined) {
                return fail(
                    'FOREIGN_INHERITED_IDENTITY',
                    identityPath,
                    'Identity is not inherited through a direct parent'
                );
            }
            if (mentionedGroups.has(group) || assignedGroups.has(group)) {
                return fail(
                    'DUPLICATE_INHERITED_IDENTITY',
                    identityPath,
                    'Inherited identity class is assigned more than once'
                );
            }
            mentionedGroups.add(group);
            assignedGroups.set(group, ordinal);
            groupsByField[ordinal].push(group);
        });
    });
    inherited.classes.forEach((group, index) => {
        if (!assignedGroups.has(index)) {
            return fail(
                'MISSING_INHERITED_IDENTITY',
                'input.fieldBindings',
                `Missing inherited identity ` +
                    `'${displaySymbol(
                        group.canonicalCandidates[0].declaringClass
                    )}#${group.canonicalCandidates[0].ordinal}'`
            );
        }
    });

    const slotByIdentity = new Map<string, number>();
    const slots: CoreLfClassInheritanceSlot[] =
        schema.declaredMethods.map((method, index) => {
            const local = cloneData(method.identity);
            const groupIndexes = [...groupsByField[index]].sort(
                (left, right) => left - right
            );
            const inheritedIdentities = groupIndexes.flatMap(group =>
                inherited.classes[group].identities.map(cloneData)
            );
            const identities = [local, ...inheritedIdentities]
                .sort(compareIdentity)
                .filter((identity, identityIndex, values) =>
                    identityIndex === 0 ||
                    !sameIdentity(identity, values[identityIndex - 1])
                );
            const candidates = groupIndexes.flatMap(group =>
                inherited.classes[group].canonicalCandidates
            ).sort(compareIdentity);
            const canonical = cloneData(candidates[0] ?? local);
            identities.forEach(identity =>
                slotByIdentity.set(identityKey(identity), index)
            );
            return {
                ordinal: index,
                physicalField: cloneData(method.projection),
                localIdentity: local,
                canonicalIdentity: canonical,
                identities
            };
        });

    const aliasMap = new Map<string, CoreLfClassQualifiedMethodAlias>();
    const addAlias = (alias: CoreLfClassQualifiedMethodAlias): void => {
        const key = `${symbolKey(alias.declaringClass)}\u0000${alias.binderName}`;
        const existing = aliasMap.get(key);
        if (
            existing !== undefined &&
            (
                existing.slotOrdinal !== alias.slotOrdinal ||
                !sameIdentity(existing.identity, alias.identity)
            )
        ) {
            fail(
                'INVALID_INHERITANCE_LAYOUT',
                'input.directParentLayouts',
                'Qualified parent alias is inconsistent across a diamond'
            );
        }
        if (existing === undefined) aliasMap.set(key, alias);
    };
    schema.declaredMethods.forEach((method, index) => addAlias({
        declaringClass: cloneData(schema.classId),
        binderName: method.projection.binderName,
        identity: cloneData(method.identity),
        slotOrdinal: index
    }));
    parents.forEach(parent => parent.qualifiedMethods.forEach(alias => {
        const slotOrdinal = slotByIdentity.get(identityKey(alias.identity));
        if (slotOrdinal === undefined) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                'input.directParentLayouts',
                'Inherited alias has no assigned child physical slot'
            );
        }
        addAlias({
            declaringClass: cloneData(alias.declaringClass),
            binderName: alias.binderName,
            identity: cloneData(alias.identity),
            slotOrdinal
        });
    }));
    const resolutionRank = new Map<string, number>();
    resolutionOrder.forEach((entry, index) =>
        resolutionRank.set(symbolKey(entry.classId), index)
    );
    const qualifiedMethods = [...aliasMap.values()].sort((left, right) => {
        const leftRank = resolutionRank.get(symbolKey(left.declaringClass));
        const rightRank = resolutionRank.get(symbolKey(right.declaringClass));
        if (leftRank === undefined || rightRank === undefined) {
            return fail(
                'INVALID_INHERITANCE_LAYOUT',
                'input.directParentLayouts',
                'Qualified alias owner is absent from strict C3 order'
            );
        }
        if (leftRank !== rightRank) return leftRank - rightRank;
        if (left.binderName < right.binderName) return -1;
        if (left.binderName > right.binderName) return 1;
        return compareIdentity(left.identity, right.identity);
    });
    const aliasesByName = new Map<
        string,
        CoreLfClassQualifiedMethodAlias[]
    >();
    qualifiedMethods.forEach(alias => {
        const entries = aliasesByName.get(alias.binderName) ?? [];
        entries.push(alias);
        aliasesByName.set(alias.binderName, entries);
    });
    const unqualifiedMethods = [...aliasesByName.entries()]
        .map(([binderName, aliases]) => {
            const ordinals = new Set(aliases.map(alias => alias.slotOrdinal));
            if (ordinals.size !== 1) {
                return fail(
                    'FIELD_NAME_CONFLICT',
                    'input.fieldBindings',
                    `Unqualified method '${binderName}' names distinct ` +
                        'physical slots; add an explicit share or rename'
                );
            }
            const selected = aliases[0];
            const slot = slots[selected.slotOrdinal];
            return {
                binderName,
                slotOrdinal: selected.slotOrdinal,
                canonicalIdentity: cloneData(slot.canonicalIdentity),
                selectedDeclaringClass: cloneData(selected.declaringClass)
            };
        })
        .sort((left, right) => left.binderName < right.binderName
            ? -1
            : left.binderName > right.binderName ? 1 : 0);

    return deepFreeze(cloneData({
        revision: CORE_LF_CLASS_INHERITANCE_LAYOUT_PROFILE.revision,
        status: 'identity-layout-planned' as const,
        classId: schema.classId,
        schema,
        directParents: schema.directParents.map(parent => parent.parent),
        resolutionOrder,
        slots,
        qualifiedMethods,
        unqualifiedMethods
    }));
}
