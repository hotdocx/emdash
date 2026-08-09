import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfClassMethodIdentity,
    CoreLfClassSchema,
    CoreLfQualifiedSymbol,
    CoreLfStructureAvailableGlobalInput,
    CoreLfStructureDeclarationExpansion,
    CoreLfStructureMacroScope,
    binderMode,
    coreLfClassParameterTerm,
    declareCoreLfClassSchema
} from '../src/v3_2';
import {
    CORE_LF_CLASS_INHERITANCE_LAYOUT_PROFILE,
    CoreLfClassInheritanceError,
    CoreLfClassInheritanceErrorCode,
    CoreLfClassInheritanceLayout,
    planCoreLfClassInheritance
} from '../src/v3_2/lf_class_inheritance';

const moduleId = 'fixture.class_inheritance';
const authorityPath = 'tests/fixtures/class_inheritance.lp';
const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

const symbol = (name: string): CoreLfQualifiedSymbol => ({
    moduleId,
    name
});

const code = symbol('Code');

const availableFixture = ():
readonly CoreLfStructureAvailableGlobalInput[] => [{
    symbol: code,
    type: { tag: 'type' },
    availability: 'earlier-fragment',
    order: 0
}];

const expandClass = (
    name: string,
    fields: readonly string[]
): CoreLfStructureDeclarationExpansion => {
    const scope = new CoreLfStructureMacroScope(
        moduleId,
        availableFixture()
    );
    const resolvedCode = scope.resolve(code);
    const prefix = name.replace(/Class$/u, '').toLowerCase();
    return scope.declareStructure({
        order: 1,
        carrierName: name,
        constructorName: `Mk${name}`,
        fields(builder) {
            builder.parameter({
                binderName: 'A',
                modes: {
                    carrier: implicitMode,
                    constructor: implicitMode,
                    projection: implicitMode
                },
                type: builder.global(resolvedCode)
            });
            fields.forEach(field => builder.field({
                binderName: field,
                projectionName: `${prefix}_${field}`,
                mode: explicitMode,
                type: builder.global(resolvedCode)
            }));
        },
        provenance: {
            authorityPath,
            sourceFragment: `inheritance fixture ${name}`
        }
    });
};

const declareSchema = (
    name: string,
    fields: readonly string[],
    parents: readonly CoreLfClassSchema[] = []
): CoreLfClassSchema => {
    const expansion = expandClass(name, fields);
    const childParameter = coreLfClassParameterTerm(
        expansion,
        expansion.handle.parameters[0]
    );
    return declareCoreLfClassSchema({
        expansion,
        directParents: parents.map(parent => ({
            parent,
            arguments: [{
                parameter: parent.structure.parameters[0],
                value: childParameter
            }]
        }))
    });
};

const method = (
    schema: CoreLfClassSchema,
    binderName: string
) => {
    const found = schema.declaredMethods.find(candidate =>
        candidate.projection.binderName === binderName
    );
    assert.notEqual(found, undefined);
    return found!;
};

const slot = (
    layout: CoreLfClassInheritanceLayout,
    binderName: string
) => {
    const found = layout.slots.find(candidate =>
        candidate.physicalField.binderName === binderName
    );
    assert.notEqual(found, undefined);
    return found!;
};

const binding = (
    schema: CoreLfClassSchema,
    binderName: string,
    inherited: readonly CoreLfClassMethodIdentity[]
) => ({
    field: method(schema, binderName).projection,
    inherited
});

const parentFreeLayout = (
    schema: CoreLfClassSchema
): CoreLfClassInheritanceLayout => planCoreLfClassInheritance({
    schema,
    directParentLayouts: []
});

interface AlgebraicDiamond {
    readonly mul: CoreLfClassInheritanceLayout;
    readonly one: CoreLfClassInheritanceLayout;
    readonly semigroup: CoreLfClassInheritanceLayout;
    readonly mulOne: CoreLfClassInheritanceLayout;
    readonly monoidSchema: CoreLfClassSchema;
    readonly monoid: CoreLfClassInheritanceLayout;
}

const algebraicDiamond = (
    reverseBindings = false,
    copyParents = false
): AlgebraicDiamond => {
    const mulSchema = declareSchema('MulClass', ['mul']);
    const oneSchema = declareSchema('OneClass', ['one']);
    const mul = parentFreeLayout(mulSchema);
    const one = parentFreeLayout(oneSchema);

    const semigroupSchema = declareSchema(
        'SemigroupClass',
        ['mul', 'assoc'],
        [mulSchema]
    );
    const semigroup = planCoreLfClassInheritance({
        schema: semigroupSchema,
        directParentLayouts: [mul],
        fieldBindings: [binding(
            semigroupSchema,
            'mul',
            [slot(mul, 'mul').canonicalIdentity]
        )]
    });

    const mulOneSchema = declareSchema(
        'MulOneClass',
        ['mul', 'one', 'one_mul', 'mul_one'],
        [mulSchema, oneSchema]
    );
    const mulOne = planCoreLfClassInheritance({
        schema: mulOneSchema,
        directParentLayouts: [mul, one],
        fieldBindings: [
            binding(
                mulOneSchema,
                'mul',
                [slot(mul, 'mul').canonicalIdentity]
            ),
            binding(
                mulOneSchema,
                'one',
                [slot(one, 'one').canonicalIdentity]
            )
        ]
    });

    const monoidSchema = declareSchema(
        'MonoidClass',
        ['mul', 'assoc', 'one', 'one_mul', 'mul_one'],
        [semigroupSchema, mulOneSchema]
    );
    const fieldBindings = [
        binding(
            monoidSchema,
            'mul',
            [slot(mul, 'mul').canonicalIdentity]
        ),
        binding(
            monoidSchema,
            'assoc',
            [slot(semigroup, 'assoc').canonicalIdentity]
        ),
        binding(
            monoidSchema,
            'one',
            [slot(one, 'one').canonicalIdentity]
        ),
        binding(
            monoidSchema,
            'one_mul',
            [slot(mulOne, 'one_mul').canonicalIdentity]
        ),
        binding(
            monoidSchema,
            'mul_one',
            [slot(mulOne, 'mul_one').canonicalIdentity]
        )
    ];
    const parentLayouts = copyParents
        ? JSON.parse(JSON.stringify([semigroup, mulOne])) as
            CoreLfClassInheritanceLayout[]
        : [semigroup, mulOne];
    const monoid = planCoreLfClassInheritance({
        schema: monoidSchema,
        directParentLayouts: parentLayouts,
        fieldBindings: reverseBindings
            ? [...fieldBindings].reverse()
            : fieldBindings
    });
    return { mul, one, semigroup, mulOne, monoidSchema, monoid };
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const throwsInheritance = (
    action: () => unknown,
    code: CoreLfClassInheritanceErrorCode,
    path: string
): CoreLfClassInheritanceError => {
    let caught: CoreLfClassInheritanceError | undefined;
    assert.throws(action, error => {
        assert.equal(error instanceof CoreLfClassInheritanceError, true);
        caught = error as CoreLfClassInheritanceError;
        assert.equal(caught.code, code);
        assert.equal(caught.path, path);
        return true;
    });
    return caught!;
};

describe('outer LF class inheritance identity layout', () => {
    it('bootstraps deterministic parent-free physical slots', () => {
        const schema = declareSchema('ParentFreeClass', ['first', 'second']);
        const layout = parentFreeLayout(schema);

        assert.equal(
            layout.revision,
            CORE_LF_CLASS_INHERITANCE_LAYOUT_PROFILE.revision
        );
        assert.equal(layout.status, 'identity-layout-planned');
        assert.deepEqual(
            layout.resolutionOrder.map(entry => entry.classId.name),
            ['ParentFreeClass']
        );
        assert.deepEqual(
            layout.slots.map(entry => ({
                field: entry.physicalField.binderName,
                canonical: entry.canonicalIdentity.ordinal,
                identities: entry.identities.length
            })),
            [{ field: 'first', canonical: 0, identities: 1 }, {
                field: 'second', canonical: 1, identities: 1
            }]
        );
        assert.deepEqual(
            layout.unqualifiedMethods.map(entry => [
                entry.binderName,
                entry.slotOrdinal,
                entry.selectedDeclaringClass.name
            ]),
            [
                ['first', 0, 'ParentFreeClass'],
                ['second', 1, 'ParentFreeClass']
            ]
        );
        assertDeepFrozen(layout);
        assert.doesNotThrow(() => JSON.parse(JSON.stringify(layout)));
    });

    it('computes the strict algebraic C3 order with one shared Mul slot', () => {
        const { monoid } = algebraicDiamond(false, true);

        assert.deepEqual(
            monoid.resolutionOrder.map(entry => entry.classId.name),
            [
                'MonoidClass',
                'SemigroupClass',
                'MulOneClass',
                'MulClass',
                'OneClass'
            ]
        );
        const mulIdentity = monoid.qualifiedMethods.find(alias =>
            alias.declaringClass.name === 'MulClass' &&
            alias.binderName === 'mul'
        )!.identity;
        const matchingSlots = monoid.slots.filter(candidate =>
            candidate.identities.some(identity =>
                identity.declaringClass.name === 'MulClass' &&
                identity.ordinal === mulIdentity.ordinal
            )
        );
        assert.equal(matchingSlots.length, 1);
        assert.equal(matchingSlots[0].physicalField.binderName, 'mul');
        assert.equal(
            matchingSlots[0].canonicalIdentity.declaringClass.name,
            'MulClass'
        );
        assert.deepEqual(
            matchingSlots[0].identities.map(identity =>
                identity.declaringClass.name
            ),
            ['MonoidClass', 'MulClass', 'MulOneClass', 'SemigroupClass']
                .sort()
        );
        assert.equal(
            monoid.unqualifiedMethods.find(entry =>
                entry.binderName === 'mul'
            )?.slotOrdinal,
            matchingSlots[0].ordinal
        );
        assertDeepFrozen(monoid);
    });

    it('is stable across field-binding permutations and preserves inputs', () => {
        const ordinary = algebraicDiamond(false, true);
        const reversed = algebraicDiamond(true, true);
        assert.deepEqual(ordinary.monoid, reversed.monoid);

        const parentCopies = JSON.parse(JSON.stringify([
            ordinary.semigroup,
            ordinary.mulOne
        ])) as CoreLfClassInheritanceLayout[];
        const bindings = [binding(
            ordinary.monoidSchema,
            'mul',
            [slot(ordinary.mul, 'mul').canonicalIdentity]
        ), binding(
            ordinary.monoidSchema,
            'assoc',
            [slot(ordinary.semigroup, 'assoc').canonicalIdentity]
        ), binding(
            ordinary.monoidSchema,
            'one',
            [slot(ordinary.one, 'one').canonicalIdentity]
        ), binding(
            ordinary.monoidSchema,
            'one_mul',
            [slot(ordinary.mulOne, 'one_mul').canonicalIdentity]
        ), binding(
            ordinary.monoidSchema,
            'mul_one',
            [slot(ordinary.mulOne, 'mul_one').canonicalIdentity]
        )];
        const beforeParents = structuredClone(parentCopies);
        const beforeBindings = structuredClone(bindings);
        planCoreLfClassInheritance({
            schema: structuredClone(ordinary.monoidSchema),
            directParentLayouts: parentCopies,
            fieldBindings: bindings
        });
        assert.deepEqual(parentCopies, beforeParents);
        assert.deepEqual(bindings, beforeBindings);
        assert.equal(Object.isFrozen(parentCopies), false);
        assert.equal(Object.isFrozen(bindings), false);
    });

    it('requires explicit sharing for unrelated same-named fields', () => {
        const leftSchema = declareSchema('LeftOperationClass', ['op']);
        const rightSchema = declareSchema('RightOperationClass', ['op']);
        const left = parentFreeLayout(leftSchema);
        const right = parentFreeLayout(rightSchema);
        const sharedSchema = declareSchema(
            'SharedOperationClass',
            ['op'],
            [leftSchema, rightSchema]
        );
        const shared = planCoreLfClassInheritance({
            schema: sharedSchema,
            directParentLayouts: [left, right],
            fieldBindings: [binding(sharedSchema, 'op', [
                slot(left, 'op').canonicalIdentity,
                slot(right, 'op').canonicalIdentity
            ])]
        });
        assert.equal(shared.slots.length, 1);
        assert.equal(shared.slots[0].identities.length, 3);
        assert.equal(
            shared.unqualifiedMethods.find(entry =>
                entry.binderName === 'op'
            )?.slotOrdinal,
            0
        );

        const conflictSchema = declareSchema(
            'ConflictingOperationClass',
            ['leftOp', 'rightOp'],
            [leftSchema, rightSchema]
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: conflictSchema,
                directParentLayouts: [left, right],
                fieldBindings: [
                    binding(conflictSchema, 'leftOp', [
                        slot(left, 'op').canonicalIdentity
                    ]),
                    binding(conflictSchema, 'rightOp', [
                        slot(right, 'op').canonicalIdentity
                    ])
                ]
            }),
            'FIELD_NAME_CONFLICT',
            'input.fieldBindings'
        );
    });

    it('rejects invalid schemas, parent order, fields, and identities', () => {
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: {} as CoreLfClassSchema,
                directParentLayouts: []
            }),
            'INVALID_INHERITANCE_LAYOUT',
            'input.schema'
        );

        const leftSchema = declareSchema('ValidationLeftClass', ['left']);
        const rightSchema = declareSchema('ValidationRightClass', ['right']);
        const left = parentFreeLayout(leftSchema);
        const right = parentFreeLayout(rightSchema);
        const childSchema = declareSchema(
            'ValidationChildClass',
            ['left', 'right'],
            [leftSchema, rightSchema]
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [right, left]
            }),
            'PARENT_LAYOUT_MISMATCH',
            'input.directParentLayouts[0]'
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [left, right],
                fieldBindings: [{
                    field: leftSchema.declaredMethods[0].projection,
                    inherited: [slot(left, 'left').canonicalIdentity]
                }]
            }),
            'FOREIGN_FIELD',
            'input.fieldBindings[0].field'
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [left, right],
                fieldBindings: [
                    binding(childSchema, 'left', [
                        slot(left, 'left').canonicalIdentity
                    ]),
                    binding(childSchema, 'left', [
                        slot(right, 'right').canonicalIdentity
                    ])
                ]
            }),
            'DUPLICATE_FIELD_BINDING',
            'input.fieldBindings[1].field'
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [left, right],
                fieldBindings: [binding(childSchema, 'left', [{
                    declaringClass: childSchema.classId,
                    ordinal: 0
                }])]
            }),
            'FOREIGN_INHERITED_IDENTITY',
            'input.fieldBindings[0].inherited[0]'
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [left, right],
                fieldBindings: [binding(childSchema, 'left', [
                    slot(left, 'left').canonicalIdentity,
                    slot(left, 'left').canonicalIdentity
                ])]
            }),
            'DUPLICATE_INHERITED_IDENTITY',
            'input.fieldBindings[0].inherited[1]'
        );
        throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [left, right],
                fieldBindings: [binding(childSchema, 'left', [
                    slot(left, 'left').canonicalIdentity
                ])]
            }),
            'MISSING_INHERITED_IDENTITY',
            'input.fieldBindings'
        );
    });

    it('rejects the classic inconsistent strict-C3 hierarchy', () => {
        const rootSchema = declareSchema('C3RootClass', ['op']);
        const root = parentFreeLayout(rootSchema);
        const extendRoot = (name: string) => {
            const schema = declareSchema(name, ['op'], [rootSchema]);
            return {
                schema,
                layout: planCoreLfClassInheritance({
                    schema,
                    directParentLayouts: [root],
                    fieldBindings: [binding(schema, 'op', [
                        slot(root, 'op').canonicalIdentity
                    ])]
                })
            };
        };
        const x = extendRoot('C3XClass');
        const y = extendRoot('C3YClass');
        const extendPair = (
            name: string,
            first: typeof x,
            second: typeof y
        ) => {
            const schema = declareSchema(
                name,
                ['op'],
                [first.schema, second.schema]
            );
            return {
                schema,
                layout: planCoreLfClassInheritance({
                    schema,
                    directParentLayouts: [first.layout, second.layout],
                    fieldBindings: [binding(schema, 'op', [
                        slot(root, 'op').canonicalIdentity
                    ])]
                })
            };
        };
        const a = extendPair('C3AClass', x, y);
        const b = extendPair('C3BClass', y, x);
        const impossible = declareSchema(
            'C3ImpossibleClass',
            ['op'],
            [a.schema, b.schema]
        );
        const error = throwsInheritance(
            () => planCoreLfClassInheritance({
                schema: impossible,
                directParentLayouts: [a.layout, b.layout],
                fieldBindings: []
            }),
            'INCONSISTENT_C3',
            'input.directParentLayouts'
        );
        assert.equal((error.evidence?.length ?? 0) >= 2, true);
        assert.equal(
            error.evidence?.some(entry => entry.includes('C3XClass')),
            true
        );
        assert.equal(
            error.evidence?.some(entry => entry.includes('C3YClass')),
            true
        );
    });
});
