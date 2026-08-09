import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreLfClassMethodIdentity,
    CoreLfClassSchema,
    CoreLfClassInheritanceLayout,
    CoreLfClassInheritanceLoweringError,
    CoreLfClassInheritanceLoweringErrorCode,
    CoreLfClassInheritanceLoweringExpansion,
    CoreLfClassParentConversionHandle,
    CoreLfDeclarationCompilerError,
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfStructureAvailableGlobalInput,
    CoreLfStructureDeclarationExpansion,
    CoreLfStructureMacroScope,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferPolicyEntry,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferRuntimeRule,
    binderMode,
    compileCoreLfMixedPhases,
    CORE_LF_CLASS_INHERITANCE_LOWERING_PROFILE,
    applyCoreLfClassParentConversion,
    coreLfClassParameterTerm,
    coreLfCombinedNormalize,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay,
    declareCoreLfClassSchema,
    kernelExpressionEquals,
    lowerCoreLfClassInheritance,
    planCoreLfClassInheritance,
    planCoreLfMixedPhases
} from '../src/v3_2';

const moduleId = 'fixture.class_inheritance_lowering';
const authorityPath = 'tests/fixtures/class_inheritance_lowering.lp';
const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

const symbol = (name: string): CoreLfQualifiedSymbol => ({
    moduleId,
    name
});

const code = symbol('Code');

const global = (
    value: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({ tag: 'global', symbol: value });

const bound = (index: number): CoreLfTransferExpression => ({
    tag: 'bound',
    index
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
    arguments: arguments_
});

const explicit = (value: CoreLfTransferExpression) => ({
    plicity: 'explicit' as const,
    value
});

const implicit = (value: CoreLfTransferExpression) => ({
    plicity: 'implicit' as const,
    value
});

const source = (sourceFragment: string) => ({
    authorityPath,
    sourceFragment
});

const codeDeclaration = (): CoreLfTransferDeclaration => ({
    order: 0,
    symbol: code,
    type: { tag: 'type' },
    body: coreLfTransferAbsentBody(),
    modifiers: {
        visibility: 'public',
        rigidity: 'constant',
        sourceOpacity: 'opaque'
    },
    provenance: source('constant symbol Code : TYPE;')
});

const availableFixture = ():
readonly CoreLfStructureAvailableGlobalInput[] => [{
    symbol: code,
    type: { tag: 'type' },
    availability: 'earlier-fragment',
    order: 0
}];

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

interface ClassEntry {
    readonly expansion: CoreLfStructureDeclarationExpansion;
    readonly schema: CoreLfClassSchema;
    readonly layout: CoreLfClassInheritanceLayout;
}

interface AlgebraicFixture {
    readonly structures: readonly CoreLfStructureDeclarationExpansion[];
    readonly mul: ClassEntry;
    readonly one: ClassEntry;
    readonly semigroup: ClassEntry;
    readonly mulOne: ClassEntry;
    readonly monoid: ClassEntry;
    readonly lowerings:
        readonly CoreLfClassInheritanceLoweringExpansion[];
    readonly mulLowering: CoreLfClassInheritanceLoweringExpansion;
    readonly oneLowering: CoreLfClassInheritanceLoweringExpansion;
    readonly semigroupLowering: CoreLfClassInheritanceLoweringExpansion;
    readonly mulOneLowering: CoreLfClassInheritanceLoweringExpansion;
    readonly monoidLowering: CoreLfClassInheritanceLoweringExpansion;
    readonly nextOrder: number;
}

const algebraicFixture = (): AlgebraicFixture => {
    const scope = new CoreLfStructureMacroScope(
        moduleId,
        availableFixture()
    );
    const resolvedCode = scope.resolve(code);
    let order = 1;

    const expand = (
        name: string,
        fields: readonly string[]
    ): CoreLfStructureDeclarationExpansion => {
        const prefix = name.replace(/Class$/u, '').toLowerCase();
        const expansion = scope.declareStructure({
            order,
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
            provenance: source(`class inheritance structure ${name}`)
        });
        order = expansion.nextOrder;
        return expansion;
    };

    const schema = (
        expansion: CoreLfStructureDeclarationExpansion,
        parents: readonly CoreLfClassSchema[] = []
    ): CoreLfClassSchema => {
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

    const mulExpansion = expand('MulClass', ['mul']);
    const mulSchema = schema(mulExpansion);
    const mulLayout = parentFreeLayout(mulSchema);
    const mul: ClassEntry = {
        expansion: mulExpansion,
        schema: mulSchema,
        layout: mulLayout
    };

    const oneExpansion = expand('OneClass', ['one']);
    const oneSchema = schema(oneExpansion);
    const oneLayout = parentFreeLayout(oneSchema);
    const one: ClassEntry = {
        expansion: oneExpansion,
        schema: oneSchema,
        layout: oneLayout
    };

    const semigroupExpansion = expand(
        'SemigroupClass',
        ['mul', 'assoc']
    );
    const semigroupSchema = schema(semigroupExpansion, [mulSchema]);
    const semigroupLayout = planCoreLfClassInheritance({
        schema: semigroupSchema,
        directParentLayouts: [mulLayout],
        fieldBindings: [binding(
            semigroupSchema,
            'mul',
            [slot(mulLayout, 'mul').canonicalIdentity]
        )]
    });
    const semigroup: ClassEntry = {
        expansion: semigroupExpansion,
        schema: semigroupSchema,
        layout: semigroupLayout
    };

    const mulOneExpansion = expand(
        'MulOneClass',
        ['mul', 'one', 'one_mul', 'mul_one']
    );
    const mulOneSchema = schema(
        mulOneExpansion,
        [mulSchema, oneSchema]
    );
    const mulOneLayout = planCoreLfClassInheritance({
        schema: mulOneSchema,
        directParentLayouts: [mulLayout, oneLayout],
        fieldBindings: [
            binding(
                mulOneSchema,
                'mul',
                [slot(mulLayout, 'mul').canonicalIdentity]
            ),
            binding(
                mulOneSchema,
                'one',
                [slot(oneLayout, 'one').canonicalIdentity]
            )
        ]
    });
    const mulOne: ClassEntry = {
        expansion: mulOneExpansion,
        schema: mulOneSchema,
        layout: mulOneLayout
    };

    const monoidExpansion = expand(
        'MonoidClass',
        ['mul', 'assoc', 'one', 'one_mul', 'mul_one']
    );
    const monoidSchema = schema(
        monoidExpansion,
        [semigroupSchema, mulOneSchema]
    );
    const monoidLayout = planCoreLfClassInheritance({
        schema: monoidSchema,
        directParentLayouts: [semigroupLayout, mulOneLayout],
        fieldBindings: [
            binding(
                monoidSchema,
                'mul',
                [slot(mulLayout, 'mul').canonicalIdentity]
            ),
            binding(
                monoidSchema,
                'assoc',
                [slot(semigroupLayout, 'assoc').canonicalIdentity]
            ),
            binding(
                monoidSchema,
                'one',
                [slot(oneLayout, 'one').canonicalIdentity]
            ),
            binding(
                monoidSchema,
                'one_mul',
                [slot(mulOneLayout, 'one_mul').canonicalIdentity]
            ),
            binding(
                monoidSchema,
                'mul_one',
                [slot(mulOneLayout, 'mul_one').canonicalIdentity]
            )
        ]
    });
    const monoid: ClassEntry = {
        expansion: monoidExpansion,
        schema: monoidSchema,
        layout: monoidLayout
    };

    const mulLowering = lowerCoreLfClassInheritance({
        layout: mulLayout,
        order,
        directParents: [],
        provenance: source('parent-free MulClass lowering')
    });
    const oneLowering = lowerCoreLfClassInheritance({
        layout: oneLayout,
        order,
        directParents: [],
        provenance: source('parent-free OneClass lowering')
    });
    const semigroupLowering = lowerCoreLfClassInheritance({
        layout: semigroupLayout,
        order,
        directParents: [{
            layout: mulLayout,
            conversionName: 'semigroup_to_mul'
        }],
        provenance: source('SemigroupClass parent conversions')
    });
    order = semigroupLowering.nextOrder;
    const mulOneLowering = lowerCoreLfClassInheritance({
        layout: mulOneLayout,
        order,
        directParents: [{
            layout: oneLayout,
            conversionName: 'mul_one_to_one'
        }, {
            layout: mulLayout,
            conversionName: 'mul_one_to_mul'
        }],
        provenance: source('MulOneClass parent conversions')
    });
    order = mulOneLowering.nextOrder;
    const monoidLowering = lowerCoreLfClassInheritance({
        layout: monoidLayout,
        order,
        directParents: [{
            layout: mulOneLayout,
            conversionName: 'monoid_to_mul_one'
        }, {
            layout: semigroupLayout,
            conversionName: 'monoid_to_semigroup'
        }],
        provenance: source('MonoidClass parent conversions')
    });
    order = monoidLowering.nextOrder;

    return {
        structures: [
            mulExpansion,
            oneExpansion,
            semigroupExpansion,
            mulOneExpansion,
            monoidExpansion
        ],
        mul,
        one,
        semigroup,
        mulOne,
        monoid,
        lowerings: [
            mulLowering,
            oneLowering,
            semigroupLowering,
            mulOneLowering,
            monoidLowering
        ],
        mulLowering,
        oneLowering,
        semigroupLowering,
        mulOneLowering,
        monoidLowering,
        nextOrder: order
    };
};

const conversionTo = (
    lowering: CoreLfClassInheritanceLoweringExpansion,
    parentName: string
): CoreLfClassParentConversionHandle => {
    const found = lowering.directParentConversions.find(conversion =>
        conversion.parent.classId.name === parentName
    );
    assert.notEqual(found, undefined);
    return found!;
};

const classAt = (
    entry: ClassEntry,
    parameter: CoreLfTransferExpression
): CoreLfTransferExpression => call(
    global(entry.schema.structure.carrier),
    [implicit(parameter)]
);

const constantDeclaration = (
    order: number,
    value: CoreLfQualifiedSymbol,
    type: CoreLfTransferExpression,
    body?: CoreLfTransferExpression
): CoreLfTransferDeclaration => ({
    order,
    symbol: value,
    type,
    body: body === undefined
        ? coreLfTransferAbsentBody()
        : coreLfTransferExplicitBody(body),
    modifiers: {
        visibility: 'public',
        rigidity: body === undefined ? 'constant' : 'ordinary',
        sourceOpacity: body === undefined ? 'opaque' : 'transparent'
    },
    provenance: source(`class lowering fixture ${value.name}`)
});

interface PolicySource {
    readonly sourceOrder: number;
    readonly entry: Omit<CoreLfTransferPolicyEntry, 'order'>;
}

const fixturePolicy = (
    module: CoreLfModuleSpec
): CoreLfTransferPolicyOverlay => {
    const entries: PolicySource[] = [
        ...module.declarations.map(declaration => ({
            sourceOrder: declaration.order,
            entry: {
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: declaration.body.kind === 'explicit-term'
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
                evidence: declaration.body.kind === 'explicit-term'
                    ? 'checked class parent conversion or consumer'
                    : 'class lowering fixture signature'
            }
        })),
        ...module.runtimeRules.map(rule => ({
            sourceOrder: rule.order,
            entry: {
                target: {
                    kind: 'runtime-rule' as const,
                    id: rule.id
                },
                policy: 'runtime-rewrite' as const,
                evidence: 'generated structure projection beta'
            }
        }))
    ];
    entries.sort((left, right) => left.sourceOrder - right.sourceOrder);
    return createCoreLfTransferPolicyOverlay(module, {
        revision: 'class-inheritance-lowering-policy-1',
        moduleRevision: module.revision,
        entries: entries.map(({ entry }, order) => ({ order, ...entry }))
    });
};

const compileFixture = (
    declarations: readonly CoreLfTransferDeclaration[],
    runtimeRules: readonly CoreLfTransferRuntimeRule[]
) => {
    const module = createCoreLfModuleSpec({
        revision: 'class-inheritance-lowering-fixture-1',
        moduleId,
        fragmentId: 'class-inheritance-lowering',
        authorityPath,
        sourceSha256:
            'sha256:abababababababababababababababababababababababababababababababab',
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules,
        proofRules: []
    });
    const policy = fixturePolicy(module);
    const plan = planCoreLfMixedPhases(module, policy);
    const linkage = createCoreLfMixedDeclarationLinkage(plan, {
        revision: 'class-inheritance-lowering-linkage-1',
        moduleRevision: module.revision,
        entries: [...declarations]
            .sort((left, right) => left.order - right.order)
            .map((declaration, order) => ({
                order,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName: `class_lowering_${declaration.symbol.name}`,
                backendName: declaration.symbol.name
            }))
    });
    return compileCoreLfMixedPhases(plan, linkage);
};

const sharedFieldFixture = (
    rightFieldType: 'code' | 'decoded'
) => {
    const el = symbol('El');
    const elType: CoreLfTransferExpression = {
        tag: 'pi',
        binder: {
            hint: 'A',
            mode: explicitMode,
            type: global(code)
        },
        body: { tag: 'type' }
    };
    const initialDeclarations: readonly CoreLfTransferDeclaration[] = [
        codeDeclaration(),
        {
            order: 1,
            symbol: el,
            type: elType,
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'constant',
                sourceOpacity: 'opaque'
            },
            provenance: source('constant symbol El (A : Code) : TYPE;')
        }
    ];
    const scope = new CoreLfStructureMacroScope(moduleId, [{
        symbol: code,
        type: { tag: 'type' },
        availability: 'earlier-fragment',
        order: 0
    }, {
        symbol: el,
        type: elType,
        availability: 'earlier-fragment',
        order: 1
    }]);
    const resolvedCode = scope.resolve(code);
    const resolvedEl = scope.resolve(el);
    let order = 2;
    const expand = (
        name: string,
        fieldType: 'code' | 'decoded'
    ): CoreLfStructureDeclarationExpansion => {
        const expansion = scope.declareStructure({
            order,
            carrierName: name,
            constructorName: `Mk${name}`,
            fields(builder) {
                const A = builder.parameter({
                    binderName: 'A',
                    modes: {
                        carrier: implicitMode,
                        constructor: implicitMode,
                        projection: implicitMode
                    },
                    type: builder.global(resolvedCode)
                });
                builder.field({
                    binderName: 'op',
                    projectionName: `${name.toLowerCase()}_op`,
                    mode: explicitMode,
                    type: fieldType === 'code'
                        ? builder.global(resolvedCode)
                        : builder.apply(builder.global(resolvedEl), A)
                });
            },
            provenance: source(`explicit share structure ${name}`)
        });
        order = expansion.nextOrder;
        return expansion;
    };
    const leftExpansion = expand('ShareLeftClass', 'code');
    const rightExpansion = expand('ShareRightClass', rightFieldType);
    const childExpansion = expand('ShareChildClass', 'code');
    const schema = (
        expansion: CoreLfStructureDeclarationExpansion,
        parents: readonly CoreLfClassSchema[] = []
    ) => {
        const A = coreLfClassParameterTerm(
            expansion,
            expansion.handle.parameters[0]
        );
        return declareCoreLfClassSchema({
            expansion,
            directParents: parents.map(parent => ({
                parent,
                arguments: [{
                    parameter: parent.structure.parameters[0],
                    value: A
                }]
            }))
        });
    };
    const leftSchema = schema(leftExpansion);
    const rightSchema = schema(rightExpansion);
    const childSchema = schema(
        childExpansion,
        [leftSchema, rightSchema]
    );
    const leftLayout = parentFreeLayout(leftSchema);
    const rightLayout = parentFreeLayout(rightSchema);
    const childLayout = planCoreLfClassInheritance({
        schema: childSchema,
        directParentLayouts: [leftLayout, rightLayout],
        fieldBindings: [binding(childSchema, 'op', [
            slot(leftLayout, 'op').canonicalIdentity,
            slot(rightLayout, 'op').canonicalIdentity
        ])]
    });
    const lowering = lowerCoreLfClassInheritance({
        layout: childLayout,
        order,
        directParents: [{
            layout: rightLayout,
            conversionName: 'share_to_right'
        }, {
            layout: leftLayout,
            conversionName: 'share_to_left'
        }],
        provenance: source('explicit shared parent conversions')
    });
    const structures = [leftExpansion, rightExpansion, childExpansion];
    return {
        lowering,
        declarations: [
            ...initialDeclarations,
            ...structures.flatMap(entry => entry.declarations),
            ...lowering.declarations
        ],
        runtimeRules: structures.flatMap(entry => entry.runtimeRules)
    };
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const throwsLowering = (
    action: () => unknown,
    code_: CoreLfClassInheritanceLoweringErrorCode,
    path?: string
): CoreLfClassInheritanceLoweringError => {
    let caught: CoreLfClassInheritanceLoweringError | undefined;
    assert.throws(action, error => {
        assert.equal(
            error instanceof CoreLfClassInheritanceLoweringError,
            true
        );
        caught = error as CoreLfClassInheritanceLoweringError;
        assert.equal(caught.code, code_);
        if (path !== undefined) assert.equal(caught.path, path);
        return true;
    });
    return caught!;
};

describe('outer LF class inheritance lowering', () => {
    it('bootstraps a finite parent-free expansion', () => {
        const fixture = algebraicFixture();
        const lowering = fixture.mulLowering;

        assert.equal(
            lowering.revision,
            CORE_LF_CLASS_INHERITANCE_LOWERING_PROFILE.revision
        );
        assert.equal(lowering.status, 'parent-conversions-expanded');
        assert.deepEqual(lowering.sourceOrders, []);
        assert.deepEqual(lowering.declarations, []);
        assert.deepEqual(lowering.directParentConversions, []);
        assert.equal(
            lowering.nextOrder,
            fixture.monoid.expansion.nextOrder
        );
        assertDeepFrozen(lowering);
        assert.doesNotThrow(() => JSON.parse(JSON.stringify(lowering)));
    });

    it('canonicalizes direct parents and generates exact shifted terms', () => {
        const fixture = algebraicFixture();
        const lowering = fixture.monoidLowering;

        assert.deepEqual(
            lowering.directParentConversions.map(entry => [
                entry.ordinal,
                entry.parent.classId.name,
                entry.symbol.name
            ]),
            [
                [0, 'SemigroupClass', 'monoid_to_semigroup'],
                [1, 'MulOneClass', 'monoid_to_mul_one']
            ]
        );
        assert.deepEqual(
            lowering.sourceOrders,
            [lowering.declarations[0].order, lowering.declarations[1].order]
        );
        const conversion = lowering.declarations[0];
        assert.equal(conversion.body.kind, 'explicit-term');
        assert.equal(conversion.type.tag, 'pi');
        if (conversion.type.tag !== 'pi') return;
        assert.deepEqual(conversion.type.binder.mode, implicitMode);
        assert.equal(conversion.type.body.tag, 'pi');
        if (conversion.type.body.tag !== 'pi') return;
        assert.deepEqual(conversion.type.body.binder.mode, explicitMode);
        assert.equal(conversion.type.body.body.tag, 'call');
        if (conversion.type.body.body.tag !== 'call') return;
        assert.deepEqual(
            conversion.type.body.body.arguments[0].value,
            bound(1)
        );
        if (conversion.body.kind !== 'explicit-term') return;
        assert.equal(conversion.body.term.tag, 'lambda');
        if (conversion.body.term.tag !== 'lambda') return;
        assert.equal(conversion.body.term.body.tag, 'lambda');
        if (conversion.body.term.body.tag !== 'lambda') return;
        const construction = conversion.body.term.body.body;
        assert.equal(construction.tag, 'call');
        if (construction.tag !== 'call') return;
        assert.deepEqual(construction.arguments[0].value, bound(1));
        const inheritedMul = construction.arguments[1].value;
        assert.equal(inheritedMul.tag, 'call');
        if (inheritedMul.tag !== 'call') return;
        assert.deepEqual(
            inheritedMul.arguments.map(argument => argument.value),
            [bound(1), bound(0)]
        );
        assertDeepFrozen(lowering);
    });

    it('preserves a two-parameter telescope and named application order',
        () => {
            const scope = new CoreLfStructureMacroScope(
                moduleId,
                availableFixture()
            );
            const resolvedCode = scope.resolve(code);
            let order = 1;
            const expand = (
                name: 'BinaryParentClass' | 'BinaryChildClass'
            ) => {
                const expansion = scope.declareStructure({
                    order,
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
                        builder.parameter({
                            binderName: 'B',
                            modes: {
                                carrier: explicitMode,
                                constructor: explicitMode,
                                projection: explicitMode
                            },
                            type: builder.global(resolvedCode)
                        });
                        builder.field({
                            binderName: 'op',
                            projectionName: `${name.toLowerCase()}_op`,
                            mode: explicitMode,
                            type: builder.global(resolvedCode)
                        });
                    },
                    provenance: source(`binary structure ${name}`)
                });
                order = expansion.nextOrder;
                return expansion;
            };
            const parentExpansion = expand('BinaryParentClass');
            const parentSchema = declareCoreLfClassSchema({
                expansion: parentExpansion
            });
            const parentLayout = parentFreeLayout(parentSchema);
            const childExpansion = expand('BinaryChildClass');
            const childA = coreLfClassParameterTerm(
                childExpansion,
                childExpansion.handle.parameters[0]
            );
            const childB = coreLfClassParameterTerm(
                childExpansion,
                childExpansion.handle.parameters[1]
            );
            const childSchema = declareCoreLfClassSchema({
                expansion: childExpansion,
                directParents: [{
                    parent: parentSchema,
                    arguments: [{
                        parameter: parentSchema.structure.parameters[1],
                        value: childB
                    }, {
                        parameter: parentSchema.structure.parameters[0],
                        value: childA
                    }]
                }]
            });
            const childLayout = planCoreLfClassInheritance({
                schema: childSchema,
                directParentLayouts: [parentLayout],
                fieldBindings: [binding(childSchema, 'op', [
                    slot(parentLayout, 'op').canonicalIdentity
                ])]
            });
            const lowering = lowerCoreLfClassInheritance({
                layout: childLayout,
                order,
                directParents: [{
                    layout: parentLayout,
                    conversionName: 'binary_child_to_parent'
                }],
                provenance: source('binary parent conversion')
            });
            const conversion = lowering.directParentConversions[0];
            const type = lowering.declarations[0].type;
            assert.equal(type.tag, 'pi');
            if (type.tag !== 'pi') return;
            assert.deepEqual(type.binder.mode, implicitMode);
            assert.equal(type.body.tag, 'pi');
            if (type.body.tag !== 'pi') return;
            assert.deepEqual(type.body.binder.mode, explicitMode);
            assert.equal(type.body.body.tag, 'pi');
            if (type.body.body.tag !== 'pi') return;
            assert.deepEqual(type.body.body.binder.mode, explicitMode);
            assert.equal(type.body.body.body.tag, 'call');
            if (type.body.body.body.tag !== 'call') return;
            assert.deepEqual(
                type.body.body.body.arguments.map(argument => argument.value),
                [bound(2), bound(1)]
            );

            const A0 = symbol('binary_A0');
            const B0 = symbol('binary_B0');
            const evidence = symbol('binary_evidence');
            const applied = applyCoreLfClassParentConversion({
                conversion,
                parameters: [{
                    parameter: childSchema.structure.parameters[1],
                    value: global(B0)
                }, {
                    parameter: childSchema.structure.parameters[0],
                    value: global(A0)
                }],
                evidence: global(evidence)
            });
            assert.deepEqual(applied, call(global(conversion.symbol), [
                implicit(global(A0)),
                explicit(global(B0)),
                explicit(global(evidence))
            ]));

            const compiled = compileFixture([
                codeDeclaration(),
                ...parentExpansion.declarations,
                ...childExpansion.declarations,
                ...lowering.declarations
            ], [
                ...parentExpansion.runtimeRules,
                ...childExpansion.runtimeRules
            ]);
            assert.equal(
                compiled.declarations.declaration(conversion.symbol)?.status,
                'installed-transparent'
            );
        }
    );

    it('preserves copied inputs and applies a copied handle by name', () => {
        const fixture = algebraicFixture();
        const layout = structuredClone(fixture.monoid.layout);
        const directParents = structuredClone([{
            layout: fixture.mulOne.layout,
            conversionName: 'copy_to_mul_one'
        }, {
            layout: fixture.semigroup.layout,
            conversionName: 'copy_to_semigroup'
        }]);
        const beforeLayout = structuredClone(layout);
        const beforeParents = structuredClone(directParents);
        const lowering = lowerCoreLfClassInheritance({
            layout,
            order: fixture.nextOrder,
            directParents,
            provenance: source('copied lowering inputs')
        });
        assert.deepEqual(layout, beforeLayout);
        assert.deepEqual(directParents, beforeParents);
        assert.equal(Object.isFrozen(layout), false);
        assert.equal(Object.isFrozen(directParents), false);

        const conversion = structuredClone(conversionTo(
            lowering,
            'SemigroupClass'
        ));
        const A0 = symbol('copy_A0');
        const evidence = symbol('copy_monoid');
        const application = applyCoreLfClassParentConversion({
            conversion,
            parameters: [{
                parameter: structuredClone(
                    fixture.monoid.schema.structure.parameters[0]
                ),
                value: global(A0)
            }],
            evidence: global(evidence)
        });
        assert.deepEqual(application, call(global(conversion.symbol), [
            implicit(global(A0)),
            explicit(global(evidence))
        ]));
        assertDeepFrozen(application);
        assert.doesNotThrow(() => JSON.parse(JSON.stringify(lowering)));
    });

    it('checks five direct edges and computes one canonical diamond', () => {
        const fixture = algebraicFixture();
        const A0 = symbol('A0');
        const monoidEvidence = symbol('monoid_evidence');
        const leftRoute = symbol('mul_via_semigroup');
        const rightRoute = symbol('mul_via_mul_one');
        const expectedRoute = symbol('mul_expected');

        const monoidToSemigroup = conversionTo(
            fixture.monoidLowering,
            'SemigroupClass'
        );
        const monoidToMulOne = conversionTo(
            fixture.monoidLowering,
            'MulOneClass'
        );
        const semigroupToMul = conversionTo(
            fixture.semigroupLowering,
            'MulClass'
        );
        const mulOneToMul = conversionTo(
            fixture.mulOneLowering,
            'MulClass'
        );
        const semigroupEvidence = applyCoreLfClassParentConversion({
            conversion: monoidToSemigroup,
            parameters: [{
                parameter: fixture.monoid.schema.structure.parameters[0],
                value: global(A0)
            }],
            evidence: global(monoidEvidence)
        });
        const mulOneEvidence = applyCoreLfClassParentConversion({
            conversion: monoidToMulOne,
            parameters: [{
                parameter: fixture.monoid.schema.structure.parameters[0],
                value: global(A0)
            }],
            evidence: global(monoidEvidence)
        });
        const left = applyCoreLfClassParentConversion({
            conversion: semigroupToMul,
            parameters: [{
                parameter: fixture.semigroup.schema.structure.parameters[0],
                value: global(A0)
            }],
            evidence: semigroupEvidence
        });
        const right = applyCoreLfClassParentConversion({
            conversion: mulOneToMul,
            parameters: [{
                parameter: fixture.mulOne.schema.structure.parameters[0],
                value: global(A0)
            }],
            evidence: mulOneEvidence
        });
        const expected = call(
            global(fixture.mul.schema.structure.constructor),
            [
                implicit(global(A0)),
                explicit(call(
                    global(method(
                        fixture.monoid.schema,
                        'mul'
                    ).projection.symbol),
                    [
                        implicit(global(A0)),
                        explicit(global(monoidEvidence))
                    ]
                ))
            ]
        );

        let order = fixture.nextOrder;
        const consumers = [
            constantDeclaration(order++, A0, global(code)),
            constantDeclaration(
                order++,
                monoidEvidence,
                classAt(fixture.monoid, global(A0))
            ),
            constantDeclaration(
                order++,
                leftRoute,
                classAt(fixture.mul, global(A0)),
                left
            ),
            constantDeclaration(
                order++,
                rightRoute,
                classAt(fixture.mul, global(A0)),
                right
            ),
            constantDeclaration(
                order,
                expectedRoute,
                classAt(fixture.mul, global(A0)),
                expected
            )
        ];
        const declarations = [
            codeDeclaration(),
            ...fixture.structures.flatMap(entry => entry.declarations),
            ...fixture.lowerings.flatMap(entry => entry.declarations),
            ...consumers
        ];
        const runtimeRules = fixture.structures.flatMap(
            entry => entry.runtimeRules
        );
        const compiled = compileFixture(declarations, runtimeRules);
        assert.equal(
            fixture.lowerings.flatMap(entry =>
                entry.directParentConversions
            ).length,
            5
        );
        fixture.lowerings.flatMap(entry => entry.declarations).forEach(
            declaration => assert.equal(
                compiled.declarations.declaration(declaration.symbol)?.status,
                'installed-transparent'
            )
        );
        const runtime = compiled.latestRuntime?.runtime;
        assert.notEqual(runtime, undefined);
        if (runtime === undefined) return;
        const body = (value: CoreLfQualifiedSymbol) => {
            const term = compiled.declarations.declaration(value)?.body;
            assert.notEqual(term, undefined);
            return term!;
        };
        const normalize = (value: CoreLfQualifiedSymbol) =>
            coreLfCombinedNormalize(
                compiled.declarations.environment,
                body(value),
                100,
                undefined,
                runtime
            );
        const normalizedLeft = normalize(leftRoute);
        const normalizedRight = normalize(rightRoute);
        const normalizedExpected = normalize(expectedRoute);
        assert.equal(normalizedLeft.status, 'normal');
        assert.equal(normalizedRight.status, 'normal');
        assert.equal(normalizedExpected.status, 'normal');
        assert.equal(
            kernelExpressionEquals(
                normalizedLeft.expression,
                normalizedRight.expression
            ),
            true
        );
        assert.equal(
            kernelExpressionEquals(
                normalizedLeft.expression,
                normalizedExpected.expression
            ),
            true
        );
        assert.equal(
            normalizedLeft.trace.some(entry =>
                entry.reduction.kind === 'runtime'
            ),
            true
        );
        assert.equal(
            normalizedRight.trace.some(entry =>
                entry.reduction.kind === 'runtime'
            ),
            true
        );
    });

    it('fails closed on layouts, parent mappings, symbols, and slots', () => {
        const fixture = algebraicFixture();
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: {} as CoreLfClassInheritanceLayout,
                order: fixture.nextOrder,
                directParents: [],
                provenance: source('invalid layout')
            }),
            'LAYOUT_MISMATCH',
            'input.layout'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.semigroup.layout,
                order: -1,
                directParents: [],
                provenance: source('invalid order')
            }),
            'INVALID_INHERITANCE_LOWERING',
            'input.order'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.semigroup.layout,
                order: fixture.nextOrder,
                directParents: [],
                provenance: source('missing parent')
            }),
            'MISSING_PARENT_CONVERSION',
            'input.directParents'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.semigroup.layout,
                order: fixture.nextOrder,
                directParents: [{
                    layout: fixture.one.layout,
                    conversionName: 'wrong_parent'
                }],
                provenance: source('foreign parent')
            }),
            'PARENT_LAYOUT_MISMATCH',
            'input.directParents[0].layout'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.semigroup.layout,
                order: fixture.nextOrder,
                directParents: [{
                    layout: fixture.mul.layout,
                    conversionName: 'first'
                }, {
                    layout: fixture.mul.layout,
                    conversionName: 'second'
                }],
                provenance: source('duplicate parent')
            }),
            'DUPLICATE_PARENT_CONVERSION',
            'input.directParents[1].layout'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.semigroup.layout,
                order: fixture.nextOrder,
                directParents: [{
                    layout: fixture.mul.layout,
                    conversionName: 'not-valid'
                }],
                provenance: source('invalid name')
            }),
            'INVALID_PARENT_CONVERSION',
            'input.directParents[0]'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.mulOne.layout,
                order: fixture.nextOrder,
                directParents: [{
                    layout: fixture.mul.layout,
                    conversionName: 'same_conversion'
                }, {
                    layout: fixture.one.layout,
                    conversionName: 'same_conversion'
                }],
                provenance: source('duplicate conversion symbol')
            }),
            'DUPLICATE_SYMBOL',
            'input.directParents[1].conversionName'
        );
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: fixture.semigroup.layout,
                order: fixture.nextOrder,
                directParents: [{
                    layout: fixture.mul.layout,
                    conversionName:
                        fixture.semigroup.schema.structure.projections[0]
                            .symbol.name
                }],
                provenance: source('child symbol collision')
            }),
            'DUPLICATE_SYMBOL',
            'input.directParents[0].conversionName'
        );

        const copied = structuredClone(fixture.semigroup.layout);
        const local = copied.slots[0].localIdentity;
        const unmapped: CoreLfClassInheritanceLayout = {
            ...copied,
            slots: copied.slots.map((entry, index) => index === 0
                ? {
                    ...entry,
                    canonicalIdentity: local,
                    identities: [local]
                }
                : entry),
            qualifiedMethods: copied.qualifiedMethods.filter(alias =>
                alias.declaringClass.name === 'SemigroupClass'
            ),
            unqualifiedMethods: copied.unqualifiedMethods.map(entry =>
                entry.binderName === 'mul'
                    ? {
                        ...entry,
                        canonicalIdentity: local,
                        selectedDeclaringClass:
                            fixture.semigroup.schema.classId
                    }
                    : entry
            )
        };
        throwsLowering(
            () => lowerCoreLfClassInheritance({
                layout: unmapped,
                order: fixture.nextOrder,
                directParents: [{
                    layout: fixture.mul.layout,
                    conversionName: 'unmapped_to_mul'
                }],
                provenance: source('unmapped parent identity')
            }),
            'UNMAPPED_PARENT_FIELD',
            'input.directParents[0].layout.slots[0]'
        );
    });

    it('rejects incomplete, duplicate, foreign, and malformed applications',
        () => {
            const fixture = algebraicFixture();
            const conversion = conversionTo(
                fixture.monoidLowering,
                'SemigroupClass'
            );
            const parameter = fixture.monoid.schema.structure.parameters[0];
            const A0 = global(symbol('application_A0'));
            const evidence = global(symbol('application_monoid'));

            throwsLowering(
                () => applyCoreLfClassParentConversion({
                    conversion,
                    parameters: [],
                    evidence
                }),
                'MISSING_ARGUMENT',
                'input.parameters'
            );
            throwsLowering(
                () => applyCoreLfClassParentConversion({
                    conversion,
                    parameters: [{ parameter, value: A0 }, {
                        parameter,
                        value: A0
                    }],
                    evidence
                }),
                'DUPLICATE_ARGUMENT',
                'input.parameters[1].parameter'
            );
            throwsLowering(
                () => applyCoreLfClassParentConversion({
                    conversion,
                    parameters: [{
                        parameter:
                            fixture.semigroup.schema.structure.parameters[0],
                        value: A0
                    }],
                    evidence
                }),
                'FOREIGN_ARGUMENT',
                'input.parameters[0].parameter'
            );
            throwsLowering(
                () => applyCoreLfClassParentConversion({
                    conversion,
                    parameters: [{ parameter, value: A0 }],
                    evidence: {
                        tag: 'capture',
                        name: 'rule_only'
                    }
                }),
                'INVALID_APPLICATION',
                'input.evidence'
            );
            throwsLowering(
                () => applyCoreLfClassParentConversion({
                    conversion: {} as CoreLfClassParentConversionHandle,
                    parameters: [],
                    evidence
                }),
                'INVALID_APPLICATION',
                'input.conversion'
            );
        }
    );

    it('leaves explicit sharing compatibility to the ordinary LF checker',
        () => {
            const compatible = sharedFieldFixture('code');
            const compiled = compileFixture(
                compatible.declarations,
                compatible.runtimeRules
            );
            assert.deepEqual(
                compatible.lowering.directParentConversions.map(entry =>
                    compiled.declarations.declaration(entry.symbol)?.status
                ),
                ['installed-transparent', 'installed-transparent']
            );

            const incompatible = sharedFieldFixture('decoded');
            assert.throws(
                () => compileFixture(
                    incompatible.declarations,
                    incompatible.runtimeRules
                ),
                error =>
                    error instanceof CoreLfDeclarationCompilerError &&
                    error.code === 'DECLARATION_CHECK_FAILED'
            );
        }
    );
});
