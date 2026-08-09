import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_CLASS_SCHEMA_PROFILE,
    CoreLfClassSchema,
    CoreLfClassSchemaError,
    CoreLfClassSchemaErrorCode,
    CoreLfQualifiedSymbol,
    CoreLfStructureAvailableGlobalInput,
    CoreLfStructureDeclarationExpansion,
    CoreLfStructureMacroScope,
    CoreLfTransferExpression,
    binderMode,
    coreLfClassParameterTerm,
    declareCoreLfClassSchema
} from '../src/v3_2';

const moduleId = 'fixture.class_schema';
const authorityPath = 'tests/fixtures/class_schema.lp';

const symbol = (name: string): CoreLfQualifiedSymbol => ({
    moduleId,
    name
});

const code = symbol('Code');
const el = symbol('El');

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

const explicitMode = binderMode('explicit', 'functorial');
const implicitMode = binderMode('implicit', 'functorial');

const availableFixture = ():
readonly CoreLfStructureAvailableGlobalInput[] => [{
    symbol: code,
    type: { tag: 'type' },
    availability: 'earlier-fragment',
    order: 0
}, {
    symbol: el,
    type: {
        tag: 'pi',
        binder: {
            hint: 'code',
            mode: explicitMode,
            type: global(code)
        },
        body: { tag: 'type' }
    },
    availability: 'earlier-fragment',
    order: 1
}];

const expandClass = (
    carrierName: string
): CoreLfStructureDeclarationExpansion => {
    const scope = new CoreLfStructureMacroScope(
        moduleId,
        availableFixture()
    );
    const resolvedCode = scope.resolve(code);
    const resolvedEl = scope.resolve(el);
    const lower = carrierName.replace(/Class$/u, '').toLowerCase();
    return scope.declareStructure({
        order: 2,
        carrierName,
        constructorName: `Mk${carrierName}`,
        fields(builder) {
            const A = builder.parameter({
                binderName: 'A',
                modes: {
                    carrier: implicitMode,
                    constructor: explicitMode,
                    projection: implicitMode
                },
                type: builder.global(resolvedCode)
            });
            builder.parameter({
                binderName: 'a',
                modes: {
                    carrier: explicitMode,
                    constructor: implicitMode,
                    projection: explicitMode
                },
                type: builder.apply(builder.global(resolvedEl), A)
            });
            builder.field({
                binderName: 'value',
                projectionName: `${lower}_value`,
                mode: explicitMode,
                type: builder.apply(builder.global(resolvedEl), A)
            });
            builder.field({
                binderName: 'witness',
                projectionName: `${lower}_witness`,
                mode: implicitMode,
                type: builder.global(resolvedCode)
            });
        },
        provenance: {
            authorityPath,
            sourceFragment: `class schema fixture ${carrierName}`
        }
    });
};

const schema = (name: string): CoreLfClassSchema =>
    declareCoreLfClassSchema({ expansion: expandClass(name) });

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const throwsSchema = (
    action: () => unknown,
    code: CoreLfClassSchemaErrorCode,
    path: string
): void => {
    assert.throws(action, error => {
        assert.equal(error instanceof CoreLfClassSchemaError, true);
        const schemaError = error as CoreLfClassSchemaError;
        assert.equal(schemaError.code, code);
        assert.equal(schemaError.path, path);
        return true;
    });
};

describe('outer LF class schema metadata', () => {
    it('derives a parent-free schema with stable declared metadata', () => {
        const expansion = expandClass('CapabilityClass');
        const copiedExpansion = structuredClone(expansion);
        const result = declareCoreLfClassSchema({
            expansion: copiedExpansion,
            parameterRoles: [{
                parameter: structuredClone(expansion.handle.parameters[1]),
                role: 'semi-output'
            }]
        });

        assert.equal(
            result.revision,
            CORE_LF_CLASS_SCHEMA_PROFILE.revision
        );
        assert.equal(result.classId.name, 'CapabilityClass');
        assert.equal(result.layoutStatus, 'parent-free');
        assert.deepEqual(
            result.parameters.map(parameter => ({
                id: [
                    parameter.identity.declaringClass.name,
                    parameter.identity.ordinal
                ],
                name: parameter.parameter.binderName,
                role: parameter.role,
                type: parameter.declaredType
            })),
            [{
                id: ['CapabilityClass', 0],
                name: 'A',
                role: 'input',
                type: global(code)
            }, {
                id: ['CapabilityClass', 1],
                name: 'a',
                role: 'semi-output',
                type: call(global(el), [explicit(bound(0))])
            }]
        );
        assert.deepEqual(
            result.declaredMethods.map(method => ({
                id: [
                    method.identity.declaringClass.name,
                    method.identity.ordinal
                ],
                name: method.projection.binderName,
                receiver: method.receiver,
                type: method.declaredType
            })),
            [{
                id: ['CapabilityClass', 0],
                name: 'value',
                receiver: {
                    authoringRole: 'class-evidence',
                    corePlicity: 'explicit'
                },
                type: call(global(el), [explicit(bound(1))])
            }, {
                id: ['CapabilityClass', 1],
                name: 'witness',
                receiver: {
                    authoringRole: 'class-evidence',
                    corePlicity: 'explicit'
                },
                type: global(code)
            }]
        );
        assert.notEqual(result.structure, expansion.handle);
        assert.equal(Object.isFrozen(copiedExpansion), false);
        assertDeepFrozen(result);

        const outputRole = declareCoreLfClassSchema({
            expansion,
            parameterRoles: [{
                parameter: expansion.handle.parameters[0],
                role: 'output'
            }]
        });
        assert.deepEqual(
            outputRole.parameters.map(parameter => parameter.role),
            ['output', 'input']
        );
    });

    it('references parameters in the complete class telescope', () => {
        const expansion = expandClass('ParameterReferenceClass');
        assert.deepEqual(
            coreLfClassParameterTerm(
                expansion,
                structuredClone(expansion.handle.parameters[0])
            ),
            bound(1)
        );
        assert.deepEqual(
            coreLfClassParameterTerm(
                expansion,
                expansion.handle.parameters[1]
            ),
            bound(0)
        );
        assertDeepFrozen(coreLfClassParameterTerm(
            expansion,
            expansion.handle.parameters[0]
        ));
    });

    it('records ordered parents with canonical arguments and plicity', () => {
        const first = schema('FirstParentClass');
        const second = schema('SecondParentClass');
        const childExpansion = expandClass('ChildClass');
        const A = structuredClone(coreLfClassParameterTerm(
            childExpansion,
            childExpansion.handle.parameters[0]
        ));
        const a = structuredClone(coreLfClassParameterTerm(
            childExpansion,
            childExpansion.handle.parameters[1]
        ));
        const inputs = [{
            parent: JSON.parse(JSON.stringify(second)) as CoreLfClassSchema,
            arguments: [{
                parameter: second.structure.parameters[1],
                value: a
            }, {
                parameter: second.structure.parameters[0],
                value: A
            }]
        }, {
            parent: first,
            arguments: [{
                parameter: first.structure.parameters[1],
                value: a
            }, {
                parameter: first.structure.parameters[0],
                value: A
            }]
        }];
        const before = structuredClone(inputs);
        const result = declareCoreLfClassSchema({
            expansion: childExpansion,
            directParents: inputs
        });

        assert.equal(result.layoutStatus, 'parents-unlowered');
        assert.deepEqual(
            result.directParents.map(parent => [
                parent.ordinal,
                parent.parent.classId.name,
                parent.parent.parameterCount
            ]),
            [
                [0, 'SecondParentClass', 2],
                [1, 'FirstParentClass', 2]
            ]
        );
        result.directParents.forEach(parent => {
            assert.deepEqual(parent.arguments, [implicit(bound(1)),
                explicit(bound(0))]);
            assert.deepEqual(parent.application, call(
                global(parent.parent.classId),
                [implicit(bound(1)), explicit(bound(0))]
            ));
        });
        assert.deepEqual(inputs, before);
        assert.equal(Object.isFrozen(inputs), false);
        assert.equal(Object.isFrozen(A), false);
        assert.doesNotThrow(() => JSON.parse(JSON.stringify(result)));
        assertDeepFrozen(result);
    });

    it('rejects malformed expansions and parameter role assignments', () => {
        const expansion = expandClass('RoleClass');
        const foreign = expandClass('ForeignRoleClass');

        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion: {
                    ...expansion,
                    runtimeRules: []
                }
            }),
            'INVALID_CLASS_SCHEMA',
            'input.expansion'
        );
        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion,
                parameterRoles: [{
                    parameter: expansion.handle.parameters[0],
                    role: 'unknown' as 'input'
                }]
            }),
            'INVALID_PARAMETER_ROLE',
            'input.parameterRoles[0].role'
        );
        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion,
                parameterRoles: [{
                    parameter: foreign.handle.parameters[0],
                    role: 'input'
                }]
            }),
            'FOREIGN_PARAMETER',
            'input.parameterRoles[0].parameter'
        );
        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion,
                parameterRoles: [{
                    parameter: expansion.handle.parameters[0],
                    role: 'input'
                }, {
                    parameter: expansion.handle.parameters[0],
                    role: 'output'
                }]
            }),
            'DUPLICATE_PARAMETER_ROLE',
            'input.parameterRoles[1].parameter'
        );
        throwsSchema(
            () => coreLfClassParameterTerm(
                expansion,
                foreign.handle.parameters[0]
            ),
            'FOREIGN_PARAMETER',
            'parameter'
        );
    });

    it('rejects invalid, self, and duplicate direct parents', () => {
        const childExpansion = expandClass('ParentValidationClass');
        const child = declareCoreLfClassSchema({
            expansion: childExpansion
        });
        const parent = schema('RepeatedParentClass');
        const args = parent.structure.parameters.map(
            (parameter, index) => ({
                parameter,
                value: bound(1 - index)
            })
        );

        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion: childExpansion,
                directParents: [{ parent: {} as CoreLfClassSchema, arguments: [] }]
            }),
            'INVALID_PARENT',
            'input.directParents[0].parent'
        );
        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion: childExpansion,
                directParents: [{ parent: child, arguments: args }]
            }),
            'INVALID_PARENT',
            'input.directParents[0].parent'
        );
        throwsSchema(
            () => declareCoreLfClassSchema({
                expansion: childExpansion,
                directParents: [{ parent, arguments: args }, {
                    parent,
                    arguments: args
                }]
            }),
            'DUPLICATE_PARENT',
            'input.directParents[1].parent'
        );
    });

    it('rejects incomplete, duplicate, foreign, and invalid parent arguments', () => {
        const childExpansion = expandClass('ParentArgumentsClass');
        const parent = schema('ArgumentParentClass');
        const foreign = schema('ForeignArgumentParentClass');
        const first = {
            parameter: parent.structure.parameters[0],
            value: bound(1)
        };
        const second = {
            parameter: parent.structure.parameters[1],
            value: bound(0)
        };
        const construct = (arguments_: readonly {
            readonly parameter: typeof first.parameter;
            readonly value: CoreLfTransferExpression;
        }[]) => declareCoreLfClassSchema({
            expansion: childExpansion,
            directParents: [{ parent, arguments: arguments_ }]
        });

        throwsSchema(
            () => construct([first]),
            'MISSING_PARENT_ARGUMENT',
            'input.directParents[0].arguments'
        );
        throwsSchema(
            () => construct([first, first, second]),
            'DUPLICATE_PARENT_ARGUMENT',
            'input.directParents[0].arguments[1].parameter'
        );
        throwsSchema(
            () => construct([{
                parameter: foreign.structure.parameters[0],
                value: bound(1)
            }, second]),
            'FOREIGN_PARENT_ARGUMENT',
            'input.directParents[0].arguments[0].parameter'
        );
        throwsSchema(
            () => construct([{
                ...first,
                value: bound(2)
            }, second]),
            'INVALID_PARENT_ARGUMENT',
            'input.directParents[0].arguments[0].value.index'
        );
        throwsSchema(
            () => construct([{
                ...first,
                value: { tag: 'capture', name: 'A' }
            }, second]),
            'INVALID_PARENT_ARGUMENT',
            'input.directParents[0].arguments[0].value'
        );
    });
});
