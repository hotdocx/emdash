import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_INSTANCE_SCOPE_PROFILE,
    CORE_LF_INSTANCE_SYNTHESIS_PROFILE,
    CoreLfClassInheritanceLayout,
    CoreLfClassInheritanceLoweringExpansion,
    CoreLfClassMethodIdentity,
    CoreLfClassSchema,
    CoreLfModuleSpec,
    CoreLfInstanceProviderDeclaration,
    CoreLfInstanceSynthesisError,
    CoreLfInstanceSynthesisErrorCode,
    CoreLfInstanceScopeError,
    CoreLfInstanceScopeErrorCode,
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
    coreLfClassParameterTerm,
    coreLfTransferAbsentBody,
    createCoreLfChecker,
    createCoreLfInstanceRegistrySnapshot,
    createCoreLfInstanceScopeSnapshot,
    createCoreLfMixedDeclarationLinkage,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay,
    declareCoreLfClassSchema,
    declareCoreLfGlobalInstanceProvider,
    declareCoreLfLocalInstanceProvider,
    declareCoreLfSuperclassInstanceProvider,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    lowerCoreLfClassInheritance,
    planCoreLfClassInheritance,
    planCoreLfMixedPhases,
    provenance,
    serializeCoreLfInstanceRegistrySnapshot,
    serializeCoreLfInstanceScopeSnapshot,
    serializeCoreLfInstanceSynthesisReport,
    synthesizeCoreLfInstance
} from '../src/v3_2';

const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

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

const implicit = (value: CoreLfTransferExpression) => ({
    plicity: 'implicit' as const,
    value
});

const assertDeepFrozen = (
    value: unknown,
    seen = new Set<object>()
): void => {
    if (value === null || typeof value !== 'object' || seen.has(value)) return;
    seen.add(value);
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(entry =>
        assertDeepFrozen(entry, seen)
    );
};

const capture = (
    thunk: () => unknown,
    code: CoreLfInstanceScopeErrorCode
): CoreLfInstanceScopeError => {
    let captured: CoreLfInstanceScopeError | undefined;
    assert.throws(thunk, error => {
        if (
            error instanceof CoreLfInstanceScopeError &&
            error.code === code
        ) {
            captured = error;
            return true;
        }
        return false;
    });
    return captured!;
};

const captureSynthesis = (
    thunk: () => unknown,
    code: CoreLfInstanceSynthesisErrorCode
): CoreLfInstanceSynthesisError => {
    let captured: CoreLfInstanceSynthesisError | undefined;
    assert.throws(thunk, error => {
        if (
            error instanceof CoreLfInstanceSynthesisError &&
            error.code === code
        ) {
            captured = error;
            return true;
        }
        return false;
    });
    return captured!;
};

interface ClassEntry {
    readonly expansion: CoreLfStructureDeclarationExpansion;
    readonly schema: CoreLfClassSchema;
    readonly layout: CoreLfClassInheritanceLayout;
}

interface AlgebraicFixture {
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly code: CoreLfQualifiedSymbol;
    readonly module: CoreLfModuleSpec;
    readonly compiled: ReturnType<typeof compileCoreLfMixedPhases>;
    readonly classes: {
        readonly mul: ClassEntry;
        readonly one: ClassEntry;
        readonly semigroup: ClassEntry;
        readonly mulOne: ClassEntry;
        readonly monoid: ClassEntry;
    };
    readonly lowerings: readonly CoreLfClassInheritanceLoweringExpansion[];
    readonly instanceSymbols: {
        readonly primary: CoreLfQualifiedSymbol;
        readonly secondary: CoreLfQualifiedSymbol;
        readonly named: CoreLfQualifiedSymbol;
    };
    readonly recursiveSymbols: {
        readonly cycle: CoreLfQualifiedSymbol;
        readonly underconstrained: CoreLfQualifiedSymbol;
    };
}

const buildAlgebraicFixture = (
    moduleId: string,
    shaDigit: string
): AlgebraicFixture => {
    const authorityPath = `tests/fixtures/${moduleId}.lp`;
    const symbol = (name: string): CoreLfQualifiedSymbol => ({
        moduleId,
        name
    });
    const source = (sourceFragment: string) => ({
        authorityPath,
        sourceFragment
    });
    const code = symbol('Code');
    const codeDeclaration: CoreLfTransferDeclaration = {
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
    };
    const available: readonly CoreLfStructureAvailableGlobalInput[] = [{
        symbol: code,
        type: { tag: 'type' },
        availability: 'earlier-fragment',
        order: 0
    }];
    const scope = new CoreLfStructureMacroScope(moduleId, available);
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
            provenance: source(`instance-scope structure ${name}`)
        });
        order = expansion.nextOrder;
        return expansion;
    };

    const schema = (
        expansion: CoreLfStructureDeclarationExpansion,
        parents: readonly CoreLfClassSchema[] = []
    ): CoreLfClassSchema => {
        const parameter = coreLfClassParameterTerm(
            expansion,
            expansion.handle.parameters[0]
        );
        const role = expansion.handle.carrier.name === 'OneClass'
            ? 'output' as const
            : expansion.handle.carrier.name === 'SemigroupClass'
                ? 'semi-output' as const
                : 'input' as const;
        return declareCoreLfClassSchema({
            expansion,
            parameterRoles: [{
                parameter: expansion.handle.parameters[0],
                role
            }],
            directParents: parents.map(parent => ({
                parent,
                arguments: [{
                    parameter: parent.structure.parameters[0],
                    value: parameter
                }]
            }))
        });
    };

    const method = (entry: CoreLfClassSchema, name: string) => {
        const found = entry.declaredMethods.find(candidate =>
            candidate.projection.binderName === name
        );
        assert.notEqual(found, undefined);
        return found!;
    };
    const slot = (layout: CoreLfClassInheritanceLayout, name: string) => {
        const found = layout.slots.find(candidate =>
            candidate.physicalField.binderName === name
        );
        assert.notEqual(found, undefined);
        return found!;
    };
    const binding = (
        entry: CoreLfClassSchema,
        name: string,
        inherited: readonly CoreLfClassMethodIdentity[]
    ) => ({ field: method(entry, name).projection, inherited });

    const mulExpansion = expand('MulClass', ['mul']);
    const mulSchema = schema(mulExpansion);
    const mul: ClassEntry = {
        expansion: mulExpansion,
        schema: mulSchema,
        layout: planCoreLfClassInheritance({
            schema: mulSchema,
            directParentLayouts: []
        })
    };
    const oneExpansion = expand('OneClass', ['one']);
    const oneSchema = schema(oneExpansion);
    const one: ClassEntry = {
        expansion: oneExpansion,
        schema: oneSchema,
        layout: planCoreLfClassInheritance({
            schema: oneSchema,
            directParentLayouts: []
        })
    };
    const semigroupExpansion = expand('SemigroupClass', ['mul', 'assoc']);
    const semigroupSchema = schema(semigroupExpansion, [mul.schema]);
    const semigroup: ClassEntry = {
        expansion: semigroupExpansion,
        schema: semigroupSchema,
        layout: planCoreLfClassInheritance({
            schema: semigroupSchema,
            directParentLayouts: [mul.layout],
            fieldBindings: [binding(
                semigroupSchema,
                'mul',
                [slot(mul.layout, 'mul').canonicalIdentity]
            )]
        })
    };
    const mulOneExpansion = expand(
        'MulOneClass',
        ['mul', 'one', 'one_mul', 'mul_one']
    );
    const mulOneSchema = schema(mulOneExpansion, [mul.schema, one.schema]);
    const mulOne: ClassEntry = {
        expansion: mulOneExpansion,
        schema: mulOneSchema,
        layout: planCoreLfClassInheritance({
            schema: mulOneSchema,
            directParentLayouts: [mul.layout, one.layout],
            fieldBindings: [
                binding(
                    mulOneSchema,
                    'mul',
                    [slot(mul.layout, 'mul').canonicalIdentity]
                ),
                binding(
                    mulOneSchema,
                    'one',
                    [slot(one.layout, 'one').canonicalIdentity]
                )
            ]
        })
    };
    const monoidExpansion = expand(
        'MonoidClass',
        ['mul', 'assoc', 'one', 'one_mul', 'mul_one']
    );
    const monoidSchema = schema(
        monoidExpansion,
        [semigroup.schema, mulOne.schema]
    );
    const monoid: ClassEntry = {
        expansion: monoidExpansion,
        schema: monoidSchema,
        layout: planCoreLfClassInheritance({
            schema: monoidSchema,
            directParentLayouts: [semigroup.layout, mulOne.layout],
            fieldBindings: [
                binding(
                    monoidSchema,
                    'mul',
                    [slot(mul.layout, 'mul').canonicalIdentity]
                ),
                binding(
                    monoidSchema,
                    'assoc',
                    [slot(semigroup.layout, 'assoc').canonicalIdentity]
                ),
                binding(
                    monoidSchema,
                    'one',
                    [slot(one.layout, 'one').canonicalIdentity]
                ),
                binding(
                    monoidSchema,
                    'one_mul',
                    [slot(mulOne.layout, 'one_mul').canonicalIdentity]
                ),
                binding(
                    monoidSchema,
                    'mul_one',
                    [slot(mulOne.layout, 'mul_one').canonicalIdentity]
                )
            ]
        })
    };

    const lower = (
        child: ClassEntry,
        parents: readonly {
            readonly entry: ClassEntry;
            readonly name: string;
        }[]
    ) => {
        const expansion = lowerCoreLfClassInheritance({
            layout: child.layout,
            order,
            directParents: parents.map(parent => ({
                layout: parent.entry.layout,
                conversionName: parent.name
            })),
            provenance: source(`instance-scope conversions ${child.schema.classId.name}`)
        });
        order = expansion.nextOrder;
        return expansion;
    };
    const mulLowering = lower(mul, []);
    const oneLowering = lower(one, []);
    const semigroupLowering = lower(semigroup, [{
        entry: mul,
        name: 'semigroup_to_mul'
    }]);
    const mulOneLowering = lower(mulOne, [{
        entry: mul,
        name: 'mul_one_to_mul'
    }, {
        entry: one,
        name: 'mul_one_to_one'
    }]);
    const monoidLowering = lower(monoid, [{
        entry: semigroup,
        name: 'monoid_to_semigroup'
    }, {
        entry: mulOne,
        name: 'monoid_to_mul_one'
    }]);
    const lowerings = [
        mulLowering,
        oneLowering,
        semigroupLowering,
        mulOneLowering,
        monoidLowering
    ];

    const instanceSymbols = {
        primary: symbol('primaryMonoid'),
        secondary: symbol('secondaryMonoid'),
        named: symbol('namedMonoid')
    };
    const monoidAt = (parameter: CoreLfTransferExpression) => call(
        global(monoid.schema.structure.carrier),
        [implicit(parameter)]
    );
    const instanceType: CoreLfTransferExpression = {
        tag: 'pi',
        binder: {
            hint: 'A',
            mode: implicitMode,
            type: global(code)
        },
        body: monoidAt(bound(0))
    };
    const instances = Object.values(instanceSymbols).map((entry, index) => ({
        order: order + index,
        symbol: entry,
        type: instanceType,
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'constant' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: source(`instance declaration ${entry.name}`)
    }));
    const recursiveSymbols = {
        cycle: symbol('cycleMonoid'),
        underconstrained: symbol('underconstrainedMonoid')
    };
    const cycleType: CoreLfTransferExpression = {
        tag: 'pi',
        binder: {
            hint: 'A',
            mode: implicitMode,
            type: global(code)
        },
        body: {
            tag: 'pi',
            binder: {
                hint: 'inst',
                mode: implicitMode,
                type: monoidAt(bound(0))
            },
            body: monoidAt(bound(1))
        }
    };
    const underconstrainedType: CoreLfTransferExpression = {
        tag: 'pi',
        binder: {
            hint: 'A',
            mode: implicitMode,
            type: global(code)
        },
        body: {
            tag: 'pi',
            binder: {
                hint: 'B',
                mode: implicitMode,
                type: global(code)
            },
            body: monoidAt(bound(1))
        }
    };
    const recursiveDeclarations = [{
        order: order + instances.length,
        symbol: recursiveSymbols.cycle,
        type: cycleType,
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'constant' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: source('recursive cycle instance declaration')
    }, {
        order: order + instances.length + 1,
        symbol: recursiveSymbols.underconstrained,
        type: underconstrainedType,
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'constant' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: source('underconstrained instance declaration')
    }];

    const structures = [mul, one, semigroup, mulOne, monoid];
    const declarations = [
        codeDeclaration,
        ...structures.flatMap(entry => entry.expansion.declarations),
        ...lowerings.flatMap(entry => entry.declarations),
        ...instances,
        ...recursiveDeclarations
    ];
    const runtimeRules = structures.flatMap(entry =>
        entry.expansion.runtimeRules
    );
    const module = createCoreLfModuleSpec({
        revision: 'instance-scope-fixture-1',
        moduleId,
        fragmentId: 'instance-scope-fixture',
        authorityPath,
        sourceSha256: `sha256:${shaDigit.repeat(64)}`,
        dependencies: [],
        externalSymbols: [],
        declarations,
        inductives: [],
        runtimeRules,
        proofRules: []
    });
    const policySources: {
        readonly sourceOrder: number;
        readonly entry: Omit<CoreLfTransferPolicyEntry, 'order'>;
    }[] = [
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
                evidence: 'checked instance-scope fixture declaration'
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
    ].sort((left, right) => left.sourceOrder - right.sourceOrder);
    const policy: CoreLfTransferPolicyOverlay =
        createCoreLfTransferPolicyOverlay(module, {
            revision: 'instance-scope-policy-1',
            moduleRevision: module.revision,
            entries: policySources.map(({ entry }, index) => ({
                order: index,
                ...entry
            }))
        });
    const plan = planCoreLfMixedPhases(module, policy);
    const linkage = createCoreLfMixedDeclarationLinkage(plan, {
        revision: 'instance-scope-linkage-1',
        moduleRevision: module.revision,
        entries: [...declarations]
            .sort((left, right) => left.order - right.order)
            .map((declaration, index) => ({
                order: index,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName: `instance_scope_${shaDigit}_${declaration.symbol.name}`,
                backendName: declaration.symbol.name
            }))
    });
    const compiled = compileCoreLfMixedPhases(plan, linkage);
    return {
        moduleId,
        authorityPath,
        code,
        module,
        compiled,
        classes: { mul, one, semigroup, mulOne, monoid },
        lowerings,
        instanceSymbols,
        recursiveSymbols
    };
};

const declareOrdinaryProviders = (
    fixture: AlgebraicFixture
) => {
    const scope = {
        moduleId: fixture.moduleId,
        name: 'algebra'
    };
    return {
        primary: declareCoreLfGlobalInstanceProvider({
            declarations: fixture.compiled.declarations,
            module: fixture.module,
            provider: fixture.instanceSymbols.primary,
            resultClass: fixture.classes.monoid.layout
        }),
        secondary: declareCoreLfGlobalInstanceProvider({
            declarations: fixture.compiled.declarations,
            module: fixture.module,
            provider: fixture.instanceSymbols.secondary,
            resultClass: fixture.classes.monoid.layout
        }),
        named: declareCoreLfGlobalInstanceProvider({
            declarations: fixture.compiled.declarations,
            module: fixture.module,
            provider: fixture.instanceSymbols.named,
            resultClass: fixture.classes.monoid.layout,
            priority: 2000,
            visibility: { kind: 'named', scope }
        }),
        scope
    };
};

const declareRecursiveProviders = (
    fixture: AlgebraicFixture
) => ({
    cycle: declareCoreLfGlobalInstanceProvider({
        declarations: fixture.compiled.declarations,
        module: fixture.module,
        provider: fixture.recursiveSymbols.cycle,
        resultClass: fixture.classes.monoid.layout,
        instancePremises: [{
            binderOrdinal: 1,
            classLayout: fixture.classes.monoid.layout
        }]
    }),
    underconstrained: declareCoreLfGlobalInstanceProvider({
        declarations: fixture.compiled.declarations,
        module: fixture.module,
        provider: fixture.recursiveSymbols.underconstrained,
        resultClass: fixture.classes.monoid.layout
    })
});

const classById = (
    fixture: AlgebraicFixture,
    classId: CoreLfQualifiedSymbol
): ClassEntry => {
    const found = Object.values(fixture.classes).find(entry =>
        entry.schema.classId.moduleId === classId.moduleId &&
        entry.schema.classId.name === classId.name
    );
    assert.notEqual(found, undefined);
    return found!;
};

const declareSuperclassProviders = (
    fixture: AlgebraicFixture
): readonly CoreLfInstanceProviderDeclaration[] => fixture.lowerings.flatMap(
    lowering => lowering.directParentConversions.map(conversion =>
        declareCoreLfSuperclassInstanceProvider({
            declarations: fixture.compiled.declarations,
            module: fixture.module,
            conversion,
            childClass: lowering.layout,
            parentClass: classById(
                fixture,
                conversion.parent.classId
            ).layout
        })
    )
);

const declareLocalProviders = (
    fixture: AlgebraicFixture
) => {
    const codeDeclaration = fixture.compiled.declarations.declaration(
        fixture.code
    );
    const monoidDeclaration = fixture.compiled.declarations.declaration(
        fixture.classes.monoid.schema.classId
    );
    assert.equal(codeDeclaration?.link.kind, 'free-declaration');
    assert.equal(monoidDeclaration?.link.kind, 'free-declaration');
    if (
        codeDeclaration?.link.kind !== 'free-declaration' ||
        monoidDeclaration?.link.kind !== 'free-declaration'
    ) {
        throw new Error('local provider fixture did not compile free heads');
    }
    const witness = provenance('derived', 'instance-scope local fixture');
    const checker = createCoreLfChecker(
        fixture.compiled.declarations.environment
    );
    const withA = checker.rootContext.extend({
        name: 'A',
        type: kernelFree(codeDeclaration.link.coreName, witness),
        mode: explicitMode,
        provenance: witness
    });
    const outerType = kernelCall(
        kernelFree(monoidDeclaration.link.coreName, witness),
        [{ plicity: 'implicit', value: kernelBound(0, witness) }],
        witness
    );
    const withOuter = withA.extend({
        name: 'outerMonoid',
        type: outerType,
        mode: explicitMode,
        provenance: witness
    });
    const innerType = kernelCall(
        kernelFree(monoidDeclaration.link.coreName, witness),
        [{ plicity: 'implicit', value: kernelBound(1, witness) }],
        witness
    );
    const context = withOuter.extend({
        name: 'innerMonoid',
        type: innerType,
        mode: explicitMode,
        provenance: witness
    });
    const localSource = (sourceFragment: string) => ({
        authorityPath: fixture.authorityPath,
        sourceFragment
    });
    const outer = declareCoreLfLocalInstanceProvider({
        declarations: fixture.compiled.declarations,
        context,
        module: fixture.module,
        providerId: {
            moduleId: fixture.moduleId,
            name: 'localOuterMonoid'
        },
        binderIndex: 1,
        frameId: 'section.outer',
        frameKind: 'section',
        resultClass: fixture.classes.monoid.layout,
        priority: 9000,
        provenance: localSource('section instance outerMonoid')
    });
    const inner = declareCoreLfLocalInstanceProvider({
        declarations: fixture.compiled.declarations,
        context,
        module: fixture.module,
        providerId: {
            moduleId: fixture.moduleId,
            name: 'localInnerMonoid'
        },
        binderIndex: 0,
        frameId: 'proof.inner',
        frameKind: 'local',
        resultClass: fixture.classes.monoid.layout,
        priority: 1,
        provenance: localSource('local instance innerMonoid')
    });
    return { context, outer, inner };
};

describe('v3.2 immutable instance providers and scopes', () => {
    const current = buildAlgebraicFixture(
        'fixture.instance_scope_current',
        'a'
    );
    const imported = buildAlgebraicFixture(
        'fixture.instance_scope_imported',
        'b'
    );
    const currentOrdinary = declareOrdinaryProviders(current);
    const importedOrdinary = declareOrdinaryProviders(imported);
    const currentLocals = declareLocalProviders(current);
    const currentRecursive = declareRecursiveProviders(current);
    const currentSuperclasses = declareSuperclassProviders(current);
    const currentRuntime = current.compiled.latestRuntime?.runtime;
    assert.notEqual(currentRuntime, undefined);
    if (currentRuntime === undefined) {
        throw new Error('synthesis fixture did not compile its runtime');
    }
    const synthesisWitness = provenance(
        'derived',
        'bounded recursive instance-synthesis fixture'
    );

    const classTarget = (
        entry: ClassEntry,
        parameterIndex = 2
    ) => {
        const declaration = current.compiled.declarations.declaration(
            entry.schema.classId
        );
        assert.equal(declaration?.link.kind, 'free-declaration');
        if (declaration?.link.kind !== 'free-declaration') {
            throw new Error('synthesis target class did not compile');
        }
        return kernelCall(
            kernelFree(declaration.link.coreName, synthesisWitness),
            [{
                plicity: 'implicit',
                value: kernelBound(parameterIndex, synthesisWitness)
            }],
            synthesisWitness
        );
    };

    const synthesisArtifacts = (
        providers: readonly CoreLfInstanceProviderDeclaration[],
        local: 'none' | 'outer' | 'inner' | 'both' = 'none'
    ) => {
        const registry = createCoreLfInstanceRegistrySnapshot({
            revision: 'recursive-synthesis-registry-1',
            providers
        });
        const localFrames = [
            ...local === 'outer' || local === 'both' ? [{
                frameId: 'section.outer',
                kind: 'section' as const,
                providers: [currentLocals.outer.providerId]
            }] : [],
            ...local === 'inner' || local === 'both' ? [{
                frameId: 'proof.inner',
                kind: 'local' as const,
                providers: [currentLocals.inner.providerId]
            }] : []
        ];
        const scope = createCoreLfInstanceScopeSnapshot({
            revision: 'recursive-synthesis-scope-1',
            registry,
            moduleId: current.moduleId,
            contextDepth: currentLocals.context.depth,
            localFrames
        });
        return { registry, scope, runtimeProgram: currentRuntime };
    };

    const synthesize = (
        entry: ClassEntry,
        providers: readonly CoreLfInstanceProviderDeclaration[],
        local: 'none' | 'outer' | 'inner' | 'both' = 'none',
        limits: Parameters<typeof synthesizeCoreLfInstance>[0]['limits'] =
            undefined
    ) => {
        const artifacts = synthesisArtifacts(providers, local);
        return synthesizeCoreLfInstance({
            declarations: current.compiled.declarations,
            context: currentLocals.context,
            targetClass: entry.layout,
            target: classTarget(entry),
            ...artifacts,
            limits
        });
    };

    describe('bounded recursive instance synthesis', () => {
        it('selects exact lexical evidence before lower scope ranks', () => {
            const outcome = synthesize(
                current.classes.monoid,
                [
                    currentLocals.outer,
                    currentLocals.inner,
                    currentOrdinary.primary
                ],
                'both'
            );
            assert.equal(outcome.status, 'solved');
            if (outcome.status !== 'solved') return;
            assert.deepEqual(
                outcome.selected,
                currentLocals.inner.providerId
            );
            assert.equal(outcome.resultSize, 1);
            assert.equal(
                kernelExpressionEquals(
                    outcome.term,
                    kernelBound(0, synthesisWitness)
                ),
                true
            );
            assert.equal(
                outcome.report.revision,
                CORE_LF_INSTANCE_SYNTHESIS_PROFILE.revision
            );
            assert.deepEqual(
                outcome.report.runtimeFingerprintMaterial,
                {
                    revision: currentRuntime.revision,
                    ruleIds: currentRuntime.ruleIds
                }
            );
            assert.equal(outcome.report.goals.length, 1);
            assert.deepEqual(
                outcome.report.goals[0].candidates.map(candidate => [
                    candidate.providerId.name,
                    candidate.outcome
                ]),
                [
                    ['localInnerMonoid', 'success'],
                    ['localOuterMonoid', 'skipped'],
                    ['primaryMonoid', 'skipped']
                ]
            );
            assertDeepFrozen(outcome);
        });

        it('tables recursive superclass goals and collapses the diamond', () => {
            const outcome = synthesize(
                current.classes.mul,
                [
                    currentLocals.inner,
                    ...currentSuperclasses
                ],
                'inner'
            );
            assert.equal(outcome.status, 'solved');
            if (outcome.status !== 'solved') return;
            assert.equal(outcome.resultSize, 3);
            const root = outcome.report.goals[0];
            assert.equal(root.outcome, 'solved');
            assert.equal(root.equivalentProviders?.length, 2);
            assert.deepEqual(
                [...root.equivalentProviders!]
                    .map(provider => provider.name)
                    .sort(),
                ['mul_one_to_mul', 'semigroup_to_mul']
            );
            assert.equal(
                outcome.report.goals.flatMap(goal =>
                    goal.candidates.flatMap(candidate => candidate.premises)
                ).some(premise => premise.disposition === 'table-hit'),
                true
            );
            assert.equal(
                root.candidates.filter(candidate =>
                    candidate.outcome === 'success' ||
                    candidate.outcome === 'equivalent-success'
                ).length,
                2
            );

            const outputRole = synthesize(
                current.classes.one,
                [currentLocals.inner, ...currentSuperclasses],
                'inner'
            );
            assert.equal(outputRole.status, 'solved');
            assert.equal(
                outputRole.report.goals[0].target.arguments[0].role,
                'output'
            );
        });

        it('uses priority intentionally and reports genuine ambiguity', () => {
            const ambiguous = synthesize(
                current.classes.monoid,
                [currentOrdinary.primary, currentOrdinary.secondary]
            );
            assert.equal(ambiguous.status, 'ambiguous');
            assert.deepEqual(
                ambiguous.report.goals[0].candidates.map(candidate =>
                    candidate.outcome
                ),
                ['ambiguous-success', 'ambiguous-success']
            );

            const preferred = declareCoreLfGlobalInstanceProvider({
                declarations: current.compiled.declarations,
                module: current.module,
                provider: current.instanceSymbols.primary,
                resultClass: current.classes.monoid.layout,
                priority: 2000
            });
            const fallback = declareCoreLfGlobalInstanceProvider({
                declarations: current.compiled.declarations,
                module: current.module,
                provider: current.instanceSymbols.secondary,
                resultClass: current.classes.monoid.layout,
                priority: 1000
            });
            const selected = synthesize(
                current.classes.monoid,
                [fallback, preferred]
            );
            assert.equal(selected.status, 'solved');
            if (selected.status !== 'solved') return;
            assert.deepEqual(selected.selected, preferred.providerId);
            assert.deepEqual(
                selected.report.goals[0].candidates.map(candidate => [
                    candidate.providerId.name,
                    candidate.outcome
                ]),
                [
                    ['primaryMonoid', 'success'],
                    ['secondaryMonoid', 'skipped']
                ]
            );
        });

        it('distinguishes finite missing, cycles, and stuck providers', () => {
            const empty = synthesize(current.classes.monoid, []);
            assert.equal(empty.status, 'missing');

            const cyclic = synthesize(
                current.classes.monoid,
                [currentRecursive.cycle]
            );
            assert.equal(cyclic.status, 'missing');
            assert.equal(
                cyclic.report.goals.flatMap(goal =>
                    goal.candidates.flatMap(candidate => candidate.premises)
                ).some(premise => premise.disposition === 'cycle'),
                true
            );

            const withBase = synthesize(
                current.classes.monoid,
                [currentRecursive.cycle, currentOrdinary.primary]
            );
            assert.equal(withBase.status, 'solved');

            const stuck = synthesize(
                current.classes.monoid,
                [currentRecursive.underconstrained]
            );
            assert.equal(stuck.status, 'stuck');
            assert.equal(
                stuck.report.goals[0].candidates[0].reason,
                'ordinary-parameter-not-goal-determined'
            );
        });

        it('propagates nested ambiguity and every independent search bound', () => {
            const toSemigroup = currentSuperclasses.find(provider =>
                provider.providerId.name === 'monoid_to_semigroup'
            )!;
            const providers = [
                currentOrdinary.primary,
                currentOrdinary.secondary,
                toSemigroup
            ];
            const nested = synthesize(current.classes.semigroup, providers);
            assert.equal(nested.status, 'ambiguous');
            assert.equal(
                nested.report.goals[0].candidates[0].reason,
                'instance-premise-ambiguous'
            );

            const recursive = [currentOrdinary.primary, toSemigroup];
            assert.equal(
                synthesize(
                    current.classes.semigroup,
                    recursive,
                    'none',
                    { maxDepth: 0 }
                ).status,
                'limit-exceeded'
            );
            assert.equal(
                synthesize(
                    current.classes.semigroup,
                    recursive,
                    'none',
                    { maxTableEntries: 1 }
                ).status,
                'limit-exceeded'
            );
            assert.equal(
                synthesize(
                    current.classes.semigroup,
                    recursive,
                    'none',
                    { maxResultSize: 1 }
                ).status,
                'limit-exceeded'
            );
            assert.equal(
                synthesize(
                    current.classes.monoid,
                    [currentOrdinary.primary],
                    'none',
                    { maxFuel: 0 }
                ).status,
                'limit-exceeded'
            );
            assert.equal(
                synthesize(
                    current.classes.mul,
                    [currentLocals.inner, ...currentSuperclasses],
                    'inner',
                    { comparisonStepLimit: 0 }
                ).status,
                'limit-exceeded'
            );
        });

        it('is canonical across replay and fails closed on invalid inputs', () => {
            const providers = [
                currentLocals.inner,
                ...currentSuperclasses
            ];
            const artifacts = synthesisArtifacts(providers, 'inner');
            const first = synthesizeCoreLfInstance({
                declarations: current.compiled.declarations,
                context: currentLocals.context,
                targetClass: current.classes.mul.layout,
                target: classTarget(current.classes.mul),
                ...artifacts
            });
            const registry = createCoreLfInstanceRegistrySnapshot(
                JSON.parse(JSON.stringify({
                    revision: artifacts.registry.registryRevision,
                    providers: [...artifacts.registry.providers].reverse()
                }))
            );
            const scope = createCoreLfInstanceScopeSnapshot({
                revision: artifacts.scope.scopeRevision,
                registry,
                moduleId: artifacts.scope.moduleId,
                contextDepth: artifacts.scope.contextDepth,
                localFrames: artifacts.scope.localFrames.map(frame => ({
                    frameId: frame.frameId,
                    kind: frame.kind,
                    providers: [...frame.providers].reverse()
                }))
            });
            const replay = synthesizeCoreLfInstance({
                declarations: current.compiled.declarations,
                context: currentLocals.context,
                runtimeProgram: currentRuntime,
                targetClass: current.classes.mul.layout,
                target: classTarget(current.classes.mul),
                registry,
                scope
            });
            assert.equal(
                serializeCoreLfInstanceSynthesisReport(first.report),
                serializeCoreLfInstanceSynthesisReport(replay.report)
            );
            assertDeepFrozen(first);

            captureSynthesis(
                () => synthesizeCoreLfInstance(null as never),
                'INVALID_INPUT'
            );
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: createCoreLfChecker(
                        imported.compiled.declarations.environment
                    ).rootContext,
                    targetClass: current.classes.mul.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts
                }),
                'INVALID_CONTEXT'
            );
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: currentLocals.context,
                    targetClass: current.classes.one.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts
                }),
                'INVALID_CLASS_HEAD'
            );
            const metaSession = createCoreLfChecker(
                current.compiled.declarations.environment,
                undefined,
                currentRuntime
            ).lfSession;
            const targetWithMeta = classTarget(current.classes.mul);
            assert.equal(targetWithMeta.tag, 'call');
            if (targetWithMeta.tag !== 'call') return;
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: currentLocals.context,
                    targetClass: current.classes.mul.layout,
                    target: kernelCall(
                        targetWithMeta.callee,
                        [{
                            plicity: 'implicit',
                            value: metaSession.freshMeta(
                                currentLocals.context,
                                currentLocals.context.lookupIndex(2)!.type,
                                synthesisWitness
                            )
                        }],
                        synthesisWitness
                    ),
                    ...artifacts
                }),
                'INVALID_TARGET'
            );
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: currentLocals.context,
                    targetClass: current.classes.mul.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts,
                    limits: { maxFuel: -1 }
                }),
                'INVALID_LIMITS'
            );
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: currentLocals.context,
                    targetClass: current.classes.mul.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts,
                    runtimeProgram: {
                        revision: 'malformed-runtime',
                        ruleIds: ['duplicate', 'duplicate'],
                        rewriteHead: currentRuntime.rewriteHead.bind(
                            currentRuntime
                        )
                    }
                }),
                'INVALID_INPUT'
            );
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: currentLocals.context,
                    targetClass: current.classes.mul.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts,
                    registry: {
                        ...artifacts.registry,
                        providers: artifacts.registry.providers.map(
                            (provider, index) => index === 0
                                ? {
                                    ...provider,
                                    revision: 'wrong-provider-profile' as never
                                }
                                : provider
                        )
                    }
                }),
                'INVALID_REGISTRY'
            );
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: currentLocals.context,
                    targetClass: current.classes.mul.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts,
                    scope: {
                        ...artifacts.scope,
                        candidates: artifacts.scope.candidates.map(
                            (candidate, index) => index === 0
                                ? { ...candidate, priority: 99 }
                                : candidate
                        )
                    }
                }),
                'INVALID_SCOPE'
            );

            const codeDeclaration =
                current.compiled.declarations.declaration(current.code)!;
            assert.equal(codeDeclaration.link.kind, 'free-declaration');
            if (codeDeclaration.link.kind !== 'free-declaration') return;
            const wrongContext = createCoreLfChecker(
                current.compiled.declarations.environment
            ).rootContext.extend({
                name: 'A',
                type: kernelFree(
                    codeDeclaration.link.coreName,
                    synthesisWitness
                ),
                mode: explicitMode,
                provenance: synthesisWitness
            }).extend({
                name: 'outerMonoid',
                type: classTarget(current.classes.monoid, 0),
                mode: explicitMode,
                provenance: synthesisWitness
            }).extend({
                name: 'notMonoid',
                type: kernelFree(
                    codeDeclaration.link.coreName,
                    synthesisWitness
                ),
                mode: explicitMode,
                provenance: synthesisWitness
            });
            captureSynthesis(
                () => synthesizeCoreLfInstance({
                    declarations: current.compiled.declarations,
                    context: wrongContext,
                    targetClass: current.classes.mul.layout,
                    target: classTarget(current.classes.mul),
                    ...artifacts
                }),
                'INVALID_PROVIDER'
            );
            captureSynthesis(
                () => serializeCoreLfInstanceSynthesisReport({
                    ...first.report,
                    invalid: () => undefined
                } as never),
                'NON_PORTABLE_DATA'
            );
        });
    });

    it('derives exact checked global and local provider metadata', () => {
        const globalProvider = currentOrdinary.primary;
        assert.equal(
            globalProvider.revision,
            CORE_LF_INSTANCE_SCOPE_PROFILE.providerRevision
        );
        assert.deepEqual(
            globalProvider.telescope.map(binder => [
                binder.ordinal,
                binder.kind,
                binder.binderName,
                binder.mode.plicity
            ]),
            [[0, 'ordinary', 'A', 'implicit']]
        );
        assert.deepEqual(globalProvider.result.class, {
            classId: current.classes.monoid.schema.classId,
            parameterCount: 1
        });
        assert.deepEqual(
            globalProvider.result.arguments.map(argument => argument.role),
            ['input']
        );
        assert.equal(globalProvider.source.kind, 'global-declaration');
        assert.equal(globalProvider.term.tag, 'reference');

        assert.equal(currentLocals.outer.ambientDepth, 3);
        assert.equal(currentLocals.outer.term.tag, 'bound');
        assert.equal(
            currentLocals.outer.term.tag === 'bound'
                ? currentLocals.outer.term.index
                : -1,
            1
        );
        assert.equal(currentLocals.inner.term.tag, 'bound');
        assert.equal(
            currentLocals.inner.result.arguments[0].value.tag,
            'bound'
        );
        assert.equal(
            currentLocals.inner.result.arguments[0].value.tag === 'bound'
                ? currentLocals.inner.result.arguments[0].value.index
                : -1,
            2
        );
        assertDeepFrozen(globalProvider);
        assertDeepFrozen(currentLocals.outer);
        assertDeepFrozen(currentLocals.inner);
        assert.equal(Object.isFrozen(current.module), true);
    });

    it('registers exactly the five direct algebraic superclass providers', () => {
        const providers = declareSuperclassProviders(current);
        assert.equal(providers.length, 5);
        assert.deepEqual(
            providers.map(provider => provider.providerId.name).sort(),
            [
                'monoid_to_mul_one',
                'monoid_to_semigroup',
                'mul_one_to_mul',
                'mul_one_to_one',
                'semigroup_to_mul'
            ]
        );
        providers.forEach(provider => {
            assert.equal(provider.source.kind, 'superclass-conversion');
            assert.deepEqual(
                provider.telescope.map(binder => binder.kind),
                ['ordinary', 'instance-premise']
            );
            const premise = provider.telescope[1];
            assert.equal(premise.kind, 'instance-premise');
            if (
                provider.source.kind === 'superclass-conversion' &&
                premise.kind === 'instance-premise'
            ) {
                assert.deepEqual(premise.target.class, provider.source.child);
                assert.deepEqual(provider.result.class, provider.source.parent);
            }
            assertDeepFrozen(provider);
        });
        const roles = new Set(providers.flatMap(provider => [
            ...provider.result.arguments.map(argument => argument.role),
            ...provider.telescope.flatMap(binder =>
                binder.kind === 'instance-premise'
                    ? binder.target.arguments.map(argument => argument.role)
                    : []
            )
        ]));
        assert.deepEqual([...roles].sort(), [
            'input',
            'output',
            'semi-output'
        ]);
    });

    it('replays providers from JSON into a canonical immutable registry', () => {
        const providers = [
            currentOrdinary.named,
            currentLocals.inner,
            currentOrdinary.primary,
            ...declareSuperclassProviders(current)
        ];
        const before = structuredClone(providers);
        const first = createCoreLfInstanceRegistrySnapshot({
            revision: 'registry-current-1',
            providers
        });
        const second = createCoreLfInstanceRegistrySnapshot({
            revision: 'registry-current-1',
            providers: JSON.parse(JSON.stringify([...providers].reverse()))
        });
        assert.equal(
            serializeCoreLfInstanceRegistrySnapshot(first),
            serializeCoreLfInstanceRegistrySnapshot(second)
        );
        assert.deepEqual(providers, before);
        assert.equal(Object.isFrozen(providers), false);
        assertDeepFrozen(first);
    });

    it('freezes explicit lexical, named, imported, and global ranks', () => {
        const registryProviders = [
            currentLocals.outer,
            currentLocals.inner,
            currentOrdinary.primary,
            currentOrdinary.secondary,
            currentOrdinary.named,
            importedOrdinary.primary,
            importedOrdinary.named
        ];
        const registry = createCoreLfInstanceRegistrySnapshot({
            revision: 'scope-registry-1',
            providers: registryProviders
        });
        const importInput = {
            moduleId: imported.moduleId,
            moduleRevision: imported.module.revision,
            interfaceRevision: 'imported-instance-interface-1',
            interfaceSha256: `sha256:${'c'.repeat(64)}`,
            providers: [
                importedOrdinary.named.providerId,
                importedOrdinary.primary.providerId
            ]
        };
        const input = {
            revision: 'scope-current-1',
            registry,
            moduleId: current.moduleId,
            contextDepth: currentLocals.context.depth,
            localFrames: [{
                frameId: 'section.outer',
                kind: 'section' as const,
                providers: [currentLocals.outer.providerId]
            }, {
                frameId: 'proof.inner',
                kind: 'local' as const,
                providers: [currentLocals.inner.providerId]
            }],
            openedNamedScopes: [
                importedOrdinary.scope,
                currentOrdinary.scope
            ],
            imports: [importInput]
        };
        const scope = createCoreLfInstanceScopeSnapshot(input);
        assert.deepEqual(
            scope.candidates.map(entry => [
                entry.providerId.name,
                entry.tier,
                entry.rank,
                entry.priority,
                entry.activation.kind
            ]),
            [
                ['localInnerMonoid', 'local', 0, 1, 'local-frame'],
                ['localOuterMonoid', 'local', 1, 9000, 'local-frame'],
                ['namedMonoid', 'named', 2, 2000, 'named-scope'],
                ['namedMonoid', 'named', 2, 2000, 'named-scope'],
                ['primaryMonoid', 'ambient', 3, 1000, 'current-global'],
                ['secondaryMonoid', 'ambient', 3, 1000, 'current-global'],
                ['primaryMonoid', 'ambient', 3, 1000, 'imported-global']
            ]
        );
        assert.notEqual(
            scope.candidates[2].providerId.moduleId,
            scope.candidates[3].providerId.moduleId
        );
        assert.equal(scope.candidates[2].activation.kind, 'named-scope');
        assert.equal(scope.candidates[3].activation.kind, 'named-scope');
        if (
            scope.candidates[2].activation.kind === 'named-scope' &&
            scope.candidates[3].activation.kind === 'named-scope'
        ) {
            assert.deepEqual(
                [
                    scope.candidates[2].activation.availability.kind,
                    scope.candidates[3].activation.availability.kind
                ].sort(),
                ['current-module', 'imported-interface']
            );
        }
        const permutedRegistry = createCoreLfInstanceRegistrySnapshot({
            revision: 'scope-registry-1',
            providers: [...registryProviders].reverse()
        });
        const permuted = createCoreLfInstanceScopeSnapshot({
            ...input,
            registry: permutedRegistry,
            openedNamedScopes: [...input.openedNamedScopes].reverse(),
            imports: [{
                ...importInput,
                providers: [...importInput.providers].reverse()
            }]
        });
        assert.equal(
            serializeCoreLfInstanceScopeSnapshot(scope),
            serializeCoreLfInstanceScopeSnapshot(permuted)
        );
        const replayed = createCoreLfInstanceScopeSnapshot(
            JSON.parse(JSON.stringify(input))
        );
        assert.equal(
            serializeCoreLfInstanceScopeSnapshot(scope),
            serializeCoreLfInstanceScopeSnapshot(replayed)
        );
        const reversedFrames = createCoreLfInstanceScopeSnapshot({
            ...input,
            localFrames: [...input.localFrames].reverse()
        });
        assert.notEqual(
            serializeCoreLfInstanceScopeSnapshot(scope),
            serializeCoreLfInstanceScopeSnapshot(reversedFrames)
        );
        const text = serializeCoreLfInstanceScopeSnapshot(scope);
        assert.doesNotMatch(text, /selected|synthesis|searchResult/u);
        assertDeepFrozen(scope);
    });

    it('fails closed for every provider and registry diagnostic family', () => {
        const base = {
            declarations: current.compiled.declarations,
            module: current.module,
            provider: current.instanceSymbols.primary,
            resultClass: current.classes.monoid.layout
        };
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                priority: -1
            }),
            'INVALID_PROVIDER'
        );
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                provider: {
                    moduleId: current.moduleId,
                    name: 'missingProvider'
                }
            }),
            'UNAVAILABLE_PROVIDER'
        );

        const primaryDeclaration =
            current.compiled.declarations.declaration(
                current.instanceSymbols.primary
            );
        const codeDeclaration = current.compiled.declarations.declaration(
            current.code
        );
        assert.notEqual(primaryDeclaration, undefined);
        assert.equal(codeDeclaration?.link.kind, 'free-declaration');
        if (
            primaryDeclaration === undefined ||
            codeDeclaration?.link.kind !== 'free-declaration'
        ) return;
        const codeCoreName = codeDeclaration.link.coreName;
        const overrideDeclaration = (
            replacement: typeof primaryDeclaration
        ) => ({
            environment: current.compiled.declarations.environment,
            declaration(symbol: CoreLfQualifiedSymbol) {
                return symbol.moduleId === current.instanceSymbols.primary.moduleId &&
                    symbol.name === current.instanceSymbols.primary.name
                    ? replacement
                    : current.compiled.declarations.declaration(symbol);
            }
        });
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                declarations: overrideDeclaration({
                    ...primaryDeclaration,
                    status: 'excluded'
                })
            }),
            'UNSUPPORTED_PROVIDER'
        );
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                declarations: overrideDeclaration({
                    ...primaryDeclaration,
                    type: kernelFree(
                        codeCoreName,
                        provenance('derived', 'spoofed provider type')
                    )
                })
            }),
            'INVALID_PROVIDER_TYPE'
        );
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                resultClass: current.classes.mul.layout
            }),
            'INVALID_CLASS_HEAD'
        );
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                instancePremises: [{
                    binderOrdinal: 0,
                    classLayout: current.classes.monoid.layout
                }]
            }),
            'INVALID_PREMISE'
        );
        capture(
            () => declareCoreLfGlobalInstanceProvider({
                ...base,
                instancePremises: [{
                    binderOrdinal: 0,
                    classLayout: current.classes.monoid.layout
                }, {
                    binderOrdinal: 0,
                    classLayout: current.classes.monoid.layout
                }]
            }),
            'DUPLICATE_PREMISE'
        );

        const conversion = current.lowerings.flatMap(entry =>
            entry.directParentConversions
        )[0];
        const child = classById(current, conversion.child.classId);
        capture(
            () => declareCoreLfSuperclassInstanceProvider({
                declarations: current.compiled.declarations,
                module: current.module,
                conversion,
                childClass: child.layout,
                parentClass: current.classes.one.layout
            }),
            'INVALID_SUPERCLASS_PROVIDER'
        );

        capture(
            () => createCoreLfInstanceRegistrySnapshot({
                revision: 'not a revision',
                providers: []
            }),
            'INVALID_REGISTRY'
        );
        capture(
            () => createCoreLfInstanceRegistrySnapshot({
                revision: 'duplicate-registry-1',
                providers: [
                    currentOrdinary.primary,
                    currentOrdinary.primary
                ]
            }),
            'DUPLICATE_PROVIDER'
        );
        const nonportable = JSON.parse(JSON.stringify(
            currentOrdinary.primary
        ));
        nonportable.term = {
            tag: 'meta',
            provenance: {
                origin: 'derived',
                detail: 'forbidden portable meta'
            }
        };
        capture(
            () => createCoreLfInstanceRegistrySnapshot({
                revision: 'nonportable-registry-1',
                providers: [nonportable]
            }),
            'NON_PORTABLE_DATA'
        );
    });

    it('fails closed for every explicit scope diagnostic family', () => {
        const providers = [
            currentLocals.outer,
            currentLocals.inner,
            currentOrdinary.primary,
            currentOrdinary.named,
            importedOrdinary.primary,
            importedOrdinary.named
        ];
        const registry = createCoreLfInstanceRegistrySnapshot({
            revision: 'scope-errors-registry-1',
            providers
        });
        const validImport = {
            moduleId: imported.moduleId,
            moduleRevision: imported.module.revision,
            interfaceRevision: 'scope-errors-interface-1',
            interfaceSha256: `sha256:${'d'.repeat(64)}`,
            providers: [
                importedOrdinary.primary.providerId,
                importedOrdinary.named.providerId
            ]
        };
        const valid = {
            revision: 'scope-errors-1',
            registry,
            moduleId: current.moduleId,
            contextDepth: currentLocals.context.depth,
            localFrames: [{
                frameId: 'section.outer',
                kind: 'section' as const,
                providers: [currentLocals.outer.providerId]
            }],
            openedNamedScopes: [currentOrdinary.scope],
            imports: [validImport]
        };
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                moduleId: 'not a module id'
            }),
            'INVALID_SCOPE'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                localFrames: [{
                    frameId: 'section.outer',
                    kind: 'section',
                    providers: [{
                        moduleId: current.moduleId,
                        name: 'missingLocal'
                    }]
                }]
            }),
            'UNKNOWN_PROVIDER'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                localFrames: [{
                    frameId: 'bad frame',
                    kind: 'section',
                    providers: []
                }]
            }),
            'INVALID_LOCAL_FRAME'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                localFrames: [{
                    frameId: 'same.frame',
                    kind: 'section',
                    providers: []
                }, {
                    frameId: 'same.frame',
                    kind: 'local',
                    providers: []
                }]
            }),
            'DUPLICATE_LOCAL_FRAME'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                openedNamedScopes: [{
                    moduleId: current.moduleId,
                    name: 'unknownScope'
                }]
            }),
            'INVALID_NAMED_SCOPE'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                openedNamedScopes: [
                    currentOrdinary.scope,
                    currentOrdinary.scope
                ]
            }),
            'DUPLICATE_NAMED_SCOPE'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                imports: [{
                    ...validImport,
                    interfaceSha256: 'sha256:bad'
                }]
            }),
            'INVALID_IMPORT'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                imports: [validImport, validImport]
            }),
            'DUPLICATE_IMPORT'
        );
        capture(
            () => createCoreLfInstanceScopeSnapshot({
                ...valid,
                localFrames: [{
                    frameId: 'section.outer',
                    kind: 'section',
                    providers: [currentOrdinary.primary.providerId]
                }]
            }),
            'INELIGIBLE_PROVIDER'
        );
    });
});
