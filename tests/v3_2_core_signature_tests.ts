/**
 * Focused ELAB-2A3A tests for Core universes, generic calls, and owner types.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_OWNER_SCHEMAS,
    CORE_OWNER_TYPE_SCHEMAS,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreOwnerTypeCatalogInput,
    KernelCall,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    binderMode,
    checkLambdapiProbe,
    coreOwnerResultType,
    coreOwnerSignatureType,
    coreOwnerSlotType,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelPi,
    kernelShift,
    kernelSubstitute,
    kernelUniverse,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan,
    validateCoreOwnerTypeCatalog
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_core_signature.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');
const implicitFunctorial = binderMode('implicit', 'functorial');

const free = (name: string, line: number) =>
    kernelFree(name, because(line, `ELAB-2A3A free occurrence ${name}`));

const bound = (index: number, line: number) =>
    kernelBound(index, because(line, `ELAB-2A3A bound occurrence ${index}`));

const expectBoundIndex = (
    expression: KernelExpression,
    expected: number
) => {
    assert.equal(expression.tag, 'bound');
    assert.equal(
        expression.tag === 'bound' ? expression.index : undefined,
        expected
    );
};

const cloneCatalog = (): Record<
    string,
    CoreOwnerTypeCatalogInput[string]
> => ({ ...CORE_OWNER_TYPE_SCHEMAS });

const categoryUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'category-universe',
        [],
        because(line, 'ELAB-2A3A category universe')
    );

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => {
    const nodeProvenance = because(
        line,
        'ELAB-2A3A category object type'
    );
    return kernelApplication('decode', [{
        value: kernelApplication('object-classifier', [{
            value: category
        }], nodeProvenance)
    }], nodeProvenance);
};

const categoryPolymorphicIdentityType = (
    line: number
): KernelExpression => {
    const nodeProvenance = because(
        line,
        'ELAB-2A3A category-polymorphic identity type'
    );
    return kernelPi(
        kernelBinder(
            'A',
            categoryUniverse(line),
            implicitFunctorial,
            nodeProvenance
        ),
        kernelPi(
            kernelBinder(
                'x',
                objectType(bound(0, line), line),
                explicitFunctorial,
                nodeProvenance
            ),
            objectType(bound(1, line), line),
            nodeProvenance
        ),
        nodeProvenance
    );
};

describe('TypeScript v3.2 ELAB-2A3A Core signatures', () => {
    it('covers every owner with a scoped dependent Pi signature', () => {
        assert.deepEqual(
            Object.keys(CORE_OWNER_TYPE_SCHEMAS).sort(),
            Object.keys(CORE_OWNER_SCHEMAS).sort()
        );
        assert.doesNotThrow(() => validateCoreOwnerTypeCatalog());

        for (const owner of Object.keys(
            CORE_OWNER_SCHEMAS
        ) as (keyof typeof CORE_OWNER_SCHEMAS)[]) {
            assert.doesNotThrow(() =>
                kernelAssertScoped(
                    coreOwnerSignatureType(
                        owner,
                        because(10, `${owner} materialized signature`)
                    )
                )
            );
        }
    });

    it('rejects catalog drift, forward dependencies, and malformed owner arity', () => {
        const wrongPlicity = cloneCatalog();
        const functorObject =
            CORE_OWNER_TYPE_SCHEMAS['functor-object'];
        wrongPlicity['functor-object'] = {
            ...functorObject,
            slots: functorObject.slots.map((slot, index) =>
                index === 0
                    ? { ...slot, plicity: 'explicit' }
                    : slot
            )
        };
        assert.throws(
            () => validateCoreOwnerTypeCatalog(wrongPlicity),
            /typed slot 0 is explicit A, expected implicit A/
        );

        const forwardDependency = cloneCatalog();
        forwardDependency['object-classifier'] = {
            ...CORE_OWNER_TYPE_SCHEMAS['object-classifier'],
            slots: [{
                name: 'A',
                plicity: 'explicit',
                type: { tag: 'slot', name: 'A' }
            }]
        };
        assert.throws(
            () => validateCoreOwnerTypeCatalog(forwardDependency),
            /unavailable slot 'A'/
        );

        const malformedArity = cloneCatalog();
        malformedArity['groupoid-universe'] = {
            slots: [],
            result: {
                tag: 'owner-application',
                owner: 'category-universe',
                arguments: [{ tag: 'universe' }]
            }
        };
        assert.throws(
            () => validateCoreOwnerTypeCatalog(malformedArity),
            /category-universe to 1 arguments, expected 0/
        );

        const missing = cloneCatalog();
        delete missing.decode;
        assert.throws(
            () => validateCoreOwnerTypeCatalog(missing),
            /missing owner 'decode'/
        );

        const extra = cloneCatalog();
        extra['legacy-owner'] = {
            slots: [],
            result: { tag: 'universe' }
        };
        assert.throws(
            () => validateCoreOwnerTypeCatalog(extra),
            /unknown owner 'legacy-owner'/
        );
    });

    it('materializes exact representative active owner telescopes', () => {
        const nodeProvenance = because(20, 'materialized owner type');
        assert.equal(
            serializeKernelExpression(
                coreOwnerSignatureType(
                    'functor-object',
                    nodeProvenance
                )
            ),
            'Π [v0 : Cat], Π [v1 : Cat], ' +
            'Π (v2 : τ (Functor v0 v1)), ' +
            'Π (v3 : τ (Obj v0)), τ (Obj v1)'
        );
        assert.equal(
            serializeKernelExpression(
                coreOwnerSignatureType(
                    'functor-hom-capped',
                    nodeProvenance
                )
            ),
            'Π [v0 : Cat], Π [v1 : Cat], ' +
            'Π (v2 : τ (Functor v0 v1)), ' +
            'Π [v3 : τ (Obj v0)], Π [v4 : τ (Obj v0)], ' +
            'Π (v5 : τ (Hom v0 v3 v4)), ' +
            'τ (Hom v1 (@fapp0 v0 v1 v2 v3) ' +
            '(@fapp0 v0 v1 v2 v4))'
        );
        assert.equal(
            serializeKernelExpression(
                coreOwnerSignatureType(
                    'transfor-hom-full',
                    nodeProvenance
                )
            ),
            'Π [v0 : Cat], Π [v1 : Cat], ' +
            'Π [v2 : τ (Functor v0 v1)], ' +
            'Π [v3 : τ (Functor v0 v1)], ' +
            'Π [v4 : τ (Obj v0)], Π [v5 : τ (Obj v0)], ' +
            'Π (v6 : τ (@Transf v0 v1 v2 v3)), ' +
            'τ (Functor (Hom_cat v0 v4 v5) ' +
            '(Hom_cat v1 (@fapp0 v0 v1 v2 v4) ' +
            '(@fapp0 v0 v1 v3 v5)))'
        );
    });

    it('instantiates dependent slot and result types from earlier arguments', () => {
        const arguments_ = [
            free('signature_A', 30),
            free('signature_B', 30),
            free('signature_F', 30),
            free('signature_X', 30),
            free('signature_Y', 30)
        ];
        const nodeProvenance = because(30, 'signature instantiation');

        assert.equal(
            serializeKernelExpression(coreOwnerSlotType(
                'functor-hom-capped',
                5,
                arguments_,
                nodeProvenance
            )),
            'τ (Hom signature_A signature_X signature_Y)'
        );
        assert.equal(
            serializeKernelExpression(coreOwnerResultType(
                'functor-hom-capped',
                [...arguments_, free('signature_f', 30)],
                nodeProvenance
            )),
            'τ (Hom signature_B ' +
            '(@fapp0 signature_A signature_B signature_F signature_X) ' +
            '(@fapp0 signature_A signature_B signature_F signature_Y))'
        );
        assert.throws(
            () => coreOwnerSlotType(
                'functor-hom-capped',
                5,
                arguments_.slice(0, 4),
                nodeProvenance
            ),
            /requires exactly 5 earlier arguments/
        );
        assert.throws(
            () => coreOwnerResultType(
                'functor-hom-capped',
                arguments_,
                nodeProvenance
            ),
            /requires 6 arguments/
        );
    });

    it('traverses generic calls through scope, shift, and substitution', () => {
        const call = kernelCall(
            free('signature_poly', 40),
            [
                {
                    plicity: 'implicit',
                    value: bound(1, 40)
                },
                {
                    plicity: 'explicit',
                    value: bound(0, 40)
                }
            ],
            because(40, 'open generic call')
        );
        assert.doesNotThrow(() => kernelAssertScoped(call, 2));

        const shifted = kernelShift(call, 1);
        assert.equal(shifted.tag, 'call');
        if (shifted.tag !== 'call') {
            throw new Error('Expected shifted generic call');
        }
        expectBoundIndex(shifted.arguments[0].value, 2);
        expectBoundIndex(shifted.arguments[1].value, 1);

        const substituted = kernelSubstitute(
            call,
            0,
            free('signature_x', 41)
        );
        assert.equal(substituted.tag, 'call');
        if (substituted.tag !== 'call') {
            throw new Error('Expected substituted generic call');
        }
        assert.equal(
            serializeKernelExpression(
                kernelPi(
                    kernelBinder(
                        'T',
                        kernelUniverse(because(42, 'call scope universe')),
                        explicitFunctorial,
                        because(42, 'call scope binder')
                    ),
                    kernelPi(
                        kernelBinder(
                            'ignored',
                            kernelUniverse(
                                because(42, 'call substitution binder type')
                            ),
                            explicitFunctorial,
                            because(42, 'call substitution binder')
                        ),
                        substituted,
                        because(42, 'call substitution wrapper')
                    ),
                    because(42, 'call scope wrapper')
                )
            ),
            'Π (v0 : TYPE), Π (v1 : TYPE), ' +
            '@signature_poly v0 signature_x'
        );

        const explicitCall = kernelCall(
            free('signature_poly', 43),
            [{
                plicity: 'explicit',
                value: bound(1, 43)
            }, {
                plicity: 'explicit',
                value: bound(0, 43)
            }],
            because(43, 'wrong-plicity structural comparison')
        );
        assert.equal(kernelExpressionEquals(call, explicitCall), false);
        assert.throws(
            () => kernelCall(
                free('signature_poly', 44),
                [],
                because(44, 'empty generic call')
            ),
            /requires at least one argument/
        );
    });

    it('serializes nested and combined generic calls identically', () => {
        const nested = kernelCall(
            kernelCall(
                free('signature_poly', 50),
                [{
                    plicity: 'implicit',
                    value: free('signature_T', 50)
                }],
                because(50, 'inner generic call')
            ),
            [{
                plicity: 'explicit',
                value: free('signature_x', 50)
            }],
            because(50, 'outer generic call')
        );
        const combined = kernelCall(
            free('signature_poly', 51),
            [{
                plicity: 'implicit',
                value: free('signature_T', 51)
            }, {
                plicity: 'explicit',
                value: free('signature_x', 51)
            }],
            because(51, 'combined generic call')
        );

        assert.equal(
            serializeKernelExpression(nested),
            '@signature_poly signature_T signature_x'
        );
        assert.equal(
            serializeKernelExpression(combined),
            serializeKernelExpression(nested)
        );
    });

    it('validates free names and zonks metas in call heads and arguments', () => {
        const typeProvenance = because(60, 'call environment type');
        const environment = CoreDeclarationEnvironment.empty()
            .extend({
                name: 'signature_A',
                type: categoryUniverse(60),
                mode: explicitFunctorial,
                provenance: typeProvenance
            })
            .extend({
                name: 'signature_poly',
                type: categoryPolymorphicIdentityType(61),
                mode: explicitFunctorial,
                provenance: because(61, 'call environment function')
            });
        const session = new CoreElaborationSession(environment);
        const headMeta = session.freshMeta(
            session.rootContext,
            categoryPolymorphicIdentityType(62),
            because(62, 'generic call head meta')
        );
        const argumentMeta = session.freshMeta(
            session.rootContext,
            categoryUniverse(63),
            because(63, 'generic call argument meta')
        );
        session.solve(headMeta, free('signature_poly', 64));
        session.solve(argumentMeta, free('signature_A', 64));

        const zonked = session.zonk(kernelCall(
            headMeta,
            [{
                plicity: 'implicit',
                value: argumentMeta
            }],
            because(64, 'meta-bearing generic call')
        ));
        assert.equal(zonked.tag, 'call');
        if (zonked.tag !== 'call') {
            throw new Error('Expected zonked generic call');
        }
        assert.equal(zonked.callee.tag, 'reference');
        assert.equal(zonked.arguments[0].value.tag, 'reference');
        assert.doesNotThrow(() => session.rootContext.assertScoped(zonked));

        const undeclared = {
            ...zonked,
            callee: free('signature_missing', 65)
        } satisfies KernelCall;
        assert.throws(
            () => session.rootContext.assertScoped(undeclared),
            /undeclared free name 'signature_missing'/
        );
    });

    it(
        'checks every saturated owner signature against Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const declarations: {
                name: string;
                type: KernelExpression;
                span: ReturnType<typeof at>;
            }[] = [];
            const assertions: {
                label: string;
                term: KernelExpression;
                type: KernelExpression;
                span: ReturnType<typeof at>;
            }[] = [];
            let sourceLine = 70;

            for (const owner of Object.keys(
                CORE_OWNER_SCHEMAS
            ) as (keyof typeof CORE_OWNER_SCHEMAS)[]) {
                const ownerArguments: KernelExpression[] = [];
                const slots: readonly { readonly name: string }[] =
                    CORE_OWNER_SCHEMAS[owner].slots;
                slots.forEach((slot, index) => {
                    const name =
                        `signature_${owner.replace(/-/g, '_')}_` +
                        `${slot.name}_${index}`;
                    const nodeProvenance = because(
                        sourceLine,
                        `${owner} argument ${slot.name}`
                    );
                    declarations.push({
                        name,
                        type: coreOwnerSlotType(
                            owner,
                            index,
                            ownerArguments,
                            nodeProvenance
                        ),
                        span: at(sourceLine, 1, 60)
                    });
                    ownerArguments.push(free(name, sourceLine));
                    sourceLine++;
                });

                const nodeProvenance = because(
                    sourceLine,
                    `${owner} saturated application`
                );
                assertions.push({
                    label: `ELAB-2A3A owner signature ${owner}`,
                    term: kernelApplication(
                        owner,
                        ownerArguments.map(value => ({ value })),
                        nodeProvenance
                    ),
                    type: coreOwnerResultType(
                        owner,
                        ownerArguments,
                        nodeProvenance
                    ),
                    span: at(sourceLine, 1, 80)
                });
                sourceLine++;
            }

            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations,
                assertions
            };
            const serialized = serializeKernelProbe(probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected complete owner-signature acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
            assert.equal(
                assertions.length,
                Object.keys(CORE_OWNER_SCHEMAS).length
            );
        }
    );

    it(
        'emits a polymorphic generic call accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const type = kernelUniverse(
                because(70, 'polymorphic probe universe')
            );
            const term = kernelCall(
                free('signature_poly', 73),
                [{
                    plicity: 'implicit',
                    value: free('signature_A', 73)
                }, {
                    plicity: 'explicit',
                    value: free('signature_x', 73)
                }],
                because(73, 'polymorphic probe call')
            );
            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: [{
                    name: 'signature_A',
                    type: categoryUniverse(70),
                    span: at(70, 1, 20)
                }, {
                    name: 'signature_x',
                    type: objectType(free('signature_A', 71), 71),
                    span: at(71, 1, 24)
                }, {
                    name: 'signature_poly',
                    type: categoryPolymorphicIdentityType(72),
                    span: at(72, 1, 50)
                }],
                assertions: [{
                    label: 'ELAB-2A3A universe term',
                    term: categoryUniverse(73),
                    type,
                    span: at(73, 1, 20)
                }, {
                    label: 'ELAB-2A3A polymorphic generic call',
                    term,
                    type: objectType(free('signature_A', 73), 73),
                    span: at(73, 1, 42)
                }]
            };
            const serialized = serializeKernelProbe(probe);
            assert.match(
                serialized.source,
                /assert ⊢ @signature_poly signature_A signature_x/
            );
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected polymorphic call acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
