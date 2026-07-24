/**
 * Focused ELAB-2A1 tests for persistent Core declarations and local scopes.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreBindingInput,
    CoreContext,
    CoreContextError,
    CoreDeclarationEnvironment,
    KernelApplication,
    KernelExpression,
    KernelProbe,
    LAMBDAPI_V32_MODULE,
    binderMode,
    checkLambdapiProbe,
    kernelApplication,
    kernelAssertScoped,
    kernelBound,
    kernelExpressionEquals,
    kernelFree,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_core_context.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');
const implicitNatural = binderMode('implicit', 'natural');
const explicitObjectOnly = binderMode('explicit', 'object-only');

const categoryUniverse = (line = 1) => kernelApplication(
    'category-universe',
    [],
    because(line, 'ELAB-2A1 category universe')
);

const free = (name: string, line: number) =>
    kernelFree(name, because(line, `ELAB-2A1 free occurrence ${name}`));

const bound = (index: number, line: number) =>
    kernelBound(index, because(line, `ELAB-2A1 bound occurrence ${index}`));

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => {
    const nodeProvenance = because(line, 'ELAB-2A1 object type');
    return kernelApplication('decode', [{
        value: kernelApplication('object-classifier', [{
            value: category
        }], nodeProvenance)
    }], nodeProvenance);
};

const binding = (
    name: string,
    type: KernelExpression,
    line: number,
    mode = explicitFunctorial
): CoreBindingInput => ({
    name,
    type,
    mode,
    provenance: because(line, `ELAB-2A1 binding ${name}`)
});

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

const expectObjectCategoryIndex = (
    expression: KernelExpression,
    expected: number
) => {
    assert.equal(expression.tag, 'application');
    const decode = expression as KernelApplication;
    assert.equal(decode.owner, 'decode');
    const classifier = decode.arguments[0].value;
    assert.equal(classifier.tag, 'application');
    assert.equal(
        classifier.tag === 'application' ? classifier.owner : undefined,
        'object-classifier'
    );
    if (classifier.tag !== 'application') {
        throw new Error('Expected an object-classifier application');
    }
    expectBoundIndex(classifier.arguments[0].value, expected);
};

describe('TypeScript v3.2 ELAB-2A1 Core contexts', () => {
    it('keeps ordered declaration extension persistent and session-local', () => {
        const empty = CoreDeclarationEnvironment.empty();
        const withA = empty.extend(binding(
            'context_A',
            categoryUniverse(10),
            10
        ));
        const withAB = withA.extend(binding(
            'context_B',
            categoryUniverse(11),
            11,
            implicitNatural
        ));
        const otherSession = empty.extend(binding(
            'context_A',
            categoryUniverse(12),
            12,
            explicitObjectOnly
        ));

        assert.deepEqual(empty.declarations, []);
        assert.deepEqual(
            withA.declarations.map(declaration => declaration.name),
            ['context_A']
        );
        assert.deepEqual(
            withAB.declarations.map(declaration => declaration.name),
            ['context_A', 'context_B']
        );
        assert.equal(withA.lookup('context_B'), undefined);
        assert.deepEqual(
            withAB.lookup('context_B')?.mode,
            implicitNatural
        );
        assert.deepEqual(
            otherSession.lookup('context_A')?.mode,
            explicitObjectOnly
        );
        assert.equal(Object.isFrozen(withAB.declarations), true);
        assert.equal(Object.isFrozen(withAB.declarations[0]), true);
    });

    it('rejects duplicate free declarations at the new declaration span', () => {
        const environment = CoreDeclarationEnvironment.empty().extend(
            binding('duplicate_A', categoryUniverse(15), 15)
        );

        assert.throws(
            () => environment.extend(
                binding('duplicate_A', categoryUniverse(16), 16)
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'DUPLICATE_DECLARATION');
                assert.equal(error.provenance.span?.start.line, 16);
                assert.match(error.message, /duplicate_A.*16:1/i);
                return true;
            }
        );
    });

    it('allows earlier free dependencies and rejects forward references', () => {
        const withA = CoreDeclarationEnvironment.empty().extend(
            binding('dependency_A', categoryUniverse(20), 20)
        );
        const withX = withA.extend(binding(
            'dependency_x',
            objectType(free('dependency_A', 21), 21),
            22
        ));

        assert.equal(withX.lookup('dependency_x')?.type.tag, 'application');
        assert.doesNotThrow(() =>
            kernelAssertScoped(withX.lookup('dependency_x')!.type)
        );

        assert.throws(
            () => withA.extend(binding(
                'dependency_y',
                objectType(free('dependency_missing', 23), 23),
                24
            )),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'UNBOUND_FREE_REFERENCE');
                assert.equal(error.provenance.span?.start.line, 23);
                assert.match(error.message, /dependency_missing.*23:1/);
                return true;
            }
        );
    });

    it('validates free declaration types at binder depth zero', () => {
        assert.throws(
            () => CoreDeclarationEnvironment.empty().extend(binding(
                'escaping_declaration',
                bound(0, 30),
                31
            )),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'ILL_SCOPED_DECLARATION_TYPE');
                assert.equal(error.provenance.span?.start.line, 30);
                assert.equal(
                    error.scopeError?.code,
                    'DANGLING_BOUND_VARIABLE'
                );
                return true;
            }
        );
    });

    it('extends a dependent local telescope without mutating ancestors', () => {
        const empty = CoreContext.empty();
        const withA = empty.extend(binding(
            'local_A',
            categoryUniverse(40),
            40,
            implicitNatural
        ));
        const withX = withA.extend(binding(
            'local_x',
            objectType(bound(0, 41), 41),
            42,
            explicitObjectOnly
        ));

        assert.equal(empty.depth, 0);
        assert.equal(withA.depth, 1);
        assert.equal(withX.depth, 2);
        assert.deepEqual(
            withA.telescope.map(local => local.name),
            ['local_A']
        );
        assert.deepEqual(
            withX.telescope.map(local => local.name),
            ['local_A', 'local_x']
        );
        assert.deepEqual(withA.lookup('local_A')?.mode, implicitNatural);
        assert.deepEqual(withX.lookup('local_x')?.mode, explicitObjectOnly);
        assert.equal(withX.telescope[1].ownerDepth, 1);
        assert.equal(withX.telescope[1].provenance.span?.start.line, 42);
        assert.equal(Object.isFrozen(withX.telescope), true);
        assert.equal(Object.isFrozen(withX.telescope[1]), true);
    });

    it('returns nearest indices and types lifted under newer binders', () => {
        const withA = CoreContext.empty().extend(binding(
            'lift_A',
            categoryUniverse(50),
            50
        ));
        const withX = withA.extend(binding(
            'lift_x',
            objectType(bound(0, 51), 51),
            51
        ));
        const withY = withX.extend(binding(
            'lift_y',
            objectType(bound(1, 52), 52),
            52
        ));

        const y = withY.resolve('lift_y', because(53, 'use lift_y'));
        const x = withY.resolve('lift_x', because(54, 'use lift_x'));
        const A = withY.resolve('lift_A', because(55, 'use lift_A'));

        assert.equal(y.kind, 'local');
        assert.equal(x.kind, 'local');
        assert.equal(A.kind, 'local');
        if (y.kind !== 'local' || x.kind !== 'local' || A.kind !== 'local') {
            throw new Error('Expected three local lookup results');
        }

        assert.equal(y.index, 0);
        assert.equal(x.index, 1);
        assert.equal(A.index, 2);
        expectBoundIndex(y.term, 0);
        expectBoundIndex(x.term, 1);
        expectBoundIndex(A.term, 2);
        expectObjectCategoryIndex(y.type, 2);
        expectObjectCategoryIndex(x.type, 2);
        assert.equal(y.term.provenance.span?.start.line, 53);
        assert.equal(x.term.provenance.span?.start.line, 54);
    });

    it('keeps free identity separate from local and nested shadowing', () => {
        const declarations = CoreDeclarationEnvironment.empty().extend(
            binding('shadowed', categoryUniverse(60), 60)
        );
        const base = CoreContext.empty(declarations);
        const outer = base.extend(binding(
            'shadowed',
            categoryUniverse(61),
            61
        ));
        const inner = outer.extend(binding(
            'shadowed',
            bound(0, 62),
            62,
            implicitNatural
        ));

        const nearest = inner.resolve(
            'shadowed',
            because(63, 'nearest shadowed use')
        );
        const freeDeclaration = inner.lookupDeclaration(
            'shadowed',
            because(64, 'explicit free shadowed use')
        );
        const persistentOuter = outer.resolve(
            'shadowed',
            because(65, 'outer shadowed use')
        );

        assert.equal(nearest.kind, 'local');
        assert.equal(persistentOuter.kind, 'local');
        assert.equal(freeDeclaration?.kind, 'free');
        if (
            nearest.kind !== 'local' ||
            persistentOuter.kind !== 'local' ||
            !freeDeclaration
        ) {
            throw new Error('Expected local and free shadowing results');
        }
        assert.equal(nearest.index, 0);
        assert.equal(persistentOuter.index, 0);
        expectBoundIndex(nearest.type, 1);
        assert.equal(
            kernelExpressionEquals(nearest.term, freeDeclaration.term),
            false
        );
        assert.equal(freeDeclaration.term.name, 'shadowed');
        assert.equal(nearest.mode.variation, 'natural');
        assert.equal(outer.depth, 1);
        assert.equal(inner.depth, 2);
    });

    it('rejects escaping and undeclared names in local types', () => {
        assert.throws(
            () => CoreContext.empty().extend(binding(
                'escaping_local',
                bound(0, 70),
                71
            )),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'ILL_SCOPED_LOCAL_TYPE');
                assert.equal(error.provenance.span?.start.line, 70);
                return true;
            }
        );

        const withOne = CoreContext.empty().extend(binding(
            'scope_outer',
            categoryUniverse(72),
            72
        ));
        assert.throws(
            () => withOne.extend(binding(
                'scope_inner',
                bound(1, 73),
                74
            )),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'ILL_SCOPED_LOCAL_TYPE');
                assert.equal(error.provenance.span?.start.line, 73);
                return true;
            }
        );

        assert.throws(
            () => CoreContext.empty().extend(binding(
                'unknown_free_local',
                free('not_declared', 75),
                76
            )),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'UNBOUND_FREE_REFERENCE');
                assert.equal(error.provenance.span?.start.line, 75);
                return true;
            }
        );
    });

    it('reports an unbound lookup at the use-site provenance', () => {
        assert.throws(
            () => CoreContext.empty().resolve(
                'not_in_scope',
                because(80, 'missing name use')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreContextError);
                assert.equal(error.code, 'UNBOUND_NAME');
                assert.equal(error.provenance.span?.start.line, 80);
                assert.match(error.message, /not_in_scope.*80:1/);
                return true;
            }
        );
    });

    it('abstracts a dependent telescope into closed Pi and lambda terms', () => {
        const withA = CoreContext.empty().extend(binding(
            'abstract_A',
            categoryUniverse(90),
            90
        ));
        const context = withA.extend(binding(
            'abstract_x',
            objectType(bound(0, 91), 91),
            91
        ));
        const x = context.resolve(
            'abstract_x',
            because(92, 'abstracted x use')
        );
        assert.equal(x.kind, 'local');
        if (x.kind !== 'local') {
            throw new Error('Expected abstract_x to resolve locally');
        }

        const term = context.abstractLambda(x.term);
        const type = context.abstractPi(x.type);

        assert.equal(
            serializeKernelExpression(term),
            'λ (v0 : Cat), λ (v1 : τ (Obj v0)), v1'
        );
        assert.equal(
            serializeKernelExpression(type),
            'Π (v0 : Cat), Π (v1 : τ (Obj v0)), τ (Obj v0)'
        );
        assert.doesNotThrow(() => kernelAssertScoped(term));
        assert.doesNotThrow(() => kernelAssertScoped(type));
    });

    it(
        'emits a context-abstracted dependent identity accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const context = CoreContext.empty()
                .extend(binding(
                    'probe_A',
                    categoryUniverse(100),
                    100
                ))
                .extend(binding(
                    'probe_x',
                    objectType(bound(0, 101), 101),
                    101
                ));
            const x = context.resolve(
                'probe_x',
                because(102, 'probe x use')
            );
            assert.equal(x.kind, 'local');
            if (x.kind !== 'local') {
                throw new Error('Expected probe_x to resolve locally');
            }

            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: [],
                assertions: [{
                    label: 'ELAB-2A1 context-dependent identity',
                    term: context.abstractLambda(x.term),
                    type: context.abstractPi(x.type),
                    span: at(102, 1, 45)
                }]
            };
            const serialized = serializeKernelProbe(probe);
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });

            assert.equal(
                result.accepted,
                true,
                `Expected context probe acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
