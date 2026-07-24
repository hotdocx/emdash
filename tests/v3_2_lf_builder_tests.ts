/**
 * Focused DTTLF LF-SURFACE-1 tests for scoped builder lowering.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreCheckerError,
    CoreLfBuilderError,
    CoreLfBuilderTerm,
    CoreLfDeclarationEnvironment,
    CoreLfScopedBuilder,
    KernelExpression,
    binderMode,
    coreLfCombinedWeakHead,
    createCoreLfChecker,
    kernelApplication,
    kernelBound,
    kernelExpressionEquals,
    provenance,
    serializeKernelExpression,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_lf_builder.surface.ts';
const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const builder = (line: number): CoreLfScopedBuilder =>
    new CoreLfScopedBuilder(
        because(line, 'LF-SURFACE-1 builder default')
    );

const category = (
    scoped: CoreLfScopedBuilder,
    line: number
): CoreLfBuilderTerm => scoped.application(
    'category-universe',
    [],
    because(line, 'LF-SURFACE-1 category universe')
);

const objectType = (
    scoped: CoreLfScopedBuilder,
    category_: CoreLfBuilderTerm,
    line: number
): CoreLfBuilderTerm => scoped.application(
    'decode',
    [scoped.application(
        'object-classifier',
        [category_],
        because(line, 'LF-SURFACE-1 object classifier')
    )],
    because(line, 'LF-SURFACE-1 decoded object type')
);

const baseEnvironment = (
    name: string,
    line: number
): CoreLfDeclarationEnvironment =>
    CoreLfDeclarationEnvironment.empty().extend({
        name,
        type: kernelApplication(
            'category-universe',
            [],
            because(line, `LF-SURFACE-1 category type for ${name}`)
        ),
        mode: binderMode('explicit', 'functorial'),
        provenance: because(line, `LF-SURFACE-1 declaration ${name}`)
    });

const containsFunction = (
    value: unknown,
    visited = new Set<object>()
): boolean => {
    if (typeof value === 'function') return true;
    if (typeof value !== 'object' || value === null) return false;
    if (visited.has(value)) return false;
    visited.add(value);
    return Reflect.ownKeys(value).some(key =>
        containsFunction(
            (value as Record<PropertyKey, unknown>)[key],
            visited
        )
    );
};

describe('TypeScript v3.2 DTTLF LF-SURFACE-1 scoped builder', () => {
    it('runs binder callbacks once and stores no JavaScript closure', () => {
        const scoped = builder(10);
        const Cat = category(scoped, 10);
        let callbackCount = 0;
        const identity = scoped.lam(
            'value',
            Cat,
            value => {
                callbackCount++;
                return value;
            },
            undefined,
            because(10, 'LF-SURFACE-1 one-shot identity')
        );

        assert.equal(callbackCount, 1);
        assert.equal(containsFunction(identity), false);
        const first = scoped.lower(identity);
        const second = scoped.lower(identity);
        assert.equal(callbackCount, 1);
        assert.equal(kernelExpressionEquals(first, second), true);
        assert.equal(containsFunction(first), false);
        assert.equal(
            serializeKernelExpression(first),
            'λ (v0 : Cat), v0'
        );
    });

    it('lowers alpha-equivalent hints to structural Core equality', () => {
        const leftBuilder = builder(20);
        const rightBuilder = builder(21);
        const left = leftBuilder.lam(
            'leftHint',
            category(leftBuilder, 20),
            value => value
        );
        const right = rightBuilder.lam(
            'rightHint',
            category(rightBuilder, 21),
            value => value
        );

        assert.equal(
            kernelExpressionEquals(
                leftBuilder.lower(left),
                rightBuilder.lower(right)
            ),
            true
        );
    });

    it('resolves a genuinely dependent nested Pi by token identity', () => {
        const scoped = builder(30);
        const Cat = category(scoped, 30);
        const dependentPi = scoped.pi('A', Cat, A => {
            const ObjA = objectType(scoped, A, 31);
            return scoped.pi('x', ObjA, _x => ObjA);
        });
        const lowered = scoped.lower(dependentPi);

        assert.equal(
            serializeKernelExpression(lowered),
            'Π (v0 : Cat), Π (v1 : τ (Obj v0)), τ (Obj v0)'
        );
    });

    it('constructs and checks a direct explicit beta redex', () => {
        const scoped = builder(40);
        const Cat = category(scoped, 40);
        const identity = scoped.lam('value', Cat, value => value);
        const redex = scoped.apply(
            identity,
            scoped.free('lf_builder_A', because(40, 'builder A')),
            'explicit',
            because(40, 'LF-SURFACE-1 explicit beta')
        );
        const lowered = scoped.lower(redex);
        const environment = baseEnvironment('lf_builder_A', 40);
        const checker = createCoreLfChecker(environment);
        const inferred = checker.infer(checker.rootContext, lowered);

        assert.equal(
            serializeKernelExpression(inferred.type as KernelExpression),
            'Cat'
        );
        const reduced = coreLfCombinedWeakHead(
            environment,
            lowered,
            1
        );
        assert.equal(reduced.status, 'weak-head-normal');
        assert.deepEqual(
            reduced.trace.map(entry => entry.kind),
            ['beta']
        );
        assert.equal(
            serializeKernelExpression(reduced.expression),
            'lf_builder_A'
        );
    });

    it('preserves implicit binder plicity through lowering and beta', () => {
        const scoped = builder(50);
        const Cat = category(scoped, 50);
        const identity = scoped.lam(
            'implicitValue',
            Cat,
            value => value,
            binderMode('implicit', 'natural')
        );
        const redex = scoped.apply(
            identity,
            scoped.free('lf_builder_implicit_A'),
            'implicit'
        );
        const lowered = scoped.lower(redex);
        const environment = baseEnvironment(
            'lf_builder_implicit_A',
            50
        );
        const checker = createCoreLfChecker(environment);
        assert.doesNotThrow(() =>
            checker.infer(checker.rootContext, lowered)
        );

        const reduced = coreLfCombinedWeakHead(
            environment,
            lowered,
            1
        );
        assert.equal(reduced.status, 'weak-head-normal');
        assert.equal(reduced.trace[0].kind, 'beta');
        assert.equal(
            reduced.trace[0].kind === 'beta'
                ? reduced.trace[0].binderPlicity
                : undefined,
            'implicit'
        );
    });

    it('lowers dependent let sugar to beta without adding a Core let node', () => {
        const scoped = builder(60);
        const Cat = category(scoped, 60);
        let callbackCount = 0;
        const dependentLet = scoped.let_(
            'A',
            Cat,
            scoped.free('lf_builder_let_A'),
            A => {
                callbackCount++;
                const ObjA = objectType(scoped, A, 61);
                return scoped.lam('x', ObjA, x => x);
            }
        );
        assert.equal(callbackCount, 1);

        const lowered = scoped.lower(dependentLet);
        assert.equal(lowered.tag, 'call');
        const environment = baseEnvironment('lf_builder_let_A', 60);
        const checker = createCoreLfChecker(environment);
        const inferred = checker.infer(checker.rootContext, lowered);
        assert.equal(
            serializeKernelExpression(inferred.type as KernelExpression),
            'Π (v0 : τ (Obj lf_builder_let_A)), ' +
            'τ (Obj lf_builder_let_A)'
        );

        const reduced = coreLfCombinedWeakHead(
            environment,
            lowered,
            1
        );
        assert.equal(reduced.status, 'weak-head-normal');
        assert.equal(
            serializeKernelExpression(reduced.expression),
            'λ (v0 : τ (Obj lf_builder_let_A)), v0'
        );
        assert.equal(callbackCount, 1);
        assert.equal(
            Reflect.ownKeys(lowered).includes('let'),
            false
        );
    });

    it('uses builder terms as checked transparent definitions', () => {
        const scoped = builder(70);
        const Cat = category(scoped, 70);
        const identityType = scoped.pi('value', Cat, _value => Cat);
        const identityBody = scoped.lam('value', Cat, value => value);
        let environment = baseEnvironment('lf_builder_def_A', 70);
        environment = environment.extend({
            name: 'lf_builder_identity',
            type: scoped.lower(identityType),
            mode: binderMode('explicit', 'functorial'),
            provenance: because(71, 'LF-SURFACE-1 identity definition'),
            body: scoped.lower(identityBody),
            transparency: 'transparent'
        });

        const call = scoped.lower(scoped.apply(
            scoped.free('lf_builder_identity'),
            scoped.free('lf_builder_def_A')
        ));
        const checker = createCoreLfChecker(environment);
        assert.doesNotThrow(() =>
            checker.infer(checker.rootContext, call)
        );
        const reduced = coreLfCombinedWeakHead(
            environment,
            call,
            2
        );
        assert.equal(reduced.status, 'weak-head-normal');
        assert.deepEqual(
            reduced.trace.map(entry => entry.kind),
            ['delta', 'beta']
        );
        assert.equal(
            serializeKernelExpression(reduced.expression),
            'lf_builder_def_A'
        );
    });

    it('rejects foreign, escaped, open, and Type-in-Type construction paths', () => {
        const left = builder(80);
        const right = builder(81);
        const Cat = category(left, 80);

        assert.throws(
            () => left.apply(
                left.free('lf_builder_foreign_function'),
                right.free('lf_builder_foreign_value')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfBuilderError);
                assert.equal(error.code, 'FOREIGN_TERM');
                return true;
            }
        );
        assert.throws(
            () => left.lam('x', Cat, _x =>
                right.free('lf_builder_foreign_body')
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfBuilderError);
                assert.equal(error.code, 'FOREIGN_TERM');
                return true;
            }
        );

        let escaped: CoreLfBuilderTerm | undefined;
        left.lam('escaped', Cat, token => {
            escaped = token;
            return token;
        });
        const escapedUse = left.apply(
            left.free('lf_builder_escaped_function'),
            escaped!
        );
        assert.throws(
            () => left.lower(escapedUse),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfBuilderError);
                assert.equal(error.code, 'ESCAPED_BINDER_TOKEN');
                return true;
            }
        );

        assert.throws(
            () => left.embed(
                kernelBound(0, because(82, 'open embedded bound variable'))
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfBuilderError);
                assert.equal(error.code, 'OPEN_EMBEDDED_CORE');
                return true;
            }
        );
        assert.throws(
            () => left.application('decode', []),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfBuilderError);
                assert.equal(error.code, 'INVALID_OWNER_ARITY');
                return true;
            }
        );

        const universe = left.lower(left.universe());
        const checker = createCoreLfChecker(
            CoreLfDeclarationEnvironment.empty()
        );
        assert.throws(
            () => checker.check(
                checker.rootContext,
                universe,
                universe
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                return true;
            }
        );
    });
});
