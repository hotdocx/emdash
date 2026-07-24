/**
 * Focused ELAB-2A0 tests for locally nameless Core binding operations.
 */

import assert from 'node:assert';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    KernelApplication,
    KernelExpression,
    KernelProbe,
    KernelScopeError,
    LAMBDAPI_V32_MODULE,
    binderMode,
    checkLambdapiProbe,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelExpressionEquals,
    kernelFree,
    kernelInstantiate,
    kernelLambda,
    kernelPi,
    kernelShift,
    kernelSubstitute,
    provenance,
    serializeKernelExpression,
    serializeKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_core_binder.surface.ts';
const at = (line: number, startColumn = 1, endColumn = startColumn + 1) =>
    sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const categoryUniverse = (line = 1) => kernelApplication(
    'category-universe',
    [],
    because(line, 'ELAB-2A0 category universe')
);

const free = (name: string, line = 1) =>
    kernelFree(name, because(line, `ELAB-2A0 free declaration ${name}`));

const bound = (index: number, line = 1) =>
    kernelBound(index, because(line, `ELAB-2A0 bound index ${index}`));

const binder = (
    hint: string,
    type: KernelExpression,
    line: number,
    mode = explicitFunctorial
) => kernelBinder(
    hint,
    type,
    mode,
    because(line, `ELAB-2A0 binder hint ${hint}`)
);

const objectClassifierType = (
    category: KernelExpression,
    line: number
) => {
    const nodeProvenance = because(line, 'ELAB-2A0 object classifier type');
    return kernelApplication('decode', [{
        value: kernelApplication('object-classifier', [{
            value: category
        }], nodeProvenance)
    }], nodeProvenance);
};

const homCategory = (
    category: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    line: number
) => kernelApplication('hom-category', [
    { value: category },
    { value: source },
    { value: target }
], because(line, 'ELAB-2A0 Hom category'));

const functorClassifier = (
    source: KernelExpression,
    target: KernelExpression,
    line: number
) => kernelApplication('functor-classifier', [
    { value: source },
    { value: target }
], because(line, 'ELAB-2A0 functor classifier'));

const identityLambda = (
    hint: string,
    line: number,
    mode = explicitFunctorial
) => kernelLambda(
    binder(hint, categoryUniverse(line), line, mode),
    bound(0, line),
    because(line, 'ELAB-2A0 identity lambda')
);

function nestedHomLambda(
    outerHint: string,
    innerHint: string,
    line: number
): KernelExpression {
    const A = free('binder_A', line);
    const objectOfA = objectClassifierType(A, line);
    return kernelLambda(
        binder(outerHint, objectOfA, line),
        kernelLambda(
            binder(innerHint, objectOfA, line),
            homCategory(A, bound(1, line), bound(0, line), line),
            because(line, 'ELAB-2A0 inner lambda')
        ),
        because(line, 'ELAB-2A0 outer lambda')
    );
}

const applicationArgumentIndices = (
    expression: KernelExpression
): readonly number[] => {
    assert.equal(expression.tag, 'application');
    return (expression as KernelApplication).arguments.map(argument => {
        assert.equal(argument.value.tag, 'bound');
        if (argument.value.tag !== 'bound') {
            throw new Error('Expected a bound-variable application argument');
        }
        return argument.value.index;
    });
};

describe('TypeScript v3.2 ELAB-2A0 Core binders', () => {
    it('separates named free declarations from bound occurrences', () => {
        const freeV0 = free('v0', 10);
        const boundV0 = bound(0, 10);

        assert.deepEqual(
            { tag: freeV0.tag, namespace: freeV0.namespace, name: freeV0.name },
            { tag: 'reference', namespace: 'free', name: 'v0' }
        );
        assert.deepEqual(
            { tag: boundV0.tag, index: boundV0.index },
            { tag: 'bound', index: 0 }
        );
        assert.equal(kernelExpressionEquals(freeV0, boundV0), false);
        assert.doesNotThrow(() =>
            kernelAssertScoped(identityLambda('ignored', 11))
        );
    });

    it('rejects invalid, dangling, and downward-escaping indices', () => {
        assert.throws(
            () => bound(-1, 12),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'INVALID_BOUND_INDEX');
                return true;
            }
        );
        assert.throws(
            () => kernelAssertScoped(bound(0, 13)),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'DANGLING_BOUND_VARIABLE');
                assert.equal(error.provenance.span?.start.line, 13);
                return true;
            }
        );
        assert.throws(
            () => kernelShift(bound(0, 14), -1),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'BOUND_INDEX_ESCAPE');
                return true;
            }
        );
        assert.throws(
            () => kernelShift(bound(0, 15), 0.5),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'INVALID_SHIFT');
                return true;
            }
        );
        assert.throws(
            () => kernelShift(bound(Number.MAX_SAFE_INTEGER, 15), 1),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'INVALID_SHIFT');
                return true;
            }
        );
        assert.throws(
            () => serializeKernelExpression(bound(0, 16)),
            (error: unknown) => {
                assert.ok(error instanceof KernelScopeError);
                assert.equal(error.code, 'DANGLING_BOUND_VARIABLE');
                return true;
            }
        );
    });

    it('makes alpha-equivalence structural while preserving binder modes', () => {
        const left = identityLambda('x', 20);
        const right = identityLambda('renamed', 21);

        assert.equal(kernelExpressionEquals(left, right), true);
        assert.equal(
            serializeKernelExpression(left),
            'λ (v0 : Cat), v0'
        );
        assert.equal(
            serializeKernelExpression(left),
            serializeKernelExpression(right)
        );

        const implicit = identityLambda(
            'x',
            22,
            binderMode('implicit', 'functorial')
        );
        const natural = identityLambda(
            'x',
            23,
            binderMode('explicit', 'natural')
        );
        assert.equal(kernelExpressionEquals(left, implicit), false);
        assert.equal(kernelExpressionEquals(left, natural), false);

        const freeBody = kernelLambda(
            binder('x', categoryUniverse(24), 24),
            free('x', 24),
            because(24, 'ELAB-2A0 free-body lambda')
        );
        assert.equal(kernelExpressionEquals(left, freeBody), false);

        const dependentPiLeft = kernelPi(
            binder('A', categoryUniverse(25), 25),
            objectClassifierType(bound(0, 25), 25),
            because(25, 'ELAB-2A0 dependent Pi')
        );
        const dependentPiRight = kernelPi(
            binder('renamed_A', categoryUniverse(26), 26),
            objectClassifierType(bound(0, 26), 26),
            because(26, 'ELAB-2A0 alpha-renamed dependent Pi')
        );
        assert.equal(
            kernelExpressionEquals(dependentPiLeft, dependentPiRight),
            true
        );
        assert.equal(
            serializeKernelExpression(dependentPiLeft),
            'Π (v0 : Cat), τ (Obj v0)'
        );
    });

    it('serializes nested shadowing canonically and alpha-invariantly', () => {
        const shadowed = nestedHomLambda('x', 'x', 30);
        const renamed = nestedHomLambda('outer', 'inner', 31);

        assert.equal(kernelExpressionEquals(shadowed, renamed), true);
        assert.equal(
            serializeKernelExpression(shadowed),
            'λ (v0 : τ (Obj binder_A)), ' +
            'λ (v1 : τ (Obj binder_A)), ' +
            'Hom_cat binder_A v0 v1'
        );
        assert.equal(
            serializeKernelExpression(shadowed),
            serializeKernelExpression(renamed)
        );
    });

    it('generates binder names that cannot capture free declarations', () => {
        const captureCandidate = kernelLambda(
            binder('v0', categoryUniverse(35), 35),
            functorClassifier(free('v0', 35), bound(0, 35), 35),
            because(35, 'ELAB-2A0 capture-avoidance serialization')
        );

        assert.equal(
            serializeKernelExpression(captureCandidate),
            'λ (v1 : Cat), Functor v0 v1'
        );
    });

    it('shifts open indices uniformly through owner applications and binders', () => {
        const openPair = functorClassifier(bound(1, 40), bound(0, 40), 40);
        const shifted = kernelShift(openPair, 1);

        assert.deepEqual(applicationArgumentIndices(shifted), [2, 1]);

        const closed = nestedHomLambda('left', 'right', 41);
        assert.equal(
            kernelExpressionEquals(kernelShift(closed, 3), closed),
            true
        );
    });

    it('substitutes under binders without capturing the replacement', () => {
        const A = free('binder_A', 45);
        const objectOfA = objectClassifierType(A, 45);
        const openBody = kernelLambda(
            binder('inner', objectOfA, 45),
            homCategory(A, bound(1, 45), bound(0, 45), 45),
            because(45, 'ELAB-2A0 open inner lambda')
        );

        const replacementFromOuterScope = bound(0, 46);
        const instantiated = kernelInstantiate(
            openBody,
            replacementFromOuterScope
        );
        const closed = kernelLambda(
            binder('ambient', objectOfA, 46),
            instantiated,
            because(46, 'ELAB-2A0 closes replacement scope')
        );

        assert.equal(
            kernelExpressionEquals(
                closed,
                nestedHomLambda('ambient2', 'inner2', 47)
            ),
            true
        );

        const substitutedWithoutRemoval = kernelSubstitute(
            openBody,
            0,
            free('binder_b', 48)
        );
        assert.equal(
            serializeKernelExpression(substitutedWithoutRemoval),
            'λ (v0 : τ (Obj binder_A)), ' +
            'Hom_cat binder_A binder_b v0'
        );
    });

    it('instantiates dependencies in a nested binder type only', () => {
        const dependentBody = kernelLambda(
            binder(
                'x',
                objectClassifierType(bound(0, 49), 49),
                49
            ),
            bound(0, 49),
            because(49, 'ELAB-2A0 dependent inner lambda')
        );
        const closedDependent = kernelLambda(
            binder('A', categoryUniverse(49), 49),
            dependentBody,
            because(49, 'ELAB-2A0 dependent outer lambda')
        );
        assert.equal(
            serializeKernelExpression(closedDependent),
            'λ (v0 : Cat), λ (v1 : τ (Obj v0)), v1'
        );

        const instantiated = kernelInstantiate(
            dependentBody,
            free('binder_A', 49)
        );
        assert.equal(
            serializeKernelExpression(instantiated),
            'λ (v0 : τ (Obj binder_A)), v0'
        );
    });

    it('composes nearest-binder instantiation in telescope order', () => {
        const openPair = functorClassifier(bound(1, 50), bound(0, 50), 50);
        const afterNearest = kernelInstantiate(
            openPair,
            free('binder_X', 50)
        );
        assert.equal(afterNearest.tag, 'application');
        const nearestArguments =
            (afterNearest as KernelApplication).arguments;
        assert.equal(nearestArguments[0].value.tag, 'bound');
        assert.equal(
            nearestArguments[0].value.tag === 'bound'
                ? nearestArguments[0].value.index
                : undefined,
            0
        );
        assert.equal(
            serializeKernelExpression(
                kernelLambda(
                    binder('remaining', categoryUniverse(50), 50),
                    afterNearest,
                    because(50, 'ELAB-2A0 closes remaining binder')
                )
            ),
            'λ (v0 : Cat), Functor v0 binder_X'
        );

        const closed = kernelInstantiate(
            afterNearest,
            free('binder_Y', 51)
        );
        assert.equal(
            serializeKernelExpression(closed),
            'Functor binder_Y binder_X'
        );
    });

    it(
        'emits closed alpha-canonical binders accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const identity = identityLambda('surface_hint', 60);
            const identityType = kernelPi(
                binder('different_hint', categoryUniverse(60), 60),
                categoryUniverse(60),
                because(60, 'ELAB-2A0 identity Pi type')
            );
            const dependentTerm = kernelLambda(
                binder('A_hint', categoryUniverse(61), 61),
                kernelLambda(
                    binder(
                        'x_hint',
                        objectClassifierType(bound(0, 61), 61),
                        61
                    ),
                    bound(0, 61),
                    because(61, 'ELAB-2A0 dependent identity body')
                ),
                because(61, 'ELAB-2A0 dependent identity')
            );
            const dependentType = kernelPi(
                binder('A_type_hint', categoryUniverse(61), 61),
                kernelPi(
                    binder(
                        'x_type_hint',
                        objectClassifierType(bound(0, 61), 61),
                        61
                    ),
                    objectClassifierType(bound(1, 61), 61),
                    because(61, 'ELAB-2A0 dependent identity inner Pi')
                ),
                because(61, 'ELAB-2A0 dependent identity outer Pi')
            );
            const probe: KernelProbe = {
                requiredModule: LAMBDAPI_V32_MODULE,
                declarations: [],
                assertions: [
                    {
                        label: 'ELAB-2A0 closed identity binder',
                        term: identity,
                        type: identityType,
                        span: at(60, 1, 40)
                    },
                    {
                        label: 'ELAB-2A0 dependent identity binders',
                        term: dependentTerm,
                        type: dependentType,
                        span: at(61, 1, 60)
                    }
                ]
            };
            const serialized = serializeKernelProbe(probe);

            assert.match(
                serialized.source,
                /assert ⊢ λ \(v0 : Cat\), v0 : Π \(v0 : Cat\), Cat;/
            );
            assert.match(
                serialized.source,
                /assert ⊢ λ \(v0 : Cat\), λ \(v1 : τ \(Obj v0\)\), v1 : Π \(v0 : Cat\), Π \(v1 : τ \(Obj v0\)\), τ \(Obj v0\);/
            );
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected Core binder probe acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
