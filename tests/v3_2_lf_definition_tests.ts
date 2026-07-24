/**
 * Focused DTTLF LF-1B tests for checked immutable definitions and delta.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreLfDeclarationEnvironment,
    CoreLfDeclarationError,
    CoreLfDeclarationInput,
    CoreLfEvaluationError,
    KernelCall,
    KernelExpression,
    binderMode,
    coreLfBetaWeakHead,
    coreLfDeltaReduceHead,
    coreLfDeltaWeakHead,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance,
    serializeKernelExpression,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_lf_definition.surface.ts';
const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(fixture, line, startColumn, line, endColumn);

const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const categoryUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'category-universe',
        [],
        because(line, 'LF-1B category universe')
    );

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `LF-1B free declaration ${name}`));

const declaration = (
    name: string,
    type: KernelExpression,
    line: number,
    options: Pick<
        CoreLfDeclarationInput,
        'body' | 'transparency'
    > = {}
): CoreLfDeclarationInput => ({
    name,
    type,
    mode: explicitFunctorial,
    provenance: because(line, `LF-1B declaration ${name}`),
    ...options
});

const categoryAssumption = (
    environment: CoreLfDeclarationEnvironment,
    name: string,
    line: number
) => environment.extend(
    declaration(name, categoryUniverse(line), line)
);

const categoryIdentityType = (line: number): KernelExpression => kernelPi(
    kernelBinder(
        'value',
        categoryUniverse(line),
        explicitFunctorial,
        because(line, 'LF-1B identity type binder')
    ),
    categoryUniverse(line),
    because(line, 'LF-1B identity type')
);

const categoryIdentityBody = (line: number): KernelExpression =>
    kernelLambda(
        kernelBinder(
            'value',
            categoryUniverse(line),
            explicitFunctorial,
            because(line, 'LF-1B identity body binder')
        ),
        kernelBound(0, because(line, 'LF-1B identity bound body')),
        because(line, 'LF-1B identity body')
    );

describe('TypeScript v3.2 DTTLF LF-1B checked definitions and delta', () => {
    it('extends checked declaration state persistently with explicit transparency', () => {
        const empty = CoreLfDeclarationEnvironment.empty();
        const withA = categoryAssumption(empty, 'lf_def_A', 10);
        const withAlias = withA.extend(declaration(
            'lf_def_alias',
            categoryUniverse(11),
            11,
            {
                body: free('lf_def_A', 11),
                transparency: 'transparent'
            }
        ));
        const withOpaqueDefault = withAlias.extend(declaration(
            'lf_def_opaque',
            categoryUniverse(12),
            12,
            {
                body: free('lf_def_alias', 12)
            }
        ));

        assert.deepEqual(empty.declarations, []);
        assert.deepEqual(
            withA.declarations.map(item => item.name),
            ['lf_def_A']
        );
        assert.deepEqual(
            withAlias.declarations.map(item => item.name),
            ['lf_def_A', 'lf_def_alias']
        );
        assert.equal(withA.lookup('lf_def_alias'), undefined);
        assert.deepEqual(
            withAlias.lookup('lf_def_alias')?.bodyDependencies,
            ['lf_def_A']
        );
        assert.equal(withAlias.lookup('lf_def_alias')?.ordinal, 1);
        assert.equal(
            withAlias.lookup('lf_def_alias')?.transparency,
            'transparent'
        );
        assert.equal(
            withOpaqueDefault.lookup('lf_def_opaque')?.transparency,
            'opaque'
        );
        assert.deepEqual(
            withOpaqueDefault.coreEnvironment.declarations.map(item =>
                item.name
            ),
            ['lf_def_A', 'lf_def_alias', 'lf_def_opaque']
        );
        assert.equal(Object.isFrozen(withAlias), true);
        assert.equal(Object.isFrozen(withAlias.declarations), true);
        assert.equal(
            Object.isFrozen(withAlias.lookup('lf_def_alias')!),
            true
        );
        assert.equal(
            Object.isFrozen(
                withAlias.lookup('lf_def_alias')!.bodyDependencies
            ),
            true
        );
    });

    it('rejects self, forward, transparent-assumption, and ill-typed bodies atomically', () => {
        const withA = categoryAssumption(
            CoreLfDeclarationEnvironment.empty(),
            'lf_def_guard_A',
            20
        );

        const expectDeclarationError = (
            operation: () => unknown,
            code: CoreLfDeclarationError['code']
        ): CoreLfDeclarationError => {
            let observed: CoreLfDeclarationError | undefined;
            assert.throws(operation, (error: unknown) => {
                assert.ok(error instanceof CoreLfDeclarationError);
                assert.equal(error.code, code);
                observed = error;
                return true;
            });
            return observed!;
        };

        expectDeclarationError(
            () => withA.extend(declaration(
                'lf_def_self',
                categoryUniverse(21),
                21,
                {
                    body: free('lf_def_self', 21),
                    transparency: 'transparent'
                }
            )),
            'SELF_REFERENCE'
        );
        expectDeclarationError(
            () => withA.extend(declaration(
                'lf_def_forward',
                categoryUniverse(22),
                22,
                {
                    body: free('lf_def_later', 22),
                    transparency: 'transparent'
                }
            )),
            'UNBOUND_BODY_REFERENCE'
        );
        expectDeclarationError(
            () => withA.extend(declaration(
                'lf_def_no_body',
                categoryUniverse(23),
                23,
                { transparency: 'transparent' }
            )),
            'TRANSPARENT_ASSUMPTION'
        );
        const illTyped = expectDeclarationError(
            () => withA.extend(declaration(
                'lf_def_bad_body',
                categoryUniverse(24),
                24,
                {
                    body: kernelUniverse(
                        because(24, 'LF-1B KIND-valued bad body')
                    ),
                    transparency: 'transparent'
                }
            )),
            'INVALID_DEFINITION_BODY'
        );
        assert.match(illTyped.message, /lf_def_bad_body/);

        assert.deepEqual(
            withA.declarations.map(item => item.name),
            ['lf_def_guard_A']
        );
        assert.equal(withA.lookup('lf_def_self'), undefined);
        assert.equal(withA.lookup('lf_def_forward'), undefined);
        assert.equal(withA.lookup('lf_def_bad_body'), undefined);
    });

    it('makes cycles unconstructible through strictly earlier body dependencies', () => {
        const withBase = categoryAssumption(
            CoreLfDeclarationEnvironment.empty(),
            'lf_cycle_base',
            30
        );
        const withFirst = withBase.extend(declaration(
            'lf_cycle_first',
            categoryUniverse(31),
            31,
            {
                body: free('lf_cycle_base', 31),
                transparency: 'transparent'
            }
        ));
        const withSecond = withFirst.extend(declaration(
            'lf_cycle_second',
            categoryUniverse(32),
            32,
            {
                body: free('lf_cycle_first', 32),
                transparency: 'transparent'
            }
        ));

        for (const item of withSecond.declarations) {
            for (const dependencyName of item.bodyDependencies) {
                const dependency = withSecond.lookup(dependencyName);
                assert.ok(dependency);
                assert.ok(dependency.ordinal < item.ordinal);
            }
        }
        assert.throws(
            () => withSecond.extend(declaration(
                'lf_cycle_attempt',
                categoryUniverse(33),
                33,
                {
                    body: free('lf_cycle_future', 33),
                    transparency: 'transparent'
                }
            )),
            (error: unknown) => {
                assert.ok(error instanceof CoreLfDeclarationError);
                assert.equal(error.code, 'UNBOUND_BODY_REFERENCE');
                return true;
            }
        );
    });

    it('unfolds transparent heads while keeping opaque and assumed names closed', () => {
        const withA = categoryAssumption(
            CoreLfDeclarationEnvironment.empty(),
            'lf_delta_A',
            40
        );
        const withTransparent = withA.extend(declaration(
            'lf_delta_alias',
            categoryUniverse(41),
            41,
            {
                body: free('lf_delta_A', 41),
                transparency: 'transparent'
            }
        ));
        const environment = withTransparent.extend(declaration(
            'lf_delta_opaque',
            categoryUniverse(42),
            42,
            {
                body: free('lf_delta_alias', 42),
                transparency: 'opaque'
            }
        ));

        const transparentReference = free('lf_delta_alias', 43);
        const transparent = coreLfDeltaWeakHead(
            environment,
            transparentReference,
            1
        );
        assert.equal(transparent.status, 'weak-head-normal');
        assert.equal(transparent.steps, 1);
        assert.equal(
            kernelExpressionEquals(
                transparent.expression,
                free('lf_delta_A', 43)
            ),
            true
        );
        assert.deepEqual(
            transparent.trace.map(entry => [
                entry.kind,
                entry.declarationName,
                entry.declarationOrdinal
            ]),
            [['delta', 'lf_delta_alias', 1]]
        );

        const opaque = coreLfDeltaWeakHead(
            environment,
            free('lf_delta_opaque', 44),
            3
        );
        assert.equal(opaque.status, 'weak-head-normal');
        assert.equal(
            opaque.status === 'weak-head-normal' ? opaque.reason : undefined,
            'declaration-opaque'
        );
        assert.equal(opaque.steps, 0);

        const assumption = coreLfDeltaWeakHead(
            environment,
            free('lf_delta_A', 45),
            3
        );
        assert.equal(assumption.status, 'weak-head-normal');
        assert.equal(
            assumption.status === 'weak-head-normal'
                ? assumption.reason
                : undefined,
            'declaration-without-body'
        );

        const unknown = coreLfDeltaWeakHead(
            environment,
            free('lf_delta_unknown', 46),
            3
        );
        assert.equal(unknown.status, 'weak-head-normal');
        assert.equal(
            unknown.status === 'weak-head-normal'
                ? unknown.reason
                : undefined,
            'declaration-not-found'
        );
    });

    it('traces a bounded transparent chain with decreasing declaration ordinals', () => {
        const withBase = categoryAssumption(
            CoreLfDeclarationEnvironment.empty(),
            'lf_delta_chain_base',
            50
        );
        const withFirst = withBase.extend(declaration(
            'lf_delta_chain_first',
            categoryUniverse(51),
            51,
            {
                body: free('lf_delta_chain_base', 51),
                transparency: 'transparent'
            }
        ));
        const environment = withFirst.extend(declaration(
            'lf_delta_chain_second',
            categoryUniverse(52),
            52,
            {
                body: free('lf_delta_chain_first', 52),
                transparency: 'transparent'
            }
        ));
        const reference = free('lf_delta_chain_second', 53);

        const zero = coreLfDeltaWeakHead(environment, reference, 0);
        assert.equal(zero.status, 'step-limit-exceeded');
        assert.deepEqual(
            zero.status === 'step-limit-exceeded' ? zero.next : undefined,
            {
                declarationName: 'lf_delta_chain_second',
                declarationOrdinal: 2
            }
        );

        const one = coreLfDeltaWeakHead(environment, reference, 1);
        assert.equal(one.status, 'step-limit-exceeded');
        assert.equal(one.steps, 1);
        assert.deepEqual(
            one.status === 'step-limit-exceeded' ? one.next : undefined,
            {
                declarationName: 'lf_delta_chain_first',
                declarationOrdinal: 1
            }
        );

        const complete = coreLfDeltaWeakHead(environment, reference, 2);
        assert.equal(complete.status, 'weak-head-normal');
        assert.equal(complete.steps, 2);
        assert.deepEqual(
            complete.trace.map(entry => entry.declarationOrdinal),
            [2, 1]
        );
        assert.equal(
            kernelExpressionEquals(
                complete.expression,
                free('lf_delta_chain_base', 54)
            ),
            true
        );
    });

    it('exposes delta then beta as separate candidate layers on a checked definition', () => {
        const withA = categoryAssumption(
            CoreLfDeclarationEnvironment.empty(),
            'lf_delta_call_A',
            60
        );
        const environment = withA.extend(declaration(
            'lf_delta_identity',
            categoryIdentityType(61),
            61,
            {
                body: categoryIdentityBody(61),
                transparency: 'transparent'
            }
        ));
        const argument = free('lf_delta_call_A', 62);
        const redex = kernelCall(
            free('lf_delta_identity', 62),
            [{
                plicity: 'explicit',
                value: argument,
                provenance: because(62, 'LF-1B identity call argument')
            }],
            because(62, 'LF-1B delta-call redex')
        );

        const delta = coreLfDeltaWeakHead(environment, redex, 1);
        assert.equal(delta.status, 'weak-head-normal');
        assert.equal(delta.steps, 1);
        assert.equal(delta.expression.tag, 'call');
        if (delta.expression.tag !== 'call') {
            throw new Error('Expected delta to preserve the call spine');
        }
        assert.equal(delta.expression.callee.tag, 'lambda');
        assert.equal(delta.expression.arguments[0].value, argument);

        const beta = coreLfBetaWeakHead(delta.expression, 1);
        assert.equal(beta.status, 'weak-head-normal');
        assert.equal(beta.steps, 1);
        assert.equal(kernelExpressionEquals(beta.expression, argument), true);
        assert.deepEqual(
            [delta.trace[0].kind, beta.trace[0].kind],
            ['delta', 'beta']
        );

        assert.equal(
            serializeKernelExpression(redex),
            'lf_delta_identity lf_delta_call_A'
        );
    });

    it('keeps malformed empty calls irreducible and rejects invalid delta limits', () => {
        const environment = categoryAssumption(
            CoreLfDeclarationEnvironment.empty(),
            'lf_delta_guard_A',
            70
        );
        const empty: KernelCall = {
            tag: 'call',
            callee: free('lf_delta_guard_A', 70),
            arguments: Object.freeze([]),
            provenance: because(70, 'LF-1B empty delta call')
        };
        const emptyHead = coreLfDeltaReduceHead(environment, empty);
        assert.equal(emptyHead.status, 'irreducible');
        assert.equal(
            emptyHead.status === 'irreducible'
                ? emptyHead.reason
                : undefined,
            'empty-call'
        );

        const neutralCall = kernelCall(
            categoryIdentityBody(71),
            [{
                plicity: 'explicit',
                value: free('lf_delta_guard_A', 71)
            }],
            because(71, 'LF-1B non-reference delta head')
        );
        const neutral = coreLfDeltaWeakHead(
            environment,
            neutralCall,
            0
        );
        assert.equal(neutral.status, 'weak-head-normal');
        assert.equal(
            neutral.status === 'weak-head-normal'
                ? neutral.reason
                : undefined,
            'not-a-reference-head'
        );

        for (const invalid of [-1, 0.25, Number.NaN]) {
            assert.throws(
                () => coreLfDeltaWeakHead(
                    environment,
                    free('lf_delta_guard_A', 72),
                    invalid
                ),
                (error: unknown) => {
                    assert.ok(error instanceof CoreLfEvaluationError);
                    assert.equal(error.code, 'INVALID_STEP_LIMIT');
                    return true;
                }
            );
        }
    });
});
