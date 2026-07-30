/**
 * Focused SYNTAX-1A ordinary categorical text-adapter corpus.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalCategory,
    CoreCategoricalProgram
} from '../src/v3_2/categorical_program';
import {
    CoreCategoricalHomBoundary,
    CoreCategoricalTerm
} from '../src/v3_2/categorical_surface';
import {
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    elaborateCoreCategoricalText
} from '../src/v3_2/categorical_text';

const sourceFile = 'tests/fixtures/categorical-text.emdash';

interface TextFixture {
    readonly program: CoreCategoricalProgram;
    readonly A: CoreCategoricalCategory;
    readonly B: CoreCategoricalCategory;
    readonly C: CoreCategoricalCategory;
    readonly functorsBC: CoreCategoricalCategory;
    readonly H: CoreCategoricalTerm;
    readonly K: CoreCategoricalTerm;
    readonly F: CoreCategoricalTerm;
    readonly G: CoreCategoricalTerm;
    readonly D: CoreCategoricalTerm;
    readonly c: CoreCategoricalTerm;
    readonly y0: CoreCategoricalTerm;
    readonly x0: CoreCategoricalTerm;
    readonly pA: CoreCategoricalHomBoundary;
    readonly pB: CoreCategoricalHomBoundary;
    readonly environment: readonly CoreCategoricalTextBinding[];
}

const categoryBinding = (
    name: string,
    value: CoreCategoricalCategory
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'category' as const,
    value
});

const termBinding = (
    name: string,
    value: CoreCategoricalTerm
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'term' as const,
    value
});

const boundaryBinding = (
    name: string,
    value: CoreCategoricalHomBoundary
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'hom-boundary' as const,
    value
});

const fixture = (): TextFixture => {
    const program = new CoreCategoricalProgram({ sourceFile });
    const A = program.category('text_A', { line: 1 });
    const B = program.category('text_B', { line: 2 });
    const C = program.category('text_C', { line: 3 });
    const functorsBC = program.functorCategory(B, C, { line: 4 });
    const functorsAC = program.functorCategory(A, C, { line: 5 });
    const H = program.functor('text_H', A, functorsBC, { line: 6 });
    const K = program.functor('text_K', A, B, { line: 7 });
    const F = program.functor('text_F', A, functorsBC, { line: 8 });
    const G = program.functor('text_G', A, B, { line: 9 });
    const D = program.functor('text_D', A, functorsAC, { line: 10 });
    const c = program.object('text_c', C, { line: 11 });
    const y0 = program.object('text_y0', B, { line: 12 });
    const x0 = program.object('text_x0', A, { line: 13 });
    const x1 = program.object('text_x1', A, { line: 14 });
    const b0 = program.object('text_b0', B, { line: 15 });
    const b1 = program.object('text_b1', B, { line: 16 });
    const pA = program.homBoundary(A, x0, x1, { line: 17 });
    const pB = program.homBoundary(B, b0, b1, { line: 18 });
    const environment = Object.freeze([
        categoryBinding('A', A),
        categoryBinding('B', B),
        categoryBinding('C', C),
        termBinding('H', H),
        termBinding('K', K),
        termBinding('F', F),
        termBinding('G', G),
        termBinding('D', D),
        termBinding('c', c),
        termBinding('y0', y0),
        termBinding('x0', x0),
        boundaryBinding('pA', pA),
        boundaryBinding('pB', pB)
    ]);
    return Object.freeze({
        program,
        A,
        B,
        C,
        functorsBC,
        H,
        K,
        F,
        G,
        D,
        c,
        y0,
        x0,
        pA,
        pB,
        environment
    });
};

const textLambda = (
    data: TextFixture,
    source: string,
    target: CoreCategoricalCategory = data.C,
    environment = data.environment
): CoreCategoricalTerm => elaborateCoreCategoricalText(
    data.program,
    {
        source,
        sourceFile,
        environment,
        expected: {
            kind: 'ordinary-functor',
            source: data.A,
            target
        }
    }
);

const captureTextError = (
    action: () => unknown,
    code: CoreCategoricalTextErrorCode
): CoreCategoricalTextError => {
    let captured: unknown;
    try {
        action();
    } catch (error: unknown) {
        captured = error;
    }
    assert.equal(captured instanceof CoreCategoricalTextError, true);
    const diagnostic = captured as CoreCategoricalTextError;
    assert.equal(diagnostic.code, code);
    return diagnostic;
};

describe('SYNTAX-1A ordinary categorical text adapter', () => {
    it('matches direct pointwise bracket lowering exactly', () => {
        const data = fixture();
        const parsed = textLambda(
            data,
            'λ^f x. (H x) (K x)',
            data.C,
            data.environment.filter(binding => binding.name !== 'A')
        );
        const direct = data.program.lambda(
            'x',
            data.A,
            data.C,
            x => data.program.apply(
                data.program.apply(data.H, x),
                data.program.apply(data.K, x)
            )
        );
        const parsedCompilation = data.program.compile(parsed);
        const directCompilation = data.program.compile(direct);

        assert.equal(
            parsedCompilation.explicitCore,
            directCompilation.explicitCore
        );
        assert.deepEqual(
            parsedCompilation.structuralPrerequisites,
            directCompilation.structuralPrerequisites
        );
        assert.equal(data.program.compare(parsed, direct).status, 'equal');
    });

    it('keeps Unicode and ASCII lambda spellings equivalent', () => {
        const data = fixture();
        const unicode = textLambda(
            data,
            'λ^f x : A. (H x) (K x)'
        );
        const ascii = textLambda(
            data,
            '\\^f x : A. (H x) (K x)'
        );

        assert.equal(data.program.compare(unicode, ascii).status, 'equal');
        assert.equal(
            data.program.compile(unicode).explicitCore,
            data.program.compile(ascii).explicitCore
        );
    });

    it('checks an explicit annotation but infers an omitted one from expectation', () => {
        const data = fixture();
        const withoutAnnotation = textLambda(
            data,
            'λ^f x. F x y0',
            data.C,
            data.environment.filter(binding => binding.name !== 'A')
        );
        const withAnnotation = textLambda(
            data,
            'λ^f x : A. F x y0'
        );

        assert.equal(
            data.program.compare(
                withoutAnnotation,
                withAnnotation
            ).status,
            'equal'
        );
        assert.equal(
            data.program.compile(withoutAnnotation).explicitCore,
            data.program.compile(withAnnotation).explicitCore
        );
    });

    it('recurses through fixed inner evaluation without sub-brackets', () => {
        const data = fixture();
        const parsed = textLambda(data, 'λ^f x. F x y0');
        const direct = data.program.lambda(
            'x',
            data.A,
            data.C,
            x => data.program.apply(
                data.program.apply(data.F, x),
                data.y0
            )
        );
        const compiled = data.program.compile(parsed);

        assert.equal(data.program.compare(parsed, direct).status, 'equal');
        assert.equal(
            compiled.explicitCore,
            data.program.compile(direct).explicitCore
        );
        assert.equal(
            compiled.structuralPrerequisites.includes(
                'constant-functor-abstraction'
            ),
            true
        );
        assert.equal(
            compiled.structuralPrerequisites.includes(
                'evaluation-functor'
            ),
            true
        );
    });

    it('selects whole-Hom action from one neutral application node', () => {
        const data = fixture();
        const parsed = elaborateCoreCategoricalText(
            data.program,
            {
                source: 'G pA',
                sourceFile,
                environment: data.environment,
                expected: {
                    kind: 'term',
                    applicationShape: 'whole-hom-action'
                }
            }
        );
        const direct = data.program.apply(data.G, data.pA, {
            expectedShape: 'whole-hom-action'
        });
        const compiled = data.program.compile(parsed);

        assert.equal(data.program.compare(parsed, direct).status, 'equal');
        assert.equal(
            compiled.explicitCore.includes('"functor-hom-full"'),
            true
        );
    });

    it('forwards expected application shape only to the root apply', () => {
        const calls: Array<string | undefined> = [];
        const opaqueTerm = (): CoreCategoricalTerm =>
            Object.freeze({}) as CoreCategoricalTerm;
        const program = {
            inspect: () => Object.freeze({}),
            apply: (
                _subject: CoreCategoricalTerm,
                _argument:
                    | CoreCategoricalTerm
                    | CoreCategoricalHomBoundary,
                options: { readonly expectedShape?: string }
            ) => {
                calls.push(options.expectedShape);
                return opaqueTerm();
            }
        } as unknown as CoreCategoricalProgram;
        elaborateCoreCategoricalText(
            program,
            {
                source: 'F x y',
                sourceFile,
                environment: [
                    termBinding('F', opaqueTerm()),
                    termBinding('x', opaqueTerm()),
                    termBinding('y', opaqueTerm())
                ],
                expected: {
                    kind: 'term',
                    applicationShape: 'whole-hom-action'
                }
            }
        );

        assert.deepEqual(calls, [undefined, 'whole-hom-action']);
    });

    it('retains zero, one, and two binder-use structural evidence', () => {
        const data = fixture();
        const cases = [
            {
                source: 'λ^f x. c',
                direct: data.program.lambda(
                    'x',
                    data.A,
                    data.C,
                    () => data.c
                )
            },
            {
                source: 'λ^f x. G x',
                direct: data.program.lambda(
                    'x',
                    data.A,
                    data.B,
                    x => data.program.apply(data.G, x)
                ),
                target: data.B
            },
            {
                source: 'λ^f x. (D x) x',
                direct: data.program.lambda(
                    'x',
                    data.A,
                    data.C,
                    x => data.program.apply(
                        data.program.apply(data.D, x),
                        x
                    )
                )
            }
        ] as const;

        for (const testCase of cases) {
            const parsed = textLambda(
                data,
                testCase.source,
                'target' in testCase
                    ? testCase.target
                    : data.C
            );
            assert.equal(
                data.program.compare(parsed, testCase.direct).status,
                'equal'
            );
            assert.equal(
                data.program.compile(parsed).explicitCore,
                data.program.compile(testCase.direct).explicitCore
            );
        }

        assert.deepEqual(
            data.program.compile(
                textLambda(data, cases[0].source)
            ).structuralPrerequisites,
            ['constant-functor-abstraction']
        );
        assert.equal(
            data.program.compile(
                textLambda(data, cases[2].source)
            ).structuralPrerequisites.includes(
                'diagonal-functor-abstraction'
            ),
            true
        );
    });

    it('reports parsing failures at exact end-exclusive spans', () => {
        const data = fixture();
        const empty = captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: '',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'UNEXPECTED_END'
        );
        assert.deepEqual(empty.span.start, { line: 1, column: 1 });
        assert.deepEqual(empty.span.end, { line: 1, column: 1 });

        const token = captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'G )',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'UNEXPECTED_TOKEN'
        );
        assert.deepEqual(token.span.start, { line: 1, column: 3 });
        assert.deepEqual(token.span.end, { line: 1, column: 4 });

        const identifier = captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: '_bad',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'INVALID_IDENTIFIER'
        );
        assert.deepEqual(
            identifier.span.start,
            { line: 1, column: 1 }
        );
    });

    it('distinguishes lexical and expected-routing failures', () => {
        const data = fixture();
        captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'missing',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'UNKNOWN_IDENTIFIER'
        );
        captureTextError(
            () => textLambda(data, 'λ^f x : c. x'),
            'EXPECTED_CATEGORY'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'A',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'EXPECTED_TERM'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'G A',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'EXPECTED_ARGUMENT'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'λ^f x. x',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'MISSING_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'λ^f x : A. x',
                sourceFile,
                environment: data.environment,
                expected: {
                    kind: 'ordinary-functor',
                    source: data.B,
                    target: data.A
                }
            }),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        for (const mode of ['n', 'fd', 'nd']) {
            captureTextError(
                () => textLambda(data, `λ^${mode} x. x`),
                'UNSUPPORTED_BINDER_MODE'
            );
        }
        captureTextError(
            () => textLambda(
                data,
                'λ^f x. λ^f y : B. c',
                data.functorsBC
            ),
            'UNSUPPORTED_NESTED_ABSTRACTION'
        );
    });

    it('rejects duplicate host names before resolution', () => {
        const data = fixture();
        const duplicate = [
            ...data.environment,
            categoryBinding('A', data.A)
        ];
        const error = captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'G',
                sourceFile,
                environment: duplicate,
                expected: { kind: 'term' }
            }),
            'DUPLICATE_BINDING'
        );
        assert.deepEqual(error.span.start, { line: 1, column: 1 });
        assert.deepEqual(error.span.end, { line: 1, column: 1 });
    });

    it('preserves parenthesized multiline spans on categorical rejection', () => {
        const data = fixture();
        const source = '(G\n c)';
        const error = captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source,
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }),
            'CATEGORICAL_REJECTION'
        );
        assert.deepEqual(error.span.start, { line: 1, column: 1 });
        assert.deepEqual(error.span.end, { line: 2, column: 4 });
        assert.equal(error.underlying instanceof Error, true);
    });

    it('rejects a bare foreign term at the existing program boundary', () => {
        const data = fixture();
        const foreignProgram = new CoreCategoricalProgram();
        const foreignCategory = foreignProgram.category('foreign_A');
        const foreign = foreignProgram.object(
            'foreign_x',
            foreignCategory
        );
        const error = captureTextError(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'foreign',
                sourceFile,
                environment: [termBinding('foreign', foreign)],
                expected: { kind: 'term' }
            }),
            'CATEGORICAL_REJECTION'
        );

        assert.equal(error.underlying instanceof Error, true);
        assert.equal(
            (error.underlying as Error).message.includes(
                'another scoped builder'
            ),
            true
        );
    });

    it('has no Node builtin or parser-package dependency', () => {
        const root = resolve(__dirname, '..');
        const source = readFileSync(
            resolve(root, 'src/v3_2/categorical_text.ts'),
            'utf8'
        );
        const packageSource = readFileSync(
            resolve(root, 'package.json'),
            'utf8'
        );
        const lockSource = readFileSync(
            resolve(root, 'pnpm-lock.yaml'),
            'utf8'
        );

        assert.equal(/from ['"]node:/.test(source), false);
        assert.equal(/\brequire\s*\(/.test(source), false);
        assert.equal(/parsimmon/i.test(packageSource), false);
        assert.equal(/parsimmon/i.test(lockSource), false);
    });
});
