/**
 * Focused SYNTAX-PARITY-1B1 contextual-index text corpus.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramOptions
} from '../src/v3_2/categorical_program';
import {
    CoreCategoricalSlotToken,
    CoreCategoricalTerm
} from '../src/v3_2/categorical_surface';
import {
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    CoreCategoricalTextTermExpected,
    elaborateCoreCategoricalText
} from '../src/v3_2/categorical_text';

const sourceFile =
    'tests/fixtures/categorical-text-structural.emdash';

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

const fixture = (
    profile: NonNullable<CoreCategoricalProgramOptions['profile']> =
        'fibred-weaken-reindex-1'
) => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile
    });
    const K = program.category('structural_K');
    const E = program.displayedFamily('structural_E', K);
    const D = program.displayedFamily('structural_D', K);
    const Q = program.displayedFamily('structural_Q', K);
    const s = program.section('structural_s', D);
    const environment: CoreCategoricalTextBinding[] = [
        { name: 'K', kind: 'category', value: K },
        { name: 'E', kind: 'displayed-family', value: E },
        { name: 'D', kind: 'displayed-family', value: D },
        { name: 'Q', kind: 'displayed-family', value: Q },
        { name: 's', kind: 'term', value: s }
    ];
    return {
        program,
        K,
        E,
        D,
        Q,
        s,
        environment
    };
};

const elaborate = (
    program: CoreCategoricalProgram,
    environment: readonly CoreCategoricalTextBinding[],
    source: string,
    expected: CoreCategoricalTextTermExpected
): CoreCategoricalTerm => elaborateCoreCategoricalText(program, {
    source,
    sourceFile,
    environment,
    expected
});

describe('SYNTAX-PARITY-1B1 contextual index', () => {
    it('matches direct displayed weakening exactly', () => {
        const {
            program,
            E,
            D,
            s,
            environment
        } = fixture();
        const parsed = elaborate(
            program,
            environment,
            'λ^fd a : E. s (indexOf a)',
            {
                kind: 'displayed-functor',
                source: E,
                target: D
            }
        );
        const direct = program.displayedFunctorLambda(
            'a',
            E,
            D,
            a => program.apply(s, program.indexOf(a))
        );
        const parsedCompilation = program.compile(parsed);
        const directCompilation = program.compile(direct);
        assert.equal(
            parsedCompilation.explicitCore,
            directCompilation.explicitCore
        );
        assert.equal(
            parsedCompilation.explicitInferredType,
            directCompilation.explicitInferredType
        );
        assert.equal(
            parsedCompilation.explicitExpectedType,
            directCompilation.explicitExpectedType
        );
        assert.equal(program.compare(parsed, direct).status, 'equal');
        assert.equal(
            parsedCompilation.abstractions.at(-1)?.rule,
            'categorical.displayed-functor-weakening'
        );
        assert.match(
            parsedCompilation.explicitCore,
            /emdash\.categorical\.section-pullback/u
        );
        assert.match(
            parsedCompilation.explicitCore,
            /emdash\.categorical\.sigma-first-projection/u
        );
    });

    it('infers the optional family annotation from expectation', () => {
        const {
            program,
            E,
            D,
            environment
        } = fixture();
        const annotated = elaborate(
            program,
            environment,
            'λ^fd a : E. s (indexOf a)',
            {
                kind: 'displayed-functor',
                source: E,
                target: D
            }
        );
        const inferred = elaborate(
            program,
            environment,
            'λ^fd a. s (indexOf a)',
            {
                kind: 'displayed-functor',
                source: E,
                target: D
            }
        );
        assert.equal(
            program.compare(annotated, inferred).status,
            'equal'
        );
    });

    it('delegates unavailable profiles and wrong targets to the program',
        () => {
            const unavailable = fixture('fibred-binder-1');
            const profileError = captureTextError(
                () => elaborate(
                    unavailable.program,
                    unavailable.environment,
                    'λ^fd a : E. s (indexOf a)',
                    {
                        kind: 'displayed-functor',
                        source: unavailable.E,
                        target: unavailable.D
                    }
                ),
                'CATEGORICAL_REJECTION'
            );
            assert.equal(
                (profileError.underlying as {
                    readonly code?: string;
                }).code,
                'UNAVAILABLE_WEAKEN_REINDEX'
            );

            const data = fixture();
            const targetError = captureTextError(
                () => elaborate(
                    data.program,
                    data.environment,
                    'λ^fd a : E. s (indexOf a)',
                    {
                        kind: 'displayed-functor',
                        source: data.E,
                        target: data.Q
                    }
                ),
                'CATEGORICAL_REJECTION'
            );
            assert.equal(targetError.span.start.column, 1);
        });

    it('rejects closed and foreign terms as contextual indices', () => {
        const data = fixture();
        const k = data.program.object('structural_k', data.K);
        const fibre = data.program.fibre(data.E, k);
        const closed = data.program.object('structural_a0', fibre);
        const closedError = captureTextError(
            () => elaborate(
                data.program,
                [
                    ...data.environment,
                    { name: 'a0', kind: 'term', value: closed }
                ],
                'indexOf a0',
                { kind: 'term' }
            ),
            'CATEGORICAL_REJECTION'
        );
        assert.equal(closedError.span.start.column, 1);

        const foreign = fixture();
        let foreignToken: CoreCategoricalSlotToken | undefined;
        foreign.program.displayedFunctorLambda(
            'foreign',
            foreign.E,
            foreign.E,
            token => {
                foreignToken = token;
                return token;
            }
        );
        assert.notEqual(foreignToken, undefined);
        const foreignError = captureTextError(
            () => elaborate(
                data.program,
                [
                    ...data.environment,
                    {
                        name: 'foreign',
                        kind: 'term',
                        value: foreignToken as CoreCategoricalSlotToken
                    }
                ],
                'indexOf foreign',
                { kind: 'term' }
            ),
            'CATEGORICAL_REJECTION'
        );
        assert.deepEqual(foreignError.span, {
            file: sourceFile,
            start: { line: 1, column: 9 },
            end: { line: 1, column: 16 }
        });
    });

    it('keeps wrong arities fail-closed at exact spans', () => {
        const data = fixture();
        const missing = captureTextError(
            () => elaborate(
                data.program,
                data.environment,
                'λ^fd a : E. s indexOf',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.D
                }
            ),
            'UNKNOWN_IDENTIFIER'
        );
        assert.deepEqual(missing.span, {
            file: sourceFile,
            start: { line: 1, column: 15 },
            end: { line: 1, column: 22 }
        });

        const extra = captureTextError(
            () => elaborate(
                data.program,
                data.environment,
                'λ^fd a : E. s (indexOf a a)',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.D
                }
            ),
            'CATEGORICAL_REJECTION'
        );
        assert.equal(extra.span.start.column, 15);
    });
});
