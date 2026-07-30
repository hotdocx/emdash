/**
 * Focused SYNTAX-PARITY-1D1 nested ordinary-abstraction corpus.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_REVISION,
    CoreCategoricalProgram,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    CoreCategoricalTextOrdinaryFunctorExpected,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-nested-ordinary.emdash';

const fixture = () => {
    const program = new CoreCategoricalProgram({ sourceFile });
    const A = program.category('nested_text_A');
    const B = program.category('nested_text_B');
    const C = program.category('nested_text_C');
    const D = program.category('nested_text_D');
    const functorsAC = program.functorCategory(A, C);
    const functorsBC = program.functorCategory(B, C);
    const functorsCD = program.functorCategory(C, D);
    const functorsBCD = program.functorCategory(B, functorsCD);
    const E = program.functor('nested_text_E', B, functorsAC);
    const Q = program.functor('nested_text_Q', B, D);
    const R = program.functor('nested_text_R', A, functorsBCD);
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'A', kind: 'category', value: A },
            { name: 'B', kind: 'category', value: B },
            { name: 'C', kind: 'category', value: C },
            { name: 'D', kind: 'category', value: D },
            { name: 'E', kind: 'term', value: E },
            { name: 'Q', kind: 'term', value: Q },
            { name: 'R', kind: 'term', value: R }
        ]);
    return {
        program,
        A,
        B,
        C,
        D,
        functorsBC,
        functorsCD,
        functorsBCD,
        E,
        Q,
        R,
        environment
    };
};

const elaborate = (
    data: ReturnType<typeof fixture>,
    source: string,
    expected: CoreCategoricalTextOrdinaryFunctorExpected,
    environment = data.environment
): CoreCategoricalTerm => elaborateCoreCategoricalText(
    data.program,
    {
        source,
        sourceFile,
        environment,
        expected
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
    assert.equal(diagnostic.span.file, sourceFile);
    return diagnostic;
};

const assertDirectEquality = (
    data: ReturnType<typeof fixture>,
    source: string,
    expected: CoreCategoricalTextOrdinaryFunctorExpected,
    direct: CoreCategoricalTerm
): void => {
    const parsed = elaborate(data, source, expected);
    const parsedCompilation = data.program.compile(parsed);
    const directCompilation = data.program.compile(direct);
    assert.equal(
        parsedCompilation.explicitCore,
        directCompilation.explicitCore
    );
    assert.equal(
        parsedCompilation.explicitInferredType,
        directCompilation.explicitInferredType
    );
    assert.equal(
        data.program.compare(parsed, direct, 60_000).status,
        'equal'
    );
};

describe('SYNTAX-PARITY-1D1 nested ordinary text', () => {
    it('matches the reviewed exchange/currying construction exactly', () => {
        const data = fixture();
        const expected: CoreCategoricalTextOrdinaryFunctorExpected = {
            kind: 'ordinary-functor',
            source: data.A,
            target: data.functorsBC,
            bodyExpected: {
                kind: 'ordinary-functor',
                source: data.B,
                target: data.C
            }
        };
        const direct = data.program.lambda(
            'x',
            data.A,
            data.functorsBC,
            x => data.program.lambda(
                'y',
                data.B,
                data.C,
                y => data.program.apply(
                    data.program.apply(data.E, y),
                    x
                )
            )
        );

        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'SYNTAX-PARITY-1D1-CATEGORICAL-TEXT-1'
        );
        assertDirectEquality(
            data,
            'λ^f x : A. λ^f y : B. E y x',
            expected,
            direct
        );
    });

    it('recurses only to the finite depth in the expected tree', () => {
        const data = fixture();
        const expected: CoreCategoricalTextOrdinaryFunctorExpected = {
            kind: 'ordinary-functor',
            source: data.A,
            target: data.functorsBCD,
            bodyExpected: {
                kind: 'ordinary-functor',
                source: data.B,
                target: data.functorsCD,
                bodyExpected: {
                    kind: 'ordinary-functor',
                    source: data.C,
                    target: data.D
                }
            }
        };
        const direct = data.program.lambda(
            'x',
            data.A,
            data.functorsBCD,
            x => data.program.lambda(
                'y',
                data.B,
                data.functorsCD,
                y => data.program.lambda(
                    'z',
                    data.C,
                    data.D,
                    z => data.program.apply(
                        data.program.apply(
                            data.program.apply(data.R, x),
                            y
                        ),
                        z
                    )
                )
            )
        );

        assertDirectEquality(
            data,
            'λ^f x : A. λ^f y : B. λ^f z : C. R x y z',
            expected,
            direct
        );
    });

    it('requires an exact recursive contract at every nested lambda', () => {
        const data = fixture();
        const withoutBodyExpected:
            CoreCategoricalTextOrdinaryFunctorExpected = {
                kind: 'ordinary-functor',
                source: data.A,
                target: data.functorsBC
            };
        const missing = captureTextError(
            () => elaborate(
                data,
                'λ^f x : A. λ^f y : B. E y x',
                withoutBodyExpected
            ),
            'UNSUPPORTED_NESTED_ABSTRACTION'
        );
        assert.equal(missing.span.start.column, 12);

        const withBodyExpected:
            CoreCategoricalTextOrdinaryFunctorExpected = {
                ...withoutBodyExpected,
                bodyExpected: {
                    kind: 'ordinary-functor',
                    source: data.B,
                    target: data.C
                }
            };
        captureTextError(
            () => elaborate(
                data,
                'λ^f x : A. E',
                withBodyExpected
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^f x : A. λ^n y : B. E y x',
                withBodyExpected
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^f x : A. λ^f y : A. E y x',
                withBodyExpected
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
    });

    it('leaves classifier, program ownership, and body checks fail-closed',
        () => {
            const data = fixture();
            captureTextError(
                () => elaborate(
                    data,
                    'λ^f x : A. λ^f y : B. Q y',
                    {
                        kind: 'ordinary-functor',
                        source: data.A,
                        target: data.functorsBC,
                        bodyExpected: {
                            kind: 'ordinary-functor',
                            source: data.B,
                            target: data.D
                        }
                    }
                ),
                'CATEGORICAL_REJECTION'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^f x : A. λ^f y : B. E x y',
                    {
                        kind: 'ordinary-functor',
                        source: data.A,
                        target: data.functorsBC,
                        bodyExpected: {
                            kind: 'ordinary-functor',
                            source: data.B,
                            target: data.C
                        }
                    }
                ),
                'CATEGORICAL_REJECTION'
            );

            const foreign = new CoreCategoricalProgram();
            const foreignB = foreign.category('nested_text_foreign_B');
            captureTextError(
                () => elaborate(
                    data,
                    'λ^f x : A. λ^f y. E y x',
                    {
                        kind: 'ordinary-functor',
                        source: data.A,
                        target: data.functorsBC,
                        bodyExpected: {
                            kind: 'ordinary-functor',
                            source: foreignB,
                            target: data.C
                        }
                    }
                ),
                'CATEGORICAL_REJECTION'
            );
        });
});
