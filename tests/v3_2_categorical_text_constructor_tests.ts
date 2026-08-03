/**
 * Focused SYNTAX-PARITY-1C1 ordinary constructor text corpus.
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
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-constructor.emdash';

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-displayed-chain-2a'
    });
    const A = program.category('constructor_text_A');
    const B = program.category('constructor_text_B');
    const C = program.category('constructor_text_C');
    const X = program.category('constructor_text_X');
    const Y = program.category('constructor_text_Y');
    const F = program.functor('constructor_text_F', A, B);
    const G = program.functor('constructor_text_G', B, C);
    const H = program.functor('constructor_text_H', A, C);
    const P = program.functor('constructor_text_P', X, Y);
    const a = program.object('constructor_text_a', A);
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'A', kind: 'category', value: A },
            { name: 'B', kind: 'category', value: B },
            { name: 'C', kind: 'category', value: C },
            { name: 'X', kind: 'category', value: X },
            { name: 'Y', kind: 'category', value: Y },
            { name: 'F', kind: 'term', value: F },
            { name: 'G', kind: 'term', value: G },
            { name: 'H', kind: 'term', value: H },
            { name: 'P', kind: 'term', value: P },
            { name: 'a', kind: 'term', value: a }
        ]);
    return {
        program,
        A,
        B,
        C,
        X,
        Y,
        F,
        G,
        H,
        P,
        a,
        environment
    };
};

const elaborate = (
    data: ReturnType<typeof fixture>,
    source: string,
    environment = data.environment
): CoreCategoricalTerm => elaborateCoreCategoricalText(
    data.program,
    {
        source,
        sourceFile,
        environment,
        expected: { kind: 'term' }
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
    direct: CoreCategoricalTerm
): void => {
    const parsed = elaborate(data, source);
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

describe('SYNTAX-PARITY-1C1 ordinary constructor text', () => {
    it('matches all six existing structural methods exactly', () => {
        const data = fixture();
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'COMPOSITIONAL-NATURAL-TEXT-PARITY-1D-CATEGORICAL-TEXT-1'
        );
        for (const [source, direct] of [
            ['id A', data.program.identityFunctor(data.A)],
            [
                'compose G F',
                data.program.composeFunctors(data.G, data.F)
            ],
            [
                'pair F H',
                data.program.functorPair(data.F, data.H)
            ],
            [
                'map F P',
                data.program.productMap(data.F, data.P)
            ],
            [
                'pi1 B C',
                data.program.productLeftProjection(data.B, data.C)
            ],
            [
                'pi2 B C',
                data.program.productRightProjection(data.B, data.C)
            ]
        ] as const) {
            assertDirectEquality(data, source, direct);
        }
    });

    it('resolves nested constructors and subsequent application recursively',
        () => {
            const data = fixture();
            assertDirectEquality(
                data,
                'compose (pi1 B C) (pair F H)',
                data.program.composeFunctors(
                    data.program.productLeftProjection(data.B, data.C),
                    data.program.functorPair(data.F, data.H)
                )
            );
            assertDirectEquality(
                data,
                'pair (compose G F) H',
                data.program.functorPair(
                    data.program.composeFunctors(data.G, data.F),
                    data.H
                )
            );
            assertDirectEquality(
                data,
                'map (compose G F) P',
                data.program.productMap(
                    data.program.composeFunctors(data.G, data.F),
                    data.P
                )
            );
            assertDirectEquality(
                data,
                'compose G F a',
                data.program.apply(
                    data.program.composeFunctors(data.G, data.F),
                    data.a
                )
            );
        });

    it('rejects non-category expressions in category positions', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(data, 'id F'),
            'EXPECTED_CATEGORY'
        );
        captureTextError(
            () => elaborate(data, 'pi1 F B'),
            'EXPECTED_CATEGORY'
        );
        captureTextError(
            () => elaborate(data, 'id (id A)'),
            'EXPECTED_CATEGORY'
        );
        captureTextError(
            () => elaborate(data, 'compose A F'),
            'EXPECTED_TERM'
        );
    });

    it('delegates endpoint and shared-source rejection to the program', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(data, 'compose F G'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'pair F G'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'map A P'),
            'EXPECTED_TERM'
        );
    });

    it('preserves reserved-head arity and ordinary application boundaries',
        () => {
            const data = fixture();
            captureTextError(
                () => elaborate(data, 'id'),
                'UNKNOWN_IDENTIFIER'
            );
            captureTextError(
                () => elaborate(data, 'pi1 A'),
                'UNKNOWN_IDENTIFIER'
            );
            const invalidApplication = captureTextError(
                () => elaborate(data, 'id A B'),
                'EXPECTED_ARGUMENT'
            );
            assert.equal(invalidApplication.phase, 'resolution');
        });

    it('rejects foreign categories and unavailable profiles', () => {
        const data = fixture();
        const foreignProgram = new CoreCategoricalProgram({
            sourceFile,
            profile: 'fibred-displayed-chain-2a'
        });
        const foreign = foreignProgram.category('foreign_A');
        const foreignEnvironment: readonly CoreCategoricalTextBinding[] =
            Object.freeze([
                ...data.environment,
                {
                    name: 'Foreign',
                    kind: 'category' as const,
                    value: foreign
                }
            ]);
        captureTextError(
            () => elaborate(data, 'id Foreign', foreignEnvironment),
            'CATEGORICAL_REJECTION'
        );

        const predecessor = new CoreCategoricalProgram({
            sourceFile,
            profile: 'reviewed-usability-2a1'
        });
        const A = predecessor.category('predecessor_A');
        const B = predecessor.category('predecessor_B');
        const C = predecessor.category('predecessor_C');
        const F = predecessor.functor('predecessor_F', A, B);
        const G = predecessor.functor('predecessor_G', B, C);
        assert.throws(
            () => elaborateCoreCategoricalText(predecessor, {
                source: 'compose G F',
                sourceFile,
                environment: [
                    { name: 'F', kind: 'term', value: F },
                    { name: 'G', kind: 'term', value: G }
                ],
                expected: { kind: 'term' }
            }),
            error =>
                error instanceof CoreCategoricalTextError &&
                error.code === 'CATEGORICAL_REJECTION'
        );
    });
});
