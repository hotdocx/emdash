/**
 * Focused SYNTAX-PARITY-1A text/direct-TypeScript equivalence corpus.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalCategory,
    CoreCategoricalDisplayedFamily,
    CoreCategoricalProgram
} from '../src/v3_2/categorical_program';
import {
    CoreCategoricalTerm
} from '../src/v3_2/categorical_surface';
import {
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    CoreCategoricalTextExpected,
    elaborateCoreCategoricalText
} from '../src/v3_2/categorical_text';

const sourceFile =
    'tests/fixtures/categorical-text-parity.emdash';

interface TextParityFixture {
    readonly program: CoreCategoricalProgram;
    readonly K: CoreCategoricalCategory;
    readonly L: CoreCategoricalCategory;
    readonly E: CoreCategoricalDisplayedFamily;
    readonly D: CoreCategoricalDisplayedFamily;
    readonly Q: CoreCategoricalDisplayedFamily;
    readonly R: CoreCategoricalDisplayedFamily;
    readonly FF: CoreCategoricalTerm;
    readonly GG: CoreCategoricalTerm;
    readonly s: CoreCategoricalTerm;
    readonly F0: CoreCategoricalTerm;
    readonly F1: CoreCategoricalTerm;
    readonly F2: CoreCategoricalTerm;
    readonly F3: CoreCategoricalTerm;
    readonly eta: CoreCategoricalTerm;
    readonly theta: CoreCategoricalTerm;
    readonly iota: CoreCategoricalTerm;
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

const familyBinding = (
    name: string,
    value: CoreCategoricalDisplayedFamily
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'displayed-family' as const,
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

const fixture = (): TextParityFixture => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-transfd-1'
    });
    const K = program.category('text_parity_K');
    const L = program.category('text_parity_L');
    const E = program.displayedFamily('text_parity_E', K);
    const D = program.displayedFamily('text_parity_D', K);
    const Q = program.displayedFamily('text_parity_Q', K);
    const R = program.displayedFamily('text_parity_R', K);
    const FF = program.displayedFunctor('text_parity_FF', E, D);
    const GG = program.displayedFunctor('text_parity_GG', D, Q);
    const s = program.section('text_parity_s', E);
    const F0 = program.displayedFunctor('text_parity_F0', E, D);
    const F1 = program.displayedFunctor('text_parity_F1', E, D);
    const F2 = program.displayedFunctor('text_parity_F2', E, D);
    const F3 = program.displayedFunctor('text_parity_F3', E, D);
    const eta = program.displayedTransfor(
        'text_parity_eta',
        F0,
        F1
    );
    const theta = program.displayedTransfor(
        'text_parity_theta',
        F1,
        F2
    );
    const iota = program.displayedTransfor(
        'text_parity_iota',
        F2,
        F3
    );
    return Object.freeze({
        program,
        K,
        L,
        E,
        D,
        Q,
        R,
        FF,
        GG,
        s,
        F0,
        F1,
        F2,
        F3,
        eta,
        theta,
        iota,
        environment: Object.freeze([
            categoryBinding('K', K),
            categoryBinding('L', L),
            familyBinding('E', E),
            familyBinding('D', D),
            familyBinding('Q', Q),
            familyBinding('R', R),
            termBinding('FF', FF),
            termBinding('GG', GG),
            termBinding('s', s),
            termBinding('F0', F0),
            termBinding('F1', F1),
            termBinding('F2', F2),
            termBinding('F3', F3),
            termBinding('eta', eta),
            termBinding('theta', theta),
            termBinding('iota', iota)
        ])
    });
};

const data = fixture();

const elaborate = (
    source: string,
    expected: CoreCategoricalTextExpected,
    program = data.program,
    environment = data.environment
): CoreCategoricalTerm => elaborateCoreCategoricalText(program, {
    source,
    sourceFile,
    environment,
    expected
});

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

const assertDirectEquality = (
    parsed: CoreCategoricalTerm,
    direct: CoreCategoricalTerm,
    rule: string
): void => {
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
        parsedCompilation.explicitExpectedType,
        directCompilation.explicitExpectedType
    );
    assert.equal(data.program.compare(parsed, direct).status, 'equal');
    assert.equal(
        data.program.inspect(parsed).abstractions.at(-1)?.rule,
        rule
    );
};

describe('SYNTAX-PARITY-1A categorical binder modes', () => {
    it('matches direct indexed-section composition for ^n', () => {
        const parsed = elaborate(
            'λ^n k : K. (FF k) (s k)',
            {
                kind: 'dependent-section',
                base: data.K,
                target: data.D
            }
        );
        const direct = data.program.dependentLambda(
            'k',
            data.D,
            k => data.program.apply(
                data.program.apply(data.FF, k),
                data.program.apply(data.s, k)
            )
        );
        assertDirectEquality(
            parsed,
            direct,
            'categorical.dependent-section-composition'
        );
    });

    it('matches direct displayed-functor composition for ^fd', () => {
        const parsed = elaborate(
            'λ^fd a : E. GG (FF a)',
            {
                kind: 'displayed-functor',
                source: data.E,
                target: data.Q
            }
        );
        const direct = data.program.displayedFunctorLambda(
            'a',
            data.E,
            data.Q,
            a => data.program.apply(
                data.GG,
                data.program.apply(data.FF, a)
            )
        );
        assertDirectEquality(
            parsed,
            direct,
            'categorical.displayed-functor-composition'
        );
    });

    it('matches recursive coherent component composition for ^nd', () => {
        const parsed = elaborate(
            'λ^nd k : K. composeCells (theta k) (eta k)',
            {
                kind: 'displayed-transfor',
                base: data.K,
                source: data.F0,
                target: data.F2
            }
        );
        const direct = data.program.displayedTransforLambda(
            'k',
            data.F0,
            data.F2,
            k => data.program.composeCells(
                data.program.apply(data.theta, k),
                data.program.apply(data.eta, k)
            )
        );
        assertDirectEquality(
            parsed,
            direct,
            'categorical.displayed-transfor-composition'
        );
    });

    it('retains eta, identity, optional annotations, and nested cells', () => {
        const sectionEta = elaborate(
            'λ^n k. s k',
            {
                kind: 'dependent-section',
                base: data.K,
                target: data.E
            }
        );
        assert.equal(
            data.program.compare(sectionEta, data.s).status,
            'equal'
        );

        const identity = elaborate(
            'λ^fd a. a',
            {
                kind: 'displayed-functor',
                source: data.E,
                target: data.E
            }
        );
        assert.equal(
            data.program.inspect(identity).abstractions.at(-1)?.rule,
            'categorical.displayed-functor-identity'
        );

        const transforEta = elaborate(
            'λ^nd k. eta k',
            {
                kind: 'displayed-transfor',
                base: data.K,
                source: data.F0,
                target: data.F1
            }
        );
        assert.equal(
            data.program.compare(transforEta, data.eta).status,
            'equal'
        );

        const nested = elaborate(
            'λ^nd k. composeCells (iota k) ' +
                '(composeCells (theta k) (eta k))',
            {
                kind: 'displayed-transfor',
                base: data.K,
                source: data.F0,
                target: data.F3
            }
        );
        const directNested = data.program.composeDisplayedTransfor(
            data.iota,
            data.program.composeDisplayedTransfor(
                data.theta,
                data.eta
            )
        );
        assert.equal(
            data.program.compare(nested, directNested).status,
            'equal'
        );
        assert.equal(
            data.program.inspect(nested).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-composition'
        );
    });

    it('rejects wrong annotation kinds at their exact source spans', () => {
        const natural = captureTextError(
            () => elaborate(
                'λ^n k : E. s k',
                {
                    kind: 'dependent-section',
                    base: data.K,
                    target: data.E
                }
            ),
            'EXPECTED_CATEGORY'
        );
        assert.deepEqual(natural.span, {
            file: sourceFile,
            start: { line: 1, column: 9 },
            end: { line: 1, column: 10 }
        });

        const displayed = captureTextError(
            () => elaborate(
                'λ^fd a : K. a',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.E
                }
            ),
            'EXPECTED_DISPLAYED_FAMILY'
        );
        assert.deepEqual(displayed.span, {
            file: sourceFile,
            start: { line: 1, column: 10 },
            end: { line: 1, column: 11 }
        });
    });

    it('rejects incompatible annotations and expected binder modes', () => {
        const wrongBase = captureTextError(
            () => elaborate(
                'λ^nd k : L. eta k',
                {
                    kind: 'displayed-transfor',
                    base: data.K,
                    source: data.F0,
                    target: data.F1
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.equal(wrongBase.span.start.column, 10);

        const wrongFamily = captureTextError(
            () => elaborate(
                'λ^fd a : D. FF a',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.D
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.equal(wrongFamily.span.start.column, 10);

        const wrongMode = captureTextError(
            () => elaborate(
                'λ^n k. s k',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.E
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.equal(wrongMode.span.start.column, 1);
    });

    it('preserves profile, endpoint, coherence, and nesting boundaries', () => {
        const unavailable = new CoreCategoricalProgram();
        const unavailableError = captureTextError(
            () => elaborate(
                'λ^nd k. eta k',
                {
                    kind: 'displayed-transfor',
                    base: data.K,
                    source: data.F0,
                    target: data.F1
                },
                unavailable,
                [
                    termBinding('eta', data.eta)
                ]
            ),
            'CATEGORICAL_REJECTION'
        );
        assert.equal(
            (unavailableError.underlying as { readonly code?: string })
                .code,
            'UNAVAILABLE_FIBRED_TRANSFD'
        );

        captureTextError(
            () => elaborate(
                'λ^fd a. FF a',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.Q
                }
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                'λ^nd k. composeCells (eta k) (theta k)',
                {
                    kind: 'displayed-transfor',
                    base: data.K,
                    source: data.F1,
                    target: data.F1
                }
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                'λ^nd k. eta',
                {
                    kind: 'displayed-transfor',
                    base: data.K,
                    source: data.F0,
                    target: data.F1
                }
            ),
            'CATEGORICAL_REJECTION'
        );
        const nested = captureTextError(
            () => elaborate(
                'λ^n k. λ^fd a. a',
                {
                    kind: 'dependent-section',
                    base: data.K,
                    target: data.E
                }
            ),
            'UNSUPPORTED_NESTED_ABSTRACTION'
        );
        assert.equal(nested.span.start.column, 8);
    });

    it('keeps unreviewed modes and non-lambda expectations fail-closed', () => {
        const unsupported = captureTextError(
            () => elaborate(
                'λ^o x. x',
                {
                    kind: 'displayed-functor',
                    source: data.E,
                    target: data.E
                }
            ),
            'UNSUPPORTED_BINDER_MODE'
        );
        assert.equal(unsupported.span.start.column, 2);

        const noLambda = captureTextError(
            () => elaborate(
                'eta',
                {
                    kind: 'displayed-transfor',
                    base: data.K,
                    source: data.F0,
                    target: data.F1
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.equal(noLambda.span.start.column, 1);
    });
});
