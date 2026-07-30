/**
 * Focused SYNTAX-PARITY-1B2 independent-sibling text corpus.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalDisplayedFamily,
    CoreCategoricalProgram,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    CoreCategoricalTextExpected,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-sibling.emdash';

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

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-displayed-bracket-1'
    });
    const K = program.category('sibling_K');
    const B = program.displayedFamily('sibling_B', K);
    const C = program.displayedFamily('sibling_C', K);
    const D = program.displayedFamily('sibling_D', K);
    const Q = program.displayedFamily('sibling_Q', K);
    const FF = program.displayedFunctor('sibling_FF', B, D);
    const GG = program.displayedFunctor('sibling_GG', C, Q);
    const target = program.displayedProduct(D, Q);
    const x = program.object('sibling_x', K);
    const y = program.object('sibling_y', K);
    const p = program.hom('sibling_p', K, x, y);
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            familyBinding('B', B),
            familyBinding('C', C),
            familyBinding('D', D),
            familyBinding('Q', Q),
            termBinding('FF', FF),
            termBinding('GG', GG),
            termBinding('x', x)
        ]);
    const expected: CoreCategoricalTextExpected = Object.freeze({
        kind: 'displayed-context-functor' as const,
        sources: Object.freeze([B, C]),
        target
    });
    return {
        program,
        K,
        B,
        C,
        D,
        Q,
        FF,
        GG,
        target,
        x,
        y,
        p,
        environment,
        expected
    };
};

const elaborate = (
    data: ReturnType<typeof fixture>,
    source: string,
    expected: CoreCategoricalTextExpected = data.expected,
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

describe('SYNTAX-PARITY-1B2 independent-sibling text', () => {
    it('matches the existing direct contextual compiler exactly', () => {
        const data = fixture();
        let callbacks = 0;
        const direct = data.program.displayedContextLambda(
            [
                { name: 'b', family: data.B },
                { name: 'c', family: data.C }
            ],
            data.target,
            ([b, c]) => {
                callbacks += 1;
                return data.program.fibrePair(
                    data.program.apply(data.FF, b),
                    data.program.apply(data.GG, c)
                );
            }
        );
        const parsed = elaborate(
            data,
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)'
        );
        assert.equal(callbacks, 1);

        const directCompilation = data.program.compile(direct);
        const parsedCompilation = data.program.compile(parsed);
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
        assert.deepEqual(
            parsedCompilation.structuralPrerequisites,
            directCompilation.structuralPrerequisites
        );
        assert.deepEqual(
            parsedCompilation.dependentPrerequisites,
            directCompilation.dependentPrerequisites
        );
        assert.equal(
            data.program.compare(parsed, direct, 12_000).status,
            'equal'
        );

        const trace = parsedCompilation.abstractions.at(-1);
        assert.equal(
            trace?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            trace?.rule !==
                'categorical.displayed-context-bracket'
        ) {
            assert.fail('Missing displayed-context lowering trace');
        }
        assert.deepEqual(trace.bindingNames, ['b', 'c']);
        assert.equal(
            trace.contextRelation,
            'shared-minimal-base-siblings'
        );
        assert.equal(trace.body.tag, 'typed-pair');
        for (const prerequisite of [
            'displayed-product-left-projection',
            'displayed-product-right-projection',
            'generic-category-composition',
            'displayed-product-pair'
        ]) {
            assert.equal(
                parsedCompilation.dependentPrerequisites.some(
                    candidate => candidate === prerequisite
                ),
                true
            );
        }
    });

    it('infers omitted sibling annotations positionally', () => {
        const data = fixture();
        const annotated = elaborate(
            data,
            'λ^fd (b : B, c : C). fibrePair (FF b) (GG c)'
        );
        const omitted = elaborate(
            data,
            'λ^fd (b, c). fibrePair (FF b) (GG c)',
            data.expected,
            data.environment.filter(binding =>
                binding.name !== 'B' && binding.name !== 'C'
            )
        );
        const mixed = elaborate(
            data,
            'λ^fd (b : B, c). fibrePair (FF b) (GG c)'
        );
        assert.equal(
            data.program.compare(annotated, omitted, 12_000).status,
            'equal'
        );
        assert.equal(
            data.program.compare(annotated, mixed, 12_000).status,
            'equal'
        );
        assert.equal(
            data.program.compile(annotated).explicitCore,
            data.program.compile(omitted).explicitCore
        );
    });

    it('preserves applicable object and internalized-arrow action', () => {
        const data = fixture();
        const parsed = elaborate(
            data,
            'λ^fd (b, c). fibrePair (FF b) (GG c)'
        );
        const direct = data.program.displayedContextLambda(
            [
                { name: 'b', family: data.B },
                { name: 'c', family: data.C }
            ],
            data.target,
            ([b, c]) => data.program.fibrePair(
                data.program.apply(data.FF, b),
                data.program.apply(data.GG, c)
            )
        );

        const parsedObjectAction = data.program.apply(
            parsed,
            data.x,
            { expectedShape: 'fibre-functor' }
        );
        const directObjectAction = data.program.apply(
            direct,
            data.x,
            { expectedShape: 'fibre-functor' }
        );
        assert.equal(
            data.program.compare(
                parsedObjectAction,
                directObjectAction,
                12_000
            ).status,
            'equal'
        );

        const projection = elaborate(
            data,
            'λ^fd (b : B, c : C). b',
            {
                kind: 'displayed-context-functor',
                sources: [data.B, data.C],
                target: data.B
            }
        );
        const cappedAction = data.program.apply(
            projection,
            data.p,
            { expectedShape: 'transport-functor' }
        );
        const fullAction = data.program.apply(
            data.program.displayedFunctorFullAction(
                projection,
                data.x,
                data.y
            ),
            data.p
        );
        assert.equal(
            data.program.compare(
                cappedAction,
                fullAction,
                12_000
            ).status,
            'equal'
        );
    });

    it('rejects malformed or dependency-level binder groups locally', () => {
        const data = fixture();
        const cases: readonly [
            source: string,
            code: CoreCategoricalTextErrorCode
        ][] = [
            [
                'λ^fd (). fibrePair (FF x) (GG x)',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (b : B). FF b',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (b : B,). FF b',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (b : B; c : C). fibrePair (FF b) (GG c)',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (b : B c : C). fibrePair (FF b) (GG c)',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (b : B, b : C). fibrePair (FF b) (GG b)',
                'DUPLICATE_BINDING'
            ]
        ];
        for (const [source, code] of cases) {
            const error = captureTextError(
                () => elaborate(data, source),
                code
            );
            assert.equal(error.phase, 'parsing');
            assert.ok(error.span.end.column >= error.span.start.column);
        }
    });

    it('checks expected sources, annotations, modes, and bases', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b) (GG c)',
                {
                    kind: 'displayed-context-functor',
                    sources: [data.B],
                    target: data.target
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b : C, c : C). fibrePair (FF b) (GG c)'
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b : FF, c : C). fibrePair (FF b) (GG c)'
            ),
            'EXPECTED_DISPLAYED_FAMILY'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^f (b, c). fibrePair (FF b) (GG c)'
            ),
            'UNSUPPORTED_BINDER_MODE'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b) (GG c)',
                { kind: 'term' }
            ),
            'MISSING_ABSTRACTION_EXPECTATION'
        );

        const other = data.program.category('sibling_other_base');
        const X = data.program.displayedFamily('sibling_X', other);
        const withX = Object.freeze([
            ...data.environment,
            familyBinding('X', X)
        ]);
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b) (GG c)',
                {
                    kind: 'displayed-context-functor',
                    sources: [data.B, X],
                    target: data.target
                },
                withX
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b) (GG c)',
                {
                    kind: 'displayed-context-functor',
                    sources: [data.B, data.C],
                    target: X
                },
                withX
            ),
            'CATEGORICAL_REJECTION'
        );
    });

    it('keeps fibrePair exact, contextual, and recursively typed', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b)'
            ),
            'UNKNOWN_IDENTIFIER'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b) (GG c) c'
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                data,
                'fibrePair x x',
                { kind: 'term' }
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                data,
                'λ^fd (b, c). fibrePair (FF b) (GG b)'
            ),
            'CATEGORICAL_REJECTION'
        );
    });
});
