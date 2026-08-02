/**
 * Focused SYNTAX-PARITY-1C2A displayed constructor text corpus.
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
    'tests/fixtures/categorical-text-displayed-constructor.emdash';

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-displayed-chain-2a'
    });
    const K = program.category('displayed_text_K');
    const X = program.category('displayed_text_X');
    const E = program.displayedFamily('displayed_text_E', K);
    const B = program.displayedFamily('displayed_text_B', K);
    const C = program.displayedFamily('displayed_text_C', K);
    const D = program.displayedFamily('displayed_text_D', X);
    const FF = program.displayedFunctor('displayed_text_FF', E, B);
    const GG = program.displayedFunctor('displayed_text_GG', E, C);
    const Q = program.displayedFunctor('displayed_text_Q', B, C);
    const F0 = program.displayedFunctor('displayed_text_F0', E, B);
    const F1 = program.displayedFunctor('displayed_text_F1', E, B);
    const F2 = program.displayedFunctor('displayed_text_F2', E, B);
    const F3 = program.displayedFunctor('displayed_text_F3', E, B);
    const eta = program.displayedTransfor(
        'displayed_text_eta',
        F0,
        F1
    );
    const theta = program.displayedTransfor(
        'displayed_text_theta',
        F1,
        F2
    );
    const iota = program.displayedTransfor(
        'displayed_text_iota',
        F2,
        F3
    );
    const x = program.object('displayed_text_x', K);
    const y = program.object('displayed_text_y', K);
    const p = program.hom('displayed_text_p', K, x, y);
    const u = program.object(
        'displayed_text_u',
        program.fibre(E, x)
    );
    const v = program.object(
        'displayed_text_v',
        program.fibre(E, y)
    );
    const w = program.object(
        'displayed_text_w',
        program.fibre(B, x)
    );
    const transportedU = program.apply(
        program.familyTransport(E, p),
        u
    );
    const alpha = program.hom(
        'displayed_text_alpha',
        program.fibre(E, y),
        transportedU,
        v
    );
    const F = program.functor('displayed_text_F', X, K);
    const R = program.functor('displayed_text_R', X, X);
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'K', kind: 'category', value: K },
            { name: 'X', kind: 'category', value: X },
            { name: 'E', kind: 'displayed-family', value: E },
            { name: 'B', kind: 'displayed-family', value: B },
            { name: 'C', kind: 'displayed-family', value: C },
            { name: 'D', kind: 'displayed-family', value: D },
            { name: 'FF', kind: 'term', value: FF },
            { name: 'GG', kind: 'term', value: GG },
            { name: 'Q', kind: 'term', value: Q },
            { name: 'F0', kind: 'term', value: F0 },
            { name: 'F1', kind: 'term', value: F1 },
            { name: 'F2', kind: 'term', value: F2 },
            { name: 'F3', kind: 'term', value: F3 },
            { name: 'eta', kind: 'term', value: eta },
            { name: 'theta', kind: 'term', value: theta },
            { name: 'iota', kind: 'term', value: iota },
            { name: 'x', kind: 'term', value: x },
            { name: 'y', kind: 'term', value: y },
            { name: 'p', kind: 'term', value: p },
            { name: 'u', kind: 'term', value: u },
            { name: 'v', kind: 'term', value: v },
            { name: 'w', kind: 'term', value: w },
            { name: 'alpha', kind: 'term', value: alpha },
            { name: 'F', kind: 'term', value: F },
            { name: 'R', kind: 'term', value: R }
        ]);
    return {
        program,
        K,
        X,
        E,
        B,
        C,
        D,
        FF,
        GG,
        Q,
        F0,
        F1,
        F2,
        F3,
        eta,
        theta,
        iota,
        x,
        y,
        p,
        u,
        v,
        w,
        alpha,
        F,
        R,
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

describe('SYNTAX-PARITY-1C2A displayed constructor text', () => {
    it('matches all twelve existing typed methods exactly', () => {
        const data = fixture();
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'CONTEXTUAL-ND-TEXT-PARITY-1AI-CATEGORICAL-TEXT-1'
        );
        for (const [source, direct] of [
            [
                'pi1d B C',
                data.program.displayedProductLeftProjection(
                    data.B,
                    data.C
                )
            ],
            [
                'pi2d B C',
                data.program.displayedProductRightProjection(
                    data.B,
                    data.C
                )
            ],
            [
                'paird FF GG',
                data.program.displayedProductPair(data.FF, data.GG)
            ],
            [
                'swapd B C',
                data.program.displayedProductSwap(data.B, data.C)
            ],
            [
                'diagd B',
                data.program.displayedProductDiagonal(data.B)
            ],
            [
                'sigmaProj E',
                data.program.sigmaProjection(data.E)
            ],
            [
                'pullbackFunctord FF F',
                data.program.pullbackDisplayedFunctor(data.FF, data.F)
            ],
            [
                'sigmaPair E x u',
                data.program.dependentPair(data.E, data.x, data.u)
            ],
            [
                'transport E p',
                data.program.familyTransport(data.E, data.p)
            ],
            [
                'sigmaArrow E u v p alpha',
                data.program.sigmaArrow(
                    data.E,
                    data.u,
                    data.v,
                    data.p,
                    data.alpha
                )
            ],
            [
                'pullbackTotal F E',
                data.program.pullbackTotal(data.F, data.E)
            ],
            [
                'composeTransfd theta eta',
                data.program.composeDisplayedTransfor(
                    data.theta,
                    data.eta
                )
            ]
        ] as const) {
            assertDirectEquality(data, source, direct);
        }
    });

    it('resolves term operands recursively and preserves application',
        () => {
            const data = fixture();
            assertDirectEquality(
                data,
                'composeTransfd iota (composeTransfd theta eta)',
                data.program.composeDisplayedTransfor(
                    data.iota,
                    data.program.composeDisplayedTransfor(
                        data.theta,
                        data.eta
                    )
                )
            );
            assertDirectEquality(
                data,
                'sigmaProj E (sigmaPair E x u)',
                data.program.apply(
                    data.program.sigmaProjection(data.E),
                    data.program.dependentPair(
                        data.E,
                        data.x,
                        data.u
                    )
                )
            );
        });

    it('rejects non-family expressions in family positions', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(data, 'pi1d K C'),
            'EXPECTED_DISPLAYED_FAMILY'
        );
        captureTextError(
            () => elaborate(data, 'sigmaProj FF'),
            'EXPECTED_DISPLAYED_FAMILY'
        );
        captureTextError(
            () => elaborate(data, 'diagd (sigmaProj E)'),
            'EXPECTED_DISPLAYED_FAMILY'
        );
        captureTextError(
            () => elaborate(data, 'paird E GG'),
            'EXPECTED_TERM'
        );
    });

    it('delegates categorical compatibility to the program', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(data, 'paird FF F'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'pi1d B D'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'paird FF Q'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'sigmaPair E x w'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'transport E alpha'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'sigmaArrow E v u p alpha'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'pullbackFunctord FF R'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'composeTransfd eta theta'),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(data, 'pullbackTotal R E'),
            'CATEGORICAL_REJECTION'
        );
    });

    it('preserves arity, foreign-family, and profile boundaries', () => {
        const data = fixture();
        captureTextError(
            () => elaborate(data, 'sigmaPair E x'),
            'UNKNOWN_IDENTIFIER'
        );
        captureTextError(
            () => elaborate(data, 'sigmaProj E x'),
            'CATEGORICAL_REJECTION'
        );

        const foreignProgram = new CoreCategoricalProgram({
            profile: 'fibred-displayed-chain-2a'
        });
        const foreignK = foreignProgram.category('foreign_K');
        const foreignE = foreignProgram.displayedFamily(
            'foreign_E',
            foreignK
        );
        captureTextError(
            () => elaborate(
                data,
                'sigmaProj ForeignE',
                Object.freeze([
                    ...data.environment,
                    {
                        name: 'ForeignE',
                        kind: 'displayed-family' as const,
                        value: foreignE
                    }
                ])
            ),
            'CATEGORICAL_REJECTION'
        );

        const legacy = new CoreCategoricalProgram({
            profile: 'reviewed-usability-2a1'
        });
        const legacyK = legacy.category('legacy_K');
        const legacyE = legacy.displayedFamily('legacy_E', legacyK);
        captureTextError(
            () => elaborateCoreCategoricalText(legacy, {
                source: 'sigmaProj E',
                sourceFile,
                environment: Object.freeze([
                    {
                        name: 'E',
                        kind: 'displayed-family',
                        value: legacyE
                    }
                ]),
                expected: { kind: 'term' }
            }),
            'CATEGORICAL_REJECTION'
        );
    });

    it('retains generic component/point and gated naturality behavior',
        () => {
            const data = fixture();
            assertDirectEquality(
                data,
                'eta x',
                data.program.displayedTransforComponent(
                    data.eta,
                    data.x
                )
            );
            assertDirectEquality(
                data,
                'eta x u',
                data.program.displayedTransforPoint(
                    data.eta,
                    data.x,
                    data.u
                )
            );
            captureTextError(
                () => elaborate(data, 'eta p u'),
                'CATEGORICAL_REJECTION'
            );
            captureTextError(
                () => elaborate(data, 'displayedNaturality eta p u'),
                'UNKNOWN_IDENTIFIER'
            );
        });
});
