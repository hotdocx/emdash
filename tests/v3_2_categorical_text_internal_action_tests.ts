/**
 * Focused SYNTAX-PARITY-1C2B internal-action text corpus.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_REVISION,
    CoreCategoricalExpectedShape,
    CoreCategoricalProgram,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-internal-action.emdash';

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'fibred-displayed-nd-higher-1'
    });
    const K = program.category('internal_text_K');
    const L = program.category('internal_text_L');
    const E = program.displayedFamily('internal_text_E', K);
    const D = program.displayedFamily('internal_text_D', K);
    const C = program.displayedFamily('internal_text_C', K);
    const FF = program.displayedFunctor('internal_text_FF', E, D);
    const GG = program.displayedFunctor('internal_text_GG', E, D);
    const HH = program.displayedFunctor('internal_text_HH', E, C);
    const II = program.displayedFunctor('internal_text_II', E, C);
    const eta = program.displayedTransfor(
        'internal_text_eta',
        FF,
        GG
    );
    const etaPrime = program.displayedTransfor(
        'internal_text_eta_prime',
        FF,
        GG
    );
    const x = program.object('internal_text_x', K);
    const y = program.object('internal_text_y', K);
    const z = program.object('internal_text_z', L);
    const p = program.hom('internal_text_p', K, x, y);
    const q = program.hom('internal_text_q', L, z, z);
    const u = program.object(
        'internal_text_u',
        program.fibre(E, x)
    );
    const wrongU = program.object(
        'internal_text_wrong_u',
        program.fibre(D, x)
    );
    const transformationCategory =
        program.displayedTransforCategory(FF, GG);
    const etaBoundary = program.homBoundary(
        transformationCategory,
        eta,
        etaPrime
    );
    const m = program.hom(
        'internal_text_m',
        transformationCategory,
        eta,
        etaPrime
    );
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'FF', kind: 'term', value: FF },
            { name: 'GG', kind: 'term', value: GG },
            { name: 'HH', kind: 'term', value: HH },
            { name: 'II', kind: 'term', value: II },
            { name: 'eta', kind: 'term', value: eta },
            { name: 'etaPrime', kind: 'term', value: etaPrime },
            { name: 'x', kind: 'term', value: x },
            { name: 'y', kind: 'term', value: y },
            { name: 'z', kind: 'term', value: z },
            { name: 'p', kind: 'term', value: p },
            { name: 'q', kind: 'term', value: q },
            { name: 'u', kind: 'term', value: u },
            { name: 'wrongU', kind: 'term', value: wrongU },
            {
                name: 'etaBoundary',
                kind: 'hom-boundary',
                value: etaBoundary
            },
            { name: 'm', kind: 'term', value: m }
        ]);
    return {
        program,
        K,
        L,
        E,
        D,
        C,
        FF,
        GG,
        HH,
        II,
        eta,
        etaPrime,
        x,
        y,
        z,
        p,
        q,
        u,
        wrongU,
        transformationCategory,
        etaBoundary,
        m,
        environment
    };
};

const elaborate = (
    data: ReturnType<typeof fixture>,
    source: string,
    applicationShape?: CoreCategoricalExpectedShape,
    environment = data.environment
): CoreCategoricalTerm => elaborateCoreCategoricalText(
    data.program,
    {
        source,
        sourceFile,
        environment,
        expected: {
            kind: 'term',
            ...(applicationShape === undefined
                ? {}
                : { applicationShape })
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
    assert.equal(diagnostic.span.file, sourceFile);
    return diagnostic;
};

const assertDirectEquality = (
    data: ReturnType<typeof fixture>,
    source: string,
    direct: CoreCategoricalTerm,
    applicationShape?: CoreCategoricalExpectedShape
): void => {
    const parsed = elaborate(data, source, applicationShape);
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

describe('SYNTAX-PARITY-1C2B internal-action text', () => {
    it('matches all four existing typed methods exactly', () => {
        const data = fixture();
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN-CATEGORICAL-TEXT-1'
        );
        for (const [source, direct] of [
            [
                'fullAction FF x y',
                data.program.displayedFunctorFullAction(
                    data.FF,
                    data.x,
                    data.y
                )
            ],
            [
                'cell FF p u',
                data.program.displayedFunctorInternalCell(
                    data.FF,
                    data.p,
                    data.u
                )
            ],
            [
                'naturality eta p u',
                data.program.displayedTransforNaturality(
                    data.eta,
                    data.p,
                    data.u
                )
            ],
            [
                'internalHomAction FF GG',
                data.program.displayedTransforInternalHomAction(
                    data.FF,
                    data.GG
                )
            ]
        ] as const) {
            assertDirectEquality(data, source, direct);
        }
    });

    it('keeps constructor operands and later actions recursive', () => {
        const data = fixture();
        const paired = data.program.displayedProductPair(
            data.FF,
            data.HH
        );
        assertDirectEquality(
            data,
            'fullAction (paird FF HH) x y',
            data.program.displayedFunctorFullAction(
                paired,
                data.x,
                data.y
            )
        );
        assertDirectEquality(
            data,
            'cell (paird FF HH) p u',
            data.program.displayedFunctorInternalCell(
                paired,
                data.p,
                data.u
            )
        );

        const fullAction =
            data.program.displayedFunctorFullAction(
                data.FF,
                data.x,
                data.y
            );
        assertDirectEquality(
            data,
            'fullAction FF x y p',
            data.program.apply(fullAction, data.p)
        );

        const internalHom =
            data.program.displayedTransforInternalHomAction(
                data.FF,
                data.GG
            );
        assertDirectEquality(
            data,
            'internalHomAction FF GG eta',
            data.program.apply(internalHom, data.eta, {
                expectedShape: 'object-value'
            }),
            'object-value'
        );
        const wholeHom = data.program.apply(
            internalHom,
            data.etaBoundary,
            { expectedShape: 'whole-hom-action' }
        );
        assertDirectEquality(
            data,
            'internalHomAction FF GG etaBoundary m',
            data.program.apply(wholeHom, data.m, {
                expectedShape: 'object-value'
            }),
            'object-value'
        );
    });

    it('retains generic component, point, and object application',
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
            const transported = data.program.apply(
                data.program.apply(data.FF, data.p, {
                    expectedShape: 'transport-functor'
                }),
                data.u
            );
            assertDirectEquality(data, 'FF p u', transported);
            assert.equal(
                data.program.compile(
                    elaborate(data, 'FF p u')
                ).surfaceType.tag,
                'object'
            );
            assert.equal(
                data.program.compile(
                    elaborate(data, 'cell FF p u')
                ).surfaceType.tag,
                'hom'
            );
            captureTextError(
                () => elaborate(data, 'eta p u'),
                'CATEGORICAL_REJECTION'
            );
        });

    it('delegates classifier, base, fibre, and endpoint checks',
        () => {
            const data = fixture();
            for (const source of [
                'fullAction x x y',
                'fullAction FF z y',
                'cell eta p u',
                'cell FF q u',
                'cell FF p wrongU',
                'naturality FF p u',
                'naturality eta q u',
                'internalHomAction FF HH'
            ]) {
                captureTextError(
                    () => elaborate(data, source),
                    'CATEGORICAL_REJECTION'
                );
            }
        });

    it('preserves arity, foreign-term, and profile boundaries',
        () => {
            const data = fixture();
            captureTextError(
                () => elaborate(data, 'cell FF p'),
                'UNKNOWN_IDENTIFIER'
            );
            captureTextError(
                () => elaborate(data, 'internalHomAction FF'),
                'UNKNOWN_IDENTIFIER'
            );
            captureTextError(
                () => elaborate(data, 'cell FF p u x'),
                'CATEGORICAL_REJECTION'
            );

            const foreignProgram = new CoreCategoricalProgram({
                profile: 'fibred-displayed-nd-higher-1'
            });
            const foreignK = foreignProgram.category('foreign_K');
            const foreignE =
                foreignProgram.displayedFamily('foreign_E', foreignK);
            const foreignD =
                foreignProgram.displayedFamily('foreign_D', foreignK);
            const foreignFF = foreignProgram.displayedFunctor(
                'foreign_FF',
                foreignE,
                foreignD
            );
            captureTextError(
                () => elaborate(
                    data,
                    'fullAction ForeignFF x y',
                    undefined,
                    Object.freeze([
                        ...data.environment,
                        {
                            name: 'ForeignFF',
                            kind: 'term' as const,
                            value: foreignFF
                        }
                    ])
                ),
                'CATEGORICAL_REJECTION'
            );

            const legacy = new CoreCategoricalProgram({
                profile: 'reviewed-usability-2a1'
            });
            const legacyK = legacy.category('legacy_K');
            const legacyE =
                legacy.displayedFamily('legacy_E', legacyK);
            const legacyD =
                legacy.displayedFamily('legacy_D', legacyK);
            const legacyFF = legacy.displayedFunctor(
                'legacy_FF',
                legacyE,
                legacyD
            );
            const legacyX = legacy.object('legacy_x', legacyK);
            const legacyY = legacy.object('legacy_y', legacyK);
            captureTextError(
                () => elaborateCoreCategoricalText(legacy, {
                    source: 'fullAction FF x y',
                    sourceFile,
                    environment: Object.freeze([
                        { name: 'FF', kind: 'term', value: legacyFF },
                        { name: 'x', kind: 'term', value: legacyX },
                        { name: 'y', kind: 'term', value: legacyY }
                    ]),
                    expected: { kind: 'term' }
                }),
                'CATEGORICAL_REJECTION'
            );
        });
});
