/**
 * D-DTTLF-USABILITY-078 expanded compositional binder text parity.
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
    CORE_CATEGORICAL_TEXT_REVISION,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    CoreCategoricalTextTermExpected,
    elaborateCoreCategoricalText
} from '../src/v3_2/categorical_text';

const sourceFile =
    'tests/fixtures/categorical-compositional-text-parity.emdash';

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

const map = (
    program: CoreCategoricalProgram,
    functor: CoreCategoricalTerm,
    argument: CoreCategoricalTerm
): CoreCategoricalTerm => program.apply(functor, argument);

const point = (
    program: CoreCategoricalProgram,
    transformation: CoreCategoricalTerm,
    argument: CoreCategoricalTerm
): CoreCategoricalTerm => program.apply(
    transformation,
    argument,
    { expectedShape: 'point-component' }
);

const mappedDisplayedFunctor = (
    program: CoreCategoricalProgram,
    name: string,
    source: CoreCategoricalDisplayedFamily,
    target: CoreCategoricalDisplayedFamily,
    chain: readonly CoreCategoricalTerm[]
): CoreCategoricalTerm => program.displayedFunctorLambda(
    name,
    source,
    target,
    token => chain.reduce(
        (current, functor) => map(program, functor, current),
        token as CoreCategoricalTerm
    )
);

const buildFixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile,
        profile: 'compositional-natural-binder-1'
    });
    const K = program.category('compositional_text_K');
    const WrongBase = program.category('compositional_text_WrongBase');
    const A = program.category('compositional_text_A');
    const B = program.category('compositional_text_B');
    const E = program.displayedFamily('compositional_text_E', K);
    const D = program.displayedFamily('compositional_text_D', K);
    const Q = program.displayedFamily('compositional_text_Q', K);
    const C = program.displayedFamily('compositional_text_C', K);
    const F = program.displayedFunctor('compositional_text_F', E, D);
    const G = program.displayedFunctor('compositional_text_G', E, D);
    const H = program.displayedFunctor('compositional_text_H', E, D);
    const M = program.displayedFunctor('compositional_text_M', D, Q);
    const L = program.displayedFunctor('compositional_text_L', C, E);
    const eta = program.displayedTransfor(
        'compositional_text_eta',
        F,
        G
    );
    const theta = program.displayedTransfor(
        'compositional_text_theta',
        G,
        H
    );
    const postSource = mappedDisplayedFunctor(
        program,
        'compositional_text_MF',
        E,
        Q,
        [F, M]
    );
    const postTarget = mappedDisplayedFunctor(
        program,
        'compositional_text_MG',
        E,
        Q,
        [G, M]
    );
    const preSource = mappedDisplayedFunctor(
        program,
        'compositional_text_FL',
        C,
        D,
        [L, F]
    );
    const preTarget = mappedDisplayedFunctor(
        program,
        'compositional_text_GL',
        C,
        D,
        [L, G]
    );
    const ordinary = program.functor('compositional_text_ordinary', A, B);
    const section = program.section('compositional_text_section', E);
    const x = program.object('compositional_text_x', K);
    const y = program.object('compositional_text_y', K);
    const p = program.hom('compositional_text_p', K, x, y);
    const u = program.object(
        'compositional_text_u',
        program.fibre(E, x)
    );
    const arbitraryPoint = program.displayedTransforPoint(eta, x, u);
    const environment = Object.freeze([
        categoryBinding('K', K),
        categoryBinding('WrongBase', WrongBase),
        categoryBinding('A', A),
        categoryBinding('B', B),
        familyBinding('E', E),
        familyBinding('D', D),
        familyBinding('Q', Q),
        familyBinding('C', C),
        termBinding('F', F),
        termBinding('G', G),
        termBinding('H', H),
        termBinding('M', M),
        termBinding('L', L),
        termBinding('eta', eta),
        termBinding('theta', theta),
        termBinding('ordinary', ordinary),
        termBinding('section', section),
        termBinding('arbitraryPoint', arbitraryPoint)
    ]);
    return {
        program,
        K,
        WrongBase,
        A,
        B,
        E,
        D,
        Q,
        C,
        F,
        G,
        H,
        M,
        L,
        eta,
        theta,
        postSource,
        postTarget,
        preSource,
        preTarget,
        ordinary,
        section,
        x,
        p,
        u,
        environment
    };
};

let sharedFixture: ReturnType<typeof buildFixture> | undefined;
const fixture = (): ReturnType<typeof buildFixture> => {
    sharedFixture ??= buildFixture();
    return sharedFixture;
};

const elaborate = (
    source: string,
    expected: CoreCategoricalTextTermExpected,
    program = fixture().program,
    environment = fixture().environment
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

const assertSameCore = (
    program: CoreCategoricalProgram,
    terms: readonly CoreCategoricalTerm[]
): void => {
    const core = program.compile(terms[0]).explicitCore;
    for (const term of terms.slice(1)) {
        assert.equal(program.compile(term).explicitCore, core);
        assert.equal(program.compare(terms[0], term, 20_000).status, 'equal');
    }
};

const firstExpected = (
    source: CoreCategoricalDisplayedFamily,
    target: CoreCategoricalDisplayedFamily
): CoreCategoricalTextTermExpected => Object.freeze({
    kind: 'expanded-displayed-functor' as const,
    base: fixture().K,
    source,
    target
});

const secondExpected = (
    sourceFamily: CoreCategoricalDisplayedFamily,
    source: CoreCategoricalTerm,
    target: CoreCategoricalTerm
): CoreCategoricalTextTermExpected => Object.freeze({
    kind: 'expanded-displayed-transfor' as const,
    base: fixture().K,
    sourceFamily,
    source,
    target
});

const expandedNatural = (
    program: CoreCategoricalProgram,
    name: string,
    source: CoreCategoricalTerm,
    target: CoreCategoricalTerm,
    body: (
        base: Parameters<Parameters<
            CoreCategoricalProgram['transforLambda']
        >[3]>[0],
        fibre: Parameters<Parameters<
            CoreCategoricalProgram['transforLambda']
        >[3]>[0]
    ) => CoreCategoricalTerm
): CoreCategoricalTerm => program.transforLambda(
    `${name}Base`,
    source,
    target,
    base => program.transforLambda(
        name,
        program.apply(source, base, { expectedShape: 'fibre-functor' }),
        program.apply(target, base, { expectedShape: 'fibre-functor' }),
        fibre => body(base, fibre)
    )
);

describe('COMPOSITIONAL-NATURAL-TEXT-PARITY-1D', () => {
    it('matches direct and compact first-Hom identity, eta, and chains', () => {
        const { program, E, D, Q, F, M } = fixture();
        const cases = [
            {
                parsed: elaborate(
                    'λ^n k : K. λ^f a : E. a',
                    firstExpected(E, E)
                ),
                direct: program.transforLambda(
                    'kIdentity',
                    E,
                    E,
                    k => program.lambda(
                        'aIdentity',
                        program.fibre(E, k),
                        program.fibre(E, k),
                        a => a
                    )
                ),
                compact: program.displayedFunctorLambda(
                    'aIdentityCompact',
                    E,
                    E,
                    a => a
                )
            },
            {
                parsed: elaborate(
                    'λ^n k. λ^f a. F a',
                    firstExpected(E, D)
                ),
                direct: program.transforLambda(
                    'kEta',
                    E,
                    D,
                    k => program.lambda(
                        'aEta',
                        program.fibre(E, k),
                        program.fibre(D, k),
                        a => map(program, F, a)
                    )
                ),
                compact: program.displayedFunctorLambda(
                    'aEtaCompact',
                    E,
                    D,
                    a => map(program, F, a)
                )
            },
            {
                parsed: elaborate(
                    'λ^n k : K. λ^f a. M (F a)',
                    firstExpected(E, Q)
                ),
                direct: program.transforLambda(
                    'kChain',
                    E,
                    Q,
                    k => program.lambda(
                        'aChain',
                        program.fibre(E, k),
                        program.fibre(Q, k),
                        a => map(program, M, map(program, F, a))
                    )
                ),
                compact: program.displayedFunctorLambda(
                    'aChainCompact',
                    E,
                    Q,
                    a => map(program, M, map(program, F, a))
                )
            }
        ];
        for (const entry of cases) {
            assertSameCore(program, [
                entry.parsed,
                entry.direct,
                entry.compact
            ]);
        }
    });

    it('matches direct and compact second-Hom recursive body algebra', () => {
        const {
            program,
            E,
            C,
            F,
            G,
            H,
            M,
            L,
            eta,
            theta,
            postSource,
            postTarget,
            preSource,
            preTarget
        } = fixture();
        const cases = [
            {
                parsed: elaborate(
                    'λ^n k : K. λ^n a : E. eta a',
                    secondExpected(E, F, G)
                ),
                direct: expandedNatural(
                    program,
                    'eta',
                    F,
                    G,
                    (_k, a) => point(program, eta, a)
                ),
                compact: program.displayedTransforContextLambda(
                    'etaCompact',
                    F,
                    G,
                    a => point(program, eta, a)
                )
            },
            {
                parsed: elaborate(
                    'λ^n k. λ^n a. identityCell (F a)',
                    secondExpected(E, F, F)
                ),
                direct: expandedNatural(
                    program,
                    'identity',
                    F,
                    F,
                    (_k, a) => program.identityCell(map(program, F, a))
                ),
                compact: program.displayedTransforContextLambda(
                    'identityCompact',
                    F,
                    F,
                    a => program.identityCell(map(program, F, a))
                )
            },
            {
                parsed: elaborate(
                    'λ^n k. λ^n a. composeCells (theta a) (eta a)',
                    secondExpected(E, F, H)
                ),
                direct: expandedNatural(
                    program,
                    'composition',
                    F,
                    H,
                    (_k, a) => program.composeCells(
                        point(program, theta, a),
                        point(program, eta, a)
                    )
                ),
                compact: program.displayedTransforContextLambda(
                    'compositionCompact',
                    F,
                    H,
                    a => program.composeCells(
                        point(program, theta, a),
                        point(program, eta, a)
                    )
                )
            },
            {
                parsed: elaborate(
                    'λ^n k. λ^n a : E. M (eta a)',
                    secondExpected(E, postSource, postTarget)
                ),
                direct: expandedNatural(
                    program,
                    'post',
                    postSource,
                    postTarget,
                    (_k, a) => point(program, M, point(program, eta, a))
                ),
                compact: program.displayedTransforContextLambda(
                    'postCompact',
                    postSource,
                    postTarget,
                    a => point(program, M, point(program, eta, a))
                )
            },
            {
                parsed: elaborate(
                    'λ^n k. λ^n a : C. eta (L a)',
                    secondExpected(C, preSource, preTarget)
                ),
                direct: expandedNatural(
                    program,
                    'pre',
                    preSource,
                    preTarget,
                    (_k, a) => point(program, eta, map(program, L, a))
                ),
                compact: program.displayedTransforContextLambda(
                    'preCompact',
                    preSource,
                    preTarget,
                    a => point(program, eta, map(program, L, a))
                )
            }
        ];
        for (const entry of cases) {
            assertSameCore(program, [
                entry.parsed,
                entry.direct,
                entry.compact
            ]);
        }
    });

    it('retains component, fibre-point, and internal higher action', () => {
        const { program, E, F, G, eta, x, p, u } = fixture();
        const parsed = elaborate(
            'λ^n k. λ^n a. eta a',
            secondExpected(E, F, G)
        );
        const compact = program.displayedTransforContextLambda(
            'actionCompact',
            F,
            G,
            a => point(program, eta, a)
        );
        const observations = [
            [
                program.displayedTransforComponent(parsed, x),
                program.displayedTransforComponent(compact, x)
            ],
            [
                program.displayedTransforPoint(parsed, x, u),
                program.displayedTransforPoint(compact, x, u)
            ],
            [
                program.displayedTransforNaturality(parsed, p, u),
                program.displayedTransforNaturality(compact, p, u)
            ]
        ] as const;
        for (const [expanded, compactObservation] of observations) {
            assert.equal(
                program.compare(
                    expanded,
                    compactObservation,
                    20_000
                ).status,
                'equal'
            );
        }
        assert.match(
            program.compile(observations[2][0]).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('fails closed at modes, nesting, annotations, and semantics', () => {
        const { K, WrongBase, E, D, F, G } = fixture();
        const missing = captureTextError(
            () => elaborate('λ^n k. F k', firstExpected(E, D)),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.equal(missing.span.start.column, 8);

        const wrongInnerMode = captureTextError(
            () => elaborate(
                'λ^n k. λ^n a. F a',
                firstExpected(E, D)
            ),
            'UNSUPPORTED_BINDER_MODE'
        );
        assert.equal(wrongInnerMode.span.start.line, 1);

        captureTextError(
            () => elaborate(
                'λ^f k. λ^f a. F a',
                firstExpected(E, D)
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                'λ^n k : E. λ^f a. F a',
                firstExpected(E, D)
            ),
            'EXPECTED_CATEGORY'
        );
        captureTextError(
            () => elaborate(
                'λ^n k : WrongBase. λ^f a. F a',
                firstExpected(E, D)
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                'λ^n k : K. λ^f a : K. F a',
                firstExpected(E, D)
            ),
            'EXPECTED_DISPLAYED_FAMILY'
        );
        captureTextError(
            () => elaborate(
                'λ^n k : K. λ^f a : D. F a',
                firstExpected(E, D)
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborate(
                'λ^n k. λ^f a. F a',
                firstExpected(E, fixture().Q)
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                'λ^n k. λ^n a. eta a',
                secondExpected(E, G, F)
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                'λ^n k. λ^n a. arbitraryPoint',
                secondExpected(E, F, G)
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborate(
                'λ^n k. λ^f a. λ^f b. b',
                firstExpected(E, E)
            ),
            'UNSUPPORTED_NESTED_ABSTRACTION'
        );

        assert.equal(K.label, 'compositional_text_K');
        assert.equal(WrongBase.label, 'compositional_text_WrongBase');
    });

    it('rejects an unsupported profile at the typed route', () => {
        const unavailable = new CoreCategoricalProgram({ sourceFile });
        const unavailableK = unavailable.category('unavailable_K');
        const unavailableE = unavailable.displayedFamily(
            'unavailable_E',
            unavailableK
        );
        const unavailableD = unavailable.displayedFamily(
            'unavailable_D',
            unavailableK
        );
        const unavailableF = unavailable.displayedFunctor(
            'unavailable_F',
            unavailableE,
            unavailableD
        );
        const unavailableError = captureTextError(
            () => elaborateCoreCategoricalText(unavailable, {
                source: 'λ^n k. λ^f a. F a',
                sourceFile,
                environment: [termBinding('F', unavailableF)],
                expected: {
                    kind: 'expanded-displayed-functor',
                    base: unavailableK,
                    source: unavailableE,
                    target: unavailableD
                }
            }),
            'CATEGORICAL_REJECTION'
        );
        assert.equal(
            (unavailableError.underlying as { readonly code?: string }).code,
            'UNAVAILABLE_ORDINARY_NATURAL_BINDER'
        );
    });

    it('preserves predecessor text routes and advances one revision pin', () => {
        const {
            program,
            K,
            A,
            B,
            E,
            D,
            F,
            G,
            eta,
            ordinary
        } = fixture();
        const predecessors = [
            elaborate('λ^f z : A. ordinary z', {
                kind: 'ordinary-functor',
                source: A,
                target: B
            }),
            elaborate('λ^n k : K. section k', {
                kind: 'dependent-section',
                base: K,
                target: E
            }),
            elaborate('λ^fd a : E. F a', {
                kind: 'displayed-functor',
                source: E,
                target: D
            }),
            elaborate('λ^nd a : E. eta a', {
                kind: 'displayed-context-transfor',
                sourceFamily: E,
                source: F,
                target: G
            }),
            elaborate(
                'λ^nd (a : E, b : E). ' +
                    'identityCell (fibrePair a b)',
                {
                    kind: 'displayed-dependent-context-transfor',
                    sourceGroups: [[E, E]]
                }
            )
        ];
        predecessors.forEach(term => assert.doesNotThrow(
            () => program.inspect(term)
        ));
        assert.equal(program.compare(predecessors[0], ordinary).status,
            'equal');
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'COMPOSITIONAL-NATURAL-TEXT-PARITY-1D-CATEGORICAL-TEXT-1'
        );
    });
});
