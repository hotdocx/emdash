/**
 * Focused SYNTAX-PARITY-1B3 dependent-context text corpus.
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
    'tests/fixtures/categorical-text-dependent.emdash';

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
        profile: 'fibred-displayed-chain-2a'
    });
    const K = program.category('dependent_text_K');
    const A = program.displayedFamily('dependent_text_A', K);
    const sigmaA = program.totalCategory(A);
    const B = program.displayedFamily('dependent_text_B', sigmaA);
    const C = program.displayedFamily('dependent_text_C', sigmaA);
    const P = program.displayedProduct(B, C);
    const sigmaP = program.totalCategory(P);
    const D = program.displayedFamily('dependent_text_D', sigmaP);
    const projectionA = program.sigmaProjection(A);
    const liftedA = program.pullbackFamily(A, projectionA);
    const projectionP = program.sigmaProjection(P);
    const liftedA2 = program.pullbackFamily(liftedA, projectionP);
    const liftedB = program.pullbackFamily(B, projectionP);
    const liftedC = program.pullbackFamily(C, projectionP);
    const liftedProduct = program.displayedProduct(liftedB, liftedC);
    const HH = program.displayedFunctor(
        'dependent_text_HH',
        liftedProduct,
        liftedProduct
    );
    const closed = program.displayedFunctor(
        'dependent_text_closed',
        D,
        D
    );
    const grouped = program.groupedSequentialContext(
        'dependent_text_ka',
        sigmaA,
        [
            { name: 'b', family: B },
            { name: 'c', family: C }
        ]
    );
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            familyBinding('A', A),
            familyBinding('B', B),
            familyBinding('C', C),
            familyBinding('D', D),
            termBinding('HH', HH),
            termBinding('closed', closed)
        ]);
    const edgeExpected: CoreCategoricalTextExpected = Object.freeze({
        kind: 'displayed-dependent-context-functor' as const,
        sourceGroups: Object.freeze([
            Object.freeze([A]),
            Object.freeze([B])
        ]),
        target: liftedA
    });
    const mixedExpected: CoreCategoricalTextExpected = Object.freeze({
        kind: 'displayed-dependent-context-functor' as const,
        sourceGroups: Object.freeze([
            Object.freeze([A]),
            Object.freeze([B, C]),
            Object.freeze([D])
        ]),
        target: liftedProduct
    });
    const bindings = Object.freeze([
        { name: 'a', family: A },
        { name: 'b', family: B },
        { name: 'c', family: C },
        { name: 'd', family: D }
    ]);
    return {
        program,
        K,
        A,
        B,
        C,
        P,
        D,
        liftedA,
        liftedA2,
        liftedB,
        liftedC,
        liftedProduct,
        HH,
        grouped,
        environment,
        edgeExpected,
        mixedExpected,
        bindings
    };
};

const elaborate = (
    data: ReturnType<typeof fixture>,
    source: string,
    expected: CoreCategoricalTextExpected,
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

const directEdge = (
    data: ReturnType<typeof fixture>
): CoreCategoricalTerm =>
    data.program.displayedDependentContextLambda(
        [
            { name: 'a', family: data.A },
            { name: 'b', family: data.B }
        ],
        data.liftedA,
        ([a]) => a
    );

const directMixed = (
    data: ReturnType<typeof fixture>,
    onCallback: () => void = () => undefined
): CoreCategoricalTerm =>
    data.program.displayedDependentContextLambda(
        data.bindings,
        data.liftedProduct,
        ([, b, c]) => {
            onCallback();
            return data.program.fibrePair(b, c);
        }
    );

const makePoint = (
    data: ReturnType<typeof fixture>,
    suffix: string
) => {
    const k = data.program.object(`dependent_k_${suffix}`, data.K);
    const a = data.program.object(
        `dependent_a_${suffix}`,
        data.program.fibre(data.A, k)
    );
    const ka = data.program.dependentPair(data.A, k, a);
    const b = data.program.object(
        `dependent_b_${suffix}`,
        data.program.fibre(data.B, ka)
    );
    const c = data.program.object(
        `dependent_c_${suffix}`,
        data.program.fibre(data.C, ka)
    );
    const product = data.program.groupedSequentialObject(
        data.grouped,
        ka,
        [b, c]
    );
    const d = data.program.object(
        `dependent_d_${suffix}`,
        data.program.fibre(data.D, product.groupedObject)
    );
    return {
        k,
        a,
        ka,
        b,
        c,
        product,
        d
    };
};

const applyMixedAt = (
    data: ReturnType<typeof fixture>,
    abstraction: CoreCategoricalTerm,
    point: ReturnType<typeof makePoint>
): CoreCategoricalTerm => data.program.apply(
    data.program.apply(
        abstraction,
        point.product.groupedObject,
        { expectedShape: 'fibre-functor' }
    ),
    point.d
);

describe('SYNTAX-PARITY-1B3 dependent-context text', () => {
    it('matches the existing genuine-edge compiler exactly', () => {
        const data = fixture();
        const direct = directEdge(data);
        const annotated = elaborate(
            data,
            'λ^fd (a : A; b : B). a',
            data.edgeExpected
        );
        const omitted = elaborate(
            data,
            'λ^fd (a; b). a',
            data.edgeExpected,
            data.environment.filter(binding =>
                binding.kind !== 'displayed-family'
            )
        );
        const directCompilation = data.program.compile(direct);
        for (const parsed of [annotated, omitted]) {
            const compilation = data.program.compile(parsed);
            assert.equal(
                compilation.explicitCore,
                directCompilation.explicitCore
            );
            assert.equal(
                compilation.explicitInferredType,
                directCompilation.explicitInferredType
            );
            assert.equal(
                compilation.explicitExpectedType,
                directCompilation.explicitExpectedType
            );
            assert.equal(
                data.program.compare(parsed, direct, 60_000).status,
                'equal'
            );
        }
        const trace = directCompilation.abstractions.at(-1);
        assert.equal(
            trace?.rule,
            'categorical.displayed-dependent-context-bracket'
        );
        if (
            trace?.rule !==
                'categorical.displayed-dependent-context-bracket'
        ) {
            assert.fail('Missing genuine-edge lowering trace');
        }
        assert.deepEqual(trace.bindingNames, ['a', 'b']);
        assert.equal(
            trace.contextRelation,
            'one-genuine-dependency-edge'
        );
    });

    it('matches the existing mixed compiler and grouped trace exactly',
        () => {
            const data = fixture();
            let callbacks = 0;
            const direct = directMixed(data, () => {
                callbacks += 1;
            });
            const annotated = elaborate(
                data,
                'λ^fd (a : A; b : B, c : C; d : D). ' +
                    'fibrePair b c',
                data.mixedExpected
            );
            const omitted = elaborate(
                data,
                'λ^fd (a; b, c; d). fibrePair b c',
                data.mixedExpected,
                data.environment.filter(binding =>
                    binding.kind !== 'displayed-family'
                )
            );
            assert.equal(callbacks, 1);

            const directCompilation = data.program.compile(direct);
            for (const parsed of [annotated, omitted]) {
                const compilation = data.program.compile(parsed);
                assert.equal(
                    compilation.explicitCore,
                    directCompilation.explicitCore
                );
                assert.equal(
                    compilation.explicitInferredType,
                    directCompilation.explicitInferredType
                );
                assert.equal(
                    compilation.explicitExpectedType,
                    directCompilation.explicitExpectedType
                );
                assert.deepEqual(
                    compilation.dependentPrerequisites,
                    directCompilation.dependentPrerequisites
                );
                assert.equal(
                    data.program.compare(
                        parsed,
                        direct,
                        60_000
                    ).status,
                    'equal'
                );
            }

            const trace = directCompilation.abstractions.at(-1);
            assert.equal(
                trace?.rule,
                'categorical.displayed-mixed-dependent-context-bracket'
            );
            if (
                trace?.rule !==
                    'categorical.displayed-mixed-dependent-context-bracket'
            ) {
                assert.fail('Missing mixed-telescope lowering trace');
            }
            assert.deepEqual(
                trace.bindingNames,
                ['a', 'b', 'c', 'd']
            );
            assert.deepEqual(trace.siblingGroup, ['b', 'c']);
            assert.equal(
                trace.contextRelation,
                'two-dependency-transitions-with-middle-siblings'
            );
            assert.equal(trace.body.tag, 'typed-pair');
        });

    it('resolves every mixed slot and recursive application', () => {
        const data = fixture();
        const sourceGroups = [[data.A], [data.B, data.C], [data.D]];
        const cases = [
            {
                source: 'λ^fd (a; b, c; d). a',
                target: data.liftedA2,
                direct: data.program.displayedDependentContextLambda(
                    data.bindings,
                    data.liftedA2,
                    ([a]) => a
                )
            },
            {
                source: 'λ^fd (a; b, c; d). b',
                target: data.liftedB,
                direct: data.program.displayedDependentContextLambda(
                    data.bindings,
                    data.liftedB,
                    ([, b]) => b
                )
            },
            {
                source: 'λ^fd (a; b, c; d). c',
                target: data.liftedC,
                direct: data.program.displayedDependentContextLambda(
                    data.bindings,
                    data.liftedC,
                    ([, , c]) => c
                )
            },
            {
                source: 'λ^fd (a; b, c; d). d',
                target: data.D,
                direct: data.program.displayedDependentContextLambda(
                    data.bindings,
                    data.D,
                    ([, , , d]) => d
                )
            },
            {
                source:
                    'λ^fd (a; b, c; d). HH (fibrePair b c)',
                target: data.liftedProduct,
                direct: data.program.displayedDependentContextLambda(
                    data.bindings,
                    data.liftedProduct,
                    ([, b, c]) => data.program.apply(
                        data.HH,
                        data.program.fibrePair(b, c)
                    )
                )
            }
        ] as const;
        for (const entry of cases) {
            const parsed = elaborate(
                data,
                entry.source,
                {
                    kind: 'displayed-dependent-context-functor',
                    sourceGroups,
                    target: entry.target
                }
            );
            assert.equal(
                data.program.compile(parsed).explicitCore,
                data.program.compile(entry.direct).explicitCore
            );
        }
    });

    it('preserves mixed object and internalized-arrow action', () => {
        const data = fixture();
        const parsed = elaborate(
            data,
            'λ^fd (a; b, c; d). fibrePair b c',
            data.mixedExpected
        );
        const direct = directMixed(data);
        const p0 = makePoint(data, '0');
        assert.equal(
            data.program.compare(
                applyMixedAt(data, parsed, p0),
                applyMixedAt(data, direct, p0),
                60_000
            ).status,
            'equal'
        );

        const p1 = makePoint(data, '1');
        const p = data.program.hom(
            'dependent_p',
            data.K,
            p0.k,
            p1.k
        );
        const alpha = data.program.hom(
            'dependent_alpha',
            data.program.fibre(data.A, p1.k),
            data.program.apply(
                data.program.familyTransport(data.A, p),
                p0.a
            ),
            p1.a
        );
        const qA = data.program.sigmaArrow(
            data.A,
            p0.a,
            p1.a,
            p,
            alpha
        );
        const rho = data.program.hom(
            'dependent_rho',
            data.program.fibre(data.P, p1.ka),
            data.program.apply(
                data.program.familyTransport(data.P, qA),
                p0.product.groupedFibreObject
            ),
            p1.product.groupedFibreObject
        );
        const qP = data.program.sigmaArrow(
            data.P,
            p0.product.groupedFibreObject,
            p1.product.groupedFibreObject,
            qA,
            rho
        );
        const parsedCell = data.program.displayedFunctorInternalCell(
            parsed,
            qP,
            p0.d
        );
        const directCell = data.program.displayedFunctorInternalCell(
            direct,
            qP,
            p0.d
        );
        assert.equal(
            data.program.compare(
                parsedCell,
                directCell,
                60_000
            ).status,
            'equal'
        );
    });

    it('rejects malformed levels and duplicate telescope names', () => {
        const data = fixture();
        const cases: readonly [
            source: string,
            code: CoreCategoricalTextErrorCode
        ][] = [
            [
                'λ^fd (a : A;; b : B). a',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (a : A;). a',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (a : A,; b : B). a',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (a : A; a : B). a',
                'DUPLICATE_BINDING'
            ],
            [
                'λ^fd (a : A; b : B,). a',
                'UNEXPECTED_TOKEN'
            ],
            [
                'λ^fd (a : A). a',
                'UNEXPECTED_TOKEN'
            ]
        ];
        for (const [source, code] of cases) {
            const error = captureTextError(
                () => elaborate(data, source, data.edgeExpected),
                code
            );
            assert.equal(error.phase, 'parsing');
        }
    });

    it('checks exact group shape, grouped expectation, annotation, and mode',
        () => {
            const data = fixture();
            for (const source of [
                'λ^fd (a : A; b : B; c : C). a',
                'λ^fd (a : A, b : B; c : C). a',
                'λ^fd (a : A; b : B, c : C). a',
                'λ^fd (a : A; b : B; c : C; d : D). a'
            ]) {
                captureTextError(
                    () => elaborate(data, source, data.mixedExpected),
                    'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
                );
            }
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a; b). a',
                    {
                        kind: 'displayed-dependent-context-functor',
                        sourceGroups: [[data.A, data.B]],
                        target: data.liftedA
                    }
                ),
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a : B; b : B). a',
                    data.edgeExpected
                ),
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a : closed; b : B). a',
                    data.edgeExpected
                ),
                'EXPECTED_DISPLAYED_FAMILY'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^n (a : A; b : B). a',
                    data.edgeExpected
                ),
                'UNSUPPORTED_BINDER_MODE'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a : A; b : B). a',
                    { kind: 'term' }
                ),
                'MISSING_ABSTRACTION_EXPECTATION'
            );
    });

    it('delegates profile, base, target, and body rejection to the program',
        () => {
            const data = fixture();
            const X = data.program.displayedFamily(
                'dependent_text_X',
                data.K
            );
            const withX = Object.freeze([
                ...data.environment,
                familyBinding('X', X)
            ]);
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a; b). a',
                    {
                        kind: 'displayed-dependent-context-functor',
                        sourceGroups: [[data.A], [X]],
                        target: data.liftedA
                    },
                    withX
                ),
                'CATEGORICAL_REJECTION'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a; b). a',
                    {
                        kind: 'displayed-dependent-context-functor',
                        sourceGroups: [[data.A], [data.B]],
                        target: data.A
                    }
                ),
                'CATEGORICAL_REJECTION'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a; b, c; d). closed',
                    {
                        kind: 'displayed-dependent-context-functor',
                        sourceGroups: [
                            [data.A],
                            [data.B, data.C],
                            [data.D]
                        ],
                        target: data.D
                    }
                ),
                'CATEGORICAL_REJECTION'
            );
            captureTextError(
                () => elaborate(
                    data,
                    'λ^fd (a; b). λ^fd c. c',
                    data.edgeExpected
                ),
                'UNSUPPORTED_NESTED_ABSTRACTION'
            );

            const predecessor = new CoreCategoricalProgram({
                sourceFile,
                profile: 'fibred-displayed-chain-1'
            });
            const K = predecessor.category('predecessor_K');
            const A = predecessor.displayedFamily('predecessor_A', K);
            const sigmaA = predecessor.totalCategory(A);
            const B = predecessor.displayedFamily(
                'predecessor_B',
                sigmaA
            );
            const C = predecessor.displayedFamily(
                'predecessor_C',
                sigmaA
            );
            const P = predecessor.displayedProduct(B, C);
            const D = predecessor.displayedFamily(
                'predecessor_D',
                predecessor.totalCategory(P)
            );
            const projectionP = predecessor.sigmaProjection(P);
            const target = predecessor.displayedProduct(
                predecessor.pullbackFamily(B, projectionP),
                predecessor.pullbackFamily(C, projectionP)
            );
            assert.throws(
                () => elaborateCoreCategoricalText(predecessor, {
                    source:
                        'λ^fd (a; b, c; d). fibrePair b c',
                    sourceFile,
                    environment: [
                        familyBinding('A', A),
                        familyBinding('B', B),
                        familyBinding('C', C),
                        familyBinding('D', D)
                    ],
                    expected: {
                        kind:
                            'displayed-dependent-context-functor',
                        sourceGroups: [[A], [B, C], [D]],
                        target
                    }
                }),
                error =>
                    error instanceof CoreCategoricalTextError &&
                    error.code === 'CATEGORICAL_REJECTION'
            );
        });
});
