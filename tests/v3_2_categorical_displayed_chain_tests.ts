/**
 * DISPLAYED-CHAIN-1A root-only recursive consumer evidence.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PROGRAM_REVISION,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalSlotToken,
    CoreLfComparisonResult,
    coreCategoricalDisplayedChainCoreName
} from '../src/v3_2';

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => result.trace.flatMap(entry =>
    entry.reduction.kind === 'runtime'
        ? [entry.reduction.ruleId]
        : []
);

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-displayed-chain.ts',
        profile: 'fibred-displayed-chain-1'
    });
    const K = emdash.category('K', { line: 1 });
    const A = emdash.displayedFamily('A', K, { line: 2 });
    const D = emdash.displayedFamily('D', K, { line: 3 });
    const sigmaA = emdash.totalCategory(A, { line: 4 });
    const B = emdash.displayedFamily('B', sigmaA, { line: 5 });
    const projection = emdash.sigmaProjection(A, { line: 6 });
    const liftedA = emdash.pullbackFamily(
        A,
        projection,
        { line: 7 }
    );
    const liftedD = emdash.pullbackFamily(
        D,
        projection,
        { line: 8 }
    );
    const FF = emdash.displayedFunctor(
        'FF',
        A,
        D,
        { line: 9 }
    );
    const liftedFF = emdash.pullbackDisplayedFunctor(
        FF,
        projection,
        { line: 10 }
    );
    return {
        emdash,
        K,
        A,
        B,
        D,
        sigmaA,
        projection,
        liftedA,
        liftedD,
        FF,
        liftedFF
    };
};

const pointFixture = (
    fixtureValue: ReturnType<typeof fixture>
) => {
    const {
        emdash,
        K,
        A,
        B
    } = fixtureValue;
    const k = emdash.object('k', K, { line: 20 });
    const a = emdash.object(
        'a',
        emdash.fibre(A, k),
        { line: 21 }
    );
    const z = emdash.dependentPair(
        A,
        k,
        a,
        { line: 22 }
    );
    const b = emdash.object(
        'b',
        emdash.fibre(B, z),
        { line: 23 }
    );
    return {
        k,
        a,
        z,
        b
    };
};

describe('DISPLAYED-CHAIN-1A recursive contextual consumer', () => {
    it('compiles both variables once through one genuine edge', () => {
        const {
            emdash,
            A,
            B,
            liftedA
        } = fixture();
        let outerCallbacks = 0;
        const outer = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            liftedA,
            ([a]) => {
                outerCallbacks += 1;
                return a;
            },
            { source: { line: 30 } }
        );
        let innerCallbacks = 0;
        const inner = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            B,
            ([, b]) => {
                innerCallbacks += 1;
                return b;
            },
            { source: { line: 36 } }
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROGRAM_REVISION,
            'DISPLAYED-CHAIN-1A-CATEGORICAL-PROGRAM-1'
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW
                .approval.decisionId,
            'D-DTTLF-USABILITY-012'
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount,
            1
        );
        assert.equal(outerCallbacks, 1);
        assert.equal(innerCallbacks, 1);

        const outerCompilation = emdash.compile(outer);
        const innerCompilation = emdash.compile(inner);
        const outerEvidence = outerCompilation.abstractions.at(-1);
        const innerEvidence = innerCompilation.abstractions.at(-1);
        assert.equal(
            outerEvidence?.rule,
            'categorical.displayed-dependent-context-bracket'
        );
        if (
            outerEvidence?.rule !==
                'categorical.displayed-dependent-context-bracket'
        ) {
            assert.fail('Missing dependent contextual evidence');
        }
        assert.deepEqual(outerEvidence.bindingNames, ['a', 'b']);
        assert.equal(
            outerEvidence.contextRelation,
            'one-genuine-dependency-edge'
        );
        assert.equal(outerEvidence.contextSize, 2);
        assert.equal(outerEvidence.body.tag, 'slot-reference');
        if (outerEvidence.body.tag !== 'slot-reference') {
            assert.fail('Outer-variable body lost its slot');
        }
        assert.equal(outerEvidence.body.index, 1);
        assert.equal(innerEvidence?.body.tag, 'slot-reference');
        if (innerEvidence?.body.tag !== 'slot-reference') {
            assert.fail('Inner-variable body lost its slot');
        }
        assert.equal(innerEvidence.body.index, 0);
        assert.equal(Object.isFrozen(outerEvidence), true);
        assert.match(
            outerCompilation.explicitCore,
            /emdash\.categorical\.sigma-functord-section/u
        );
        assert.deepEqual(
            outerCompilation.dependentPrerequisites,
            [
                'displayed-identity',
                'sigma-functord-section',
                'sigma-projection-pullback',
                'sigma-pi-uncurrying-proof',
                'sigma-first-projection',
                'section-pullback-functor',
                'constant-displayed-family-object'
            ]
        );
        assert.deepEqual(
            innerCompilation.dependentPrerequisites,
            ['displayed-identity']
        );
    });

    it('computes immediate and recursively weakened variable objects', () => {
        const fixtureValue = fixture();
        const {
            emdash,
            A,
            B,
            liftedA
        } = fixtureValue;
        const {
            a,
            z,
            b
        } = pointFixture(fixtureValue);
        const outer = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            liftedA,
            ([prefix]) => prefix
        );
        const inner = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            B,
            ([, next]) => next
        );
        const applyAt = (
            displayedFunctor: typeof outer
        ) => emdash.apply(
            emdash.apply(
                displayedFunctor,
                z,
                { expectedShape: 'fibre-functor' }
            ),
            b
        );
        const outerResult = emdash.compare(
            applyAt(outer),
            a,
            30_000
        );
        const innerResult = emdash.compare(
            applyAt(inner),
            b,
            30_000
        );
        assert.equal(outerResult.status, 'equal');
        assert.equal(innerResult.status, 'equal');
        assert.equal(
            runtimeRuleIds(outerResult).includes(
                'categorical.displayed-chain.' +
                    'section-pullback-direct-object'
            ),
            true
        );
        assert.equal(
            runtimeRuleIds(outerResult).includes(
                'categorical.displayed-chain.' +
                    'sigma-functord-section-object'
            ),
            true
        );
        assert.equal(
            runtimeRuleIds(innerResult).includes(
                'categorical.displayed-identity.point.delta'
            ),
            true
        );
    });

    it('recurses beneath a closed displayed-functor application', () => {
        const fixtureValue = fixture();
        const {
            emdash,
            A,
            B,
            FF,
            liftedD,
            liftedFF
        } = fixtureValue;
        const {
            k,
            a,
            z,
            b
        } = pointFixture(fixtureValue);
        const mapped = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            liftedD,
            ([prefix]) => emdash.apply(liftedFF, prefix)
        );
        const actual = emdash.apply(
            emdash.apply(
                mapped,
                z,
                { expectedShape: 'fibre-functor' }
            ),
            b
        );
        const expected = emdash.apply(
            emdash.apply(
                FF,
                k,
                { expectedShape: 'fibre-functor' }
            ),
            a
        );
        const result = emdash.compare(actual, expected, 60_000);
        assert.equal(result.status, 'equal');
        const compilation = emdash.compile(mapped);
        assert.match(
            compilation.explicitCore,
            /generic-category-composition/u
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'sigma-functord-section'
            ),
            true
        );
        assert.equal(
            runtimeRuleIds(result).includes(
                'categorical.weaken-reindex.pullback-hom-component'
            ),
            true
        );
    });

    it('recurses through a typed pair without a body recognizer', () => {
        const {
            emdash,
            A,
            B,
            liftedA
        } = fixture();
        const target = emdash.displayedProduct(liftedA, B);
        const paired = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            target,
            ([a, b]) => emdash.fibrePair(a, b)
        );
        const compilation = emdash.compile(paired);
        const evidence = compilation.abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-dependent-context-bracket'
        );
        assert.equal(evidence?.body.tag, 'typed-pair');
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-product-pair/u
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'displayed-product-pair'
            ),
            true
        );
    });

    it('preserves internalized arrow action without collapsing it', () => {
        const fixtureValue = fixture();
        const {
            emdash,
            K,
            A,
            B,
            liftedA
        } = fixtureValue;
        const outer = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            liftedA,
            ([prefix]) => prefix
        );
        const k0 = emdash.object('k0', K, { line: 60 });
        const k1 = emdash.object('k1', K, { line: 61 });
        const p = emdash.hom('p', K, k0, k1, { line: 62 });
        const a0 = emdash.object(
            'a0',
            emdash.fibre(A, k0),
            { line: 63 }
        );
        const a1 = emdash.object(
            'a1',
            emdash.fibre(A, k1),
            { line: 64 }
        );
        const alpha = emdash.hom(
            'alpha',
            emdash.fibre(A, k1),
            emdash.apply(
                emdash.familyTransport(A, p),
                a0
            ),
            a1,
            { line: 65 }
        );
        const q = emdash.sigmaArrow(
            A,
            a0,
            a1,
            p,
            alpha,
            { line: 66 }
        );
        const z0 = emdash.dependentPair(A, k0, a0);
        const b0 = emdash.object('b0', emdash.fibre(B, z0));
        const c0 = emdash.object('c0', emdash.fibre(B, z0));
        const bCell = emdash.displayedFunctorInternalCell(
            outer,
            q,
            b0
        );
        const cCell = emdash.displayedFunctorInternalCell(
            outer,
            q,
            c0
        );
        const independence = emdash.compare(
            bCell,
            cCell,
            60_000
        );
        assert.equal(independence.status, 'equal');
        const rules = runtimeRuleIds(independence);
        assert.equal(
            rules.includes(
                'categorical.displayed-chain.' +
                    'section-pullback-direct-arrow'
            ),
            true
        );
        assert.equal(
            rules.includes(
                'categorical.displayed-chain.' +
                    'sigma-functord-section-structured-arrow'
            ),
            true
        );

        const nonCollapse = emdash.compare(
            bCell,
            alpha,
            60_000
        );
        assert.equal(nonCollapse.status, 'not-equal');
        assert.equal(nonCollapse.normalizedLeft.tag, 'call');
        if (nonCollapse.normalizedLeft.tag !== 'call') {
            assert.fail('Internalized arrow action lost its stable head');
        }
        assert.equal(
            nonCollapse.normalizedLeft.callee.tag,
            'reference'
        );
        if (
            nonCollapse.normalizedLeft.callee.tag !== 'reference'
        ) {
            assert.fail('Internalized action head is not a reference');
        }
        assert.equal(
            nonCollapse.normalizedLeft.callee.name,
            coreCategoricalDisplayedChainCoreName(
                'displayedInternalHomAction'
            )
        );
    });

    it('retains ordinary displayed reindexing after the chain compiler', () => {
        const {
            emdash,
            A,
            B,
            sigmaA,
            liftedA
        } = fixture();
        const outer = emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: B }
            ],
            liftedA,
            ([prefix]) => prefix
        );
        const L = emdash.category('L', { line: 80 });
        const u = emdash.functor('u', L, sigmaA, { line: 81 });
        const reindexed = emdash.pullbackDisplayedFunctor(
            outer,
            u,
            { line: 82 }
        );
        const compilation = emdash.compile(reindexed);
        assert.equal(
            compilation.surfaceType.tag,
            'displayed-functor'
        );
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-pullback-functor/u
        );
        assert.equal(compilation.productionLambdapiDependency, false);
    });

    it('fails closed on profile, base, arity, escaped, and foreign inputs',
        () => {
            const {
                emdash,
                K,
                A,
                B,
                liftedA
            } = fixture();
            const wrongB = emdash.displayedFamily('wrongB', K);
            assert.throws(
                () => emdash.displayedDependentContextLambda(
                    [
                        { name: 'a', family: A },
                        { name: 'b', family: wrongB }
                    ],
                    liftedA,
                    ([a]) => a
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
            assert.throws(
                () => emdash.displayedDependentContextLambda(
                    [
                        { name: 'a', family: A },
                        { name: 'b', family: B }
                    ],
                    wrongB,
                    ([, b]) => b
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
            assert.throws(
                () => emdash.displayedDependentContextLambda(
                    [{ name: 'a', family: A }],
                    liftedA,
                    ([a]) => a
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'INVALID_DISPLAYED_CONTEXT'
            );

            let escaped: CoreCategoricalSlotToken | undefined;
            emdash.displayedDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'b', family: B }
                ],
                B,
                ([a, b]) => {
                    escaped = a;
                    return b;
                }
            );
            assert.throws(
                () => emdash.fibrePair(
                    escaped as CoreCategoricalSlotToken,
                    escaped as CoreCategoricalSlotToken
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'ESCAPED_SLOT'
            );

            const foreign = fixture();
            const foreignIdentity =
                foreign.emdash.displayedDependentContextLambda(
                    [
                        { name: 'a', family: foreign.A },
                        { name: 'b', family: foreign.B }
                    ],
                    foreign.B,
                    ([, b]) => b
                );
            assert.throws(
                () => emdash.displayedDependentContextLambda(
                    [
                        { name: 'a', family: A },
                        { name: 'b', family: B }
                    ],
                    B,
                    () => foreignIdentity
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'FOREIGN_TERM'
            );

            const predecessor = new CoreCategoricalProgram({
                profile: 'fibred-displayed-evaluation-1'
            });
            const PK = predecessor.category('PK');
            const PA = predecessor.displayedFamily('PA', PK);
            const PB = predecessor.displayedFamily(
                'PB',
                predecessor.totalCategory(PA)
            );
            assert.throws(
                () => predecessor.displayedDependentContextLambda(
                    [
                        { name: 'a', family: PA },
                        { name: 'b', family: PB }
                    ],
                    PB,
                    ([, b]) => b
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_CHAIN'
            );

            assert.throws(
                () => emdash.displayedContextLambda(
                    [
                        { name: 'a', family: A },
                        { name: 'b', family: B }
                    ],
                    A,
                    ([a]) => a
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
        }
    );
});
