/**
 * DISPLAYED-EVAL-1A recursive typed-application frontend evidence.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PROGRAM_REVISION,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_VARYING_APPLICATION,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreLfComparisonResult
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
            'tests/fixtures/categorical-displayed-evaluation.ts',
        profile: 'fibred-displayed-evaluation-1'
    });
    const K = emdash.category('K', { line: 1 });
    const A = emdash.category('A', { line: 2 });
    const B = emdash.displayedFamily('B', K, { line: 3 });
    const E = emdash.displayedFamily('E', K, { line: 4 });
    const D = emdash.displayedFamily('D', K, { line: 5 });
    const stable = emdash.displayedFunctorFamily(
        A,
        B,
        { line: 6 }
    );
    const constant = emdash.constantDisplayedFamily(
        K,
        A,
        { line: 7 }
    );
    const H = emdash.displayedFunctor(
        'H',
        E,
        stable,
        { line: 8 }
    );
    const G = emdash.displayedFunctor(
        'G',
        D,
        constant,
        { line: 9 }
    );
    return {
        emdash,
        K,
        A,
        B,
        E,
        D,
        stable,
        constant,
        H,
        G
    };
};

describe('DISPLAYED-EVAL-1A recursive displayed evaluation', () => {
    it('records and compiles the direct varying F x judgment once', () => {
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PROGRAM_REVISION,
            'DISPLAYED-EVAL-1A-CATEGORICAL-PROGRAM-1'
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_VARYING_APPLICATION
                .target,
            'displayed-evaluation-varying-object'
        );
        const {
            emdash,
            B,
            stable,
            constant
        } = fixture();
        let callbackCount = 0;
        const evaluated = emdash.displayedContextLambda(
            [
                { name: 'F', family: stable },
                { name: 'x', family: constant }
            ],
            B,
            ([F, x]) => {
                callbackCount += 1;
                return emdash.apply(F, x, {
                    source: { line: 20 }
                });
            },
            { source: { line: 16 } }
        );
        assert.equal(callbackCount, 1);

        const inspection = emdash.inspect(evaluated);
        const evidence = inspection.abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-context-bracket'
        ) {
            assert.fail('Missing displayed contextual evidence');
        }
        assert.equal(evidence.body.tag, 'typed-application');
        if (evidence.body.tag !== 'typed-application') {
            assert.fail('Displayed evaluation lost its application IR');
        }
        assert.equal(
            evidence.body.judgmentId,
            'displayed-evaluation.varying-argument'
        );
        assert.equal(evidence.body.subject.tag, 'slot-reference');
        assert.equal(evidence.body.argument.tag, 'slot-reference');
        assert.equal(Object.isFrozen(inspection), true);
        assert.equal(Object.isFrozen(inspection.ir), true);
        assert.equal(Object.isFrozen(evidence.body), true);

        const compilation = emdash.compile(evaluated);
        assert.equal(compilation.surfaceType.tag, 'displayed-functor');
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-evaluation/u
        );
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-product-pair/u
        );
        assert.doesNotMatch(compilation.explicitCore, /Eval_funcd/u);
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'stable-functor-family'
            ),
            true
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'displayed-evaluation'
            ),
            true
        );
    });

    it('recurses through independently varying subject and argument', () => {
        const {
            emdash,
            B,
            E,
            D,
            H,
            G
        } = fixture();
        let callbackCount = 0;
        const nested = emdash.displayedContextLambda(
            [
                { name: 'e', family: E },
                { name: 'd', family: D }
            ],
            B,
            ([e, d]) => {
                callbackCount += 1;
                return emdash.apply(
                    emdash.apply(H, e),
                    emdash.apply(G, d)
                );
            },
            { source: { line: 30 } }
        );
        assert.equal(callbackCount, 1);
        const evidence = emdash.inspect(nested).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-context-bracket' ||
            evidence.body.tag !== 'typed-application'
        ) {
            assert.fail('Missing recursive evaluation evidence');
        }
        assert.equal(
            evidence.body.judgmentId,
            'displayed-evaluation.varying-argument'
        );
        assert.equal(evidence.body.subject.tag, 'typed-application');
        assert.equal(evidence.body.argument.tag, 'typed-application');
        if (
            evidence.body.subject.tag !== 'typed-application' ||
            evidence.body.argument.tag !== 'typed-application'
        ) {
            assert.fail('Evaluation children were not stored recursively');
        }
        assert.equal(
            evidence.body.subject.judgmentId,
            'indexed-fibre-functor.object'
        );
        assert.equal(
            evidence.body.argument.judgmentId,
            'indexed-fibre-functor.object'
        );

        const compilation = emdash.compile(nested);
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-evaluation/u
        );
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.generic-category-composition/u
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'displayed-product-left-projection'
            ),
            true
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'displayed-product-right-projection'
            ),
            true
        );
    });

    it('derives fixed F a through terminal weakening and constant sections', () => {
        const {
            emdash,
            A,
            B,
            stable
        } = fixture();
        const a = emdash.object('a', A, { line: 40 });
        const fixed = emdash.displayedContextLambda(
            [{ name: 'F', family: stable }],
            B,
            ([F]) => emdash.apply(F, a),
            { source: { line: 41 } }
        );
        const evidence = emdash.inspect(fixed).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-context-bracket'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-context-bracket' ||
            evidence.body.tag !== 'typed-application'
        ) {
            assert.fail('Missing fixed evaluation evidence');
        }
        assert.equal(
            evidence.body.judgmentId,
            'displayed-evaluation.fixed-argument'
        );

        const compilation = emdash.compile(fixed);
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-terminal/u
        );
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.constant-section-functor/u
        );
        assert.match(
            compilation.explicitCore,
            /emdash\.categorical\.displayed-evaluation/u
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'displayed-terminal'
            ),
            true
        );
        assert.equal(
            compilation.dependentPrerequisites.includes(
                'constant-section-functor'
            ),
            true
        );
    });

    it('keeps object, arrow, reindexing, and iterable action generic', () => {
        const {
            emdash,
            K,
            A,
            B,
            stable,
            constant
        } = fixture();
        const evaluated = emdash.displayedContextLambda(
            [
                { name: 'F', family: stable },
                { name: 'x', family: constant }
            ],
            B,
            ([F, x]) => emdash.apply(F, x)
        );
        const k = emdash.object('k', K, { line: 50 });
        const l = emdash.object('l', K, { line: 51 });
        const p = emdash.hom('p', K, k, l, { line: 52 });

        const stableFibre = emdash.compareCategories(
            emdash.fibre(stable, k),
            emdash.functorCategory(A, emdash.fibre(B, k)),
            4_000
        );
        assert.equal(stableFibre.status, 'equal');
        assert.equal(
            runtimeRuleIds(stableFibre).includes(
                'categorical.displayed-evaluation.' +
                    'stable-functor-family-fibre'
            ),
            true
        );

        const point = emdash.compile(
            emdash.apply(evaluated, k, {
                expectedShape: 'fibre-functor'
            })
        );
        assert.equal(point.surfaceType.tag, 'functor');
        assert.equal(point.explicitInferredType, point.explicitExpectedType);

        const capped = emdash.apply(evaluated, p, {
            expectedShape: 'transport-functor'
        });
        const fullAction = emdash.displayedFunctorFullAction(
            evaluated,
            k,
            l
        );
        const fullAtP = emdash.apply(fullAction, p);
        const arrow = emdash.compare(capped, fullAtP, 20_000);
        assert.equal(arrow.status, 'equal');
        assert.deepEqual(
            runtimeRuleIds(arrow),
            [
                'categorical.displayed-functor-transport.delta',
                'categorical.transfor-full-action.evaluate.cat-normalize'
            ]
        );
        assert.equal(
            emdash.compile(fullAction).surfaceType.tag,
            'functor'
        );

        const L = emdash.category('L', { line: 55 });
        const u = emdash.functor('u', L, K, { line: 56 });
        const reindexed = emdash.compile(
            emdash.pullbackDisplayedFunctor(evaluated, u)
        );
        assert.equal(reindexed.surfaceType.tag, 'displayed-functor');
        assert.match(
            reindexed.explicitCore,
            /emdash\.categorical\.displayed-pullback-functor/u
        );
    });

    it('rejects wrong families, wrong fixed objects, variance, and profiles', () => {
        const {
            emdash,
            K,
            A,
            B,
            stable,
            constant
        } = fixture();
        const wrongFamily = emdash.displayedFamily('Wrong', K);
        assert.throws(
            () => emdash.displayedContextLambda(
                [
                    { name: 'F', family: stable },
                    { name: 'wrong', family: wrongFamily }
                ],
                B,
                ([F, wrong]) => emdash.apply(F, wrong)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        const C = emdash.category('C');
        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'F', family: stable }],
                B,
                ([F]) => emdash.apply(F, emdash.object('c', C))
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        const arbitrarySubject =
            emdash.displayedFamily('ArbitrarySubject', K);
        assert.throws(
            () => emdash.displayedContextLambda(
                [
                    { name: 'F', family: arbitrarySubject },
                    { name: 'x', family: constant }
                ],
                B,
                ([F, x]) => emdash.apply(F, x)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'EXPECTED_FUNCTOR'
        );

        const earlier = new CoreCategoricalProgram({
            profile: 'fibred-displayed-bracket-1'
        });
        const earlierK = earlier.category('K');
        const earlierA = earlier.category('A');
        assert.throws(
            () => earlier.constantDisplayedFamily(earlierK, earlierA),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DISPLAYED_EVALUATION'
        );

        const foreign = new CoreCategoricalProgram({
            profile: 'fibred-displayed-evaluation-1'
        });
        const foreignK = foreign.category('ForeignK');
        const foreignB = foreign.displayedFamily('ForeignB', foreignK);
        assert.throws(
            () => emdash.displayedFunctorFamily(A, foreignB),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'FOREIGN_DISPLAYED_FAMILY'
        );
    });
});
