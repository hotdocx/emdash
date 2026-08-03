/**
 * D-DTTLF-USABILITY-079 displayed-functor contextual-engine sharing.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalTerm
} from '../src/v3_2';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const point = (
    emdash: CoreCategoricalProgram,
    transformation: CoreCategoricalTerm,
    argument: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    transformation,
    argument,
    { expectedShape: 'point-component' }
);

const map = (
    emdash: CoreCategoricalProgram,
    functor: CoreCategoricalTerm,
    argument: CoreCategoricalTerm,
    expectedShape: 'object-value' | 'arrow-value' = 'object-value'
): CoreCategoricalTerm => emdash.apply(
    functor,
    argument,
    { expectedShape }
);

const buildFixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/' +
            'categorical-displayed-functor-contextual-engine.ts',
        profile: 'compositional-natural-binder-1'
    });
    const K = emdash.category('contextual_engine_K');
    const A = emdash.category('contextual_engine_A');
    const E = emdash.displayedFamily('contextual_engine_E', K);
    const D = emdash.displayedFamily('contextual_engine_D', K);
    const Q = emdash.displayedFamily('contextual_engine_Q', K);
    const B = emdash.displayedFamily('contextual_engine_B', K);
    const F = emdash.displayedFunctor('contextual_engine_F', E, D);
    const G = emdash.displayedFunctor('contextual_engine_G', D, Q);
    const section = emdash.section('contextual_engine_s', D);
    const stable = emdash.displayedFunctorFamily(A, B);
    const a0 = emdash.object('contextual_engine_a0', A);
    const x = emdash.object('contextual_engine_x', K);
    const y = emdash.object('contextual_engine_y', K);
    const p = emdash.hom('contextual_engine_p', K, x, y);
    return {
        emdash,
        K,
        A,
        E,
        D,
        Q,
        B,
        F,
        G,
        section,
        stable,
        a0,
        x,
        y,
        p
    };
};

let sharedFixture: ReturnType<typeof buildFixture> | undefined;
const fixture = (): ReturnType<typeof buildFixture> => {
    sharedFixture ??= buildFixture();
    return sharedFixture;
};

const assertExactCompilation = (
    emdash: CoreCategoricalProgram,
    left: CoreCategoricalTerm,
    right: CoreCategoricalTerm
): void => {
    const leftCompilation = emdash.compile(left);
    const rightCompilation = emdash.compile(right);
    assert.equal(
        leftCompilation.explicitCore,
        rightCompilation.explicitCore
    );
    assert.equal(
        leftCompilation.explicitInferredType,
        rightCompilation.explicitInferredType
    );
};

describe('DISPLAYED-FUNCTOR-CONTEXTUAL-ENGINE-1F', () => {
    it('preserves the four historical fast paths exactly', () => {
        const {
            emdash,
            E,
            D,
            Q,
            F,
            G,
            section
        } = fixture();
        const cases = [
            {
                rule: 'categorical.displayed-functor-identity',
                compact: emdash.displayedFunctorLambda(
                    'identityCompact',
                    E,
                    E,
                    a => a
                ),
                contextual: emdash.displayedContextLambda(
                    [{ name: 'identityContextual', family: E }],
                    E,
                    ([a]) => a
                )
            },
            {
                rule: 'categorical.displayed-functor-eta',
                compact: emdash.displayedFunctorLambda(
                    'etaCompact',
                    E,
                    D,
                    a => map(emdash, F, a)
                ),
                contextual: emdash.displayedContextLambda(
                    [{ name: 'etaContextual', family: E }],
                    D,
                    ([a]) => map(emdash, F, a)
                )
            },
            {
                rule: 'categorical.displayed-functor-composition',
                compact: emdash.displayedFunctorLambda(
                    'compositionCompact',
                    E,
                    Q,
                    a => map(emdash, G, map(emdash, F, a))
                ),
                contextual: emdash.displayedContextLambda(
                    [{ name: 'compositionContextual', family: E }],
                    Q,
                    ([a]) => map(
                        emdash,
                        G,
                        map(emdash, F, a)
                    )
                )
            },
            {
                rule: 'categorical.displayed-functor-weakening',
                compact: emdash.displayedFunctorLambda(
                    'weakeningCompact',
                    E,
                    D,
                    a => emdash.apply(section, emdash.indexOf(a))
                ),
                contextual: emdash.displayedContextLambda(
                    [{ name: 'weakeningContextual', family: E }],
                    D,
                    ([a]) => emdash.apply(
                        section,
                        emdash.indexOf(a)
                    )
                )
            }
        ] as const;

        for (const candidate of cases) {
            assertExactCompilation(
                emdash,
                candidate.compact,
                candidate.contextual
            );
            assert.equal(
                emdash.inspect(candidate.compact)
                    .abstractions.at(-1)?.rule,
                candidate.rule
            );
        }
    });

    it('shares fixed evaluation across compact, contextual, and expanded forms', () => {
        const {
            emdash,
            stable,
            B,
            a0
        } = fixture();
        let compactCallbacks = 0;
        let contextualCallbacks = 0;
        let expandedOuterCallbacks = 0;
        let expandedInnerCallbacks = 0;
        const compact = emdash.displayedFunctorLambda(
            'fixedEvaluationCompact',
            stable,
            B,
            F => {
                compactCallbacks += 1;
                return map(emdash, F, a0);
            }
        );
        const contextual = emdash.displayedContextLambda(
            [{ name: 'fixedEvaluationContextual', family: stable }],
            B,
            ([F]) => {
                contextualCallbacks += 1;
                return map(emdash, F, a0);
            }
        );
        const expanded = emdash.transforLambda(
            'fixedEvaluationBase',
            stable,
            B,
            k => {
                expandedOuterCallbacks += 1;
                return emdash.lambda(
                    'fixedEvaluationOpen',
                    emdash.fibre(stable, k),
                    emdash.fibre(B, k),
                    F => {
                        expandedInnerCallbacks += 1;
                        return map(emdash, F, a0);
                    }
                );
            }
        );

        assert.equal(compactCallbacks, 1);
        assert.equal(contextualCallbacks, 1);
        assert.equal(expandedOuterCallbacks, 1);
        assert.equal(expandedInnerCallbacks, 1);
        assertExactCompilation(emdash, compact, contextual);
        assert.equal(
            emdash.compile(compact).explicitCore,
            emdash.compile(expanded).explicitCore
        );

        const inspection = emdash.inspect(compact);
        const evidence = inspection.abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-functor-contextual'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-functor-contextual'
        ) {
            assert.fail('Missing contextual displayed-functor evidence');
        }
        assert.equal(evidence.chainLength, 0);
        assert.equal(
            evidence.structuralPrerequisites.includes('product-pair'),
            true
        );
        assert.equal(
            evidence.dependentPrerequisites.includes(
                'displayed-evaluation'
            ),
            true
        );
        assert.equal(
            evidence.dependentPrerequisites.includes(
                'constant-section-functor'
            ),
            true
        );
        assert.match(
            emdash.compile(compact).explicitCore,
            /emdash\.categorical\.displayed-evaluation/u
        );
        assertDeepFrozen(inspection);
    });

    it('retains fixed-evaluation object and consumed base-arrow action', () => {
        const {
            emdash,
            stable,
            B,
            a0,
            x,
            y,
            p
        } = fixture();
        const compact = emdash.displayedFunctorLambda(
            'fixedEvaluationActionCompact',
            stable,
            B,
            F => map(emdash, F, a0)
        );
        const contextual = emdash.displayedContextLambda(
            [{ name: 'fixedEvaluationActionContextual', family: stable }],
            B,
            ([F]) => map(emdash, F, a0)
        );
        const expanded = emdash.transforLambda(
            'fixedEvaluationActionBase',
            stable,
            B,
            k => emdash.lambda(
                'fixedEvaluationActionOpen',
                emdash.fibre(stable, k),
                emdash.fibre(B, k),
                F => map(emdash, F, a0)
            )
        );
        const compactAtX = emdash.apply(
            compact,
            x,
            { expectedShape: 'fibre-functor' }
        );
        const contextualAtX = emdash.apply(
            contextual,
            x,
            { expectedShape: 'fibre-functor' }
        );
        const expandedAtX = point(emdash, expanded, x);
        const stableX = emdash.fibre(stable, x);
        const F0 = emdash.object('contextual_engine_F0', stableX);

        assert.equal(
            emdash.compare(
                map(emdash, compactAtX, F0),
                map(emdash, contextualAtX, F0),
                8_000
            ).status,
            'equal'
        );
        assert.equal(
            emdash.compare(
                map(emdash, compactAtX, F0),
                map(emdash, expandedAtX, F0),
                8_000
            ).status,
            'equal'
        );

        const fullAction = emdash.displayedFunctorFullAction(
            compact,
            x,
            y
        );
        const consumed = emdash.apply(fullAction, p);
        const capped = emdash.apply(
            compact,
            p,
            { expectedShape: 'transport-functor' }
        );
        assert.equal(
            emdash.compare(consumed, capped, 20_000).status,
            'equal'
        );
        assert.match(
            emdash.compile(fullAction).explicitCore,
            /transfor-hom-full/u
        );
        assert.equal(emdash.compile(consumed).surfaceType.tag, 'functor');
    });

    it('shares a one-variable fibre diagonal across all three forms', () => {
        const {
            emdash,
            E
        } = fixture();
        const product = emdash.displayedProduct(E, E);
        const compact = emdash.displayedFunctorLambda(
            'diagonalCompact',
            E,
            product,
            a => emdash.fibrePair(a, a)
        );
        const contextual = emdash.displayedContextLambda(
            [{ name: 'diagonalContextual', family: E }],
            product,
            ([a]) => emdash.fibrePair(a, a)
        );
        const expanded = emdash.transforLambda(
            'diagonalBase',
            E,
            product,
            k => emdash.lambda(
                'diagonalOpen',
                emdash.fibre(E, k),
                emdash.fibre(product, k),
                a => emdash.fibrePair(a, a)
            )
        );

        assertExactCompilation(emdash, compact, contextual);
        assert.equal(
            emdash.compile(compact).explicitCore,
            emdash.compile(expanded).explicitCore
        );
        const evidence = emdash.inspect(compact).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-functor-contextual'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-functor-contextual'
        ) {
            assert.fail('Missing contextual diagonal evidence');
        }
        assert.equal(
            evidence.structuralPrerequisites.includes('product-pair'),
            true
        );
        assert.equal(
            evidence.dependentPrerequisites.includes(
                'displayed-product-pair'
            ),
            true
        );
        assert.match(
            emdash.compile(compact).explicitCore,
            /displayed-product-pair/u
        );
    });

    it('preserves the base profile and rejects nonlocal capture', () => {
        const base = new CoreCategoricalProgram({
            profile: 'fibred-binder-1'
        });
        const baseK = base.category('contextual_engine_base_K');
        const baseE = base.displayedFamily(
            'contextual_engine_base_E',
            baseK
        );
        assert.throws(
            () => base.displayedFunctorLambda(
                'baseDiagonal',
                baseE,
                baseE,
                a => base.fibrePair(a, a)
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DISPLAYED_CONTEXT'
        );

        const {
            emdash,
            A,
            stable,
            B
        } = fixture();
        const displayedFunctorCategory =
            emdash.displayedFunctorCategory(stable, B);
        assert.throws(
            () => emdash.lambda(
                'capturedFixedArgument',
                A,
                displayedFunctorCategory,
                captured => emdash.displayedFunctorLambda(
                    'capturingDisplayedFunctor',
                    stable,
                    B,
                    F => map(emdash, F, captured)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' &&
                /must be a closed object/u.test(
                    error.message
                )
        );
    });
});
