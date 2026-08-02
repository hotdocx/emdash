/**
 * D-DTTLF-USABILITY-076 expanded `lambda^n k. lambda^f a` parity.
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
    CoreCategoricalScopedFibreCategory,
    CoreCategoricalSlotToken,
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
            'tests/fixtures/categorical-compositional-fd-expanded.ts',
        profile: 'compositional-natural-binder-1'
    });
    const K = emdash.category('expanded_fd_K');
    const E = emdash.displayedFamily('expanded_fd_E', K);
    const D = emdash.displayedFamily('expanded_fd_D', K);
    const Q = emdash.displayedFamily('expanded_fd_Q', K);
    const FF = emdash.displayedFunctor('expanded_fd_FF', E, D);
    const GG = emdash.displayedFunctor('expanded_fd_GG', D, Q);
    const x = emdash.object('expanded_fd_x', K);
    const y = emdash.object('expanded_fd_y', K);
    const p = emdash.hom('expanded_fd_p', K, x, y);
    return { emdash, K, E, D, Q, FF, GG, x, y, p };
};

let sharedFixture: ReturnType<typeof buildFixture> | undefined;
const fixture = (): ReturnType<typeof buildFixture> => {
    sharedFixture ??= buildFixture();
    return sharedFixture;
};

describe('COMPOSITIONAL-FD-EXPANDED-1C', () => {
    it('shares eta Core while retaining the expanded Transf_cat facade', () => {
        const { emdash, E, D, FF } = fixture();
        let callbacks = 0;
        let capturedSource:
            CoreCategoricalScopedFibreCategory | undefined;
        let capturedTarget:
            CoreCategoricalScopedFibreCategory | undefined;
        const expanded = emdash.transforLambda(
            'kEta',
            E,
            D,
            k => {
                const Ek = emdash.fibre(E, k);
                const Dk = emdash.fibre(D, k);
                capturedSource = Ek;
                capturedTarget = Dk;
                return emdash.lambda(
                    'aEta',
                    Ek,
                    Dk,
                    a => {
                        callbacks += 1;
                        return map(emdash, FF, a);
                    }
                );
            }
        );
        const compact = emdash.displayedFunctorLambda(
            'aEtaCompact',
            E,
            D,
            a => map(emdash, FF, a)
        );
        const expandedCompilation = emdash.compile(expanded);
        const compactCompilation = emdash.compile(compact);
        const inspection = emdash.inspect(expanded);

        assert.equal(callbacks, 1);
        assert.equal(expandedCompilation.surfaceType.tag, 'transfor');
        assert.equal(
            compactCompilation.surfaceType.tag,
            'displayed-functor'
        );
        assert.equal(
            expandedCompilation.explicitCore,
            compactCompilation.explicitCore
        );
        assert.match(
            expandedCompilation.explicitInferredType,
            /object-classifier/u
        );
        assert.match(
            expandedCompilation.explicitExpectedType,
            /transfor-classifier/u
        );
        assert.equal(
            inspection.abstractions.at(-1)?.rule,
            'categorical.ordinary-transfor-contextual-functor'
        );
        assert.equal(
            inspection.abstractions.some(evidence =>
                evidence.rule === 'categorical.displayed-functor-eta'
            ),
            true
        );
        assertDeepFrozen(inspection);
        assert.ok(capturedSource);
        assert.ok(capturedTarget);
        assert.throws(
            () => emdash.lambda(
                'escaped',
                capturedSource,
                capturedTarget,
                a => a
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );
    });

    it('shares identity and finite-chain Core with compact abstraction', () => {
        const { emdash, E, D, Q, FF, GG } = fixture();
        const expandedIdentity = emdash.transforLambda(
            'kIdentity',
            E,
            E,
            k => emdash.lambda(
                'aIdentity',
                emdash.fibre(E, k),
                emdash.fibre(E, k),
                a => a
            )
        );
        const compactIdentity = emdash.displayedFunctorLambda(
            'aIdentityCompact',
            E,
            E,
            a => a
        );
        const expandedChain = emdash.transforLambda(
            'kChain',
            E,
            Q,
            k => emdash.lambda(
                'aChain',
                emdash.fibre(E, k),
                emdash.fibre(Q, k),
                a => map(emdash, GG, map(emdash, FF, a))
            )
        );
        const compactChain = emdash.displayedFunctorLambda(
            'aChainCompact',
            E,
            Q,
            a => map(emdash, GG, map(emdash, FF, a))
        );

        assert.equal(
            emdash.compile(expandedIdentity).explicitCore,
            emdash.compile(compactIdentity).explicitCore
        );
        assert.equal(
            emdash.compile(expandedChain).explicitCore,
            emdash.compile(compactChain).explicitCore
        );
        assert.equal(
            emdash.inspect(expandedIdentity).abstractions.some(evidence =>
                evidence.rule ===
                    'categorical.displayed-functor-identity'
            ),
            true
        );
        assert.equal(
            emdash.inspect(expandedChain).abstractions.some(evidence =>
                evidence.rule ===
                    'categorical.displayed-functor-composition'
            ),
            true
        );
        assert.match(
            emdash.compile(expandedChain).explicitCore,
            /generic-category-composition/u
        );
    });

    it('preserves closed fibre object, arrow, and base-arrow action', () => {
        const { emdash, E, Q, FF, GG, x, y, p } = fixture();
        const expanded = emdash.transforLambda(
            'kAction',
            E,
            Q,
            k => emdash.lambda(
                'aAction',
                emdash.fibre(E, k),
                emdash.fibre(Q, k),
                a => map(emdash, GG, map(emdash, FF, a))
            )
        );
        const compact = emdash.displayedFunctorLambda(
            'aActionCompact',
            E,
            Q,
            a => map(emdash, GG, map(emdash, FF, a))
        );
        const expandedAtX = point(emdash, expanded, x);
        const compactAtX = emdash.apply(
            compact,
            x,
            { expectedShape: 'fibre-functor' }
        );
        const Ex = emdash.fibre(E, x);
        const u = emdash.object('expanded_fd_u', Ex);
        const v = emdash.object('expanded_fd_v', Ex);
        const alpha = emdash.hom('expanded_fd_alpha', Ex, u, v);

        assert.equal(
            emdash.compare(expandedAtX, compactAtX, 8_000).status,
            'equal'
        );
        assert.equal(
            emdash.compare(
                map(emdash, expandedAtX, u),
                map(emdash, compactAtX, u),
                8_000
            ).status,
            'equal'
        );
        assert.equal(
            emdash.compare(
                map(emdash, expandedAtX, alpha, 'arrow-value'),
                map(emdash, compactAtX, alpha, 'arrow-value'),
                8_000
            ).status,
            'equal'
        );

        const fullAction = emdash.displayedFunctorFullAction(
            compact,
            x,
            y
        );
        const atP = emdash.apply(fullAction, p);
        assert.match(
            emdash.compile(fullAction).explicitCore,
            /transfor-hom-full/u
        );
        assert.equal(emdash.compile(atP).surfaceType.tag, 'functor');
        assert.equal(
            emdash.compile(expanded).explicitCore,
            emdash.compile(compact).explicitCore
        );
    });

    it('fails closed on mismatches and an unfactorable fibre pair', () => {
        const { emdash, K, E, D, x } = fixture();
        const L = emdash.category('expanded_fd_L');
        const R = emdash.displayedFamily('expanded_fd_R', L);
        assert.throws(
            () => emdash.transforLambda(
                'kWrongBase',
                E,
                R,
                _k => {
                    throw new Error('unreachable');
                }
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
        assert.throws(
            () => emdash.transforLambda(
                'kWrongTarget',
                E,
                D,
                k => emdash.lambda(
                    'aWrongTarget',
                    emdash.fibre(E, k),
                    emdash.fibre(D, k),
                    a => a
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.transforLambda(
                'kMixedClosed',
                E,
                D,
                k => emdash.lambda(
                    'aMixedClosed',
                    emdash.fibre(E, k),
                    emdash.fibre(D, x) as unknown as
                        CoreCategoricalScopedFibreCategory,
                    a => a
                )
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );

        const product = emdash.displayedProduct(E, E);
        assert.throws(
            () => emdash.transforLambda(
                'kUnfactored',
                E,
                product,
                k => emdash.lambda(
                    'aUnfactored',
                    emdash.fibre(E, k),
                    emdash.fibre(product, k),
                    a => emdash.fibrePair(a, a)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );

        assert.equal(K.label, 'expanded_fd_K');
    });

    it('preserves root natural and compact displayed-natural binders', () => {
        const { emdash, K, E, D, FF } = fixture();
        const A = emdash.category('expanded_fd_A');
        const B = emdash.category('expanded_fd_B');
        const F = emdash.functor('expanded_fd_F', A, B);
        const G = emdash.functor('expanded_fd_G', A, B);
        const eta = emdash.transfor('expanded_fd_eta', F, G);
        const ordinary = emdash.transforLambda(
            'ordinaryStillWorks',
            F,
            G,
            a => point(emdash, eta, a)
        );
        const compactFd = emdash.displayedFunctorLambda(
            'compactFdStillWorks',
            E,
            D,
            a => map(emdash, FF, a)
        );
        const HH = emdash.displayedFunctor(
            'expanded_fd_HH',
            E,
            D
        );
        const displayedEta = emdash.displayedTransfor(
            'expanded_fd_displayed_eta',
            FF,
            HH
        );
        const compactNd = emdash.displayedTransforLambda(
            'compactNdStillWorks',
            FF,
            HH,
            k => emdash.apply(displayedEta, k, {
                expectedShape: 'displayed-component'
            })
        );

        assert.equal(emdash.compile(ordinary).explicitCore,
            emdash.compile(eta).explicitCore);
        assert.equal(
            emdash.compile(compactFd).surfaceType.tag,
            'displayed-functor'
        );
        assert.equal(
            emdash.compile(compactNd).surfaceType.tag,
            'displayed-transfor'
        );
        assert.equal(K.label, 'expanded_fd_K');
    });
});
