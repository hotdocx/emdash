/**
 * D-DTTLF-USABILITY-080 unary displayed-natural endpoint context.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalDisplayedFamily,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-displayed-natural-endpoint-context.ts';

const familyBinding = (
    name: string,
    value: CoreCategoricalDisplayedFamily
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'displayed-family' as const,
    value
});

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile,
        profile: 'compositional-natural-binder-1'
    });
    const K = emdash.category('natural_endpoint_K');
    const E = emdash.displayedFamily('natural_endpoint_E', K);
    const product = emdash.displayedProduct(E, E);
    const diagonal = emdash.displayedFunctorLambda(
        'natural_endpoint_diagonal',
        E,
        product,
        a => emdash.fibrePair(a, a)
    );
    const x = emdash.object('natural_endpoint_x', K);
    const y = emdash.object('natural_endpoint_y', K);
    const p = emdash.hom('natural_endpoint_p', K, x, y);
    const u = emdash.object(
        'natural_endpoint_u',
        emdash.fibre(E, x)
    );
    return {
        emdash,
        K,
        E,
        product,
        diagonal,
        x,
        y,
        p,
        u
    };
};

let sharedFixture: ReturnType<typeof fixture> | undefined;
const data = (): ReturnType<typeof fixture> => {
    sharedFixture ??= fixture();
    return sharedFixture;
};

const fibreFunctor = (
    emdash: CoreCategoricalProgram,
    functor: CoreCategoricalTerm,
    base: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    functor,
    base,
    { expectedShape: 'fibre-functor' }
);

const expandedDiagonalIdentity = (
    emdash: CoreCategoricalProgram,
    diagonal: CoreCategoricalTerm,
    onOuter: () => void = () => undefined,
    onInner: () => void = () => undefined
): CoreCategoricalTerm => emdash.transforLambda(
    'naturalEndpointBase',
    diagonal,
    diagonal,
    k => {
        onOuter();
        return emdash.transforLambda(
            'naturalEndpointFibre',
            fibreFunctor(emdash, diagonal, k),
            fibreFunctor(emdash, diagonal, k),
            a => {
                onInner();
                return emdash.identityCell(emdash.fibrePair(a, a));
            }
        );
    }
);

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

describe('DISPLAYED-NATURAL-ENDPOINT-CONTEXT-1G', () => {
    it('shares diagonal identity across compact, expanded, and closed forms',
        () => {
            const {
                emdash,
                diagonal
            } = data();
            let compactCallbacks = 0;
            let expandedOuterCallbacks = 0;
            let expandedInnerCallbacks = 0;
            const compact = emdash.displayedTransforContextLambda(
                'naturalEndpointCompact',
                diagonal,
                diagonal,
                a => {
                    compactCallbacks += 1;
                    return emdash.identityCell(emdash.fibrePair(a, a));
                }
            );
            const expanded = expandedDiagonalIdentity(
                emdash,
                diagonal,
                () => {
                    expandedOuterCallbacks += 1;
                },
                () => {
                    expandedInnerCallbacks += 1;
                }
            );
            const closed = emdash.identityCell(diagonal);

            assert.equal(compactCallbacks, 1);
            assert.equal(expandedOuterCallbacks, 1);
            assert.equal(expandedInnerCallbacks, 1);
            assertExactCompilation(emdash, compact, expanded);
            assertExactCompilation(emdash, compact, closed);
            assert.equal(emdash.compare(compact, closed).status, 'equal');

            const evidence = emdash.inspect(compact).abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.displayed-transfor-context-identity'
            );
            if (
                evidence?.rule !==
                    'categorical.displayed-transfor-context-identity'
            ) {
                assert.fail('Missing contextual diagonal identity evidence');
            }
            assert.equal(evidence.body.tag, 'typed-cell-identity');
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
                /emdash_v3_2_scale_stress_3a2a_id/u
            );
        });

    it('retains point and internal base-arrow/higher action', () => {
        const {
            emdash,
            diagonal,
            x,
            p,
            u
        } = data();
        const compact = emdash.displayedTransforContextLambda(
            'naturalEndpointAction',
            diagonal,
            diagonal,
            a => emdash.identityCell(emdash.fibrePair(a, a))
        );
        const closed = emdash.identityCell(diagonal);
        const actualPoint = emdash.displayedTransforPoint(
            compact,
            x,
            u
        );
        const expectedPoint = emdash.displayedTransforPoint(
            closed,
            x,
            u
        );
        const actualAction = emdash.displayedTransforNaturality(
            compact,
            p,
            u
        );
        const expectedAction = emdash.displayedTransforNaturality(
            closed,
            p,
            u
        );

        assert.equal(
            emdash.compare(actualPoint, expectedPoint).status,
            'equal'
        );
        assert.equal(
            emdash.compare(actualAction, expectedAction, 60_000).status,
            'equal'
        );
        assert.match(
            emdash.compile(actualAction).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('inherits compact text parity without a parser or resolver branch',
        () => {
            const {
                emdash,
                E,
                diagonal
            } = data();
            const direct = emdash.displayedTransforContextLambda(
                'a',
                diagonal,
                diagonal,
                a => emdash.identityCell(emdash.fibrePair(a, a))
            );
            const parsed = elaborateCoreCategoricalText(emdash, {
                source:
                    'λ^nd a : E. identityCell (fibrePair a a)',
                sourceFile,
                environment: Object.freeze([
                    familyBinding('E', E)
                ]),
                expected: Object.freeze({
                    kind: 'displayed-context-transfor' as const,
                    sourceFamily: E,
                    source: diagonal,
                    target: diagonal
                })
            });

            assertExactCompilation(emdash, parsed, direct);
            assert.equal(emdash.compare(parsed, direct).status, 'equal');
            assert.equal(
                emdash.inspect(parsed).abstractions.at(-1)?.rule,
                'categorical.displayed-transfor-context-identity'
            );
        });

    it('preserves direct-only and endpoint-mismatch rejection', () => {
        const {
            emdash,
            E,
            diagonal
        } = data();
        const identity = emdash.displayedFunctorLambda(
            'natural_endpoint_identity',
            E,
            E,
            a => a
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'naturalEndpointMismatch',
                identity,
                identity,
                a => emdash.identityCell(emdash.fibrePair(a, a))
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        const directOnly = new CoreCategoricalProgram({
            profile: 'fibred-transfd-1'
        });
        const directK = directOnly.category('direct_only_K');
        const directE = directOnly.displayedFamily(
            'direct_only_E',
            directK
        );
        const directProduct = directOnly.displayedProduct(
            directE,
            directE
        );
        const declaredDiagonal = directOnly.displayedFunctor(
            'direct_only_diagonal',
            directE,
            directProduct
        );
        assert.throws(
            () => directOnly.displayedTransforContextLambda(
                'directOnlyRejected',
                declaredDiagonal,
                declaredDiagonal,
                a => directOnly.identityCell(
                    directOnly.fibrePair(a, a)
                )
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DISPLAYED_CONTEXT'
        );

        assert.equal(
            emdash.compare(
                emdash.displayedTransforContextLambda(
                    'naturalEndpointDirectPreserved',
                    diagonal,
                    diagonal,
                    a => emdash.identityCell(emdash.fibrePair(a, a))
                ),
                emdash.identityCell(diagonal)
            ).status,
            'equal'
        );
    });
});
