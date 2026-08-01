/**
 * DIRECT-MIXED-INTRODUCTION-1D direct recursive binder coverage.
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
    coreCategoricalMixedActionCoreName
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

const fixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/categorical-direct-mixed-${suffix}.ts`,
        profile: 'fibred-direct-mixed-introduction-1'
    });
    const K = emdash.category(`direct_mixed_${suffix}_K`);
    const opK = emdash.oppositeCategory(K);
    const C = emdash.displayedFamily(
        `direct_mixed_${suffix}_C`,
        K
    );
    const A = emdash.displayedFamily(
        `direct_mixed_${suffix}_A`,
        opK
    );
    const B = emdash.displayedFamily(
        `direct_mixed_${suffix}_B`,
        K
    );
    const D = emdash.displayedFamily(
        `direct_mixed_${suffix}_D`,
        K
    );
    const E = emdash.displayedFamily(
        `direct_mixed_${suffix}_E`,
        K
    );
    const AB = emdash.mixedDisplayedFunctorFamily(A, B);
    const F = emdash.displayedFunctor(
        `direct_mixed_${suffix}_F`,
        C,
        AB
    );
    const G = emdash.displayedFunctor(
        `direct_mixed_${suffix}_G`,
        B,
        D
    );
    const H = emdash.displayedFunctor(
        `direct_mixed_${suffix}_H`,
        D,
        E
    );
    return { emdash, K, opK, C, A, B, D, E, F, G, H };
};

describe('DIRECT-MIXED-INTRODUCTION-1D direct binder', () => {
    it('lowers exact nested eta directly to F with three scoped binders',
    () => {
        const { emdash, C, A, B, F } = fixture('eta');
        let calls = 0;
        const result = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, a) => {
                calls += 1;
                return emdash.apply(emdash.apply(F, c), a);
            }
        );
        const compiled = emdash.compile(result);
        const inspection = emdash.inspect(result);
        const evidence = inspection.abstractions.find(candidate =>
            candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );

        assert.equal(calls, 1);
        assert.equal(
            compiled.explicitCore,
            '(free "direct_mixed_eta_F")'
        );
        assert.equal(
            compiled.explicitInferredType,
            compiled.explicitExpectedType
        );
        assert.doesNotMatch(compiled.explicitCore, /mixed_curry/u);
        assert.ok(evidence);
        assert.deepEqual(evidence.bindingNames, ['cBase', 'c', 'a']);
        assert.deepEqual(
            evidence.bindingModes,
            ['natural', 'functorial', 'functorial']
        );
        assert.equal(evidence.contextSize, 3);
        assert.equal(evidence.targetChainLength, 0);
        assert.equal(evidence.body.tag, 'typed-application');
        if (evidence.body.tag !== 'typed-application') {
            assert.fail('Missing direct mixed eta body');
        }
        assert.equal(evidence.body.argument.tag, 'slot-reference');
        if (evidence.body.argument.tag === 'slot-reference') {
            assert.equal(evidence.body.argument.index, 0);
        }
        assert.equal(evidence.body.subject.tag, 'typed-application');
        if (evidence.body.subject.tag === 'typed-application') {
            assert.equal(
                evidence.body.subject.argument.tag,
                'slot-reference'
            );
            if (
                evidence.body.subject.argument.tag ===
                    'slot-reference'
            ) {
                assert.equal(evidence.body.subject.argument.index, 1);
            }
            assert.equal(
                evidence.body.subject.subject.tag,
                'typed-application'
            );
            if (
                evidence.body.subject.subject.tag ===
                    'typed-application' &&
                evidence.body.subject.subject.argument.tag ===
                    'slot-reference'
            ) {
                assert.equal(
                    evidence.body.subject.subject.argument.index,
                    2
                );
            }
        }
        assertDeepFrozen(inspection);
    });

    it('recursively maps one and two coherent target functors', () => {
        const { emdash, C, A, D, E, F, G, H } =
            fixture('mapped');
        const one = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            D,
            (c, a) => emdash.apply(
                G,
                emdash.apply(emdash.apply(F, c), a)
            )
        );
        const two = emdash.mixedDisplayedFunctorLambda(
            { name: 'c2', family: C },
            { name: 'a2', family: A },
            E,
            (c, a) => emdash.apply(
                H,
                emdash.apply(
                    G,
                    emdash.apply(emdash.apply(F, c), a)
                )
            )
        );
        const oneCompiled = emdash.compile(one);
        const twoCompiled = emdash.compile(two);
        const actionName = coreCategoricalMixedActionCoreName(
            'mixedFunctorFamilyPartial'
        );
        const oneEvidence = emdash.inspect(one).abstractions.find(
            evidence =>
                evidence.rule ===
                    'categorical.direct-mixed-displayed-functor'
        );
        const twoEvidence = emdash.inspect(two).abstractions.find(
            evidence =>
                evidence.rule ===
                    'categorical.direct-mixed-displayed-functor'
        );

        assert.match(
            oneCompiled.explicitCore,
            /emdash\.categorical\.generic-category-composition/u
        );
        assert.match(oneCompiled.explicitCore, /functor-hom-capped/u);
        assert.match(oneCompiled.explicitCore, new RegExp(actionName, 'u'));
        assert.doesNotMatch(oneCompiled.explicitCore, /mixed_curry/u);
        assert.equal(oneCompiled.surfaceType.tag, 'displayed-functor');
        assert.equal(oneCompiled.productionLambdapiDependency, false);
        assert.equal(oneEvidence?.targetChainLength, 1);
        assert.equal(twoEvidence?.targetChainLength, 2);
        assert.equal(twoCompiled.surfaceType.tag, 'displayed-functor');
        assert.equal(twoCompiled.productionLambdapiDependency, false);
    });

    it('fails closed for wrong variance, noncanonical and unsupported bodies',
    () => {
        const { emdash, K, opK, C, A, B, D, F } =
            fixture('negative');
        const wrongA = emdash.displayedFamily(
            'direct_mixed_negative_wrong_A',
            K
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: wrongA },
                B,
                (_c, _a) => emdash.apply(
                    emdash.displayedFunctor(
                        'direct_mixed_negative_CB',
                        C,
                        B
                    ),
                    _c
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );

        const otherA = emdash.displayedFamily(
            'direct_mixed_negative_other_A',
            opK
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: otherA },
                B,
                (c, a) => emdash.apply(emdash.apply(F, c), a)
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        const noncanonical = emdash.displayedFunctor(
            'direct_mixed_negative_noncanonical',
            C,
            B
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (c, _a) => emdash.apply(noncanonical, c)
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );

        const product = emdash.displayedProduct(B, B);
        const consumePair = emdash.displayedFunctor(
            'direct_mixed_negative_consume_pair',
            product,
            D
        );
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                D,
                (c, a) => {
                    const leaf = emdash.apply(
                        emdash.apply(F, c),
                        a
                    );
                    return emdash.apply(
                        consumePair,
                        emdash.fibrePair(leaf, leaf)
                    );
                }
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );

        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (c, _a) => emdash.apply(emdash.apply(F, c), _a),
                { polarity: 'contravariant' }
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'POLARITY_MISMATCH'
        );
    });

    it('keeps the binder behind its dedicated profile', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('direct_mixed_gate_K');
        const C = emdash.displayedFamily('direct_mixed_gate_C', K);
        const A = emdash.displayedFamily(
            'direct_mixed_gate_A',
            emdash.oppositeCategory(K)
        );
        const B = emdash.displayedFamily('direct_mixed_gate_B', K);
        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (_c, _a) => _c
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code ===
                    'UNAVAILABLE_DIRECT_MIXED_INTRODUCTION'
        );
    });
});
