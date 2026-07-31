/**
 * MIXED-NEST-1A exact recursive nested displayed-functor eta.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError
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

const canonicalFixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/categorical-mixed-nested-${suffix}.ts`,
        profile: 'fibred-displayed-mixed-nest-1'
    });
    const K = emdash.category(`mixed_nested_${suffix}_K`);
    const Z = emdash.category(`mixed_nested_${suffix}_Z`);
    const C = emdash.displayedFamily(
        `mixed_nested_${suffix}_C`,
        K
    );
    const catdZ = emdash.displayedCategoryCategory(Z);
    const classifier = emdash.constantDisplayedFamily(K, catdZ);
    const Ebar = emdash.section(
        `mixed_nested_${suffix}_Ebar`,
        emdash.oppositeDisplayedFamily(classifier)
    );
    const Dbar = emdash.section(
        `mixed_nested_${suffix}_Dbar`,
        classifier
    );
    const innerFamily = emdash.mixedDisplayedHomFamily(
        classifier,
        Ebar,
        Dbar
    );
    const nested = emdash.displayedFunctor(
        `mixed_nested_${suffix}_nested`,
        C,
        innerFamily
    );
    return {
        emdash,
        K,
        Z,
        C,
        innerFamily,
        nested
    };
};

describe('MIXED-NEST-1A recursive mixed factorization', () => {
    it('factors one explicit inner ^fd eta back to the coherent subject',
    () => {
        const {
            emdash,
            C,
            innerFamily,
            nested
        } = canonicalFixture('eta');
        let outerCalls = 0;
        let innerCalls = 0;
        const result = emdash.displayedContextLambda(
            [{ name: 'c', family: C }],
            innerFamily,
            ([c]) => {
                outerCalls += 1;
                const inner = emdash.apply(nested, c);
                return emdash.nestedDisplayedFunctorLambda(
                    'e',
                    inner,
                    e => {
                        innerCalls += 1;
                        return emdash.apply(inner, e);
                    }
                );
            }
        );
        const compiled = emdash.compile(result);
        const inspection = emdash.inspect(result);
        const nestedEvidence = inspection.abstractions.find(
            evidence =>
                evidence.rule ===
                    'categorical.mixed-nested-displayed-eta'
        );
        const outerEvidence = inspection.abstractions.find(
            evidence =>
                evidence.rule ===
                    'categorical.displayed-context-bracket'
        );

        assert.equal(outerCalls, 1);
        assert.equal(innerCalls, 1);
        assert.equal(compiled.explicitCore,
            '(free "mixed_nested_eta_nested")');
        assert.equal(compiled.explicitInferredType,
            compiled.explicitExpectedType);
        assert.equal(compiled.productionLambdapiDependency, false);
        assert.ok(nestedEvidence);
        assert.equal(
            nestedEvidence.body.tag,
            'typed-nested-displayed-application'
        );
        assert.equal(
            nestedEvidence.result.tag,
            'nested-displayed-abstraction'
        );
        assert.ok(outerEvidence);
        assert.equal(
            outerEvidence.body.tag,
            'nested-displayed-abstraction'
        );
        assertDeepFrozen(inspection);
    });

    it('records both locally nameless indices and mixed endpoint polarity',
    () => {
        const {
            emdash,
            C,
            innerFamily,
            nested
        } = canonicalFixture('indices');
        const result = emdash.displayedContextLambda(
            [{ name: 'c', family: C }],
            innerFamily,
            ([c]) => {
                const inner = emdash.apply(nested, c);
                return emdash.nestedDisplayedFunctorLambda(
                    'e',
                    inner,
                    e => emdash.apply(inner, e)
                );
            }
        );
        const evidence = emdash.inspect(result).abstractions.find(
            candidate =>
                candidate.rule ===
                    'categorical.mixed-nested-displayed-eta'
        );
        assert.ok(evidence);
        assert.equal(
            evidence.body.tag,
            'typed-nested-displayed-application'
        );
        if (
            evidence.body.tag !==
                'typed-nested-displayed-application'
        ) {
            assert.fail('Missing typed nested displayed application');
        }
        assert.equal(
            evidence.body.argument.type.tag,
            'nested-indexed-object'
        );
        if (
            evidence.body.argument.type.tag !==
                'nested-indexed-object'
        ) {
            assert.fail('Missing nested indexed-object classifier');
        }
        assert.equal(evidence.body.argument.type.endpoint, 'source');
        assert.equal(evidence.body.type.endpoint, 'target');
        assert.equal(evidence.body.argument.type.innerIndex, 1);
        assert.equal(evidence.body.argument.type.outerIndex, 3);
        assert.equal(evidence.body.argument.tag, 'slot-reference');
        assert.equal(evidence.body.argument.index, 0);
        assert.equal(evidence.body.base.tag, 'slot-reference');
        assert.equal(evidence.body.base.index, 1);
    });

    it('rejects a noncanonical indexed target family', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('mixed_nested_wrong_K');
        const C = emdash.displayedFamily('mixed_nested_wrong_C', K);
        const D = emdash.displayedFamily('mixed_nested_wrong_D', K);
        const FF = emdash.displayedFunctor(
            'mixed_nested_wrong_FF',
            C,
            D
        );
        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'c', family: C }],
                D,
                ([c]) => {
                    const point = emdash.apply(FF, c);
                    return emdash.nestedDisplayedFunctorLambda(
                        'e',
                        point,
                        e => e
                    );
                }
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('rejects pointwise bodies and a different coherent subject', () => {
        const {
            emdash,
            C,
            innerFamily,
            nested
        } = canonicalFixture('negative');
        const other = emdash.displayedFunctor(
            'mixed_nested_negative_other',
            C,
            innerFamily
        );
        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'c', family: C }],
                innerFamily,
                ([c]) => {
                    const inner = emdash.apply(nested, c);
                    return emdash.nestedDisplayedFunctorLambda(
                        'e',
                        inner,
                        e => e
                    );
                }
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assert.throws(
            () => emdash.displayedContextLambda(
                [{ name: 'c', family: C }],
                innerFamily,
                ([c]) => {
                    const inner = emdash.apply(nested, c);
                    const different = emdash.apply(other, c);
                    return emdash.nestedDisplayedFunctorLambda(
                        'e',
                        inner,
                        e => emdash.apply(different, e)
                    );
                }
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
    });

    it('keeps nested factorization behind the mixed profile', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-nd-higher-1'
        });
        const A = emdash.category('mixed_nested_gate_A');
        const x = emdash.object('mixed_nested_gate_x', A);
        assert.throws(
            () => emdash.nestedDisplayedFunctorLambda(
                'e',
                x,
                e => e
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_MIXED_MODE'
        );
    });
});
