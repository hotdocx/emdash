/**
 * MIXED-NEST-0A typed canonical classifier and fold evidence.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramError
} from '../src/v3_2';

describe('MIXED-NEST-0A TypeScript profile', () => {
    it('constructs and checks the canonical nested mixed classifier', () => {
        const emdash = new CoreCategoricalProgram({
            sourceFile: 'tests/fixtures/mixed-nest-0a.ts',
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('mixed_K', { line: 1 });
        const Z = emdash.category('mixed_Z', { line: 2 });
        const C = emdash.displayedFamily('mixed_C', K, { line: 3 });
        const catdZ = emdash.displayedCategoryCategory(
            Z,
            { line: 4 }
        );
        const classifierFamily = emdash.constantDisplayedFamily(
            K,
            catdZ,
            { line: 5 }
        );
        const negativeClassifierFamily =
            emdash.oppositeDisplayedFamily(
                classifierFamily,
                { line: 6 }
            );
        const Ebar = emdash.section(
            'mixed_Ebar',
            negativeClassifierFamily,
            { line: 7 }
        );
        const Dbar = emdash.section(
            'mixed_Dbar',
            classifierFamily,
            { line: 8 }
        );
        const inner = emdash.mixedDisplayedHomFamily(
            classifierFamily,
            Ebar,
            Dbar,
            { line: 9 }
        );
        const classifier = emdash.displayedFunctorCategory(
            C,
            inner,
            { line: 10 }
        );
        const nested = emdash.displayedFunctor(
            'mixed_nested',
            C,
            inner,
            { line: 11 }
        );
        const checked = emdash.compile(nested);
        const serialized = emdash.serializeCategory(classifier);

        assert.match(
            serialized,
            /emdash\.categorical\.displayed-functor-category/u
        );
        assert.match(serialized, /emdash_v3_2_mixed_nest_0a_Hom_catd/u);
        assert.match(serialized, /displayed-category-category/u);
        assert.match(serialized, /mixed_Ebar/u);
        assert.match(serialized, /mixed_Dbar/u);
        assert.equal(
            checked.explicitInferredType,
            checked.explicitExpectedType
        );
        assert.match(
            checked.explicitExpectedType,
            /emdash_v3_2_mixed_nest_0a_Hom_catd/u
        );
        assert.equal(checked.productionLambdapiDependency, false);
    });

    it('reduces Hom_catd of Functor_catd to Transf_catd', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('fold_K');
        const opK = emdash.oppositeCategory(K);
        const A = emdash.displayedFamily('fold_A', opK);
        const B = emdash.displayedFamily('fold_B', K);
        const functors = emdash.mixedDisplayedFunctorFamily(A, B);
        const negativeFunctors =
            emdash.oppositeDisplayedFamily(functors);
        const FF = emdash.section('fold_FF', negativeFunctors);
        const GG = emdash.section('fold_GG', functors);
        const homFamily = emdash.mixedDisplayedHomFamily(
            functors,
            FF,
            GG
        );
        const transforFamily = emdash.mixedDisplayedTransforFamily(
            A,
            B,
            FF,
            GG
        );
        const comparison = emdash.compareDisplayedFamilies(
            homFamily,
            transforFamily
        );
        const eta = emdash.section('fold_eta', homFamily);
        const checked = emdash.compile(eta);

        assert.equal(comparison.status, 'equal');
        assert.equal(
            comparison.trace.some(entry =>
                entry.reduction.kind === 'runtime' &&
                entry.reduction.ruleId ===
                    'categorical.mixed-mode.functor-hom-fold'
            ),
            true
        );
        assert.equal(
            checked.explicitInferredType,
            checked.explicitExpectedType
        );
    });

    it('preserves profile and classifier failures', () => {
        const earlier = new CoreCategoricalProgram({
            profile: 'fibred-displayed-nd-higher-1'
        });
        const K = earlier.category('earlier_K');
        assert.throws(
            () => earlier.oppositeCategory(K),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_MIXED_MODE'
        );

        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const A = emdash.category('wrong_A');
        const B = emdash.category('wrong_B');
        const domain = emdash.displayedFamily('wrong_domain', A);
        const target = emdash.displayedFamily('wrong_target', B);
        assert.throws(
            () => emdash.mixedDisplayedFunctorFamily(domain, target),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
    });
});
