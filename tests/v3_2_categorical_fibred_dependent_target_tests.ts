/**
 * End-user dependent-target and total-context eta evidence.
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

describe('FIBRED-DEPENDENT-TARGET-1 TypeScript profile', () => {
    it(
        'computes B[k,M] to Pi(G[k],M) and checks total-context eta',
        () => {
            const emdash = new CoreCategoricalProgram({
                sourceFile:
                    'tests/fixtures/fibred-dependent-target.ts',
                profile: 'fibred-dependent-target-1'
            });
            const K = emdash.category('K', { line: 1 });
            const G = emdash.contravariantCategoryFamily(
                'G',
                K,
                { line: 2 }
            );
            const motive = emdash.dependentSectionMotive(
                G,
                { line: 3 }
            );
            const target = emdash.dependentSectionTarget(
                G,
                { line: 4 }
            );
            const k = emdash.object('k', K, { line: 5 });
            const M = emdash.object(
                'M',
                emdash.fibre(motive, k),
                { line: 6 }
            );
            const pair = emdash.dependentPair(
                motive,
                k,
                M,
                { line: 7 }
            );
            const actual = emdash.fibre(target, pair, { line: 8 });
            const expected = emdash.dependentSectionCategoryAt(
                G,
                k,
                M,
                { line: 9 }
            );
            const compatibility =
                emdash.dependentTargetCategoryCompatibility(
                    actual,
                    expected
                );

            assert.equal(compatibility.runtime.status, 'equal');
            assert.equal(compatibility.proofTime.status, 'solved');
            assert.equal(
                compatibility
                    .runtimeCategoryPresentationCollapseInstalled,
                false
            );
            assert.equal(
                compatibility.runtime.trace.some(entry =>
                    entry.reduction.kind === 'runtime' &&
                    entry.reduction.ruleId ===
                        'categorical.dependent-target.' +
                        'section-functor-object'
                ),
                true
            );
            assert.equal(
                compatibility.runtime.trace.some(entry =>
                    entry.reduction.kind === 'runtime' &&
                    entry.reduction.ruleId ===
                        'categorical.dependent-target.' +
                        'category-presentation'
                ),
                false
            );
            assert.match(
                emdash.serializeCategory(expected),
                /section-category/u
            );

            const section = emdash.section(
                'target_section',
                target,
                { line: 12 }
            );
            let callbackCount = 0;
            const eta = emdash.dependentLambda(
                'z',
                target,
                z => {
                    callbackCount += 1;
                    return emdash.apply(section, z, {
                        expectedShape: 'dependent-object',
                        source: { line: 16 }
                    });
                },
                {
                    variation: 'natural',
                    dependency: 'displayed',
                    source: { line: 14 }
                }
            );
            const compilation = emdash.compile(eta);
            assert.equal(callbackCount, 1);
            assert.equal(
                compilation.explicitCore,
                '(free "target_section")'
            );
            assert.equal(
                compilation.explicitInferredType,
                compilation.explicitExpectedType
            );
            assert.match(
                compilation.explicitExpectedType,
                /dttlf_Sigma_catd_functord_catd/u
            );
            assert.equal(
                compilation.productionLambdapiDependency,
                false
            );

            const wrongTarget = emdash.functor('wrong_G', K, K);
            assert.throws(
                () => emdash.dependentSectionMotive(wrongTarget),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'EXPECTED_FUNCTOR' &&
                    /Op\(Cat_cat\)/u.test(error.message)
            );
            assert.throws(
                () => emdash.dependentSectionCategoryAt(
                    G,
                    k,
                    emdash.object('wrong_M', K)
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'EXPECTED_CATEGORY_OBJECT'
            );

            const total = emdash.totalCategory(motive);
            const otherTarget =
                emdash.displayedFamily('other_target', total);
            const otherSection =
                emdash.section('other_section', otherTarget);
            assert.throws(
                () => emdash.dependentLambda(
                    'z',
                    target,
                    z => emdash.apply(otherSection, z, {
                        expectedShape: 'dependent-object'
                    })
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
            );
        }
    );

    it('keeps the dependent target out of earlier frozen profiles', () => {
        const emdash = new CoreCategoricalProgram();
        const K = emdash.category('K');
        assert.throws(
            () => emdash.contravariantCategoryFamily('G', K),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_DEPENDENT_TARGET'
        );
    });
});
