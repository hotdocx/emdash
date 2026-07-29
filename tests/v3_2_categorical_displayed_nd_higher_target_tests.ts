/**
 * DISPLAYED-ND-HIGHER-TARGET-1A transfer, surface, and demo evidence.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_BOUNDARY,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_POLICY,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_POLICY,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    compileCoreCategoricalDisplayedNdHigherTargetTransfer,
    coreCategoricalDisplayedNdHigherTargetCoreName,
    runCoreCategoricalDisplayedNdHigherDemo,
    serializeCoreExpression
} from '../src/v3_2';

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-displayed-nd-higher-target.ts',
        profile: 'fibred-displayed-nd-higher-1'
    });
    const K = emdash.category('higher_K', { line: 1 });
    const E = emdash.displayedFamily('higher_E', K, { line: 2 });
    const D = emdash.displayedFamily('higher_D', K, { line: 3 });
    const FF = emdash.displayedFunctor('higher_FF', E, D, {
        line: 4
    });
    const GG = emdash.displayedFunctor('higher_GG', E, D, {
        line: 5
    });
    const epsilon = emdash.displayedTransfor(
        'higher_epsilon',
        FF,
        GG,
        { line: 6 }
    );
    const epsilonPrime = emdash.displayedTransfor(
        'higher_epsilon_prime',
        FF,
        GG,
        { line: 7 }
    );
    const category = emdash.displayedTransforCategory(
        FF,
        GG,
        { line: 8 }
    );
    const m = emdash.hom(
        'higher_m',
        category,
        epsilon,
        epsilonPrime,
        { line: 9 }
    );
    const action = emdash.displayedTransforInternalHomAction(
        FF,
        GG,
        { line: 10 }
    );
    const objectAction = emdash.apply(action, epsilon, {
        expectedShape: 'object-value',
        source: { line: 11 }
    });
    const wholeHomAction = emdash.apply(
        action,
        emdash.homBoundary(
            category,
            epsilon,
            epsilonPrime,
            { line: 12 }
        ),
        {
            expectedShape: 'whole-hom-action',
            source: { line: 12 }
        }
    );
    const higherCell = emdash.apply(wholeHomAction, m, {
        expectedShape: 'object-value',
        source: { line: 13 }
    });
    return {
        emdash,
        K,
        E,
        D,
        FF,
        GG,
        epsilon,
        epsilonPrime,
        category,
        m,
        action,
        objectAction,
        wholeHomAction,
        higherCell
    };
};

describe('DISPLAYED-ND-HIGHER-TARGET-1A', () => {
    it('transfers exactly three opaque interfaces and two projections',
        () => {
            assert.deepEqual(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE
                    .declarations.map(declaration =>
                        declaration.symbol.name
                    ),
                [
                    'tdapp1_int_func_transfd',
                    'tdapp1_int_fapp0_transfd',
                    'tdapp1_int_fapp1_func_transfd'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_POLICY
                    .entries.map(entry => entry.policy),
                [
                    'opaque-signature',
                    'opaque-signature',
                    'opaque-signature'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_MODULE
                    .runtimeRules.map(rule => ({
                        id: rule.id,
                        ordinal:
                            rule.provenance.canonicalCommandOrdinal
                    })),
                [
                    {
                        id:
                            'categorical.displayed-nd-higher.' +
                            'object-projection',
                        ordinal: 1075
                    },
                    {
                        id:
                            'categorical.displayed-nd-higher.' +
                            'next-hom-projection',
                        ordinal: 1077
                    }
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_POLICY
                    .entries.every(entry =>
                        entry.policy === 'runtime-rewrite'
                    ),
                true
            );
        });

    it('checks the target over the exact foundation runtime lineage',
        () => {
            const compilation =
                compileCoreCategoricalDisplayedNdHigherTargetTransfer();
            assert.deepEqual(
                compilation.compiled.declarations.map(declaration => ({
                    name: declaration.symbol.name,
                    status: declaration.status,
                    hasBody: declaration.body !== undefined
                })),
                [
                    {
                        name: 'tdapp1_int_func_transfd',
                        status: 'installed-opaque',
                        hasBody: false
                    },
                    {
                        name: 'tdapp1_int_fapp0_transfd',
                        status: 'installed-opaque',
                        hasBody: false
                    },
                    {
                        name: 'tdapp1_int_fapp1_func_transfd',
                        status: 'installed-opaque',
                        hasBody: false
                    }
                ]
            );
            assert.deepEqual(
                compilation.runtime.ruleIds,
                [
                    'categorical.displayed-nd-higher.object-projection',
                    'categorical.displayed-nd-higher.next-hom-projection'
                ]
            );
            assert.equal(
                compilation.runtime.rules.every(rule =>
                    rule.subjectValidation.kind === 'typescript-checked'
                ),
                true
            );
            assert.deepEqual(
                compilation.composedRuntime.ruleIds,
                [
                    ...compilation.prerequisite.composedRuntime.ruleIds,
                    ...compilation.runtime.ruleIds
                ]
            );
            assert.doesNotThrow(
                () => compilation.compiled.createChecker()
                    .validateEnvironment()
            );
        });

    it('uses generic object and whole-Hom application judgments', () => {
        const {
            emdash,
            objectAction,
            wholeHomAction
        } = fixture();
        const transfer =
            compileCoreCategoricalDisplayedNdHigherTargetTransfer();
        const objectCompilation = emdash.compile(objectAction);
        const homCompilation = emdash.compile(wholeHomAction);
        assert.equal(objectCompilation.surfaceType.tag, 'object');
        assert.equal(homCompilation.surfaceType.tag, 'functor');

        const objectProjection = transfer.composedRuntime.rewriteHead(
            objectCompilation.explicitTerm
        );
        const homProjection = transfer.composedRuntime.rewriteHead(
            homCompilation.explicitTerm
        );
        assert.equal(objectProjection.status, 'rewritten');
        assert.equal(homProjection.status, 'rewritten');
        if (
            objectProjection.status !== 'rewritten' ||
            homProjection.status !== 'rewritten'
        ) {
            assert.fail('Expected both higher-action projections');
        }
        assert.equal(
            objectProjection.ruleId,
            'categorical.displayed-nd-higher.object-projection'
        );
        assert.equal(
            homProjection.ruleId,
            'categorical.displayed-nd-higher.next-hom-projection'
        );
        assert.match(
            serializeCoreExpression(objectProjection.after),
            new RegExp(
                coreCategoricalDisplayedNdHigherTargetCoreName(
                    'object-action'
                )
            )
        );
        assert.match(
            serializeCoreExpression(homProjection.after),
            new RegExp(
                coreCategoricalDisplayedNdHigherTargetCoreName(
                    'next-hom-action'
                )
            )
        );
    });

    it('recursively applies the next-hom functor to a higher cell', () => {
        const {
            emdash,
            higherCell
        } = fixture();
        const compilation = emdash.compile(higherCell);
        assert.equal(compilation.surfaceType.tag, 'hom');
        assert.match(
            compilation.explicitCore,
            /owner "functor-object"/u
        );
        assert.match(
            compilation.explicitCore,
            /owner "functor-hom-full"/u
        );
        const inspection = emdash.inspect(higherCell);
        assert.equal(inspection.ir.tag, 'typed-application');
        if (inspection.ir.tag !== 'typed-application') {
            assert.fail('Missing recursive higher application');
        }
        assert.equal(inspection.ir.subject.tag, 'typed-application');
    });

    it('uses the Hom-object judgment rather than ordinary arrow action',
        () => {
            const {
                emdash,
                wholeHomAction,
                m
            } = fixture();
            assert.throws(
                () => emdash.apply(wholeHomAction, m, {
                    expectedShape: 'arrow-value'
                }),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code ===
                        'CLASSIFIER_ARGUMENT_MISMATCH'
            );
            assert.equal(
                emdash.compile(
                    emdash.apply(wholeHomAction, m, {
                        expectedShape: 'object-value'
                    })
                ).surfaceType.tag,
                'hom'
            );
        });

    it('fails closed outside the profile and on incompatible endpoints',
        () => {
            const legacy = new CoreCategoricalProgram();
            const K = legacy.category('legacy_K');
            const E = legacy.displayedFamily('legacy_E', K);
            const D = legacy.displayedFamily('legacy_D', K);
            const FF = legacy.displayedFunctor('legacy_FF', E, D);
            const GG = legacy.displayedFunctor('legacy_GG', E, D);
            assert.throws(
                () => legacy.displayedTransforCategory(FF, GG),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_ND_HIGHER'
            );

            const {
                emdash,
                K: higherK,
                E: higherE,
                FF: higherFF
            } = fixture();
            const C = emdash.displayedFamily('higher_C', higherK);
            const HH = emdash.displayedFunctor(
                'higher_HH',
                higherE,
                C
            );
            assert.throws(
                () => emdash.displayedTransforInternalHomAction(
                    higherFF,
                    HH
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_SOURCE_MISMATCH'
            );
        });

    it('runs the compact direct-TypeScript higher-action demo', () => {
        const demo = runCoreCategoricalDisplayedNdHigherDemo();
        assert.equal(demo.higherCellType, 'hom');
        assert.deepEqual(
            demo.runtimeProjectionRuleIds,
            [
                'categorical.displayed-nd-higher.object-projection',
                'categorical.displayed-nd-higher.next-hom-projection'
            ]
        );
        assert.match(
            demo.normalizedObjectAction,
            /tdapp1_int_fapp0_transfd/u
        );
        assert.match(
            demo.normalizedWholeHomAction,
            /tdapp1_int_fapp1_func_transfd/u
        );
    });

    it('preserves every D-021 zero-delta product boundary', () => {
        const boundary =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_BOUNDARY;
        assert.deepEqual(
            [
                boundary.declarationCount,
                boundary.runtimeRuleCount,
                boundary.activeLambdapiOwnerDelta,
                boundary.activeLambdapiRuleDelta,
                boundary.intrinsicCoreOwnerDelta,
                boundary.ownerSpecificCheckerOrEvaluatorDelta,
                boundary.contextualIrNodeDelta,
                boundary.binderModeDelta,
                boundary.surfaceMethodCount,
                boundary.browserPromotionDelta
            ],
            [3, 2, 0, 0, 0, 0, 0, 0, 2, 0]
        );
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /displayedTransforInternalHomAction|displayed-nd-higher/u
        );
    });
});
