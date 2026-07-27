/**
 * Focused FIBRED-COMPREHENSION-1A evidence for asymmetric base-change
 * totalization and its first genuine dependent-chain consumer.
 */

import assert from 'node:assert/strict';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_COMPREHENSION_PREREQUISITES,
    CORE_CATEGORICAL_COMPREHENSION_PROGRAM_REVISION,
    CORE_CATEGORICAL_COMPREHENSION_RUNTIME_MODULE,
    CORE_CATEGORICAL_COMPREHENSION_SYMBOLS,
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    checkLambdapiProbe,
    compileCoreCategoricalComprehensionTransfer,
    serializeCoreCategoricalExpression
} from '../src/v3_2';

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');

const program = (
    sourceFile = 'tests/fixtures/categorical-comprehension.ts'
) => new CoreCategoricalProgram({
    sourceFile,
    profile: 'fibred-comprehension-1a'
});

const chain = () => {
    const emdash = program();
    const A = emdash.category('A', { line: 1 });
    const K = emdash.category('K', { line: 2 });
    const F = emdash.functor('F', A, K, { line: 3 });
    const D = emdash.displayedFamily('D', K, { line: 4 });
    const reindexed = emdash.pullbackFamily(
        D,
        F,
        { line: 5 }
    );
    const a = emdash.object('a', A, { line: 6 });
    const b = emdash.object('b', A, { line: 7 });
    const p = emdash.hom('p', A, a, b, { line: 8 });
    const sourceFibre = emdash.fibre(
        reindexed,
        a,
        { line: 9 }
    );
    const targetFibre = emdash.fibre(
        reindexed,
        b,
        { line: 10 }
    );
    const u = emdash.object('u', sourceFibre, { line: 11 });
    const v = emdash.object('v', targetFibre, { line: 12 });
    const transport = emdash.familyTransport(
        reindexed,
        p,
        { line: 13 }
    );
    const transportedU = emdash.apply(
        transport,
        u,
        { source: { line: 14 } }
    );
    const alpha = emdash.hom(
        'alpha',
        targetFibre,
        transportedU,
        v,
        { line: 15 }
    );
    const sourcePair = emdash.dependentPair(
        reindexed,
        a,
        u,
        { line: 16 }
    );
    const targetPair = emdash.dependentPair(
        reindexed,
        b,
        v,
        { line: 17 }
    );
    const sourceArrow = emdash.sigmaArrow(
        reindexed,
        u,
        v,
        p,
        alpha,
        { line: 18 }
    );
    const totalization = emdash.pullbackTotal(
        F,
        D,
        { line: 19 }
    );
    const objectImage = emdash.apply(
        totalization,
        sourcePair,
        { source: { line: 20 } }
    );
    const arrowImage = emdash.apply(
        totalization,
        sourceArrow,
        { source: { line: 21 } }
    );

    /*
     * This is the first genuine chain consumer: Q depends on a dependent
     * pair in Sigma(D), then is substituted along the totalized base change.
     */
    const targetTotal = emdash.totalCategory(D, { line: 22 });
    const Q = emdash.displayedFamily('Q', targetTotal, { line: 23 });
    const substitutedQ = emdash.substituteFamily(
        Q,
        totalization,
        { line: 24 }
    );
    const substitutedFibre = emdash.fibre(
        substitutedQ,
        sourcePair,
        { line: 25 }
    );
    const q = emdash.object(
        'q',
        substitutedFibre,
        { line: 26 }
    );

    return {
        emdash,
        A,
        K,
        F,
        D,
        reindexed,
        a,
        b,
        p,
        u,
        v,
        alpha,
        sourcePair,
        targetPair,
        sourceArrow,
        totalization,
        objectImage,
        arrowImage,
        Q,
        substitutedQ,
        q
    };
};

describe(
    'TypeScript v3.2 FIBRED-COMPREHENSION-1A transfer',
    () => {
        it('reuses the audited pullback owner and transfers the exact closure', () => {
            assert.equal(
                CORE_CATEGORICAL_COMPREHENSION_PROGRAM_REVISION,
                'FIBRED-COMPREHENSION-1A-CATEGORICAL-PROGRAM-1'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE
                    .declarations.map(entry => entry.symbol.name),
                [
                    'Pullback_catd',
                    'sigma_arrow',
                    'sigma_pullback_total_func'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_COMPREHENSION_RUNTIME_MODULE
                    .runtimeRules.map(rule => rule.id),
                [
                    'categorical.pullback.fibre',
                    'categorical.pullback.arrow',
                    'categorical.sigma-pullback-total.object',
                    'categorical.sigma-pullback-total.arrow'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_COMPREHENSION_PREREQUISITES
                    .map(entry => entry.id),
                [
                    'displayed-pullback-owner',
                    'displayed-pullback-fibre-reduction',
                    'displayed-pullback-arrow-reduction',
                    'canonical-sigma-arrow'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY
                    .newMathematicalOwnerCount,
                1
            );
            assert.equal(
                CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY
                    .existingIntrinsicOwnerCount,
                1
            );
            assert.equal(
                CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY
                    .warningsAreDiagnosticNotSelectionVetoes,
                true
            );
            assert.equal(
                CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY
                    .arrowRulePresentation,
                'active-delta-specialized-canonical-sigma-arrow'
            );
            assert.deepEqual(
                Object.values(
                    CORE_CATEGORICAL_COMPREHENSION_SYMBOLS
                ).map(symbol => symbol.name),
                [
                    'Pullback_catd',
                    'sigma_arrow',
                    'sigma_pullback_total_func'
                ]
            );

            const compiled =
                compileCoreCategoricalComprehensionTransfer();
            assert.deepEqual(
                compiled.compiled.declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ]),
                [
                    ['Pullback_catd', 'intrinsic-conformance'],
                    ['sigma_arrow', 'installed-opaque'],
                    [
                        'sigma_pullback_total_func',
                        'installed-opaque'
                    ]
                ]
            );
            assert.deepEqual(
                compiled.runtime.rules.map(rule => [
                    rule.id,
                    rule.subjectValidation.kind
                ]),
                [
                    [
                        'categorical.pullback.fibre',
                        'typescript-checked'
                    ],
                    [
                        'categorical.pullback.arrow',
                        'typescript-checked'
                    ],
                    [
                        'categorical.sigma-pullback-total.object',
                        'typescript-checked'
                    ],
                    [
                        'categorical.sigma-pullback-total.arrow',
                        'typescript-checked'
                    ]
                ]
            );
        });

        it('constructs and checks the dependent object/arrow chain directly', () => {
            const witness = chain();
            const pair = witness.emdash.compile(witness.sourcePair);
            const arrow = witness.emdash.compile(witness.sourceArrow);
            const objectImage =
                witness.emdash.compile(witness.objectImage);
            const arrowImage =
                witness.emdash.compile(witness.arrowImage);
            const furtherDependentObject =
                witness.emdash.compile(witness.q);

            assert.equal(pair.surfaceType.tag, 'object');
            assert.equal(arrow.surfaceType.tag, 'hom');
            assert.equal(objectImage.surfaceType.tag, 'object');
            assert.equal(arrowImage.surfaceType.tag, 'hom');
            assert.equal(furtherDependentObject.surfaceType.tag, 'object');
            assert.match(
                pair.explicitCore,
                /emdash\.categorical\.dependent-pair/u
            );
            assert.match(
                arrow.explicitCore,
                /emdash\.categorical\.sigma-arrow/u
            );
            assert.match(
                objectImage.explicitCore,
                /emdash\.categorical\.sigma-pullback-total-functor/u
            );
            assert.match(
                furtherDependentObject.explicitExpectedType,
                /displayed-pullback/u
            );
            assert.match(
                furtherDependentObject.explicitExpectedType,
                /sigma-pullback-total-functor/u
            );
            assert.equal(
                furtherDependentObject.productionLambdapiDependency,
                false
            );
        });

        it('computes (a,u) to (F[a],u) in the generic runtime', () => {
            const witness = chain();
            const transfer =
                compileCoreCategoricalComprehensionTransfer();
            const term =
                witness.emdash.compile(witness.objectImage).explicitTerm;
            const rewrite = transfer.runtime.rewriteHead(term);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                assert.fail('Object totalization did not reduce');
            }
            assert.equal(
                rewrite.ruleId,
                'categorical.sigma-pullback-total.object'
            );
            const result = serializeCoreCategoricalExpression(
                rewrite.after
            );
            assert.match(
                result,
                /emdash\.categorical\.dependent-pair/u
            );
            assert.match(result, /"F"/u);
            assert.match(result, /"a"/u);
            assert.match(result, /"u"/u);
        });

        it('computes (p,alpha) to (F[p],alpha) canonically', () => {
            const witness = chain();
            const transfer =
                compileCoreCategoricalComprehensionTransfer();
            const term =
                witness.emdash.compile(witness.arrowImage).explicitTerm;
            const rewrite = transfer.runtime.rewriteHead(term);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                assert.fail('Arrow totalization did not reduce');
            }
            assert.equal(
                rewrite.ruleId,
                'categorical.sigma-pullback-total.arrow'
            );
            const result = serializeCoreCategoricalExpression(
                rewrite.after
            );
            assert.match(
                result,
                /emdash\.categorical\.sigma-arrow/u
            );
            assert.match(result, /functor-hom-capped/u);
            assert.match(result, /"F"/u);
            assert.match(result, /"p"/u);
            assert.match(result, /"alpha"/u);
        });

        it('keeps the new consumer behind its explicit root profile', () => {
            const emdash = new CoreCategoricalProgram();
            const K = emdash.category('K');
            const D = emdash.displayedFamily('D', K);
            assert.throws(
                () => emdash.totalCategory(D),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_COMPREHENSION'
            );
        });

        it('fails closed when the substitution targets the wrong base', () => {
            const emdash = program('wrong-base.ts');
            const A = emdash.category('A');
            const K = emdash.category('K');
            const L = emdash.category('L');
            const F = emdash.functor('F', A, L);
            const D = emdash.displayedFamily('D', K);
            assert.throws(
                () => emdash.pullbackFamily(D, F),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
            assert.throws(
                () => emdash.pullbackTotal(F, D),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
        });

        it(
            'agrees with Lambdapi on object and canonical arrow action',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_COMPREHENSION_PROBES !==
                    '1'
            },
            () => {
                const result = checkLambdapiProbe(
                    {
                        source: [
                            'require open emdash.emdash3_2;',
                            'symbol cc_A : Cat;',
                            'symbol cc_K : Cat;',
                            'symbol cc_F : τ (Functor cc_A cc_K);',
                            'symbol cc_D : τ (Catd cc_K);',
                            'symbol cc_a : τ (Obj cc_A);',
                            'symbol cc_b : τ (Obj cc_A);',
                            'symbol cc_p : τ (Hom cc_A cc_a cc_b);',
                            'symbol cc_u : τ (Obj (Fibre_cat ' +
                                '(@Pullback_catd cc_A cc_K cc_D cc_F) ' +
                                'cc_a));',
                            'symbol cc_v : τ (Obj (Fibre_cat ' +
                                '(@Pullback_catd cc_A cc_K cc_D cc_F) ' +
                                'cc_b));',
                            'symbol cc_alpha : τ (Hom',
                            '  (Fibre_cat cc_D (@fapp0 cc_A cc_K cc_F cc_b))',
                            '  (@fapp0',
                            '    (Fibre_cat cc_D (@fapp0 cc_A cc_K cc_F cc_a))',
                            '    (Fibre_cat cc_D (@fapp0 cc_A cc_K cc_F cc_b))',
                            '    (@catd_transport_func',
                            '      cc_K cc_D',
                            '      (@fapp0 cc_A cc_K cc_F cc_a)',
                            '      (@fapp0 cc_A cc_K cc_F cc_b)',
                            '      (@fapp1_fapp0',
                            '        cc_A cc_K cc_F cc_a cc_b cc_p))',
                            '    cc_u)',
                            '  cc_v);',
                            'assert ⊢',
                            '  @fapp0',
                            '    (@Sigma_cat cc_A',
                            '      (@Pullback_catd cc_A cc_K cc_D cc_F))',
                            '    (@Sigma_cat cc_K cc_D)',
                            '    (@sigma_pullback_total_func',
                            '      cc_A cc_K cc_F cc_D)',
                            '    (Struct_sigma cc_a cc_u)',
                            '  ≡ @Struct_sigma',
                            '      (Obj cc_K)',
                            '      (λ k : τ (Obj cc_K),',
                            '        Obj (Fibre_cat cc_D k))',
                            '      (@fapp0 cc_A cc_K cc_F cc_a)',
                            '      cc_u;',
                            'assert ⊢',
                            '  @fapp1_fapp0',
                            '    (@Sigma_cat cc_A',
                            '      (@Pullback_catd cc_A cc_K cc_D cc_F))',
                            '    (@Sigma_cat cc_K cc_D)',
                            '    (@sigma_pullback_total_func',
                            '      cc_A cc_K cc_F cc_D)',
                            '    (Struct_sigma cc_a cc_u)',
                            '    (Struct_sigma cc_b cc_v)',
                            '    (@sigma_arrow',
                            '      cc_A',
                            '      (@Pullback_catd cc_A cc_K cc_D cc_F)',
                            '      cc_a cc_b cc_u cc_v cc_p cc_alpha)',
                            '  ≡ @sigma_arrow',
                            '      cc_K cc_D',
                            '      (@fapp0 cc_A cc_K cc_F cc_a)',
                            '      (@fapp0 cc_A cc_K cc_F cc_b)',
                            '      cc_u cc_v',
                            '      (@fapp1_fapp0',
                            '        cc_A cc_K cc_F cc_a cc_b cc_p)',
                            '      cc_alpha;'
                        ].join('\n'),
                        sourceMap: []
                    },
                    {
                        packageRoot: lambdapiRoot,
                        timeoutMs: 30_000
                    }
                );
                assert.equal(result.accepted, true, result.diagnostics);
                assert.equal(result.timedOut, false);
            }
        );
    }
);
