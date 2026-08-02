/**
 * Focused FIBRED-PRODUCT-1A evidence for the transparent fibrewise product
 * and its first shared-base grouped-sibling transport.
 */

import assert from 'node:assert/strict';
import {
    createHash
} from 'node:crypto';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_PREREQUISITES,
    CORE_CATEGORICAL_FIBRED_PRODUCT_PROGRAM_REVISION,
    CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_MODULE,
    CORE_CATEGORICAL_FIBRED_PRODUCT_SOURCE_SHA256,
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreLfComparisonResult,
    checkLambdapiProbe,
    compileCoreCategoricalFibredProductTransfer
} from '../src/v3_2';

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');
const activeKernelPath = resolve(
    lambdapiRoot,
    'emdash3_2.lp'
);

const program = (
    sourceFile = 'tests/fixtures/categorical-fibred-product.ts'
) => new CoreCategoricalProgram({
    sourceFile,
    profile: 'fibred-product-1a'
});

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => result.trace.flatMap(entry =>
    entry.reduction.kind === 'runtime'
        ? [entry.reduction.ruleId]
        : []
);

const siblingWitness = () => {
    const emdash = program();
    const K = emdash.category('K', { line: 1 });
    const B = emdash.displayedFamily('B', K, { line: 2 });
    const C = emdash.displayedFamily('C', K, { line: 3 });
    const product = emdash.displayedProduct(B, C, { line: 4 });
    const x = emdash.object('x', K, { line: 5 });
    const y = emdash.object('y', K, { line: 6 });
    const p = emdash.hom('p', K, x, y, { line: 7 });
    const q = emdash.hom('q', K, x, y, { line: 8 });
    const productFibre = emdash.fibre(
        product,
        x,
        { line: 9 }
    );
    const expectedFibre = emdash.productCategory(
        emdash.fibre(B, x, { line: 10 }),
        emdash.fibre(C, x, { line: 11 }),
        { line: 12 }
    );
    const transport = emdash.familyTransport(
        product,
        p,
        { line: 13 }
    );
    const componentwise = emdash.productMap(
        emdash.familyTransport(B, p, { line: 14 }),
        emdash.familyTransport(C, p, { line: 15 }),
        { line: 16 }
    );
    const splitBase = emdash.productMap(
        emdash.familyTransport(B, p, { line: 17 }),
        emdash.familyTransport(C, q, { line: 18 }),
        { line: 19 }
    );
    return {
        emdash,
        K,
        B,
        C,
        product,
        x,
        y,
        p,
        q,
        productFibre,
        expectedFibre,
        transport,
        componentwise,
        splitBase
    };
};

describe(
    'TypeScript v3.2 FIBRED-PRODUCT-1A transfer',
    () => {
        it('reuses the transparent product and transfers the exact closure', () => {
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_PROGRAM_REVISION,
                'FIBRED-PRODUCT-1A-CATEGORICAL-PROGRAM-1'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE
                    .declarations.map(entry => entry.symbol.name),
                [
                    'Product_cat_func',
                    'Product_cat_fapp0_func',
                    'Product_cat_fapp1_fapp0_functord',
                    'Product_cat_fapp1_tapp0_func',
                    'hom_postcomp_fapp0',
                    'sigma_Fst',
                    'sigma_Snd',
                    'Product_grpd'
                ]
            );
            assert.deepEqual(
                Object.values(
                    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS
                ).map(symbol => symbol.name),
                [
                    'sigma_Fst',
                    'sigma_Snd',
                    'Product_grpd',
                    'hom_postcomp_fapp0',
                    'Product_cat_func',
                    'Product_cat_fapp0_func',
                    'Product_cat_fapp1_fapp0_functord',
                    'Product_cat_fapp1_tapp0_func'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_PRODUCT_PREREQUISITES
                    .map(entry => entry.id),
                [
                    'transparent-uncurry-package',
                    'ordinary-functor-composition-action',
                    'paired-functor-action',
                    'internal-product-object-ladder',
                    'internal-product-left-action',
                    'fixed-right-product-map-action',
                    'evaluation-action',
                    'postcomposition-object-action',
                    'explicit-core-inferred-slot-normalization'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .newRuntimeRuleIds,
                [
                    'categorical.postcomposition.arrow',
                    'categorical.fibred-product.shared-base-arrow'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .newMathematicalOwnerCount,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .newKernelDeclarationCount,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .prerequisiteRuntimeRuleCount,
                28
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .newRuntimeRuleCount,
                2
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
                30
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .relocatedGenericProductRuleIds,
                [
                    'categorical.fibred-product.product-groupoid-decode',
                    'categorical.fibred-product.product-object',
                    'categorical.fibred-product.product.general-hom'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .relocatedProductPairBetaRuleIds,
                [
                    'categorical.fibred-product.' +
                        'product-pair-left.delta-beta',
                    'categorical.fibred-product.' +
                        'product-pair-right.delta-beta'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .normalFormSpecializationRuleIds,
                [
                    'categorical.identity-functor.arrow.delta',
                    'categorical.evaluation.arrow.cat-normalize',
                    'categorical.postcomposition.object.' +
                        'identity-target-normalize',
                    'categorical.postcomposition.arrow.' +
                        'identity-target-normalize'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .wildcardOrNewPatternShapeRequired,
                true
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .necessityAudit.addedPrimitiveProductCatd,
                false
            );

            const compiled =
                compileCoreCategoricalFibredProductTransfer();
            assert.equal(compiled.compiled.declarations.length, 8);
            assert.equal(compiled.runtime.rules.length, 30);
            assert.deepEqual(
                compiled.runtime.rules.map(rule =>
                    rule.subjectValidation.kind
                ),
                Array.from(
                    { length: 30 },
                    () => 'typescript-checked'
                )
            );
            for (const id of [
                ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .relocatedGenericProductRuleIds,
                ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
                    .relocatedProductPairBetaRuleIds
            ]) {
                assert.equal(
                    compiled.composedRuntime.ruleIds.filter(candidate =>
                        candidate === id
                    ).length,
                    1
                );
            }
        });

        it('pins source bytes and both approved active rules', () => {
            const source = readFileSync(activeKernelPath, 'utf8');
            assert.equal(
                'sha256:' + createHash('sha256')
                    .update(source)
                    .digest('hex'),
                CORE_CATEGORICAL_FIBRED_PRODUCT_SOURCE_SHA256
            );
            assert.match(
                source,
                /Capped arrow action of Cat-valued postcomposition:/u
            );
            assert.match(
                source,
                /Narrow product projection for two Cat-valued family actions/u
            );
        });

        it('computes the pointwise product fibre without Product_catd', () => {
            const witness = siblingWitness();
            const result = witness.emdash.compareCategories(
                witness.productFibre,
                witness.expectedFibre,
                2_000
            );
            assert.equal(result.status, 'equal');
            assert.equal(result.steps, 12);
            assert.deepEqual(
                runtimeRuleIds(result),
                [
                    'categorical.composition.object.delta',
                    'categorical.uncurry.object.delta-normalize',
                    'categorical.postcomposition.object.' +
                        'identity-target-normalize',
                    'categorical.identity-functor.object.delta',
                    'categorical.identity-functor.object.delta',
                    'categorical.identity-functor.arrow.delta',
                    'categorical.identity-functor.object.delta',
                    'categorical.product-pair.object.delta',
                    'categorical.fixed-right-product.object',
                    'categorical.evaluation.object',
                    'categorical.internal-product.first-object',
                    'categorical.internal-product.second-object'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_MODULE
                    .runtimeRules.some(rule =>
                        rule.provenance.sourceFragment.includes(
                            'Product_catd'
                        )
                    ),
                false
            );
        });

        it('lowers shared-base transport to componentwise Product_map_func', () => {
            const witness = siblingWitness();
            const left = witness.emdash.compile(witness.transport);
            const right = witness.emdash.compile(witness.componentwise);
            assert.equal(left.surfaceType.tag, 'functor');
            assert.equal(right.surfaceType.tag, 'functor');
            assert.match(
                left.explicitCore,
                /emdash\.categorical\.functor-composition/u
            );
            assert.match(
                right.explicitCore,
                /emdash\.categorical\.product-map/u
            );

            const result = witness.emdash.compare(
                witness.transport,
                witness.componentwise,
                2_000
            );
            assert.equal(result.status, 'equal');
            assert.equal(result.steps, 26);
            assert.equal(
                runtimeRuleIds(result).at(-1),
                'categorical.fibred-product.shared-base-arrow'
            );
            assert.equal(
                runtimeRuleIds(result).some(ruleId =>
                    ruleId ===
                    'categorical.postcomposition.arrow'
                ),
                false
            );
            assert.equal(
                runtimeRuleIds(result).some(ruleId =>
                    ruleId ===
                    'categorical.postcomposition.arrow.' +
                        'identity-target-normalize'
                ),
                true
            );
        });

        it('does not fold two unrelated parallel base arrows', () => {
            const witness = siblingWitness();
            const result = witness.emdash.compare(
                witness.transport,
                witness.splitBase,
                2_000
            );
            assert.equal(result.status, 'not-equal');
            const sharedBaseSteps = result.trace.filter(
                entry =>
                    entry.reduction.kind === 'runtime' &&
                    entry.reduction.ruleId ===
                        'categorical.fibred-product.shared-base-arrow'
            );
            assert.equal(
                sharedBaseSteps.length > 0,
                true
            );
            assert.equal(
                sharedBaseSteps.every(entry => entry.side === 'left'),
                true
            );
        });

        it('keeps product construction behind its root-only profile', () => {
            const emdash = new CoreCategoricalProgram();
            const K = emdash.category('K');
            const B = emdash.displayedFamily('B', K);
            const C = emdash.displayedFamily('C', K);
            assert.throws(
                () => emdash.displayedProduct(B, C),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_FIBRED_PRODUCT'
            );
        });

        it('fails closed when sibling families have different bases', () => {
            const emdash = program('wrong-product-base.ts');
            const K = emdash.category('K');
            const L = emdash.category('L');
            const B = emdash.displayedFamily('B', K);
            const C = emdash.displayedFamily('C', L);
            assert.throws(
                () => emdash.displayedProduct(B, C),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
        });

        it(
            'agrees with Lambdapi on fibre, transport, and split-arrow non-collapse',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_FIBRED_PRODUCT_PROBES !==
                    '1'
            },
            () => {
                const result = checkLambdapiProbe(
                    {
                        source: [
                            'require open emdash.emdash3_2;',
                            'symbol fp_K : Cat;',
                            'symbol fp_B : τ (Catd fp_K);',
                            'symbol fp_C : τ (Catd fp_K);',
                            'symbol fp_x : τ (Obj fp_K);',
                            'symbol fp_y : τ (Obj fp_K);',
                            'symbol fp_p : ' +
                                'τ (Hom fp_K fp_x fp_y);',
                            'symbol fp_q : ' +
                                'τ (Hom fp_K fp_x fp_y);',
                            'symbol fp_product : τ (Catd fp_K) ≔',
                            '  @comp_cat_fapp0',
                            '    fp_K',
                            '    (Product_cat Cat_cat Cat_cat)',
                            '    Cat_cat',
                            '    (@uncurry_func',
                            '      Cat_cat Cat_cat Cat_cat',
                            '      Product_cat_func)',
                            '    (Struct_sigma fp_B fp_C);',
                            'assert ⊢ Fibre_cat fp_product fp_x',
                            '  ≡ Product_cat',
                            '      (Fibre_cat fp_B fp_x)',
                            '      (Fibre_cat fp_C fp_x);',
                            'assert ⊢ catd_transport_func fp_product fp_p',
                            '  ≡ @Product_map_func',
                            '      (Fibre_cat fp_B fp_x)',
                            '      (Fibre_cat fp_B fp_y)',
                            '      (Fibre_cat fp_C fp_x)',
                            '      (Fibre_cat fp_C fp_y)',
                            '      (catd_transport_func fp_B fp_p)',
                            '      (catd_transport_func fp_C fp_p);',
                            'assertnot ⊢',
                            '  @tapp1_fapp0',
                            '    Cat_cat Cat_cat _ _ _ _',
                            '    (@Product_cat_fapp1_fapp0_functord',
                            '      _ _',
                            '      (catd_transport_func fp_B fp_p))',
                            '    (catd_transport_func fp_C fp_q)',
                            '  ≡ @Product_map_func',
                            '      (Fibre_cat fp_B fp_x)',
                            '      (Fibre_cat fp_B fp_y)',
                            '      (Fibre_cat fp_C fp_x)',
                            '      (Fibre_cat fp_C fp_y)',
                            '      (catd_transport_func fp_B fp_p)',
                            '      (catd_transport_func fp_C fp_q);'
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
