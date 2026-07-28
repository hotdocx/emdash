/**
 * Focused FIBRED-STRUCTURE-1A evidence for the approved fixed-base
 * displayed-product universal property.
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
    CORE_CATEGORICAL_FIBRED_STRUCTURE_PROGRAM_REVISION,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreLfComparisonResult,
    checkLambdapiProbe,
    compileCoreCategoricalFibredStructureTransfer,
    validateCoreCategoricalFibredStructureReview
} from '../src/v3_2';

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');
const activeKernelPath = resolve(
    lambdapiRoot,
    'emdash3_2.lp'
);

const program = (
    sourceFile = 'tests/fixtures/categorical-fibred-structure.ts'
) => new CoreCategoricalProgram({
    sourceFile,
    profile: 'fibred-structure-1a'
});

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => result.trace.flatMap(entry =>
    entry.reduction.kind === 'runtime'
        ? [entry.reduction.ruleId]
        : []
);

const structureWitness = () => {
    const emdash = program();
    const K = emdash.category('K', { line: 1 });
    const E = emdash.displayedFamily('E', K, { line: 2 });
    const B = emdash.displayedFamily('B', K, { line: 3 });
    const C = emdash.displayedFamily('C', K, { line: 4 });
    const FF = emdash.displayedFunctor('FF', E, B, { line: 5 });
    const GG = emdash.displayedFunctor('GG', E, C, { line: 6 });
    const x = emdash.object('x', K, { line: 7 });
    const y = emdash.object('y', K, { line: 8 });
    const p = emdash.hom('p', K, x, y, { line: 9 });
    const Bx = emdash.fibre(B, x, { line: 10 });
    const Cx = emdash.fibre(C, x, { line: 11 });
    return {
        emdash,
        K,
        E,
        B,
        C,
        FF,
        GG,
        x,
        y,
        p,
        Bx,
        Cx
    };
};

describe(
    'TypeScript v3.2 FIBRED-STRUCTURE-1A transfer',
    () => {
        it('binds the exact D-006 approval without broadening it', () => {
            validateCoreCategoricalFibredStructureReview();
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW
                    .approval.decisionId,
                'D-DTTLF-USABILITY-006'
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW
                    .proposal.recommendation.authorityAuthorized,
                false
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW
                    .authorization.newInjectiveOwners,
                [
                    'Product_projL_funcd',
                    'Product_projR_funcd',
                    'Product_pair_funcd'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW
                    .authorization.kernelReindexingRuleAuthorized,
                false
            );
            assert.equal(
                Object.isFrozen(
                    CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW
                ),
                true
            );
        });

        it('transfers exactly three new owners and eleven new rules', () => {
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_PROGRAM_REVISION,
                'FIBRED-STRUCTURE-1A-CATEGORICAL-PROGRAM-1'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE
                    .declarations.map(entry => entry.symbol.name),
                [
                    'comp_cat_con_func',
                    'hom_precomp_along_fapp0',
                    'id_funcd',
                    'Product_projL_funcd',
                    'Product_projR_funcd',
                    'Product_pair_funcd'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE
                    .declarations.slice(3)
                    .map(entry => entry.modifiers.rigidity),
                ['injective', 'injective', 'injective']
            );
            assert.deepEqual(
                Object.values(
                    CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS
                ).map(symbol => symbol.name),
                [
                    'comp_cat_con_func',
                    'hom_precomp_along_fapp0',
                    'id_funcd',
                    'Product_projL_funcd',
                    'Product_projR_funcd',
                    'Product_pair_funcd'
                ]
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
                    .newMathematicalOwnerCount,
                3
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
                    .newRuntimeRuleCount,
                11
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
                    .prerequisiteRuntimeRuleCount,
                4
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
                15
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
                    .productFamilyOwnerAdded,
                false
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
                    .kernelReindexingRuleAdded,
                false
            );

            const compiled =
                compileCoreCategoricalFibredStructureTransfer();
            assert.equal(compiled.compiled.declarations.length, 6);
            assert.equal(compiled.runtime.rules.length, 15);
            assert.deepEqual(
                compiled.runtime.rules.map(rule =>
                    rule.subjectValidation.kind
                ),
                Array.from(
                    { length: 15 },
                    () => 'typescript-checked'
                )
            );
        });

        it('pins the active source bytes and exact owner/rule tranche', () => {
            const source = readFileSync(activeKernelPath, 'utf8');
            assert.equal(
                'sha256:' + createHash('sha256')
                    .update(source)
                    .digest('hex'),
                CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256
            );
            for (const owner of [
                'Product_projL_funcd',
                'Product_projR_funcd',
                'Product_pair_funcd'
            ]) {
                assert.match(
                    source,
                    new RegExp(`injective symbol ${owner}`, 'u')
                );
            }
            assert.match(
                source,
                /Fixed-base product universal-property betas/u
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE
                    .runtimeRules.length,
                15
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE
                    .runtimeRules
                    .slice(0, 11)
                    .every(rule =>
                        rule.id.startsWith(
                            'categorical.fibred-structure.'
                        )
                    ),
                true
            );
        });

        it('computes projection, pairing, swap, and diagonal points', () => {
            const witness = structureWitness();
            const leftPoint = witness.emdash.apply(
                witness.emdash.displayedProductLeftProjection(
                    witness.B,
                    witness.C,
                    { line: 20 }
                ),
                witness.x,
                {
                    expectedShape: 'fibre-functor',
                    source: { line: 21 }
                }
            );
            const expectedLeft = witness.emdash.productLeftProjection(
                witness.Bx,
                witness.Cx,
                { line: 22 }
            );
            const leftResult = witness.emdash.compare(
                leftPoint,
                expectedLeft,
                4_000
            );
            assert.equal(leftResult.status, 'equal');
            assert.equal(
                runtimeRuleIds(leftResult).includes(
                    'categorical.displayed-functor-fibre.delta'
                ),
                true
            );
            assert.equal(
                runtimeRuleIds(leftResult).includes(
                    'categorical.fibred-structure.' +
                    'left-projection.point'
                ),
                true
            );

            const pairedPoint = witness.emdash.apply(
                witness.emdash.displayedProductPair(
                    witness.FF,
                    witness.GG,
                    { line: 23 }
                ),
                witness.x,
                {
                    expectedShape: 'fibre-functor',
                    source: { line: 24 }
                }
            );
            const expectedPair = witness.emdash.functorPair(
                witness.emdash.apply(witness.FF, witness.x, {
                    expectedShape: 'fibre-functor',
                    source: { line: 25 }
                }),
                witness.emdash.apply(witness.GG, witness.x, {
                    expectedShape: 'fibre-functor',
                    source: { line: 26 }
                }),
                { line: 27 }
            );
            const pairResult = witness.emdash.compare(
                pairedPoint,
                expectedPair,
                4_000
            );
            assert.equal(pairResult.status, 'equal');
            assert.equal(
                runtimeRuleIds(pairResult).includes(
                    'categorical.fibred-structure.pairing.point'
                ),
                true
            );

            const swapPoint = witness.emdash.apply(
                witness.emdash.displayedProductSwap(
                    witness.B,
                    witness.C,
                    { line: 28 }
                ),
                witness.x,
                {
                    expectedShape: 'fibre-functor',
                    source: { line: 29 }
                }
            );
            const expectedSwap = witness.emdash.functorPair(
                witness.emdash.productRightProjection(
                    witness.Bx,
                    witness.Cx,
                    { line: 30 }
                ),
                witness.emdash.productLeftProjection(
                    witness.Bx,
                    witness.Cx,
                    { line: 31 }
                ),
                { line: 32 }
            );
            assert.equal(
                witness.emdash.compare(
                    swapPoint,
                    expectedSwap,
                    4_000
                ).status,
                'equal'
            );

            const diagonalPoint = witness.emdash.apply(
                witness.emdash.displayedProductDiagonal(
                    witness.B,
                    { line: 33 }
                ),
                witness.x,
                {
                    expectedShape: 'fibre-functor',
                    source: { line: 34 }
                }
            );
            const identity = witness.emdash.identityFunctor(
                witness.Bx,
                { line: 35 }
            );
            const expectedDiagonal = witness.emdash.functorPair(
                identity,
                identity,
                { line: 36 }
            );
            assert.equal(
                witness.emdash.compare(
                    diagonalPoint,
                    expectedDiagonal,
                    4_000
                ).status,
                'equal'
            );
        });

        it('connects full and capped projection action through active facades', () => {
            const witness = structureWitness();
            const projection =
                witness.emdash.displayedProductLeftProjection(
                    witness.B,
                    witness.C,
                    { line: 40 }
                );
            const capped = witness.emdash.apply(
                projection,
                witness.p,
                {
                    expectedShape: 'transport-functor',
                    source: { line: 41 }
                }
            );
            const full = witness.emdash.displayedFunctorFullAction(
                projection,
                witness.x,
                witness.y,
                { line: 42 }
            );
            const fullAtP = witness.emdash.apply(
                full,
                witness.p,
                { source: { line: 43 } }
            );
            const result = witness.emdash.compare(
                capped,
                fullAtP,
                4_000
            );
            assert.equal(result.status, 'equal');
            assert.equal(
                runtimeRuleIds(result).includes(
                    'categorical.displayed-functor-transport.delta'
                ),
                true
            );
            assert.equal(
                runtimeRuleIds(result).includes(
                    'categorical.transfor-full-action.' +
                    'evaluate.cat-normalize'
                ),
                true
            );
            assert.equal(
                runtimeRuleIds(result).includes(
                    'categorical.fibred-structure.' +
                    'left-projection.capped-action'
                ),
                true
            );
        });

        it('canonicalizes grouped reindexing only in the new profile', () => {
            const canonical = program('canonical-reindex.ts');
            const K = canonical.category('K');
            const A = canonical.category('A');
            const B = canonical.displayedFamily('B', K);
            const C = canonical.displayedFamily('C', K);
            const F = canonical.functor('F', A, K);
            const grouped = canonical.displayedProduct(B, C);
            const reindexed = canonical.pullbackFamily(grouped, F);
            const expected = canonical.displayedProduct(
                canonical.pullbackFamily(B, F),
                canonical.pullbackFamily(C, F)
            );
            assert.equal(
                canonical.compareDisplayedFamilies(
                    reindexed,
                    expected,
                    4_000
                ).status,
                'equal'
            );

            const raw = new CoreCategoricalProgram({
                sourceFile: 'raw-reindex.ts',
                profile: 'fibred-product-1a'
            });
            const rawK = raw.category('K');
            const rawA = raw.category('A');
            const rawB = raw.displayedFamily('B', rawK);
            const rawC = raw.displayedFamily('C', rawK);
            const rawF = raw.functor('F', rawA, rawK);
            const rawReindexed = raw.pullbackFamily(
                raw.displayedProduct(rawB, rawC),
                rawF
            );
            const rawCanonical = raw.displayedProduct(
                raw.pullbackFamily(rawB, rawF),
                raw.pullbackFamily(rawC, rawF)
            );
            assert.equal(
                raw.compareDisplayedFamilies(
                    rawReindexed,
                    rawCanonical,
                    4_000
                ).status,
                'not-equal'
            );
        });

        it('fails closed outside the profile and on unequal pair sources', () => {
            const frozen = new CoreCategoricalProgram({
                profile: 'fibred-product-1a'
            });
            const K = frozen.category('K');
            const B = frozen.displayedFamily('B', K);
            const C = frozen.displayedFamily('C', K);
            assert.throws(
                () => frozen.displayedProductLeftProjection(B, C),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_FIBRED_STRUCTURE'
            );

            const witness = structureWitness();
            const Q = witness.emdash.displayedFamily(
                'Q',
                witness.K
            );
            const HH = witness.emdash.displayedFunctor(
                'HH',
                Q,
                witness.C
            );
            assert.throws(
                () => witness.emdash.displayedProductPair(
                    witness.FF,
                    HH
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_SOURCE_MISMATCH'
            );
        });

        it(
            'agrees with Lambdapi on point, beta, and raw reindex boundaries',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_FIBRED_STRUCTURE_PROBES !==
                    '1'
            },
            () => {
                const result = checkLambdapiProbe(
                    {
                        source: [
                            'require open emdash.emdash3_2;',
                            'symbol fs_K : Cat;',
                            'symbol fs_E : τ (Catd fs_K);',
                            'symbol fs_B : τ (Catd fs_K);',
                            'symbol fs_C : τ (Catd fs_K);',
                            'symbol fs_FF : τ (Functord fs_E fs_B);',
                            'symbol fs_GG : τ (Functord fs_E fs_C);',
                            'symbol fs_x : τ (Obj fs_K);',
                            'assert ⊢',
                            '  @tapp0_fapp0 fs_K Cat_cat _ _ fs_x',
                            '    (@Product_projL_funcd fs_K fs_B fs_C)',
                            '  ≡ @Product_projL_func',
                            '      (Fibre_cat fs_B fs_x)',
                            '      (Fibre_cat fs_C fs_x);',
                            'assert ⊢',
                            '  @comp_fapp0 (@Catd_cat fs_K) _ _ _',
                            '    (@Product_projL_funcd fs_K fs_B fs_C)',
                            '    (@Product_pair_funcd',
                            '      fs_K fs_E fs_B fs_C fs_FF fs_GG)',
                            '  ≡ fs_FF;',
                            'symbol fs_A : Cat;',
                            'symbol fs_F : τ (Functor fs_A fs_K);',
                            'assertnot ⊢',
                            '  @Pullback_catd',
                            '    fs_A fs_K',
                            '    (@comp_cat_fapp0',
                            '      fs_K',
                            '      (Product_cat Cat_cat Cat_cat)',
                            '      Cat_cat',
                            '      (@uncurry_func Cat_cat Cat_cat Cat_cat',
                            '        Product_cat_func)',
                            '      (Struct_sigma fs_B fs_C))',
                            '    fs_F',
                            '  ≡ @comp_cat_fapp0',
                            '      fs_A',
                            '      (Product_cat Cat_cat Cat_cat)',
                            '      Cat_cat',
                            '      (@uncurry_func Cat_cat Cat_cat Cat_cat',
                            '        Product_cat_func)',
                            '      (Struct_sigma',
                            '        (@Pullback_catd fs_A fs_K fs_B fs_F)',
                            '        (@Pullback_catd fs_A fs_K fs_C fs_F));'
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
