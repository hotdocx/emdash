/**
 * Checked canonical-command acquisition for the first SCALE-STRESS-3
 * profunctor boundary slice.
 *
 * This pins source/export identity and five non-contiguous declarations. It
 * parses no terms, installs no declaration, and grants no semantic policy.
 */

import {
    CoreLfCanonicalSelectionContract,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition';

export const CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision:
            'SCALE-STRESS-3-PROFUNCTOR-BOUNDARY-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2',
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceSha256:
            'sha256:ccda94c638af8d4fa7ce122967dcc30159c713846eedd53cee0df83123b48a11',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2',
            imports: []
        },
        commands: [
            {
                id: 'profunctor-boundary.definitional-isomorphism',
                ordinal: 577,
                kind: 'symbol',
                textSha256:
                    'sha256:fbd0fb3b99e57a60508f5f9767cb844004d049fc45ef26935c4e737e31e19727',
                name: 'DefIso',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-boundary.category',
                ordinal: 1198,
                kind: 'symbol',
                textSha256:
                    'sha256:36453cfd6b350f61f819c8affdabb63f28938c1e58476320c5a66cf8c6ffa6a5',
                name: 'Prof_cat',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-boundary.classifier',
                ordinal: 1202,
                kind: 'symbol',
                textSha256:
                    'sha256:6521af0dd45b72eefc3f0698e4673d96cbd533c2cb331998768f345b2902bf2e',
                name: 'Prof',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'profunctor-boundary.comparison',
                ordinal: 1232,
                kind: 'symbol',
                textSha256:
                    'sha256:e404fb5c06d2b8e7eb528b040ac235e8c04c975d2ae4f6c560ee245d6cf07581',
                name: 'ProfComparison',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'profunctor-boundary.tensor',
                ordinal: 1262,
                kind: 'symbol',
                textSha256:
                    'sha256:30f8e29e5ca28287fca368e0a7b84e07f32227e560bffafcbaa16b05121843fb',
                name: 'Prof_tensor',
                modifiers: [],
                hasBody: false
            }
        ]
    });

/**
 * Checked source/export selection for the comparison push/pull action.
 *
 * The transparent Hom declaration supplies the exact checked delta body for
 * its existing semantic Core owner. The identity-arrow/functor declarations
 * and object rule are the exact source-prior computation needed to check the
 * two transparent comparison bodies. Tensor/product action is deliberately
 * not selected by this contract.
 */
export const CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision:
            'SCALE-STRESS-3-PROFUNCTOR-COMPARISON-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2',
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceSha256:
            'sha256:ccda94c638af8d4fa7ce122967dcc30159c713846eedd53cee0df83123b48a11',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2',
            imports: []
        },
        commands: [
            {
                id: 'profunctor-comparison.hom-classifier',
                ordinal: 230,
                kind: 'symbol',
                textSha256:
                    'sha256:c0f833409907d500894d3be08c7b3388bc6808dc8ef40442c93f8340d2a83178',
                name: 'Hom',
                modifiers: ['injective'],
                hasBody: true
            },
            {
                id: 'profunctor-comparison.identity-arrow',
                ordinal: 232,
                kind: 'symbol',
                textSha256:
                    'sha256:76b996552e41e51e42d5c48415a920c092b1f28eca2adad2410c37a68c8e0091',
                name: 'id',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-comparison.identity-functor',
                ordinal: 406,
                kind: 'symbol',
                textSha256:
                    'sha256:926f5a5620faf25a8e71739ceb1064f37c2941b90d2be6526db83111381a0389',
                name: 'id_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'profunctor-comparison.identity-object-action',
                ordinal: 407,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:f6dc390ae49df7e4a80f7ec0d495fe050e4d089b516873e114c5190660115113'
            },
            {
                id: 'profunctor-comparison.postcomposition-action',
                ordinal: 547,
                kind: 'symbol',
                textSha256:
                    'sha256:335d0cd9720e84fda3bb58afb7d83239aac515a4802f159714b46c47ab898115',
                name: 'hom_postcomp_fapp0',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'profunctor-comparison.forward-arrow',
                ordinal: 578,
                kind: 'symbol',
                textSha256:
                    'sha256:25a5c11a10c41564747c450d9a9acaacabdb5bcfb26b79b46645b274eb53d4b2',
                name: 'defiso_to',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'profunctor-comparison.inverse-arrow',
                ordinal: 579,
                kind: 'symbol',
                textSha256:
                    'sha256:972a1a78429d92c6943a0a031461e27d9d7aa726c60f7734d343dacb74f7612b',
                name: 'defiso_from',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'profunctor-comparison.vertical-map',
                ordinal: 1204,
                kind: 'symbol',
                textSha256:
                    'sha256:d02ad09b81faea692e0b745bef7e2e9ba7e9cbbea00e3c3f88b54061ecde74a3',
                name: 'ProfMap',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'profunctor-comparison.push',
                ordinal: 1233,
                kind: 'symbol',
                textSha256:
                    'sha256:a4925ac8df4ff702218175d3e81f9d5f486bdd796a6aa148e5d4decba0e31273',
                name: 'prof_comparison_push',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'profunctor-comparison.pull',
                ordinal: 1234,
                kind: 'symbol',
                textSha256:
                    'sha256:56c6a4f2e64a60768a306446b26b2d5398b92a0b173e7d5be606b411ddbedb3b',
                name: 'prof_comparison_pull',
                modifiers: [],
                hasBody: true
            }
        ]
    });

/**
 * Checked source/export selection for product closure and fixed-endpoint
 * profunctor tensor action.
 *
 * The six declarations and five runtime clauses are the smallest audited
 * closure that types both tensor-functor action rules. Product objects decode
 * through constant-family dependent pairs, while product homs expose the
 * component pair required by the capped arrow action.
 */
export const CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision:
            'SCALE-STRESS-3-PROFUNCTOR-TENSOR-ACTION-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2',
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceSha256:
            'sha256:ccda94c638af8d4fa7ce122967dcc30159c713846eedd53cee0df83123b48a11',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2',
            imports: []
        },
        commands: [
            {
                id: 'profunctor-tensor.sigma-first',
                ordinal: 59,
                kind: 'symbol',
                textSha256:
                    'sha256:687558ab761b3fa88e307027ee894fbc747d3991a566cf311ff19fd862f851f6',
                name: 'sigma_Fst',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-tensor.sigma-second',
                ordinal: 61,
                kind: 'symbol',
                textSha256:
                    'sha256:7523d899bc0bbc2fd62cf6581f9e11bb5a86167cf351df3ee1d19e0db79b34de',
                name: 'sigma_Snd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-tensor.product-groupoid',
                ordinal: 184,
                kind: 'symbol',
                textSha256:
                    'sha256:9b31c0ca085b3a50e5fd6dac0afd1188ad6c80651b0401eb56fff9450bf3d081',
                name: 'Product_grpd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-tensor.product-groupoid-decode',
                ordinal: 185,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:0226d55b9f02c5015797c99e7ea8c787dc8ea9fa05cef89a538153dc9215ae8b'
            },
            {
                id: 'profunctor-tensor.product-category',
                ordinal: 661,
                kind: 'symbol',
                textSha256:
                    'sha256:be0837def124ded5873293c79e6281bd8eaf8e0c4ffaa79b8f04f5c2d0861163',
                name: 'Product_cat',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'profunctor-tensor.product-object',
                ordinal: 663,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:95f279aa966104a460c6c589dcaa7c31475f9d737762efcf254ebe2fb77f909d'
            },
            {
                id: 'profunctor-tensor.product-hom-category',
                ordinal: 680,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:a7bbf36dfd47ae5fa777d95ae7a40cd9dffb6ff0bb92e41b9df77b3cec5498a8'
            },
            {
                id: 'profunctor-tensor.map',
                ordinal: 1264,
                kind: 'symbol',
                textSha256:
                    'sha256:354de0e1299652c4b0102e5560a8a039fd7d1c336f64aa3a03a842b7bd3ee575',
                name: 'Prof_tensor_map',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'profunctor-tensor.functor',
                ordinal: 1265,
                kind: 'symbol',
                textSha256:
                    'sha256:77a7bc1e7a3cded3595c3c90b0791e6a1f0c021cc5910699461b7d232aca95ea',
                name: 'Prof_tensor_func',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'profunctor-tensor.object-action',
                ordinal: 1266,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:2c27c7e2c097e902a38e1dc52c0cedd78e34ae85124d0064e78151f41004ef5d'
            },
            {
                id: 'profunctor-tensor.arrow-action',
                ordinal: 1267,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:b297848e827597af12c5e0c0e0e85059b8183da0d6ce20bbf9671beae92d4c8f'
            }
        ]
    });
