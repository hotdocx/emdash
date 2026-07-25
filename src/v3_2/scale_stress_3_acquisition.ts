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
            'sha256:f438985ca874f1037e9a63b597e58883d0c0fcc86434117a125297592739c613',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:355bd868c33553e0c7488a181d7c58661471fc2c878e63d5ceba296d26c056a0',
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
 * The transparent Hom declaration is exact fold evidence for its existing
 * semantic Core owner. The identity-arrow/functor declarations and object
 * rule are the exact source-prior computation needed to check the two
 * transparent comparison bodies. Tensor/product action is deliberately not
 * selected by this contract.
 */
export const CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision:
            'SCALE-STRESS-3-PROFUNCTOR-COMPARISON-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2',
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceSha256:
            'sha256:f438985ca874f1037e9a63b597e58883d0c0fcc86434117a125297592739c613',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:355bd868c33553e0c7488a181d7c58661471fc2c878e63d5ceba296d26c056a0',
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
