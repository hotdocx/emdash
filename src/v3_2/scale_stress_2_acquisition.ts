/**
 * Exact canonical-command acquisition contract for the first
 * SCALE-STRESS-2 proof-time uncurrying slice.
 *
 * The contract pins checked source/export evidence only. It parses no terms,
 * installs no proof rule, and grants no semantic or product policy.
 */

import {
    CoreLfCanonicalSelectionContract,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition';

export const CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'SCALE-STRESS-2-UNCURRYING-ACQUISITION-1',
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
                id: 'uncurrying.displayed-family-classifier',
                ordinal: 389,
                kind: 'symbol',
                textSha256:
                    'sha256:a86b833db85bb3ddff9af411f4b2341b715d631236f760f77eca3da7688bdafa',
                name: 'Catd',
                modifiers: ['injective'],
                hasBody: true
            },
            {
                id: 'uncurrying.displayed-functor-category',
                ordinal: 393,
                kind: 'symbol',
                textSha256:
                    'sha256:7e7c4977371498003ec72c3a8503db0187be1f935d3ee6fcc863e305a85d052c',
                name: 'Functord_cat',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'uncurrying.section-category',
                ordinal: 961,
                kind: 'symbol',
                textSha256:
                    'sha256:92bdb854bb5fe0d28580f6f4d8c612b898b8eac994f39fdc7f0333f75c58e0b6',
                name: 'Pi_cat',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'uncurrying.sigma-category',
                ordinal: 981,
                kind: 'symbol',
                textSha256:
                    'sha256:1a61c1de4ef87b206301c45224a66852bc723cd9b1a6cf4bc2974938a111a6cb',
                name: 'Sigma_cat',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'uncurrying.sigma-projection-pullback',
                ordinal: 991,
                kind: 'symbol',
                textSha256:
                    'sha256:f18555d66e70c8c4d8bb4629ae66aa0a3eba955e0276d47fd390ba088677e6bf',
                name: 'Sigma_proj1_pullback_catd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'uncurrying.sigma-section-comparison',
                ordinal: 995,
                kind: 'unif_rule',
                textSha256:
                    'sha256:0f0e404db54dc5af8d2db9e6965e9c018d53d61e0668d497139e6e8cd91ec99f'
            }
        ]
    });
