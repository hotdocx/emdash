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

/**
 * Checked source/export selection for the internal/pullback dependent-Pi
 * runtime slice. Existing continuation and SCALE-STRESS-2A declarations are
 * reused later by qualified identity; this contract pins every additional
 * declaration and prerequisite rule selected by 2B1.
 */
export const CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'SCALE-STRESS-2-INTERNAL-PI-ACQUISITION-1',
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
                id: 'internal-pi.opposite-category',
                ordinal: 236,
                kind: 'symbol',
                textSha256:
                    'sha256:ba6fcaccdc6912593ab52efeb68b485312e2cfdeb2c85e27fbf7ed0b15bb0e8d',
                name: 'Op_cat',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'internal-pi.opposite-object',
                ordinal: 238,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:453da01adc70028cd130c2f7d83d93d0a059e388637bab25a2b91a732cc4aeff'
            },
            {
                id: 'internal-pi.displayed-functor-classifier',
                ordinal: 394,
                kind: 'symbol',
                textSha256:
                    'sha256:340ce5f763e5a50f6e58402526c66ac4de7fb49b60c42f4aa08deb3b75bd0941',
                name: 'Functord',
                modifiers: ['injective'],
                hasBody: true
            },
            {
                id: 'internal-pi.displayed-category-functor',
                ordinal: 538,
                kind: 'symbol',
                textSha256:
                    'sha256:8d0531d40ff16b0081941883ca306c2e7832a161f79c04f8833fc579a90b8267',
                name: 'Catd_cat_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'internal-pi.pullback-family',
                ordinal: 926,
                kind: 'symbol',
                textSha256:
                    'sha256:d6c5bfa07c17effbf4109627d46b29e38f061c2a5fd24b6d0d346b76db5b6021',
                name: 'Pullback_catd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'internal-pi.pullback-fibre',
                ordinal: 927,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:bfa34e6ee270b4024e9c9cb1d692c38cb3e430fc443f8237612151e04679f88a'
            },
            {
                id: 'internal-pi.pullback-family-functor',
                ordinal: 930,
                kind: 'symbol',
                textSha256:
                    'sha256:dcb8d95c6a8b2eabaeaf1b4bf4f6737dac50dddede37ab5c379f23c5ea70aa56',
                name: 'Pullback_catd_func',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'internal-pi.pullback-functor-object',
                ordinal: 931,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:07f48f70c1ac7226a64f2d035ce0c8e0bd5616a404db5e6b62f35b5cb81257be'
            },
            {
                id: 'internal-pi.constant-family',
                ordinal: 936,
                kind: 'symbol',
                textSha256:
                    'sha256:da2f154125b7695570e39150c76235a7c3253e589a5d583676ed9a8a016e5507',
                name: 'Const_catd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'internal-pi.constant-fibre',
                ordinal: 939,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:5d9db2424a5ec6ec8a161c63600a2540a22d75761fd63e9e30ea6e9603e055c6'
            },
            {
                id: 'internal-pi.constant-pullback',
                ordinal: 941,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:09d6f5f01ea17d4c7e823511f4bedb399308ad56a4dc6a398cf006ccd2e187e2'
            },
            {
                id: 'internal-pi.section-functor',
                ordinal: 969,
                kind: 'symbol',
                textSha256:
                    'sha256:4fa3de83a568d56652210c00057d070801c2034812c515f11506950ac6ebdf87',
                name: 'Pi_func',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'internal-pi.section-functor-object',
                ordinal: 970,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:c06ed4abb9a781cc3e36e3039cc8d718c15edcabd28e590f3d390fc2d740278a'
            },
            {
                id: 'internal-pi.package',
                ordinal: 972,
                kind: 'symbol',
                textSha256:
                    'sha256:a33428ba27fef5b2fbea1a232ca84c288d4b26764a47b1baa75216705fa6cdcc',
                name: 'Pi_int_funcd',
                modifiers: ['constant'],
                hasBody: false
            },
            {
                id: 'internal-pi.package-component',
                ordinal: 973,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:3ecfb99b73a2b28dbf8a7477c44bd12742f758009c1cd1ca251dd217e8e1fa04'
            },
            {
                id: 'internal-pi.pullback-package',
                ordinal: 974,
                kind: 'symbol',
                textSha256:
                    'sha256:0ed7f348ea7cfc0d1ca1841d866144ec6ada85f85f3650512733cfbe74d62147',
                name: 'Pi_pullback_funcd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'internal-pi.pullback-fold',
                ordinal: 975,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:b906d4ad5aa1c949f563064a62afffcd1092600b6769f27ebfe473839cf5b462'
            },
            {
                id: 'internal-pi.pullback-component',
                ordinal: 976,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:06ece07480974614ed337e6043129318bec8fc85b7379c68f550be8b80c6c0c0'
            }
        ]
    });

/**
 * Checked source/export selection for the internal-Pi base-arrow action.
 *
 * The six selected declarations are the smallest exact type dependency
 * closure for the two active `fdapp1_int_cell` rules. Transparent bodies
 * whose wider computation closure is not selected remain explicit policy
 * boundaries in the representation layer.
 */
export const CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'SCALE-STRESS-2-PI-BASE-ACTION-ACQUISITION-1',
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
                id: 'pi-base-action.terminal-category',
                ordinal: 512,
                kind: 'symbol',
                textSha256:
                    'sha256:cefdb784ec1b0e4011340c457ee0589cd74ceedac88ac2ee697e68f5446172fb',
                name: 'Terminal_cat',
                modifiers: ['constant'],
                hasBody: false
            },
            {
                id: 'pi-base-action.fibre-category',
                ordinal: 925,
                kind: 'symbol',
                textSha256:
                    'sha256:d7aaaf14f6f371ec87a6f2a372c51f32ba74b006508ba8669573970245dcb459',
                name: 'Fibre_cat',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'pi-base-action.transport-left',
                ordinal: 1074,
                kind: 'symbol',
                textSha256:
                    'sha256:eab1554f095d3c280f6f8e4fdae536f5deac70119f097dd980272c568d539041',
                name: 'functord_transport_lhs_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'pi-base-action.transport-right',
                ordinal: 1075,
                kind: 'symbol',
                textSha256:
                    'sha256:5e5174bcbf284984062799b12ce7eac24471f94851bc3cf922c1841fa600e9ff',
                name: 'functord_transport_rhs_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'pi-base-action.internal-cell',
                ordinal: 1095,
                kind: 'symbol',
                textSha256:
                    'sha256:8f5b9674ff6c1971047eeac626c6bf0e44fc312be9c0dea09a163373e2ec4273',
                name: 'fdapp1_int_cell',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'pi-base-action.section-pullback',
                ordinal: 1189,
                kind: 'symbol',
                textSha256:
                    'sha256:6cebfc1c0241d6b67496d63e5989e3501841b6ae19e5013ecd8484c6c48d3d57',
                name: 'section_pullback_func',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'pi-base-action.internal',
                ordinal: 1195,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:883201c0f6a0ac632fa2f2a4b6567d48d2b624c534f4987f99150ce41a3221ac'
            },
            {
                id: 'pi-base-action.pullback',
                ordinal: 1196,
                kind: 'rule',
                clauseCount: 1,
                textSha256:
                    'sha256:b0e5c0dfe9828bb32f2cf5388cbbe9a08faf6e3662dbd492f2dffab7eee4865f'
            }
        ]
    });
