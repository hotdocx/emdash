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
