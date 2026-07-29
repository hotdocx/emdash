/**
 * Exact canonical-command acquisition contracts for the first representative
 * stress row. These contracts pin source/export evidence only; they do not
 * parse terms or install declarations and rules.
 */

import {
    CoreLfCanonicalSelectionContract,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition';

export const CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'SCALE-STRESS-1-CORE-ACQUISITION-1',
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
                id: 'outer-j.declaration',
                ordinal: 13,
                kind: 'symbol',
                textSha256:
                    'sha256:341581476ee754882c2953cac7bd649f38c24001fe9cd45a8c06a4129bd06e9d',
                name: 'ind_eqr',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'outer-j.reflexivity-beta',
                ordinal: 14,
                kind: 'rule',
                textSha256:
                    'sha256:5a4af969f473058ce7e16c00a7ebff00f39c273b936e48b35da718ddb14cbece',
                clauseCount: 1
            },
            {
                id: 'sigma.decoded-inductive',
                ordinal: 54,
                kind: 'inductive',
                textSha256:
                    'sha256:db4b03158723bda9d432dc5750a68bf36d30a40c7914034fbef5550cabd83f69',
                name: 'τΣ_',
                constructorCount: 1
            },
            {
                id: 'sigma.eliminator',
                ordinal: 63,
                kind: 'symbol',
                textSha256:
                    'sha256:e8a96705d438ed6d60682a30b0bea9b8124ac544453cb0bafa00c213dabc5e31',
                name: 'sigma_ind',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'sigma.eliminator-beta',
                ordinal: 64,
                kind: 'rule',
                textSha256:
                    'sha256:cdc48cbc3a997be41f8825b0f933015ed6151e25dfaf6eafd485cf4f8ac01526',
                clauseCount: 1
            },
            {
                id: 'pi.decoded-classifier',
                ordinal: 74,
                kind: 'symbol',
                textSha256:
                    'sha256:fe57925af572af813e027eca081bdebe09ce46f847e46b2803b1fb56e9d15b34',
                name: 'Pi_grpd',
                modifiers: ['constant'],
                hasBody: false
            },
            {
                id: 'pi.decoding-beta',
                ordinal: 75,
                kind: 'rule',
                textSha256:
                    'sha256:65f25ecd277a108aac576af30659ab8ddc08b4197f8e57d5e41ccd91c2119dad',
                clauseCount: 1
            }
        ]
    });

export const CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'SCALE-STRESS-1-NAT-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2_nat_arithmetic',
        authorityPath: 'emdash2/emdash3_2_nat_arithmetic.lp',
        sourceSha256:
            'sha256:5dca60b9137daf0772c8586e8c2214de4c6dbc6ef9488b6b19d9c0561fc5ae31',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:2fc300997b2de8d53f3cbf7822aff5dedf50edd4167d28c0f12fccc006dcf354',
            imports: ['emdash.emdash3_2']
        },
        commands: [
            {
                id: 'nat.import-core',
                ordinal: 0,
                kind: 'require',
                textSha256:
                    'sha256:7a29b814bc6a8453039145374a575129d10b968ced15f5ef020c5f51af11982d',
                open: true,
                modules: ['emdash.emdash3_2']
            },
            {
                id: 'nat.addition',
                ordinal: 3,
                kind: 'symbol',
                textSha256:
                    'sha256:959ea22ac18f66bf71a17e01501e728cd38672a9ea761e15d998e959cca646bb',
                name: 'nat_add',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'nat.addition-grouped-recursion',
                ordinal: 4,
                kind: 'rule',
                textSha256:
                    'sha256:e2dcace06e423877b877bcd9b6de49a5a8e19c185c4a2893648b4f1bbd577907',
                clauseCount: 3
            }
        ]
    });

export const CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS =
    Object.freeze([
        CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION,
        CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
    ]);
