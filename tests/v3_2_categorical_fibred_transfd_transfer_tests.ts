/**
 * Existing-authority transfer evidence for FIBRED-TRANSFD-1.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE,
    CORE_LF_SCALE_STRESS_2B3_LINKAGE,
    CoreCategoricalProgram,
    compileCoreCategoricalFibredTransfdTransfer
} from '../src/v3_2';

describe('FIBRED-TRANSFD-1 existing-authority transfer', () => {
    it('checks seven declarations, ten runtime rules, and one proof rule', () => {
        const compilation =
            compileCoreCategoricalFibredTransfdTransfer();
        assert.deepEqual(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .declarationNames,
            [
                'Transfd_cat',
                'Transfd',
                'tdapp0_fapp0',
                'id',
                'functord_transport_lhs_func',
                'functord_transport_rhs_func',
                'tdapp1_int_cell'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .declarationCount,
            7
        );
        assert.equal(compilation.runtime.rules.length, 10);
        assert.deepEqual(
            compilation.runtime.ruleIds.slice(-3),
            [
                'categorical.transfd.generic-component-identity',
                'categorical.transfd.' +
                    'displayed-component-identity.direct',
                'categorical.transfd.' +
                    'displayed-component-identity.ordinary'
            ]
        );
        assert.equal(
            compilation.runtime.rules.every(rule =>
                rule.subjectValidation.kind === 'typescript-checked'
            ),
            true
        );
        assert.deepEqual(
            compilation.proofProgram.ruleIds,
            ['categorical.transfd.direct-second-hom']
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .directOrdinaryRuntimeCategoryCollapseInstalled,
            false
        );
    });

    it('retains reviewed SCALE-STRESS-2B3 Core names', () => {
        for (const name of [
            'Transfd_cat',
            'Transfd',
            'tdapp0_fapp0'
        ]) {
            const reviewed = CORE_LF_SCALE_STRESS_2B3_LINKAGE.entries.find(
                entry => entry.symbol.name === name
            );
            const transferred =
                CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE
                    .entries.find(entry => entry.symbol.name === name);
            assert.equal(reviewed?.kind, 'free-declaration');
            assert.equal(transferred?.kind, 'free-declaration');
            if (
                reviewed?.kind !== 'free-declaration' ||
                transferred?.kind !== 'free-declaration'
            ) {
                assert.fail(`Missing free linkage for ${name}`);
            }
            assert.equal(transferred.coreName, reviewed.coreName);
        }
        const identity =
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE
                .entries.find(entry => entry.symbol.name === 'id');
        assert.equal(
            identity?.kind === 'free-declaration'
                ? identity.coreName
                : undefined,
            'emdash_v3_2_scale_stress_3a2a_id'
        );
    });

    it('preserves runtime presentations while solving proof/object bridges', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-transfd-1'
        });
        const K = emdash.category('K');
        const E = emdash.displayedFamily('E', K);
        const D = emdash.displayedFamily('D', K);
        const FF = emdash.displayedFunctor('FF', E, D);
        const GG = emdash.displayedFunctor('GG', E, D);
        const compatibility =
            emdash.displayedTransforClassifierCompatibility(
                FF,
                GG
            );
        assert.equal(
            compatibility.directOrdinaryRuntime.status,
            'not-equal'
        );
        assert.equal(
            compatibility.directOrdinaryProofTime.status,
            'solved'
        );
        assert.equal(
            compatibility.directOrdinaryObjectRuntime.status,
            'equal'
        );
        assert.equal(
            compatibility.directSigmaPiRuntime.status,
            'equal'
        );
        assert.equal(
            compatibility.directOrdinaryProofTime
                .ruleApplications[0]?.ruleId,
            'categorical.transfd.direct-second-hom'
        );
    });
});
