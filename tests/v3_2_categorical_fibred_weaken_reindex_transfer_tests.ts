/**
 * Existing-authority transfer evidence for FIBRED-WEAKEN-REINDEX-1.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT,
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_MODULE,
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE,
    compileCoreCategoricalFibredWeakenReindexTransfer,
    validateCoreCategoricalFibredWeakenReindexContract
} from '../src/v3_2';

describe('FIBRED-WEAKEN-REINDEX-1 existing-authority transfer', () => {
    it('freezes the exact no-new-mathematics contract', () => {
        validateCoreCategoricalFibredWeakenReindexContract();
        assert.equal(
            Object.isFrozen(
                CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT
            ),
            true
        );
        assert.deepEqual(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT
                .qualificationCases,
            [2, 3]
        );
        assert.deepEqual(
            Object.values(
                CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT
                    .semanticDelta
            ),
            [0, 0, 0, 0, false]
        );
    });

    it('transfers four signatures and the exact six-clause closure', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE
                .declarations.map(entry => entry.symbol.name),
            [
                'Pullback_catd_func',
                'Obj_func',
                'section_pullback_func',
                'section_pullback_sec'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_MODULE
                .runtimeRules.map(rule => rule.id),
            [
                'categorical.weaken-reindex.' +
                    'constant-family-object-prerequisite',
                'categorical.weaken-reindex.' +
                    'sigma-projection-pullback-fold-prerequisite',
                'categorical.weaken-reindex.pullback-functor-object',
                'categorical.weaken-reindex.pullback-hom-component',
                'categorical.weaken-reindex.section-pullback-object',
                'categorical.weaken-reindex.section-pullback-component'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
                .newMathematicalRuntimeRuleCount,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
                .prerequisiteRuntimeRuleCount,
            2
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
                .consumerRuntimeRuleCount,
            4
        );
    });

    it('checks every runtime subject with the generic engines', () => {
        const compilation =
            compileCoreCategoricalFibredWeakenReindexTransfer();
        assert.equal(compilation.compiled.declarations.length, 4);
        assert.equal(compilation.runtime.rules.length, 6);
        assert.deepEqual(
            compilation.runtime.rules.map(rule =>
                rule.subjectValidation.kind
            ),
            [
                'typescript-checked',
                'typescript-checked',
                'typescript-checked',
                'typescript-checked',
                'typescript-checked',
                'typescript-checked'
            ]
        );
        assert.equal(
            compilation.declarationContext.declaration(
                CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE
                    .declarations[3].symbol
            )?.symbol.name,
            'section_pullback_sec'
        );
    });
});
