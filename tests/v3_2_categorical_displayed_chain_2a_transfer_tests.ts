/**
 * DISPLAYED-CHAIN-2A isolated generic transfer-closure evidence.
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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_POLICY,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_SOURCE_SHA256,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_POLICY,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY,
    compileCoreCategoricalDisplayedChain2aClosureRuntime,
    compileCoreCategoricalDisplayedChain2aClosureTransfer
} from '../src/v3_2';

const activeKernelPath = resolve(
    __dirname,
    '..',
    'emdash2',
    'emdash3_2.lp'
);

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('DISPLAYED-CHAIN-2A isolated generic transfer closure', () => {
    it('pins the active source and exact existing-owner boundary', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(source)
                .digest('hex'),
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_SOURCE_SHA256
        );
        assert.match(
            source,
            /rule @fdapp1_int_cell[\s\S]*@Product_pair_funcd/u
        );
        const boundary =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY;
        assert.deepEqual(
            boundary.existingDeclarationNames,
            ['sigma_Fst', 'sigma_Snd', 'Product_grpd']
        );
        assert.deepEqual(
            [
                boundary.localExistingDeclarationCount,
                boundary.relocatedExistingDeclarationCount,
                boundary.localContinuationRuntimeRuleCount,
                boundary.inheritedContinuationRuntimeRuleCount,
                boundary.totalContinuationRuntimeRuleCount
            ],
            [0, 3, 4, 5, 9]
        );
        assert.deepEqual(
            [
                boundary.activeMathematicalSymbolDelta,
                boundary.activeRuntimeRuleDelta,
                boundary.activeProofRuleDelta
            ],
            [0, 1, 0]
        );
        assert.equal(boundary.completedChain1MutatedInPlace, false);
        assert.equal(boundary.allEntriesUseGenericTransferEngines, true);
        assertDeepFrozen(boundary);
    });

    it('checks four local rules and inherits the relocated five', () => {
        const compilation =
            compileCoreCategoricalDisplayedChain2aClosureTransfer();
        const boundary =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY;
        assert.deepEqual(compilation.compiled.declarations, []);
        assert.deepEqual(
            compilation.runtime.ruleIds,
            [
                ...boundary.localExactExistingRuntimeRuleIds,
                ...boundary.newRuntimeRuleIds
            ]
        );
        for (const id of [
            ...boundary.relocatedGenericProductRuntimeRuleIds,
            ...boundary.derivedRuntimeRuleIds
        ]) {
            assert.equal(
                compilation.runtime.ruleIds.includes(id),
                false
            );
            assert.equal(
                compilation.composedRuntime.ruleIds.filter(candidate =>
                    candidate === id
                ).length,
                1
            );
        }
        assert.equal(
            compilation.runtime.rules.every(rule =>
                rule.subjectValidation.kind === 'typescript-checked'
            ),
            true
        );
        assert.doesNotThrow(
            () => compilation.compiled.createChecker()
                .validateEnvironment()
        );
    });

    it('keeps product runtime compilation browser-safe and review-identical',
        () => {
            const programSource = readFileSync(
                resolve(
                    __dirname,
                    '..',
                    'src',
                    'v3_2',
                    'categorical_program.ts'
                ),
                'utf8'
            );
            assert.match(
                programSource,
                /compileCoreCategoricalDisplayedChain2aClosureRuntime/u
            );
            assert.doesNotMatch(
                programSource,
                /require\([\s\S]{0,120}categorical_displayed_chain_2a/u
            );
            assert.equal(
                compileCoreCategoricalDisplayedChain2aClosureRuntime(),
                compileCoreCategoricalDisplayedChain2aClosureTransfer()
            );
        });

    it('honors the selected generic budget without changing Core default',
        () => {
            const compilation =
                compileCoreCategoricalDisplayedChain2aClosureTransfer();
            const boundary =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY;
            assert.equal(
                compilation.compiled.comparisonStepLimit,
                boundary.continuationComparisonStepLimit
            );
            assert.equal(
                compilation.runtimeFragment.localProgram
                    .comparisonStepLimit,
                boundary.continuationComparisonStepLimit
            );
            assert.equal(
                boundary.defaultCoreComparisonStepLimit,
                256
            );
            assert.deepEqual(
                [
                    boundary.intrinsicCoreOwnerDelta,
                    boundary.ownerSpecificCheckerOrEvaluatorDelta,
                    boundary.externalSubjectReductionOracleCount
                ],
                [0, 0, 0]
            );
        });

    it('inherits the predecessor runtime without adding 2a rules to it',
        () => {
            const compilation =
                compileCoreCategoricalDisplayedChain2aClosureTransfer();
            assert.deepEqual(
                compilation.prerequisite.runtime.ruleIds,
                [
                    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                        .newRuntimeRuleIds,
                    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                        .transferredExistingIdentityRuntimeRuleIds
                ]
            );
            assert.equal(
                compilation.prerequisite.runtime.ruleIds.some(id =>
                    id.includes('displayed-chain-2a')
                ),
                false
            );
            assert.equal(
                compilation.composedRuntime.ruleIds.slice(-4)
                    .every(id => id.includes(
                        'categorical.displayed-chain-2a.'
                    )),
                true
            );
        });

    it('uses only the reviewed generic declaration and runtime policies',
        () => {
            assert.equal(
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE
                    .declarations.length,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_MODULE
                    .runtimeRules.length,
                4
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_POLICY
                    .entries.map(entry => entry.policy),
                []
            );
            assert.equal(
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_POLICY
                    .entries.every(entry =>
                        entry.policy === 'runtime-rewrite'
                    ),
                true
            );
        });
});
