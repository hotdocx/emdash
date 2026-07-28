/**
 * DISPLAYED-EVAL-1A generic declaration/runtime transfer evidence.
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
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_POLICY,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_POLICY,
    compileCoreCategoricalDisplayedEvaluationTransfer
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

describe('DISPLAYED-EVAL-1A generic transfer', () => {
    it('separates existing prerequisites from the exact semantic delta', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .existingPrerequisiteDeclarationNames,
            [
                'Functor_catd',
                'Terminal_func',
                'const_section_func'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .existingPrerequisiteRuntimeRuleIds,
            [
                'categorical.displayed-evaluation.' +
                    'stable-functor-family-fibre'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newOwnerNames,
            ['Eval_funcd', 'Terminal_funcd']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newRuntimeRuleIds,
            [
                'categorical.displayed-evaluation.component',
                'categorical.displayed-terminal.component'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount,
            2
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newMathematicalRuntimeRuleCount,
            2
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newIntrinsicCoreOwnerCount,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .genericFappTappCoherenceRuleCount,
            0
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
        );
    });

    it('pins the active source bytes and exact owner positions', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(source)
                .digest('hex'),
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256
        );
        assert.match(
            source,
            /injective symbol Eval_funcd \[K A : Cat\]/u
        );
        assert.match(
            source,
            /injective symbol Terminal_funcd \[K : Cat\]/u
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE
                .declarations.length,
            2
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE
                .runtimeRules.length,
            2
        );
    });

    it('checks every signature and runtime subject in TypeScript', () => {
        const compilation =
            compileCoreCategoricalDisplayedEvaluationTransfer();
        assert.deepEqual(
            compilation.prerequisiteCompiled.declarations.map(
                declaration => ({
                    name: declaration.symbol.name,
                    status: declaration.status,
                    hasBody: declaration.body !== undefined
                })
            ),
            [
                {
                    name: 'Functor_catd',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Terminal_func',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'const_section_func',
                    status: 'installed-opaque',
                    hasBody: false
                }
            ]
        );
        assert.deepEqual(
            compilation.compiled.declarations.map(declaration => ({
                name: declaration.symbol.name,
                status: declaration.status,
                hasBody: declaration.body !== undefined
            })),
            [
                {
                    name: 'Eval_funcd',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Terminal_funcd',
                    status: 'installed-opaque',
                    hasBody: false
                }
            ]
        );
        assert.deepEqual(
            compilation.prerequisiteRuntimeFragment.localProgram.rules
                .map(rule => rule.subjectValidation.kind),
            ['typescript-checked']
        );
        assert.deepEqual(
            compilation.runtime.rules.map(
                rule => rule.subjectValidation.kind
            ),
            ['typescript-checked', 'typescript-checked']
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-3),
            [
                'categorical.displayed-evaluation.' +
                    'stable-functor-family-fibre',
                'categorical.displayed-evaluation.component',
                'categorical.displayed-terminal.component'
            ]
        );
        assert.doesNotThrow(
            () => compilation.compiled.createChecker()
                .validateEnvironment()
        );
    });

    it('uses only generic transfer policies and capped component owners', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_POLICY
                .entries.map(entry => entry.policy),
            ['opaque-signature', 'opaque-signature']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_POLICY
                .entries.map(entry => entry.policy),
            ['runtime-rewrite', 'runtime-rewrite']
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE
                .runtimeRules.every(rule =>
                    rule.sourceOwner.name === 'tapp0_fapp0'
                ),
            true
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE
                .runtimeRules.some(rule =>
                    /identity|composition|naturality/u.test(rule.id)
                ),
            false
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE
        );
    });
});
