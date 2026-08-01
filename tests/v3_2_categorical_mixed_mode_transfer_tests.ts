/**
 * MIXED-NEST-0A existing-authority generic transfer evidence.
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
    CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES,
    CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE,
    CORE_CATEGORICAL_MIXED_MODE_RUNTIME_POLICY,
    CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    CORE_CATEGORICAL_MIXED_MODE_SYMBOLS,
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE,
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_POLICY,
    CoreCategoricalMixedModeSymbolId,
    compileCoreCategoricalMixedModeTransfer,
    coreCategoricalMixedModeCoreName
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

describe('MIXED-NEST-0A generic transfer', () => {
    it('pins exactly two existing owners and four existing rules', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY.declarationNames,
            ['Hom_catd', 'Transf_catd']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY.runtimeRuleIds,
            [
                'categorical.mixed-mode.displayed-opposite-fibre',
                'categorical.mixed-mode.hom-family-fibre',
                'categorical.mixed-mode.transfor-family-fibre',
                'categorical.mixed-mode.functor-hom-fold'
            ]
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .activeLambdapiOwnerDelta,
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .activeLambdapiRuleDelta,
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .ownerSpecificCheckerOrEvaluatorDelta,
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .externalCoherenceEvidenceDelta,
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .nestedAbstractionLowererDelta,
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
                    .textOrBrowserDelta
            ],
            [0, 0, 0, 0, 0, 0, 0]
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY
        );
    });

    it('uses one immutable Core-name contract for transfer linkage', () => {
        for (const id of Object.keys(
            CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES
        ) as CoreCategoricalMixedModeSymbolId[]) {
            const symbol = CORE_CATEGORICAL_MIXED_MODE_SYMBOLS[id];
            const link =
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE.entries
                    .find(candidate =>
                        candidate.symbol.moduleId === symbol.moduleId &&
                        candidate.symbol.name === symbol.name
                    );
            assert.equal(
                link?.kind === 'free-declaration'
                    ? link.coreName
                    : undefined,
                CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES[id]
            );
            assert.equal(
                coreCategoricalMixedModeCoreName(id),
                CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES[id]
            );
        }
        assertDeepFrozen(CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES);
    });

    it('pins active source bytes and owner/rule positions', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(source)
                .digest('hex'),
            CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256
        );
        assert.match(
            source,
            /injective symbol Hom_catd \[K : Cat\]/u
        );
        assert.match(
            source,
            /injective symbol Transf_catd \[K : Cat\]/u
        );
        assert.match(
            source,
            /rule @Hom_catd \$K \(@Functor_catd \$K \$A \$B\) \$FF \$GG/u
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE
                .declarations.length,
            2
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE
                .runtimeRules.length,
            4
        );
    });

    it('subject-checks every signature and runtime rule generically', () => {
        const compilation =
            compileCoreCategoricalMixedModeTransfer();
        assert.deepEqual(
            compilation.compiled.declarations.map(declaration => ({
                name: declaration.symbol.name,
                status: declaration.status,
                hasBody: declaration.body !== undefined
            })),
            [
                {
                    name: 'Hom_catd',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Transf_catd',
                    status: 'installed-opaque',
                    hasBody: false
                }
            ]
        );
        assert.deepEqual(
            compilation.runtime.rules.map(rule =>
                rule.subjectValidation.kind
            ),
            [
                'typescript-checked',
                'typescript-checked',
                'typescript-checked',
                'typescript-checked'
            ]
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-4),
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY.runtimeRuleIds
        );
        assert.doesNotThrow(
            () => compilation.compiled.createChecker()
                .validateEnvironment()
        );
    });

    it('uses only generic opaque-signature/runtime policies', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_POLICY.entries.map(
                entry => entry.policy
            ),
            ['opaque-signature', 'opaque-signature']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_MIXED_MODE_RUNTIME_POLICY.entries.map(
                entry => entry.policy
            ),
            [
                'runtime-rewrite',
                'runtime-rewrite',
                'runtime-rewrite',
                'runtime-rewrite'
            ]
        );
        assertDeepFrozen(CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE);
        assertDeepFrozen(CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE);
    });
});
