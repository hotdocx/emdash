/**
 * Focused DISPLAYED-ND-HIGHER-FOUNDATION-1A/D-020 transfer evidence.
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
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_BOUNDARY,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_DEPENDENCY_CORRECTION,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_POLICY,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_POLICY,
    compileCoreCategoricalDisplayedNdHigherFoundationTransfer
} from '../src/v3_2';

const activeKernelPath = resolve(
    __dirname,
    '..',
    'emdash2',
    'emdash3_2.lp'
);

const expectedDeclarations = [
    'id',
    'comp_catd_fapp0',
    'Op_func',
    'Op_catd_func',
    'hom_int',
    'Op_catd',
    'Op_funcd',
    'Functor_catd_func',
    'Edge_catd_func',
    'Presheaf_catd_func',
    'HomPresheaf_catd_func',
    'Homd_target_catd',
    'homd_int'
] as const;

const expectedPolicies = [
    'opaque-signature',
    'checked-transparent-definition',
    'opaque-signature',
    'opaque-signature',
    'opaque-signature',
    'opaque-signature',
    'opaque-signature',
    'opaque-signature',
    'checked-transparent-definition',
    'checked-transparent-definition',
    'checked-transparent-definition',
    'checked-transparent-definition',
    'opaque-signature'
] as const;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('DISPLAYED-ND-HIGHER-FOUNDATION-1A generic transfer', () => {
    it('records the exact directly approved D-020 correction', () => {
        const correction =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_DEPENDENCY_CORRECTION;
        assert.equal(
            correction.decision,
            'D-DTTLF-USABILITY-020-directly-approved-2026-07-29'
        );
        assert.deepEqual(
            correction.missingExistingCoreOwnerLinks,
            [
                { symbol: 'Obj', owner: 'object-classifier' },
                { symbol: 'Hom', owner: 'hom-classifier' }
            ]
        );
        assert.deepEqual(
            correction.missingExistingRuntimeRule,
            {
                id: 'categorical.opposite.involution',
                canonicalCommandOrdinal: 237,
                canonicalCommandText:
                    'rule Op_cat (Op_cat $A) ↪ $A;',
                canonicalCommandTextSha256:
                    'c9ff2c9e112c82facf9f1a01573c5cbf7aa9fa6cfa5458d1c46e77c94feb24ec',
                activeLambdapiRuleDelta: 0,
                typescriptRuntimeRuleDelta: 1
            }
        );
        assert.deepEqual(
            [
                correction.semanticScopeChanged,
                correction.intrinsicCoreOwnerDelta,
                correction.checkerBranchDelta,
                correction.surfaceMethodDelta
            ],
            [false, 0, 0, 0]
        );
        assertDeepFrozen(correction);
    });

    it('pins the active source and exact thirteen-declaration policy', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE
                .sourceSha256,
            'sha256:' + createHash('sha256').update(source).digest('hex')
        );
        assert.match(
            source,
            /rule Op_cat \(Op_cat \$A\) ↪ \$A;/u
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE
                .declarations.map(declaration => declaration.symbol.name),
            expectedDeclarations
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_POLICY
                .entries.map(entry => entry.policy),
            expectedPolicies
        );
    });

    it('links the omitted intrinsic owners and reuses the isolated id',
        () => {
            const links =
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
                    .entries;
            const obj = links.find(link => link.symbol.name === 'Obj');
            const hom = links.find(link => link.symbol.name === 'Hom');
            const identity = links.find(link => link.symbol.name === 'id');
            assert.deepEqual(
                obj === undefined ? undefined : {
                    kind: obj.kind,
                    owner: obj.kind === 'core-owner'
                        ? obj.owner
                        : undefined
                },
                {
                    kind: 'core-owner',
                    owner: 'object-classifier'
                }
            );
            assert.deepEqual(
                hom === undefined ? undefined : {
                    kind: hom.kind,
                    owner: hom.kind === 'core-owner'
                        ? hom.owner
                        : undefined
                },
                {
                    kind: 'core-owner',
                    owner: 'hom-classifier'
                }
            );
            assert.equal(
                identity?.kind === 'free-declaration'
                    ? identity.coreName
                    : undefined,
                'emdash_v3_2_scale_stress_3a2a_id'
            );
        });

    it('checks all transparent bodies and preserves opaque interfaces',
        () => {
            const compilation =
                compileCoreCategoricalDisplayedNdHigherFoundationTransfer();
            assert.deepEqual(
                compilation.compiled.declarations.map(declaration => ({
                    name: declaration.symbol.name,
                    status: declaration.status,
                    hasBody: declaration.body !== undefined
                })),
                expectedDeclarations.map((name, index) => ({
                    name,
                    status: expectedPolicies[index] ===
                        'checked-transparent-definition'
                        ? 'installed-transparent'
                        : 'installed-opaque',
                    hasBody: expectedPolicies[index] ===
                        'checked-transparent-definition'
                }))
            );
            assert.doesNotThrow(
                () => compilation.compiled.createChecker()
                    .validateEnvironment()
            );
        });

    it('compiles only the existing opposite-involution runtime rule',
        () => {
            const compilation =
                compileCoreCategoricalDisplayedNdHigherFoundationTransfer();
            assert.deepEqual(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_MODULE
                    .runtimeRules.map(rule => rule.id),
                ['categorical.opposite.involution']
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_POLICY
                    .entries.map(entry => entry.policy),
                ['runtime-rewrite']
            );
            assert.deepEqual(
                compilation.runtime.ruleIds,
                ['categorical.opposite.involution']
            );
            assert.equal(
                compilation.runtime.rules[0]?.subjectValidation.kind,
                'typescript-checked'
            );
            assert.deepEqual(
                compilation.composedRuntime.ruleIds,
                [
                    ...compilation.prerequisite.composedRuntime.ruleIds,
                    'categorical.opposite.involution'
                ]
            );
        });

    it('keeps the target package and product surface outside foundation',
        () => {
            const boundary =
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_BOUNDARY;
            assert.deepEqual(
                [
                    boundary.declarationCount,
                    boundary.checkedTransparentDefinitionCount,
                    boundary.opaqueSignatureCount,
                    boundary.runtimeRuleCount,
                    boundary.activeLambdapiOwnerDelta,
                    boundary.activeLambdapiRuleDelta,
                    boundary.intrinsicCoreOwnerDelta,
                    boundary.ownerSpecificCheckerOrEvaluatorDelta,
                    boundary.surfaceMethodDelta,
                    boundary.targetOwnersIncluded,
                    boundary.targetProjectionRulesIncluded
                ],
                [13, 5, 8, 1, 0, 0, 0, 0, 0, false, false]
            );
            assert.equal(
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE
                    .declarations.some(declaration =>
                        declaration.symbol.name.startsWith('tdapp1_int_')
                    ),
                false
            );
            assert.doesNotMatch(
                readFileSync('src/v3_2/browser.ts', 'utf8'),
                /displayed_nd_higher_foundation|opposite\.involution/u
            );
            assertDeepFrozen(boundary);
        });
});
