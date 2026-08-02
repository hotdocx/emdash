/**
 * DISPLAYED-CHAIN-1A generic declaration/runtime transfer evidence.
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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_POLICY,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_POLICY,
    compileCoreCategoricalDisplayedChainTransfer
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

describe('DISPLAYED-CHAIN-1A generic transfer', () => {
    it('separates existing acquisition from the one-owner delta', () => {
        const boundary =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY;
        assert.deepEqual(
            boundary.existingPrerequisiteDeclarationNames,
            [
                'sigma_map_func',
                'fdapp1_int_cell',
                'fdapp1_int_hom_fapp0'
            ]
        );
        assert.deepEqual(
            boundary.ambientPrerequisiteDeclarationNames,
            ['Terminal_obj', 'Const_func']
        );
        assert.deepEqual(
            boundary.checkedTransparentMirrorDeclarationNames,
            ['Obj_func__displayed_chain_mirror']
        );
        assert.equal(
            boundary.approvedExistingDeclarationPrerequisiteCount,
            5
        );
        assert.equal(boundary.totalGenericTransferDeclarationCount, 6);
        assert.equal(
            boundary.checkedTransparentMirrorAddsBackendOwnerCount,
            0
        );
        assert.deepEqual(
            boundary.newOwnerNames,
            ['sigma_functord_sec']
        );
        assert.equal(boundary.newMathematicalOwnerCount, 1);
        assert.equal(boundary.newMathematicalRuntimeRuleCount, 6);
        assert.equal(boundary.newMathematicalProofRuleCount, 0);
        assert.equal(boundary.newIntrinsicCoreOwnerCount, 0);
        assert.equal(boundary.genericFappTappCoherenceRuleCount, 0);
        assertDeepFrozen(boundary);
    });

    it('checks all declarations and preserves transparent definitions', () => {
        const compilation =
            compileCoreCategoricalDisplayedChainTransfer();
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
                    name: 'Terminal_obj',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Const_func',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Obj_func__displayed_chain_mirror',
                    status: 'installed-transparent',
                    hasBody: true
                },
                {
                    name: 'sigma_map_func',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'fdapp1_int_cell',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'fdapp1_int_hom_fapp0',
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
            [{
                name: 'sigma_functord_sec',
                status: 'installed-opaque',
                hasBody: false
            }]
        );
        assert.deepEqual(
            compilation.prerequisite.prerequisite.prerequisite
                .prerequisite.compiled.declarations
                .filter(declaration =>
                    [
                        'functord_transport_lhs_func',
                        'functord_transport_rhs_func'
                    ].includes(declaration.symbol.name)
                )
                .map(declaration => ({
                    name: declaration.symbol.name,
                    status: declaration.status,
                    hasBody: declaration.body !== undefined
                })),
            [
                {
                    name: 'functord_transport_lhs_func',
                    status: 'installed-transparent',
                    hasBody: true
                },
                {
                    name: 'functord_transport_rhs_func',
                    status: 'installed-transparent',
                    hasBody: true
                }
            ]
        );
        assert.equal(
            compilation.prerequisiteCompiled.createChecker()
                .validateEnvironment(),
            undefined
        );
        assert.equal(
            compilation.compiled.createChecker().validateEnvironment(),
            undefined
        );
    });

    it('checks the exact prerequisite and semantic runtime closures', () => {
        const compilation =
            compileCoreCategoricalDisplayedChainTransfer();
        const boundary =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY;
        assert.deepEqual(
            boundary.exactExistingRuntimeRuleIds,
            [
                'categorical.displayed-chain.sigma-map-object',
                'categorical.displayed-chain.sigma-map-structured-arrow',
                'categorical.displayed-chain.' +
                    'sigma-projection-pullback-object-prerequisite',
                'categorical.displayed-chain.' +
                    'constant-functor-object-prerequisite',
                'categorical.displayed-chain.' +
                    'constant-family-structured-arrow-prerequisite'
            ]
        );
        assert.deepEqual(
            boundary.normalFormSpecializationRuleIds,
            [
                'categorical.displayed-chain.' +
                    'section-object.delta-normalize'
            ]
        );
        assert.deepEqual(
            boundary.newRuntimeRuleIds,
            [
                'categorical.displayed-chain.' +
                    'sigma-first-projection-structured-arrow',
                'categorical.displayed-chain.' +
                    'sigma-projection-pullback-structured-arrow',
                'categorical.displayed-chain.' +
                    'sigma-functord-section-object',
                'categorical.displayed-chain.' +
                    'sigma-functord-section-structured-arrow',
                'categorical.displayed-chain.' +
                    'section-pullback-direct-object',
                'categorical.displayed-chain.' +
                    'section-pullback-direct-arrow'
            ]
        );
        assert.deepEqual(
            boundary.transferredExistingIdentityRuntimeRuleIds,
            [
                'categorical.displayed-chain.' +
                    'internal-cell-identity.direct',
                'categorical.displayed-chain.' +
                    'internal-cell-identity.ordinary'
            ]
        );
        assert.deepEqual(
            compilation.prerequisiteRuntimeFragment.localProgram.ruleIds,
            boundary.existingPrerequisiteRuntimeRuleIds
        );
        assert.deepEqual(
            compilation.runtime.ruleIds,
            [
                ...boundary.newRuntimeRuleIds,
                ...boundary.transferredExistingIdentityRuntimeRuleIds
            ]
        );
        assert.equal(
            compilation.prerequisiteRuntimeFragment.localProgram.rules
                .every(rule =>
                    rule.subjectValidation.kind === 'typescript-checked'
                ),
            true
        );
        assert.equal(
            compilation.runtime.rules.every(rule =>
                rule.subjectValidation.kind === 'typescript-checked'
            ),
            true
        );
        assert.equal(compilation.composedRuntime.ruleIds.length, 114);
        assert.equal(
            compilation.composedRuntime.ruleIds.some(ruleId =>
                /diagnostic/u.test(ruleId)
            ),
            false
        );
    });

    it('pins active source bytes and deterministic backend linkage', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(source)
                .digest('hex'),
            CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256
        );
        assert.match(
            source,
            /injective symbol sigma_functord_sec \[K : Cat\]/u
        );
        assert.match(
            source,
            /rule @fdapp1_int_cell\s+\(@Sigma_cat \$K \$R\)/u
        );
        const mirrorLink =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE
                .entries.find(entry =>
                    entry.symbol.name ===
                        'Obj_func__displayed_chain_mirror'
                );
        assert.equal(mirrorLink?.kind, 'free-declaration');
        if (mirrorLink?.kind !== 'free-declaration') {
            assert.fail('Missing checked Obj_func mirror linkage');
        }
        assert.equal(mirrorLink.backendName, 'Obj_func');
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_POLICY
                .entries.find(entry =>
                    entry.target.kind === 'declaration' &&
                    entry.target.symbol.name ===
                        'Obj_func__displayed_chain_mirror'
                )?.policy,
            'checked-transparent-definition'
        );
    });

    it('deep-freezes every transfer input', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_POLICY
                .entries.map(entry => entry.policy),
            ['opaque-signature']
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE
                .declarations.length,
            6
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE
                .declarations.length,
            1
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE
                .runtimeRules.length,
            6
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE
                .runtimeRules.length,
            8
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_POLICY
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE
        );
    });
});
