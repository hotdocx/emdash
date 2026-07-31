/**
 * MIXED-NEST-ACTION-0B existing-authority transfer and typed-consumer
 * evidence.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES,
    CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_MODULE,
    CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_POLICY,
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE,
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_POLICY,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    compileCoreCategoricalMixedActionTransfer,
    coreCategoricalDisplayedNdHigherFoundationCoreName,
    coreCategoricalMixedActionCoreName,
    coreCategoricalStructuralSymbolCoreName,
    kernelApplication,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from '../src/v3_2';
import type {
    KernelExpression,
    Plicity
} from '../src/v3_2';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('MIXED-NEST-ACTION-0B', () => {
    it('pins the measured existing-authority closure', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .declarationNames,
            [
                'hom_con',
                'hom_',
                'fib_cov_tapp0_func',
                'homd_',
                'Functor_catd_fapp0_func',
                'Homd_target_section_catd',
                'homd_src_func',
                'homd_src_sec',
                'homd_tgt_func'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .declarationCount,
            9
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .runtimeRuleCount,
            12
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .reusedProofRuleCount,
            0
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .activeLambdapiOwnerDelta,
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .activeLambdapiRuleDelta,
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .ownerSpecificCheckerOrEvaluatorDelta,
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .externalCoherenceEvidenceDelta,
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .nestedAbstractionLowererDelta,
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                    .textOrBrowserDelta
            ],
            [0, 0, 0, 0, 0, 0, 0]
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE
                .declarations.length,
            9
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_MODULE
                .runtimeRules.length,
            12
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
        );
    });

    it('subject-checks every declaration and rule generically', () => {
        const compilation =
            compileCoreCategoricalMixedActionTransfer();
        assert.equal(compilation.compiled.declarations.length, 9);
        assert.equal(compilation.runtime.rules.length, 12);
        assert.equal(
            compilation.runtime.rules.every(rule =>
                rule.subjectValidation.kind === 'typescript-checked'
            ),
            true
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-12),
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .runtimeRuleIds
        );
        assert.deepEqual(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_POLICY.entries.map(
                entry => entry.policy
            ),
            [
                'opaque-signature',
                'opaque-signature',
                'checked-transparent-definition',
                'checked-transparent-definition',
                'opaque-signature',
                'checked-transparent-definition',
                'opaque-signature',
                'opaque-signature',
                'opaque-signature'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_POLICY.entries.every(
                entry => entry.policy === 'runtime-rewrite'
            ),
            true
        );
    });

    it('computes the first and final homd_int projections', () => {
        const compilation =
            compileCoreCategoricalMixedActionTransfer();
        const nodeProvenance = provenance(
            'derived',
            'MIXED-NEST-ACTION-0B runtime witness'
        );
        const K = kernelFree('mixed_action_K', nodeProvenance);
        const D = kernelFree('mixed_action_D', nodeProvenance);
        const E = kernelFree('mixed_action_E', nodeProvenance);
        const FF = kernelFree('mixed_action_FF', nodeProvenance);
        const x = kernelFree('mixed_action_x', nodeProvenance);
        const u = kernelFree('mixed_action_u', nodeProvenance);
        const y = kernelFree('mixed_action_y', nodeProvenance);
        const v = kernelFree('mixed_action_v', nodeProvenance);
        const cat = kernelApplication(
            'category-of-categories',
            [],
            nodeProvenance
        );
        const call = (
            name: string,
            arguments_: readonly {
                readonly plicity: Plicity;
                readonly value: KernelExpression;
            }[]
        ): KernelExpression => kernelCall(
            kernelFree(name, nodeProvenance),
            arguments_,
            nodeProvenance
        );
        const homdInt = call(
            coreCategoricalDisplayedNdHigherFoundationCoreName(
                'displayedInternalHom'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'implicit', value: D },
                { plicity: 'implicit', value: E },
                { plicity: 'explicit', value: FF }
            ]
        );
        const first = kernelApplication(
            'transfor-component-capped',
            [
                { value: K },
                { value: cat },
                {
                    value: kernelFree(
                        'mixed_action_inferred_source',
                        nodeProvenance
                    )
                },
                {
                    value: kernelFree(
                        'mixed_action_inferred_target',
                        nodeProvenance
                    )
                },
                { value: x },
                { value: homdInt }
            ],
            nodeProvenance
        );
        const firstRewrite =
            compilation.runtime.rewriteHead(first);
        assert.equal(firstRewrite.status, 'rewritten');
        if (firstRewrite.status !== 'rewritten') {
            assert.fail('The first homd_int projection did not reduce');
        }
        assert.equal(
            firstRewrite.ruleId,
            'categorical.mixed-action.homd-first-projection'
        );

        const homCategory = kernelApplication(
            'hom-category',
            [
                { value: K },
                { value: x },
                { value: y }
            ],
            nodeProvenance
        );
        const oppositeHom = call(
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                .oppositeCategory,
            [{ plicity: 'explicit', value: homCategory }]
        );
        const targetCategory = call(
            coreCategoricalStructuralSymbolCoreName(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
            ),
            [
                { plicity: 'explicit', value: oppositeHom },
                { plicity: 'explicit', value: cat }
            ]
        );
        const sourceFibre = kernelApplication(
            'functor-object',
            [
                { value: K },
                { value: cat },
                { value: D },
                { value: y }
            ],
            nodeProvenance
        );
        const targetFunctor = call(
            coreCategoricalMixedActionCoreName(
                'displayedHomTargetFunctor'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'implicit', value: D },
                { plicity: 'implicit', value: E },
                { plicity: 'explicit', value: FF },
                { plicity: 'explicit', value: x },
                { plicity: 'explicit', value: u },
                { plicity: 'explicit', value: y }
            ]
        );
        const final = kernelApplication(
            'functor-object',
            [
                { value: sourceFibre },
                { value: targetCategory },
                { value: targetFunctor },
                { value: v }
            ],
            nodeProvenance
        );
        const finalRewrite =
            compilation.runtime.rewriteHead(final);
        assert.equal(finalRewrite.status, 'rewritten');
        if (finalRewrite.status !== 'rewritten') {
            assert.fail('The final homd_int projection did not reduce');
        }
        assert.equal(
            finalRewrite.ruleId,
            'categorical.mixed-action.homd-final-projection'
        );
        const expected = call(
            coreCategoricalMixedActionCoreName(
                'displayedHomEndpoint'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'implicit', value: D },
                { plicity: 'implicit', value: E },
                { plicity: 'explicit', value: FF },
                { plicity: 'explicit', value: x },
                { plicity: 'explicit', value: u },
                { plicity: 'explicit', value: y },
                { plicity: 'explicit', value: v }
            ]
        );
        assert.equal(
            kernelExpressionEquals(finalRewrite.after, expected),
            true
        );
    });

    it('exposes typed internal-hom and endpoint-family consumers', () => {
        const emdash = new CoreCategoricalProgram({
            sourceFile: 'tests/fixtures/categorical-mixed-action.ts',
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('mixed_action_program_K');
        const D = emdash.displayedFamily(
            'mixed_action_program_D',
            K
        );
        const E = emdash.displayedFamily(
            'mixed_action_program_E',
            K
        );
        const FF = emdash.displayedFunctor(
            'mixed_action_program_FF',
            D,
            E
        );
        const x = emdash.object('mixed_action_program_x', K);
        const y = emdash.object('mixed_action_program_y', K);
        const u = emdash.object(
            'mixed_action_program_u',
            emdash.fibre(E, x)
        );
        const v = emdash.object(
            'mixed_action_program_v',
            emdash.fibre(D, y)
        );
        const internalHom = emdash.displayedInternalHom(FF);
        const endpoint = emdash.displayedInternalHomEndpointFamily(
            FF,
            x,
            u,
            y,
            v
        );
        const compiled = emdash.compile(internalHom);
        const endpointTotal = emdash.serializeCategory(
            emdash.totalCategory(endpoint)
        );
        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assert.match(compiled.explicitCore, /homd_int/u);
        assert.match(endpointTotal, /homd_/u);
        assert.equal(compiled.productionLambdapiDependency, false);
    });

    it('keeps the consumers behind the mixed root profile', () => {
        const emdash = new CoreCategoricalProgram({
            profile: 'fibred-displayed-nd-higher-1'
        });
        const K = emdash.category('mixed_action_gate_K');
        const D = emdash.displayedFamily('mixed_action_gate_D', K);
        const E = emdash.displayedFamily('mixed_action_gate_E', K);
        const FF = emdash.displayedFunctor(
            'mixed_action_gate_FF',
            D,
            E
        );
        assert.throws(
            () => emdash.displayedInternalHom(FF),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_MIXED_MODE'
        );
    });
});
