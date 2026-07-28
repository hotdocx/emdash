/**
 * Existing-authority transfer evidence for FIBRED-BINDER-1.
 */

import assert from 'node:assert/strict';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY,
    CORE_LF_SCALE_STRESS_2A_MODULE,
    binderMode,
    checkLambdapiProbe,
    compileCoreCategoricalFibredBinderProof,
    compileCoreCategoricalFibredBinderTransfer,
    coreCategoricalFibredBinderClassifiers,
    coreDisplayedFamilyType,
    coreLfDefinitionalCompare,
    kernelApplication,
    kernelFree,
    provenance,
    sourceSpan
} from '../src/v3_2';

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');

const fixture = () => {
    const compilation =
        compileCoreCategoricalFibredBinderTransfer();
    const nodeProvenance = provenance(
        'surface',
        'FIBRED-BINDER-1 classifier fixture',
        sourceSpan('fibred-binder-fixture.ts', 1, 1)
    );
    const mode = binderMode('explicit', 'functorial');
    let environment = compilation.compiled.environment.extend({
        name: 'K',
        type: kernelApplication(
            'category-universe',
            [],
            nodeProvenance
        ),
        mode,
        provenance: nodeProvenance
    });
    const K = kernelFree('K', nodeProvenance);
    environment = environment.extend({
        name: 'E',
        type: coreDisplayedFamilyType(K, nodeProvenance),
        mode,
        provenance: nodeProvenance
    });
    environment = environment.extend({
        name: 'D',
        type: coreDisplayedFamilyType(K, nodeProvenance),
        mode,
        provenance: nodeProvenance
    });
    const classifiers = coreCategoricalFibredBinderClassifiers(
        K,
        kernelFree('E', nodeProvenance),
        kernelFree('D', nodeProvenance),
        nodeProvenance
    );
    const proof = compileCoreCategoricalFibredBinderProof(
        compilation,
        environment
    );
    return {
        compilation,
        environment,
        classifiers,
        proof
    };
};

describe(
    'FIBRED-BINDER-1 existing Sigma/Pi transfer closure',
    () => {
        it('reuses the exact declaration, proof, and runtime closure', () => {
            const compilation =
                compileCoreCategoricalFibredBinderTransfer();
            assert.deepEqual(
                compilation.mixed.phases.map(phase => phase.kind),
                ['declaration', 'declaration', 'proof']
            );
            assert.deepEqual(
                compilation.proofProgram.ruleIds,
                ['stress.sigma-pi.uncurrying']
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2A_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                ['Catd', 'Sigma_proj1_pullback_catd']
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY
                    .newMathematicalOwnerCount,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
                2
            );
            assert.deepEqual(
                compilation.runtime.rules.map(rule => rule.id),
                [
                    'categorical.displayed-functor-composition.point',
                    'categorical.functor-composition.object'
                ]
            );
            assert.equal(
                compilation.runtime.rules.every(rule =>
                    rule.subjectValidation.kind ===
                        'typescript-checked'
                ),
                true
            );
        });

        it('solves direct/nested classifiers in both proof orientations', () => {
            const { classifiers, proof } = fixture();
            const forward = proof.compare(
                classifiers.nested,
                classifiers.direct
            );
            const symmetric = proof.compare(
                classifiers.direct,
                classifiers.nested
            );
            assert.equal(forward.status, 'solved');
            assert.equal(symmetric.status, 'solved');
            assert.equal(
                forward.ruleApplications[0]?.ruleId,
                'stress.sigma-pi.uncurrying'
            );
            assert.equal(
                symmetric.ruleApplications[0]?.orientation,
                'symmetric'
            );
        });

        it('preserves the runtime non-conversion boundary', () => {
            const {
                compilation,
                environment,
                classifiers
            } = fixture();
            const runtime = coreLfDefinitionalCompare(
                environment,
                classifiers.nested,
                classifiers.direct,
                2_000,
                undefined,
                compilation.composedRuntime
            );
            assert.equal(runtime.status, 'not-equal');
        });

        it(
            'agrees with Lambdapi on identity, composition, and classifier compatibility',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_FIBRED_BINDER_PROBES !==
                    '1'
            },
            () => {
                const result = checkLambdapiProbe(
                    {
                        source: [
                            'require open emdash.emdash3_2;',
                            'symbol fb_K : Cat;',
                            'symbol fb_E : τ (Catd fb_K);',
                            'symbol fb_D : τ (Catd fb_K);',
                            'symbol fb_Q : τ (Catd fb_K);',
                            'symbol fb_FF : τ (Functord fb_E fb_D);',
                            'symbol fb_GG : τ (Functord fb_D fb_Q);',
                            'symbol fb_x : τ (Obj fb_K);',
                            'symbol fb_u : τ ' +
                                '(Obj (Fibre_cat fb_E fb_x));',
                            'assert ⊢',
                            '  @Fibre_func',
                            '    fb_K fb_E fb_E',
                            '    (@id (@Catd_cat fb_K) fb_E)',
                            '    fb_x',
                            '  ≡ @id Cat_cat ' +
                                '(Fibre_cat fb_E fb_x);',
                            'assert ⊢',
                            '  @Fibre_func',
                            '    fb_K fb_E fb_Q',
                            '    (@comp_fapp0',
                            '      (@Catd_cat fb_K)',
                            '      fb_E fb_D fb_Q fb_GG fb_FF)',
                            '    fb_x',
                            '  ≡ @comp_fapp0',
                            '      Cat_cat',
                            '      (Fibre_cat fb_E fb_x)',
                            '      (Fibre_cat fb_D fb_x)',
                            '      (Fibre_cat fb_Q fb_x)',
                            '      (@Fibre_func',
                            '        fb_K fb_D fb_Q fb_GG fb_x)',
                            '      (@Fibre_func',
                            '        fb_K fb_E fb_D fb_FF fb_x);',
                            'assert ⊢',
                            '  @fapp0',
                            '    (Fibre_cat fb_E fb_x)',
                            '    (Fibre_cat fb_Q fb_x)',
                            '    (@Fibre_func',
                            '      fb_K fb_E fb_Q',
                            '      (@comp_fapp0',
                            '        (@Catd_cat fb_K)',
                            '        fb_E fb_D fb_Q fb_GG fb_FF)',
                            '      fb_x)',
                            '    fb_u',
                            '  ≡ @fapp0',
                            '      (Fibre_cat fb_D fb_x)',
                            '      (Fibre_cat fb_Q fb_x)',
                            '      (@Fibre_func',
                            '        fb_K fb_D fb_Q fb_GG fb_x)',
                            '      (@fapp0',
                            '        (Fibre_cat fb_E fb_x)',
                            '        (Fibre_cat fb_D fb_x)',
                            '        (@Fibre_func',
                            '          fb_K fb_E fb_D fb_FF fb_x)',
                            '        fb_u);',
                            'assert ⊢',
                            '  @eq_refl',
                            '    Cat_grpd',
                            '    (@Pi_cat',
                            '      (@Sigma_cat fb_K fb_E)',
                            '      (@Sigma_proj1_pullback_catd',
                            '        fb_K fb_E fb_D))',
                            '  : τ (@=',
                            '      Cat_grpd',
                            '      (@Pi_cat',
                            '        (@Sigma_cat fb_K fb_E)',
                            '        (@Sigma_proj1_pullback_catd',
                            '          fb_K fb_E fb_D))',
                            '      (@Functord_cat',
                            '        fb_K fb_E fb_D));',
                            'assertnot ⊢',
                            '  @Pi_cat',
                            '    (@Sigma_cat fb_K fb_E)',
                            '    (@Sigma_proj1_pullback_catd',
                            '      fb_K fb_E fb_D)',
                            '  ≡ @Functord_cat fb_K fb_E fb_D;'
                        ].join('\n'),
                        sourceMap: []
                    },
                    {
                        packageRoot: lambdapiRoot,
                        timeoutMs: 30_000
                    }
                );
                assert.equal(result.accepted, true, result.diagnostics);
                assert.equal(result.timedOut, false);
            }
        );
    }
);
