/**
 * Existing-authority transfer evidence for FIBRED-TRANSFD-1.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CORE_LF_SCALE_STRESS_2B3_LINKAGE,
    CoreCategoricalProgram,
    compileCoreCategoricalFibredTransfdTransfer,
    coreCategoricalStructuralSymbolCoreName,
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance,
    serializeCoreExpression
} from '../src/v3_2';
import type {
    KernelExpression,
    Plicity
} from '../src/v3_2';

describe('FIBRED-TRANSFD-1 existing-authority transfer', () => {
    it('checks eight declarations, seventeen runtime rules, and one proof rule', () => {
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
                'tdapp1_int_cell',
                'comp_prod_fapp1_fapp0'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .declarationCount,
            8
        );
        assert.equal(compilation.runtime.rules.length, 17);
        assert.deepEqual(
            compilation.runtime.ruleIds.slice(-7),
            [
                'categorical.transfd.horizontal-component',
                'categorical.transfd.horizontal-point',
                'categorical.transfd.horizontal-full-action',
                'categorical.transfd.horizontal-capped-action',
                'categorical.transfd.identity-full-action',
                'categorical.transfd.identity-capped-action',
                'categorical.transfd.identity-base-action'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .acquiredPreExistingIdentityActionRuleCount,
            3
        );
        assert.equal(
            compilation.composedRuntime.ruleIds.filter(id =>
                id === 'categorical.displayed-hom-category.reduce'
            ).length,
            1
        );
        for (const id of [
            'categorical.fibred-product.product-pair-left.delta-beta',
            'categorical.fibred-product.product-pair-right.delta-beta'
        ]) {
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

    it('reduces horizontal full/capped action and each identity slot', () => {
        const runtime =
            compileCoreCategoricalFibredTransfdTransfer()
                .composedRuntime;
        const p = provenance(
            'derived',
            'D-061 horizontal and identity-action witness'
        );
        const free = (name: string): KernelExpression =>
            kernelFree(name, p);
        const call = (
            name: string,
            arguments_: readonly {
                readonly plicity: Plicity;
                readonly value: KernelExpression;
            }[]
        ): KernelExpression => kernelCall(
            kernelFree(name, p),
            arguments_,
            p
        );
        const X = free('horizontal_X');
        const Y = free('horizontal_Y');
        const Z = free('horizontal_Z');
        const F = free('horizontal_F');
        const FPrime = free('horizontal_F_prime');
        const H = free('horizontal_H');
        const eta = free('horizontal_eta');
        const i = free('horizontal_i');
        const j = free('horizontal_j');
        const arrow = free('horizontal_p');
        const sourceComposite = free('horizontal_HF');
        const targetComposite = free('horizontal_HF_prime');
        const cat = kernelApplication(
            'category-of-categories',
            [],
            p
        );
        const functorCategory = (
            source: KernelExpression,
            target: KernelExpression
        ): KernelExpression => call(
            coreCategoricalStructuralSymbolCoreName(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
            ),
            [
                { plicity: 'explicit', value: source },
                { plicity: 'explicit', value: target }
            ]
        );
        const productPair = (
            leftCategory: KernelExpression,
            rightCategory: KernelExpression,
            left: KernelExpression,
            right: KernelExpression
        ): KernelExpression => call(
            coreCategoricalStructuralSymbolCoreName(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.productPair
            ),
            [
                { plicity: 'implicit', value: leftCategory },
                { plicity: 'implicit', value: rightCategory },
                { plicity: 'explicit', value: left },
                { plicity: 'explicit', value: right }
            ]
        );
        const identity = (
            category: KernelExpression,
            object: KernelExpression
        ): KernelExpression => call(
            CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES.identityArrow,
            [
                { plicity: 'explicit', value: category },
                { plicity: 'explicit', value: object }
            ]
        );
        const leftFunctors = functorCategory(X, Y);
        const rightFunctors = functorCategory(Y, Z);
        const leftCells = kernelApplication(
            'transfor-category',
            [
                { value: X },
                { value: Y },
                { value: F },
                { value: FPrime }
            ],
            p
        );
        const rightCells = kernelApplication(
            'transfor-category',
            [
                { value: Y },
                { value: Z },
                { value: H },
                { value: H }
            ],
            p
        );
        const idH = identity(rightFunctors, H);
        const sourcePair = productPair(
            leftFunctors,
            rightFunctors,
            F,
            H
        );
        const targetPair = productPair(
            leftFunctors,
            rightFunctors,
            FPrime,
            H
        );
        const cellPair = productPair(
            leftCells,
            rightCells,
            eta,
            idH
        );
        const horizontal = call(
            CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES
                .horizontalCompositionAction,
            [
                { plicity: 'implicit', value: cat },
                { plicity: 'implicit', value: X },
                { plicity: 'implicit', value: Y },
                { plicity: 'implicit', value: Z },
                { plicity: 'implicit', value: sourcePair },
                { plicity: 'implicit', value: targetPair },
                { plicity: 'explicit', value: cellPair }
            ]
        );
        const full = runtime.rewriteHead(kernelApplication(
            'transfor-hom-full',
            [
                { value: X },
                { value: Z },
                { value: sourceComposite },
                { value: targetComposite },
                { value: i },
                { value: j },
                { value: horizontal }
            ],
            p
        ));
        const capped = runtime.rewriteHead(kernelApplication(
            'transfor-hom-capped',
            [
                { value: X },
                { value: Z },
                { value: sourceComposite },
                { value: targetComposite },
                { value: i },
                { value: j },
                { value: horizontal },
                { value: arrow }
            ],
            p
        ));
        assert.equal(full.status, 'rewritten');
        assert.equal(capped.status, 'rewritten');
        if (full.status !== 'rewritten' || capped.status !== 'rewritten') {
            assert.fail('Generic horizontal full/capped projection did not fire');
        }
        assert.equal(
            full.ruleId,
            'categorical.transfd.horizontal-full-action'
        );
        assert.equal(
            capped.ruleId,
            'categorical.transfd.horizontal-capped-action'
        );
        assert.match(
            serializeCoreExpression(full.after),
            /transfor-hom-full/u
        );
        assert.match(
            serializeCoreExpression(capped.after),
            /transfor-hom-capped/u
        );

        const identityFull = runtime.rewriteHead(kernelApplication(
            'transfor-hom-full',
            [
                { value: Y },
                { value: Z },
                { value: H },
                { value: H },
                { value: free('horizontal_Hi') },
                { value: free('horizontal_Hj') },
                { value: idH }
            ],
            p
        ));
        const identityCapped = runtime.rewriteHead(kernelApplication(
            'transfor-hom-capped',
            [
                { value: Y },
                { value: Z },
                { value: H },
                { value: H },
                { value: free('horizontal_Hi') },
                { value: free('horizontal_Hj') },
                { value: idH },
                { value: free('horizontal_Hp') }
            ],
            p
        ));
        const identityBase = runtime.rewriteHead(kernelApplication(
            'transfor-hom-capped',
            [
                { value: X },
                { value: Y },
                { value: F },
                { value: FPrime },
                { value: i },
                { value: i },
                { value: eta },
                { value: identity(X, i) }
            ],
            p
        ));
        assert.deepEqual(
            [identityFull, identityCapped, identityBase].map(result =>
                result.status === 'rewritten'
                    ? result.ruleId
                    : result.status
            ),
            [
                'categorical.transfd.identity-full-action',
                'categorical.transfd.identity-capped-action',
                'categorical.transfd.identity-base-action'
            ]
        );
    });
});
