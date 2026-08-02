/**
 * Focused DISPLAYED-ND-0A read-only coherence/higher-action audit tests.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_AUDIT,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY,
    CoreCategoricalDisplayedNdAuditError,
    measureCoreCategoricalDisplayedNdCurrentEnvelope,
    validateCoreCategoricalDisplayedNdAudit
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_ND_AUDIT
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertAuditError = (
    mutate: (audit: any) => void,
    expected: CoreCategoricalDisplayedNdAuditError['code']
): void => {
    const audit = clone();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalDisplayedNdAudit(audit),
        error =>
            error instanceof CoreCategoricalDisplayedNdAuditError &&
            error.code === expected
    );
};

describe('DISPLAYED-ND-0A coherence and higher-action audit', () => {
    it('starts from the checkpointed mixed telescope and Transfd contract',
        () => {
            const prerequisite =
                CORE_CATEGORICAL_DISPLAYED_ND_AUDIT.prerequisite;
            assert.equal(
                prerequisite.displayedChain2aCheckpoint,
                '89afe5f64710b99a262ff92cb193e2742a11827f'
            );
            assert.equal(
                prerequisite.displayedChain2aReviewRevision,
                'DISPLAYED-CHAIN-2A-CLOSURE-0A-REVIEWED-1'
            );
            assert.equal(
                prerequisite.fibredTransfdContractRevision,
                'FIBRED-TRANSFD-1-DIRECT-NEXT-HOM-CONTRACT-1'
            );
            assert.equal(
                prerequisite.semanticImplementationAuthorized,
                false
            );
        });

    it('separates introduction from all three observation levels', () => {
        const audit = CORE_CATEGORICAL_DISPLAYED_ND_AUDIT;
        assert.deepEqual(
            audit.observationMatrix.map(entry => [
                entry.id,
                entry.activeKernel,
                entry.transferredToTypescript,
                entry.status
            ]),
            [
                [
                    'object-component',
                    true,
                    true,
                    'implemented'
                ],
                [
                    'point-component',
                    true,
                    true,
                    'implemented'
                ],
                [
                    'base-arrow-cell',
                    true,
                    true,
                    'implemented'
                ],
                [
                    'internal-hom-object-action',
                    true,
                    false,
                    'existing-authority-transfer-gap'
                ],
                [
                    'next-hom-action',
                    true,
                    false,
                    'existing-authority-transfer-and-surface-gap'
                ]
            ]
        );
        assert.match(
            audit.binderMeaning.importantDistinction,
            /not-a-displayed-transformation/u
        );
        assert.match(
            audit.retainedArchitecture.coherenceCriterion,
            /well-typed-outer-Transfd/u
        );
    });

    it('reproduces the current eta, object, base-arrow, and classifier envelope',
        () => {
            assert.deepEqual(
                measureCoreCategoricalDisplayedNdCurrentEnvelope(),
                {
                    etaStatus: 'equal',
                    compositeEtaStatus: 'equal',
                    componentType: 'transfor',
                    pointType: 'hom',
                    baseArrowType: 'hom',
                    directOrdinaryRuntime: 'not-equal',
                    directOrdinaryProofTime: 'solved',
                    directOrdinaryObjectRuntime: 'equal',
                    directSigmaPiRuntime: 'equal'
                }
            );
        });

    it('finds vertical component composition feasible without kernel delta',
        () => {
            const matrix =
                CORE_CATEGORICAL_DISPLAYED_ND_AUDIT
                    .introductionMatrix;
            const vertical = matrix.find(entry =>
                entry.id === 'pointwise-vertical-composition'
            );
            assert.equal(
                vertical?.status,
                'feasible-recursive-frontend-case'
            );
            assert.equal(
                vertical?.outerLowering,
                'comp_fapp0-at-Functord_cat'
            );
            assert.equal(
                vertical?.newKernelSemanticsRequired,
                false
            );
            const arbitrary = matrix.find(entry =>
                entry.id === 'arbitrary-pointwise-component-family'
            );
            assert.equal(arbitrary?.status, 'correctly-withheld');
            const mixed = matrix.find(entry =>
                entry.id === 'mixed-variance-transf-catd-section'
            );
            assert.equal(
                mixed?.status,
                'alternative-pointwise-data-presentation-only'
            );
        });

    it('pins active next-hom authority beyond the current TS transfer', () => {
        const source = readFileSync(
            'emdash2/emdash3_2.lp',
            'utf8'
        );
        const checks = readFileSync(
            'emdash2/emdash3_2_checks.lp',
            'utf8'
        );
        for (const owner of [
            'tdapp1_int_func_transfd',
            'tdapp1_int_fapp0_transfd',
            'tdapp1_int_fapp1_func_transfd',
            'fdapp1_int_transfd',
            'tdapp1_int_cell'
        ]) {
            assert.match(source, new RegExp(
                `symbol ${owner}\\b`,
                'u'
            ));
        }
        assert.match(
            checks,
            /fapp1_func _ _ \(@tdapp1_int_func_transfd/u
        );
        assert.match(
            checks,
            /@tdapp1_int_fapp1_func_transfd/u
        );
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
    });

    it('freezes the exact bounded continuation and all non-effects', () => {
        const audit = CORE_CATEGORICAL_DISPLAYED_ND_AUDIT;
        const continuation = audit.recommendedContinuation;
        assert.equal(continuation.row, 'DISPLAYED-ND-1A');
        assert.equal(
            continuation.selectedIr.tag,
            'typed-cell-composition'
        );
        assert.equal(continuation.surfaceMethod, 'composeCells');
        assert.equal(
            continuation.selectedIr.firstAcceptedClassifier,
            'indexed-transfor'
        );
        assert.deepEqual(
            [
                continuation.activeLambdapiOwnerDelta,
                continuation.activeLambdapiRuleDelta,
                continuation.typescriptTransferEntryDelta,
                continuation.intrinsicCoreOwnerDelta,
                continuation.ownerSpecificCheckerBranchDelta
            ],
            [0, 0, 0, 0, 0]
        );
        assert.equal(continuation.nextHomTransferIncluded, false);
        assert.match(
            audit.decisionQuestion,
            /D-DTTLF-USABILITY-018/u
        );
        assert.equal(
            Object.values(audit.semanticDelta).some(value =>
                value !== 0
            ),
            false
        );
        assertDeepFrozen(audit);
    });

    it('validates fail-closed drift and remains out of the browser', () => {
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedNdAudit()
        );
        assertAuditError(
            audit => {
                audit.observationMatrix.pop();
            },
            'DISPLAYED_ND_AUDIT_BOUNDARY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.semanticDelta.frontendNodes = 1;
            },
            'DISPLAYED_ND_AUDIT_AUTHORITY_DRIFT'
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_nd|DISPLAYED-ND/u
        );
    });
});
