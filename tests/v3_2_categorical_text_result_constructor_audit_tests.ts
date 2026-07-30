/**
 * Focused executable SYNTAX-PARITY-1C3 result-constructor audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextError,
    CoreCategoricalTextResultConstructorAuditError,
    elaborateCoreCategoricalText,
    validateCoreCategoricalTextResultConstructorAudit
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-result-constructor-audit.emdash';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const cloneAudit = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT
));

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile
    });
    const K = program.category('result_K');
    const A = program.category('result_A');
    const C = program.category('result_C');
    const B = program.displayedFamily('result_B', K);
    const k = program.object('result_k', K);
    return {
        program,
        K,
        A,
        C,
        B,
        k
    };
};

const data = fixture();

describe('SYNTAX-PARITY-1C3 result-constructor audit', () => {
    it('anchors all selected methods in the public typed program API',
        () => {
            const methods = [
                'constantDisplayedFamily',
                'displayedFunctorFamily',
                'dependentSectionMotive',
                'dependentSectionTarget',
                'dependentSectionCategoryAt',
                'displayedProduct',
                'fibre',
                'totalCategory',
                'displayedTransforCategory',
                'functorCategory',
                'productCategory',
                'pullbackFamily',
                'substituteFamily'
            ] as const;
            methods.forEach(method =>
                assert.equal(typeof data.program[method], 'function')
            );
            assert.equal(
                data.program.compareCategories(
                    data.program.functorCategory(data.A, data.C),
                    data.program.functorCategory(data.A, data.C)
                ).status,
                'equal'
            );
    });

    it('measures the current typed-result and recursive-argument seam', () => {
        assert.throws(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'fibre B k',
                sourceFile,
                environment: [
                    { name: 'B', kind: 'displayed-family', value: data.B },
                    { name: 'k', kind: 'term', value: data.k }
                ],
                expected: { kind: 'category' } as any
            }),
            error =>
                error instanceof CoreCategoricalTextError &&
                error.code === 'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.throws(
            () => elaborateCoreCategoricalText(data.program, {
                source: 'id (fibre B k)',
                sourceFile,
                environment: [
                    { name: 'B', kind: 'displayed-family', value: data.B },
                    { name: 'k', kind: 'term', value: data.k }
                ],
                expected: { kind: 'term' }
            }),
            error =>
                error instanceof CoreCategoricalTextError &&
                error.code === 'EXPECTED_CATEGORY'
        );
    });

    it('freezes one pullback spelling for both direct aliases', () => {
        const audit =
            CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT;
        assert.equal(
            audit.measuredBoundary.directMethodCount,
            13
        );
        assert.equal(
            audit.measuredBoundary.canonicalTextHeadCount,
            12
        );
        assert.deepEqual(
            audit.measuredBoundary.normalizedAlias,
            {
                method: 'substituteFamily',
                canonicalDirectMethod: 'pullbackFamily',
                canonicalTextHead: 'pullback'
            }
        );
    });

    it('is deeply frozen, validates, and fails closed on drift', () => {
        const audit =
            CORE_CATEGORICAL_TEXT_RESULT_CONSTRUCTOR_AUDIT;
        assertDeepFrozen(audit);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextResultConstructorAudit()
        );

        const operationDrift = cloneAudit();
        operationDrift.proposal.operations[0].sourceName = 'changed';
        assert.throws(
            () => validateCoreCategoricalTextResultConstructorAudit(
                operationDrift
            ),
            error =>
                error instanceof
                    CoreCategoricalTextResultConstructorAuditError &&
                error.code === 'OPERATION_DRIFT'
        );

        const aliasDrift = cloneAudit();
        aliasDrift.measuredBoundary.normalizedAlias.canonicalTextHead =
            'substitute';
        assert.throws(
            () => validateCoreCategoricalTextResultConstructorAudit(
                aliasDrift
            ),
            error =>
                error instanceof
                    CoreCategoricalTextResultConstructorAuditError &&
                error.code === 'ALIAS_DRIFT'
        );
    });
});
