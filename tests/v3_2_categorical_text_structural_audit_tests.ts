/**
 * Focused executable SYNTAX-PARITY-1B0 structural-text audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextStructuralAuditError,
    validateCoreCategoricalTextStructuralAudit
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

const cloneAudit = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code: CoreCategoricalTextStructuralAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalTextStructuralAudit(audit),
        error =>
            error instanceof CoreCategoricalTextStructuralAuditError &&
            error.code === code
    );
};

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-text-structural-audit.emdash',
        profile: 'fibred-weaken-reindex-1'
    });
    const K = program.category('structural_audit_K');
    const E = program.displayedFamily('structural_audit_E', K);
    const D = program.displayedFamily('structural_audit_D', K);
    const s = program.section('structural_audit_s', D);
    return {
        program,
        K,
        E,
        D,
        s
    };
};

describe('SYNTAX-PARITY-1B0 structural text audit', () => {
    it('pins the exact current contextual-index presentation seam', () => {
        const audit = CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT;
        assert.equal(
            audit.prerequisite.textRevision,
            'SYNTAX-PARITY-1A-CATEGORICAL-TEXT-1'
        );
        assert.equal(
            audit.measuredSeam.exactSource,
            'λ^fd a : E. s (indexOf a)'
        );
        assert.deepEqual(audit.measuredSeam.currentTextFailure, {
            phase: 'resolution',
            code: 'UNKNOWN_IDENTIFIER',
            identifier: 'indexOf',
            startColumn: 16,
            endColumn: 23
        });
    });

    it('executes the already available direct weakening target', () => {
        const {
            program,
            E,
            D,
            s
        } = fixture();
        const direct = program.displayedFunctorLambda(
            'a',
            E,
            D,
            a => program.apply(s, program.indexOf(a))
        );
        const compiled = program.compile(direct);
        assert.equal(
            compiled.abstractions.at(-1)?.rule,
            'categorical.displayed-functor-weakening'
        );
        assert.match(
            compiled.explicitCore,
            /emdash\.categorical\.section-pullback/u
        );
        assert.match(
            compiled.explicitCore,
            /emdash\.categorical\.sigma-first-projection/u
        );
    });

    it('freezes the narrow 1B split and indexOf-first proposal', () => {
        const audit = CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT;
        assert.deepEqual(
            audit.oneBSplit.map(entry => entry.row),
            [
                'SYNTAX-PARITY-1B1',
                'SYNTAX-PARITY-1B2',
                'SYNTAX-PARITY-1B3'
            ]
        );
        assert.equal(
            audit.firstProposal.gate,
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-02'
        );
        assert.deepEqual(audit.firstProposal.operation, {
            sourceName: 'indexOf',
            arity: 1,
            directMethod: 'indexOf',
            admissibleArgument:
                'an active callback-local displayed slot accepted by the ' +
                'existing categorical program'
        });
        assert.equal(
            audit.firstProposal.reviewerPreset.id,
            'displayed-functor-weakening'
        );
    });

    it('is deeply frozen, validates, and installs no behavior', () => {
        assertDeepFrozen(CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextStructuralAudit()
        );
        assert.equal(
            Object.values(
                CORE_CATEGORICAL_TEXT_STRUCTURAL_AUDIT.semanticDelta
            ).some(value => value !== 0),
            false
        );
    });

    it('fails closed on prerequisite, measurement, split, and proposal drift',
        () => {
            assertAuditError(
                audit => {
                    audit.prerequisite.textRevision = 'stale';
                },
                'TEXT_STRUCTURAL_PREREQUISITE_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.measuredSeam.currentTextFailure.code = 'stale';
                },
                'TEXT_STRUCTURAL_MEASUREMENT_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.oneBSplit[0].row =
                        'SYNTAX-PARITY-1B3';
                },
                'TEXT_STRUCTURAL_SPLIT_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.firstProposal.operation.arity = 2;
                },
                'TEXT_STRUCTURAL_PROPOSAL_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.semanticDelta.textResolverBranches = 1;
                },
                'TEXT_STRUCTURAL_BOUNDARY_DRIFT'
            );
        });
});
