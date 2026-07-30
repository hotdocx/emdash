/**
 * Focused executable SYNTAX-PARITY-1C0 constructor-text audit tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT,
    CoreCategoricalProgram,
    CoreCategoricalTextConstructorAuditError,
    validateCoreCategoricalTextConstructorAudit
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
    CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code: CoreCategoricalTextConstructorAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalTextConstructorAudit(audit),
        error =>
            error instanceof CoreCategoricalTextConstructorAuditError &&
            error.code === code
    );
};

const fixture = () => {
    const program = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-text-constructor-audit.emdash',
        profile: 'fibred-displayed-chain-2a'
    });
    const A = program.category('constructor_audit_A');
    const B = program.category('constructor_audit_B');
    const C = program.category('constructor_audit_C');
    const X = program.category('constructor_audit_X');
    const Y = program.category('constructor_audit_Y');
    const F = program.functor('constructor_audit_F', A, B);
    const G = program.functor('constructor_audit_G', B, C);
    const H = program.functor('constructor_audit_H', A, C);
    const P = program.functor('constructor_audit_P', X, Y);
    return {
        program,
        A,
        B,
        C,
        F,
        G,
        H,
        P
    };
};

describe('SYNTAX-PARITY-1C0 constructor text audit', () => {
    it('pins the exact post-1B3 ordinary-constructor seam', () => {
        const audit = CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT;
        assert.equal(
            audit.prerequisite.textRevision,
            'SYNTAX-PARITY-1B3-CATEGORICAL-TEXT-1'
        );
        assert.deepEqual(
            audit.measuredTextSurface.exactOrdinaryFailure,
            {
                source: 'compose G F',
                phase: 'resolution',
                code: 'UNKNOWN_IDENTIFIER',
                identifier: 'compose',
                startColumn: 1,
                endColumn: 8
            }
        );
    });

    it('executes all six existing ordinary structural targets', () => {
        const data = fixture();
        const terms = [
            data.program.identityFunctor(data.A),
            data.program.composeFunctors(data.G, data.F),
            data.program.functorPair(data.F, data.H),
            data.program.productMap(data.F, data.P),
            data.program.productLeftProjection(data.B, data.C),
            data.program.productRightProjection(data.B, data.C)
        ];
        assert.equal(terms.length, 6);
        for (const term of terms) {
            const compilation = data.program.compile(term);
            assert.match(compilation.explicitCore, /emdash\.categorical/u);
            assert.equal(
                data.program.inspect(term).type.tag,
                'functor'
            );
        }
    });

    it('freezes the residual inventory and bounded ordinary split', () => {
        const audit = CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT;
        assert.deepEqual(
            audit.oneCSplit.map(entry => entry.row),
            [
                'SYNTAX-PARITY-1C1',
                'SYNTAX-PARITY-1C2',
                'SYNTAX-PARITY-1C3',
                'SYNTAX-PARITY-GRADUATE-1'
            ]
        );
        assert.deepEqual(
            audit.proposal.operations.map(
                operation => operation.sourceName
            ),
            ['id', 'compose', 'pair', 'map', 'pi1', 'pi2']
        );
        assert.deepEqual(
            audit.proposal.operations.map(
                operation => operation.directMethod
            ),
            [
                'identityFunctor',
                'composeFunctors',
                'functorPair',
                'productMap',
                'productLeftProjection',
                'productRightProjection'
            ]
        );
        assert.equal(
            audit.residualInventory[2].requiredDesign.includes(
                'second checker'
            ),
            true
        );
    });

    it('is deeply frozen, validates, and installs no behavior', () => {
        assertDeepFrozen(CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextConstructorAudit()
        );
        assert.equal(
            Object.values(
                CORE_CATEGORICAL_TEXT_CONSTRUCTOR_AUDIT.semanticDelta
            ).some(value => value !== 0),
            false
        );
    });

    it('fails closed on prerequisite, measurement, inventory, proposal, and boundary drift',
        () => {
            assertAuditError(
                audit => {
                    audit.prerequisite.textRevision = 'stale';
                },
                'TEXT_CONSTRUCTOR_PREREQUISITE_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.measuredTextSurface.exactOrdinaryFailure.code =
                        'stale';
                },
                'TEXT_CONSTRUCTOR_MEASUREMENT_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.oneCSplit[0].row = 'stale';
                },
                'TEXT_CONSTRUCTOR_INVENTORY_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.proposal.operations[0].sourceName = 'stale';
                },
                'TEXT_CONSTRUCTOR_PROPOSAL_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.semanticDelta.textResolverBranches = 1;
                },
                'TEXT_CONSTRUCTOR_BOUNDARY_DRIFT'
            );
        });
});
